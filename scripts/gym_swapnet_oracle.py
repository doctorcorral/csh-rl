#!/usr/bin/env python3
"""Gymnasium adapter for swap-network action ranking synthesis.

Ranking is produced by a sorting network: a fixed sequence of swap positions,
each conditionally applied based on a binary predicate over the state.
The first element of the resulting ranking is the chosen action.

This approach decomposes the permutation search (n! rankings) into
O(n^2) independent binary predicate problems, each solvable via CSHRL
coordinate descent.

Commands:
    collect_states  — run episodes with current swap predicates, return states
    score_swap      — score candidate predicates for one swap position
    validate        — run episodes and return total reward

Protocol mirrors other Synthex oracles (JSON over temp files).
"""

import sys
import json
import numpy as np
import gymnasium as gym
from multiprocessing import Pool, cpu_count


def eval_feature(feat, state):
    kind = feat[0]
    if kind == "axis":
        return state[feat[1]] < feat[2]
    elif kind == "diag":
        return feat[3] * state[feat[1]] + state[feat[2]] < 0
    elif kind == "sq_diag":
        return feat[3] * state[feat[1]] ** 2 + state[feat[2]] < 0
    elif kind == "prod":
        return state[feat[1]] * state[feat[2]] < feat[3]
    elif kind == "swap_outcome":
        upstream_pred = feat[2]
        return eval_pred(upstream_pred, state)
    elif kind == "swap_outcome_neg":
        upstream_pred = feat[2]
        return not eval_pred(upstream_pred, state)
    return False


def eval_pred(pred, state):
    if pred is None or pred == "truep":
        return True
    if pred == "falsep":
        return False
    kind = pred[0]
    if kind == "feat":
        return eval_feature(pred[1], state)
    if kind == "not":
        return not eval_pred(pred[1], state)
    if kind == "and":
        return eval_pred(pred[1], state) and eval_pred(pred[2], state)
    if kind == "or":
        return eval_pred(pred[1], state) or eval_pred(pred[2], state)
    return False


def bubble_sort_network(n, passes=1):
    """Generate bubble sort sorting network for n elements.
    Returns list of (i, j) swap pairs where i < j."""
    single = []
    for pass_idx in range(n - 1):
        for i in range(n - 1 - pass_idx):
            single.append((i, i + 1))
    return single * passes


def apply_swap_network(base_ranking, network, swap_preds, state):
    """Apply the sorting network with predicate-controlled swaps."""
    ranking = list(base_ranking)
    for (i, j), pred in zip(network, swap_preds):
        if eval_pred(pred, state):
            ranking[i], ranking[j] = ranking[j], ranking[i]
    return ranking


def swapnet_action(base_ranking, network, swap_preds, state):
    """Get the best action from the swap network ranking."""
    ranking = apply_swap_network(base_ranking, network, swap_preds, state)
    return ranking[0]


def _run_episode(args):
    env_name, base_ranking, network, swap_preds, seed, max_steps, n_dims = args
    env = gym.make(env_name)
    obs, _ = env.reset(seed=seed)
    total_r = 0.0
    for _ in range(max_steps):
        state = obs[:n_dims].tolist()
        action = swapnet_action(base_ranking, network, swap_preds, state)
        obs, r, term, trunc, _ = env.step(action)
        total_r += r
        if term or trunc:
            break
    env.close()
    return total_r


def run_episodes(env_name, base_ranking, network, swap_preds, seeds,
                 max_steps, n_dims, parallel=False):
    args_list = [(env_name, base_ranking, network, swap_preds,
                  s, max_steps, n_dims) for s in seeds]
    if parallel and len(args_list) > 8:
        n_workers = min(cpu_count(), len(args_list), 8)
        with Pool(processes=n_workers) as pool:
            results = pool.map(_run_episode, args_list,
                               chunksize=max(1, len(args_list) // (n_workers * 2)))
    else:
        results = [_run_episode(a) for a in args_list]
    total = sum(results)
    successes = sum(1 for r in results if r > 100)
    return total, successes


def collect_states(env_name, base_ranking, network, swap_preds, seeds,
                   max_steps, n_dims):
    all_states = []
    successes = 0
    for seed in seeds:
        env = gym.make(env_name)
        obs, _ = env.reset(seed=seed)
        ep_r = 0.0
        for _ in range(max_steps):
            state = obs[:n_dims].tolist()
            all_states.append(state)
            action = swapnet_action(base_ranking, network, swap_preds, state)
            obs, r, term, trunc, _ = env.step(action)
            ep_r += r
            if term or trunc:
                break
        env.close()
        if ep_r > 100:
            successes += 1
    return all_states, successes


def _score_swap_one(args):
    (idx, candidate, env_name, base_ranking, network, swap_preds,
     target_idx, seeds, max_steps, n_dims) = args
    test_preds = list(swap_preds)
    test_preds[target_idx] = candidate
    reward, successes = run_episodes(
        env_name, base_ranking, network, test_preds, seeds, max_steps, n_dims)
    return {"idx": idx, "reward": reward, "landings": successes}


def score_swap_batch(candidates, env_name, base_ranking, network, swap_preds,
                     target_idx, seeds, max_steps, n_dims):
    args_list = [
        (i, cand, env_name, base_ranking, network, swap_preds,
         target_idx, seeds, max_steps, n_dims)
        for i, cand in enumerate(candidates)
    ]
    if not args_list:
        return []
    n_workers = min(cpu_count(), len(args_list), 8)
    if len(args_list) <= 4:
        return [_score_swap_one(a) for a in args_list]
    with Pool(processes=n_workers) as pool:
        return pool.map(_score_swap_one, args_list,
                        chunksize=max(1, len(args_list) // (n_workers * 4)))


def main():
    with open(sys.argv[1]) as f:
        request = json.load(f)
    cmd = request["cmd"]

    env_name = request.get("env_name", "LunarLander-v3")
    n_actions = request.get("n_actions", 4)
    n_dims = request.get("n_dims", 6)
    base_ranking = request.get("base_ranking", list(range(n_actions)))
    network = [tuple(p) for p in request.get("network",
                                              bubble_sort_network(n_actions))]
    swap_preds = request.get("swap_predicates",
                             ["falsep"] * len(network))
    seeds = request.get("seeds", list(range(30)))
    max_steps = request.get("max_steps", 300)

    if cmd == "collect_states":
        states, n_succ = collect_states(
            env_name, base_ranking, network, swap_preds, seeds,
            max_steps, n_dims)
        result = {"states": states, "n_landings": n_succ,
                  "n_episodes": len(seeds)}

    elif cmd == "score_swap":
        candidates = request["candidates"]
        target_idx = request["target_idx"]
        baseline_reward, baseline_succ = run_episodes(
            env_name, base_ranking, network, swap_preds, seeds,
            max_steps, n_dims, parallel=True)
        scores = score_swap_batch(
            candidates, env_name, base_ranking, network, swap_preds,
            target_idx, seeds, max_steps, n_dims)
        result = {"scores": scores, "baseline_reward": baseline_reward,
                  "baseline_landings": baseline_succ}

    elif cmd == "validate":
        reward, succ = run_episodes(
            env_name, base_ranking, network, swap_preds, seeds,
            max_steps, n_dims, parallel=True)
        result = {"reward": reward, "landings": succ}

    elif cmd == "search_base":
        from itertools import permutations
        best_reward = -1e9
        best_ranking = base_ranking
        best_succ = 0
        for perm in permutations(range(n_actions)):
            r, s = run_episodes(
                env_name, list(perm), network,
                ["falsep"] * len(network), seeds, max_steps, n_dims,
                parallel=True)
            if r > best_reward:
                best_reward = r
                best_ranking = list(perm)
                best_succ = s
        result = {"best_ranking": best_ranking, "reward": best_reward,
                  "landings": best_succ}

    else:
        result = {"error": f"Unknown command: {cmd}"}

    with open(sys.argv[2], 'w') as f:
        json.dump(result, f)


if __name__ == "__main__":
    main()
