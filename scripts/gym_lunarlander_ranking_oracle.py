#!/usr/bin/env python3
"""Gymnasium adapter for LunarLander-v3 with ranking synthesis support.

Uses episode replay for exact state profiling: to evaluate all actions
at step N of an episode, we replay from the same seed with the same
actions, then branch.  No approximate state restoration needed.

Commands:
    collect_states           — run episodes, return raw states visited
    score                    — score a batch of candidate predicates
    collect_and_profile      — random episodes, profile with random follow-up
    oracle_verify_episodic   — tree-policy episodes, profile with tree follow-up
"""

import sys
import json
import numpy as np
import gymnasium as gym
from multiprocessing import Pool, cpu_count

NUM_DIMS = 6
NUM_ACTIONS = 4


def eval_feature(feat, state):
    kind = feat[0]
    if kind == "axis":
        return state[feat[1]] < feat[2]
    elif kind == "diag":
        return feat[3] * state[feat[1]] + state[feat[2]] < 0
    elif kind == "sq_diag":
        return feat[3] * state[feat[1]] ** 2 + state[feat[2]] < 0
    return False


def eval_pred(pred, state):
    if pred == "truep":
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


def chain_action(chain, default, obs):
    for pred, action in chain:
        if eval_pred(pred, obs):
            return action
    return default


def _ranking_from_rewards(action_rewards):
    """Rank by cumulative episode reward: highest reward = best action."""
    return sorted(action_rewards.keys(),
                  key=lambda a: action_rewards[a], reverse=True)


def _policy_action(state, preds_rankings, default_ranking):
    for pred, ranking in preds_rankings:
        if eval_pred(pred, state):
            return ranking[0]
    return default_ranking[0]


def _profile_at_step(seed, actions_so_far, lookahead, follow_fn,
                     max_episode_steps=300):
    """Profile all actions at a step via replay, return ranking by episode reward.

    Replays the episode up to the current step, then branches on each action
    and follows up with follow_fn. Accumulates reward from the branching
    point onward (the tested action + follow-up steps).

    For episodic envs: if lookahead <= 0, roll out until episode ends or
    max_episode_steps total steps from the start."""
    action_rewards = {}
    steps_used = len(actions_so_far) + 1
    for aid in range(NUM_ACTIONS):
        sim = gym.make("LunarLander-v3").unwrapped
        sim.reset(seed=seed)
        for a in actions_so_far:
            sim.step(a)
        test_obs, reward, term, trunc, _ = sim.step(aid)
        cumulative = reward
        if lookahead <= 0:
            steps_remaining = max(0, max_episode_steps - steps_used)
        else:
            steps_remaining = lookahead - 1
        for _ in range(steps_remaining):
            if term or trunc:
                break
            s = test_obs[:NUM_DIMS].tolist()
            test_obs, reward, term, trunc, _ = sim.step(follow_fn(s, sim))
            cumulative += reward
        action_rewards[aid] = cumulative
        sim.close()
    return _ranking_from_rewards(action_rewards)


# ── Episodic profiling ───────────────────────────────────────────

def _profile_episode_random(args):
    """Run one random episode, profile at sampled steps with random follow-up."""
    seed, max_steps, lookahead, sample_interval = args
    env = gym.make("LunarLander-v3").unwrapped
    obs, _ = env.reset(seed=seed)
    actions_taken = []
    results = []

    for step in range(max_steps):
        state = obs[:NUM_DIMS].tolist()

        if step > 0 and step % sample_interval == 0:
            ranking = _profile_at_step(
                seed, actions_taken, lookahead,
                lambda s, sim: int(sim.np_random.integers(NUM_ACTIONS)))
            results.append([state, ranking])

        action = int(env.np_random.integers(NUM_ACTIONS))
        actions_taken.append(action)
        obs, _, term, trunc, _ = env.step(action)
        if term or trunc:
            break

    env.close()
    return results


def collect_and_profile_random(seeds, max_steps, lookahead,
                               sample_interval=10):
    """Random episodes with random-follow-up profiling."""
    args_list = [(s, max_steps, lookahead, sample_interval) for s in seeds]
    n = len(args_list)
    n_workers = min(cpu_count(), n)
    if n <= 2:
        all_results = [_profile_episode_random(a) for a in args_list]
    else:
        with Pool(processes=n_workers) as pool:
            all_results = pool.map(_profile_episode_random, args_list)
    out = []
    for r in all_results:
        out.extend(r)
    return out


def _profile_episode_tree(args):
    """Run one tree-policy episode, profile at sampled steps."""
    seed, max_steps, lookahead, sample_interval, \
        preds_rankings, default_ranking = args
    env = gym.make("LunarLander-v3").unwrapped
    obs, _ = env.reset(seed=seed)
    actions_taken = []
    results = []

    def follow_fn(s, sim):
        return _policy_action(s, preds_rankings, default_ranking)

    for step in range(max_steps):
        state = obs[:NUM_DIMS].tolist()

        if step > 0 and step % sample_interval == 0:
            ranking = _profile_at_step(
                seed, actions_taken, lookahead, follow_fn,
                max_episode_steps=max_steps)
            results.append([state, ranking])

        action = _policy_action(state, preds_rankings, default_ranking)
        actions_taken.append(action)
        obs, _, term, trunc, _ = env.step(action)
        if term or trunc:
            break

    env.close()
    return results


def oracle_verify_tree_episodic(preds_rankings, default_ranking, seeds,
                                max_steps, lookahead, sample_interval=10):
    """Run tree-policy episodes, profile with tree follow-up at sampled steps."""
    args_list = [
        (s, max_steps, lookahead, sample_interval,
         preds_rankings, default_ranking)
        for s in seeds
    ]
    n = len(args_list)
    n_workers = min(cpu_count(), n)
    if n <= 2:
        all_results = [_profile_episode_tree(a) for a in args_list]
    else:
        with Pool(processes=n_workers) as pool:
            all_results = pool.map(_profile_episode_tree, args_list)
    out = []
    for r in all_results:
        out.extend(r)
    return out


# ── Episode running (for score/validation) ───────────────────────

def collect_states(chain, default, seeds, max_steps=1000):
    env = gym.make("LunarLander-v3")
    all_states = []
    n_landings = 0
    for seed in seeds:
        obs, _ = env.reset(seed=seed)
        ep_reward = 0.0
        for _ in range(max_steps):
            state = obs[:NUM_DIMS].tolist()
            all_states.append(state)
            action = chain_action(chain, default, state)
            obs, reward, terminated, truncated, _ = env.step(action)
            ep_reward += reward
            if terminated or truncated:
                break
        if ep_reward > 100:
            n_landings += 1
    env.close()
    return all_states, n_landings


def run_episodes(chain, default, seeds, max_steps=1000):
    env = gym.make("LunarLander-v3")
    total_reward = 0.0
    landings = 0
    for seed in seeds:
        obs, _ = env.reset(seed=seed)
        ep_reward = 0.0
        for _ in range(max_steps):
            state = obs[:6].tolist()
            action = chain_action(chain, default, state)
            obs, reward, terminated, truncated, _ = env.step(action)
            ep_reward += reward
            if terminated or truncated:
                break
        total_reward += ep_reward
        if ep_reward > 100:
            landings += 1
    env.close()
    return total_reward, landings


def _score_one(args):
    idx, candidate, chain_so_far, stage_action, default, seeds, \
        chain_after, max_steps = args
    test_chain = chain_so_far + [(candidate, stage_action)] + chain_after
    reward, landings = run_episodes(test_chain, default, seeds, max_steps)
    return {"idx": idx, "reward": reward, "landings": landings}


def score_batch(candidates, stage_action, default, chain_so_far, seeds,
                chain_after=None, max_steps=1000):
    if chain_after is None:
        chain_after = []
    args_list = [
        (i, cand, chain_so_far, stage_action, default, seeds,
         chain_after, max_steps)
        for i, cand in enumerate(candidates)
    ]
    n_cands = len(args_list)
    if n_cands == 0:
        return []
    n_workers = min(cpu_count(), n_cands)
    if n_cands <= 4:
        return [_score_one(a) for a in args_list]
    with Pool(processes=n_workers) as pool:
        results = pool.map(
            _score_one, args_list,
            chunksize=max(1, n_cands // (n_workers * 4)))
    return results


# ── Main dispatch ────────────────────────────────────────────────

def main():
    req_file = sys.argv[1]
    resp_file = sys.argv[2]

    with open(req_file) as f:
        request = json.load(f)

    cmd = request["cmd"]

    if cmd == "collect_states":
        chain = [(p, a) for p, a in request.get("chain", [])]
        default = request["default"]
        seeds = request.get("seeds", list(range(40)))
        max_steps = request.get("max_steps", 300)
        states, n_land = collect_states(chain, default, seeds, max_steps)
        result = {
            "states": states,
            "n_landings": n_land,
            "n_episodes": len(seeds),
        }

    elif cmd == "score":
        candidates = request["candidates"]
        stage_action = request["stage_action"]
        default = request["default"]
        chain_so_far = [(p, a) for p, a in request.get("chain_so_far", [])]
        chain_after = [(p, a) for p, a in request.get("chain_after", [])]
        seeds = request.get("seeds", list(range(30)))
        max_steps = request.get("max_steps", 1000)
        baseline_chain = chain_so_far + chain_after
        baseline_reward, baseline_landings = run_episodes(
            baseline_chain, default, seeds, max_steps)
        scores = score_batch(
            candidates, stage_action, default, chain_so_far, seeds,
            chain_after, max_steps)
        result = {
            "scores": scores,
            "baseline_reward": baseline_reward,
            "baseline_landings": baseline_landings,
        }

    elif cmd == "collect_and_profile":
        seeds = request.get("seeds", list(range(20)))
        max_steps = request.get("max_steps", 200)
        lookahead = request.get("lookahead", 30)
        sample_interval = request.get("sample_interval", 10)
        data = collect_and_profile_random(
            seeds, max_steps, lookahead, sample_interval)
        states = [d[0] for d in data]
        rankings = [d[1] for d in data]
        result = {"states": states, "rankings": rankings}

    elif cmd == "oracle_verify_episodic":
        preds_rankings = [
            (p["pred"], p["ranking"]) for p in request["preds"]]
        default_ranking = request["default_ranking"]
        seeds = request.get("seeds", list(range(20)))
        max_steps = request.get("max_steps", 300)
        lookahead = request.get("lookahead", 30)
        sample_interval = request.get("sample_interval", 10)
        data = oracle_verify_tree_episodic(
            preds_rankings, default_ranking, seeds,
            max_steps, lookahead, sample_interval)
        states = [d[0] for d in data]
        rankings = [d[1] for d in data]
        result = {"states": states, "rankings": rankings}

    else:
        result = {"error": f"Unknown command: {cmd}"}

    with open(resp_file, 'w') as f:
        json.dump(result, f)


if __name__ == "__main__":
    main()
