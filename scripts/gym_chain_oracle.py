#!/usr/bin/env python3
"""Thin Gymnasium adapter for LunarLander-v3.

All learning logic (features, CEGAR, counterexamples) lives in Synthex.
This script ONLY interacts with the environment and reports observations.

Commands:
    collect_states — run episodes, return raw states visited
    score          — score a batch of candidate predicates
"""

import sys
import json
import numpy as np
import gymnasium as gym
from multiprocessing import Pool, cpu_count

NUM_DIMS = 6


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


# ── Environment interaction ─────────────────────────────────────

def collect_states(chain, default, seeds, max_steps=1000):
    """Run episodes, return raw states visited. No learning logic."""
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


# ── Batch candidate scoring ─────────────────────────────────────

def _score_one(args):
    idx, candidate, chain_so_far, stage_action, default, seeds, chain_after, max_steps = args
    test_chain = chain_so_far + [(candidate, stage_action)] + chain_after
    reward, landings = run_episodes(test_chain, default, seeds, max_steps)
    return {"idx": idx, "reward": reward, "landings": landings}


def score_batch(candidates, stage_action, default, chain_so_far, seeds, chain_after=None, max_steps=1000):
    if chain_after is None:
        chain_after = []
    args_list = [
        (i, cand, chain_so_far, stage_action, default, seeds, chain_after, max_steps)
        for i, cand in enumerate(candidates)
    ]
    n_cands = len(args_list)
    if n_cands == 0:
        return []
    n_workers = min(cpu_count(), n_cands)
    if n_cands <= 4:
        return [_score_one(a) for a in args_list]
    with Pool(processes=n_workers) as pool:
        results = pool.map(_score_one, args_list, chunksize=max(1, n_cands // (n_workers * 4)))
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
        result = {"states": states, "n_landings": n_land, "n_episodes": len(seeds)}

    elif cmd == "score":
        candidates = request["candidates"]
        stage_action = request["stage_action"]
        default = request["default"]
        chain_so_far = [(p, a) for p, a in request.get("chain_so_far", [])]
        chain_after = [(p, a) for p, a in request.get("chain_after", [])]
        seeds = request.get("seeds", list(range(30)))
        max_steps = request.get("max_steps", 1000)
        baseline_chain = chain_so_far + chain_after
        baseline_reward, baseline_landings = run_episodes(baseline_chain, default, seeds, max_steps)
        scores = score_batch(candidates, stage_action, default, chain_so_far, seeds, chain_after, max_steps)
        result = {
            "scores": scores,
            "baseline_reward": baseline_reward,
            "baseline_landings": baseline_landings,
        }

    else:
        result = {"error": f"Unknown command: {cmd}"}

    with open(resp_file, 'w') as f:
        json.dump(result, f)


if __name__ == "__main__":
    main()
