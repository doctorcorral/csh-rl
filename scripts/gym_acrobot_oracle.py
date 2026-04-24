#!/usr/bin/env python3
"""Gymnasium adapter for Acrobot-v1 with ranking synthesis support.

State: [cos(θ1), sin(θ1), cos(θ2), sin(θ2), θ1_dot, θ2_dot] (6D)
Actions: 0=negative torque, 1=no torque, 2=positive torque
Reward: -1 per step until tip reaches height. Max 500 steps.
Higher (less negative) reward = better.

Commands: collect_states, score
"""

import sys
import json
import numpy as np
import gymnasium as gym
from multiprocessing import Pool, cpu_count

NUM_DIMS = 6
NUM_ACTIONS = 3
MAX_STEPS = 500


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


def _run_episode(args):
    chain, default, seed, max_steps = args
    env = gym.make("Acrobot-v1")
    obs, _ = env.reset(seed=seed)
    ep_r = 0.0
    for _ in range(max_steps):
        a = chain_action(chain, default, obs)
        obs, r, term, trunc, _ = env.step(a)
        ep_r += r
        if term or trunc:
            break
    env.close()
    return ep_r


def run_episodes(chain, default, seeds, max_steps=MAX_STEPS):
    total = 0.0
    wins = 0
    for s in seeds:
        r = _run_episode((chain, default, s, max_steps))
        total += r
        if r > -500:  # solved before timeout
            wins += 1
    return total, wins


def collect_states(chain, default, seeds, max_steps=MAX_STEPS):
    all_states = []
    n_wins = 0
    for seed in seeds:
        env = gym.make("Acrobot-v1")
        obs, _ = env.reset(seed=seed)
        ep_r = 0.0
        for _ in range(max_steps):
            all_states.append(obs.tolist())
            a = chain_action(chain, default, obs)
            obs, r, term, trunc, _ = env.step(a)
            ep_r += r
            if term or trunc:
                break
        env.close()
        if ep_r > -500:
            n_wins += 1
    return all_states, n_wins


def _score_one(args):
    idx, candidate, chain_so_far, stage_action, default, seeds, \
        chain_after, max_steps = args
    test_chain = chain_so_far + [(candidate, stage_action)] + chain_after
    reward, wins = run_episodes(test_chain, default, seeds, max_steps)
    return {"idx": idx, "reward": reward, "landings": wins}


def score_batch(candidates, stage_action, default, chain_so_far, seeds,
                chain_after=None, max_steps=MAX_STEPS):
    if chain_after is None:
        chain_after = []
    args_list = [
        (i, cand, chain_so_far, stage_action, default, seeds,
         chain_after, max_steps)
        for i, cand in enumerate(candidates)
    ]
    if not args_list:
        return []
    n_workers = min(cpu_count(), len(args_list), 8)
    if len(args_list) <= 4:
        return [_score_one(a) for a in args_list]
    with Pool(processes=n_workers) as pool:
        return pool.map(_score_one, args_list,
                        chunksize=max(1, len(args_list) // (n_workers * 4)))


def main():
    with open(sys.argv[1]) as f:
        request = json.load(f)
    cmd = request["cmd"]

    if cmd == "collect_states":
        chain = [(p, a) for p, a in request.get("chain", [])]
        default = request["default"]
        seeds = request.get("seeds", list(range(10)))
        max_steps = request.get("max_steps", MAX_STEPS)
        states, n_wins = collect_states(chain, default, seeds, max_steps)
        result = {"states": states, "n_landings": n_wins, "n_episodes": len(seeds)}

    elif cmd == "score":
        candidates = request["candidates"]
        stage_action = request["stage_action"]
        default = request["default"]
        chain_so_far = [(p, a) for p, a in request.get("chain_so_far", [])]
        chain_after = [(p, a) for p, a in request.get("chain_after", [])]
        seeds = request.get("seeds", list(range(10)))
        max_steps = request.get("max_steps", MAX_STEPS)
        baseline_chain = chain_so_far + chain_after
        baseline_reward, baseline_wins = run_episodes(
            baseline_chain, default, seeds, max_steps)
        scores = score_batch(
            candidates, stage_action, default, chain_so_far, seeds,
            chain_after, max_steps)
        result = {"scores": scores, "baseline_reward": baseline_reward,
                  "baseline_landings": baseline_wins}
    else:
        result = {"error": f"Unknown command: {cmd}"}

    with open(sys.argv[2], 'w') as f:
        json.dump(result, f)


if __name__ == "__main__":
    main()
