#!/usr/bin/env python3
"""Gymnasium adapter for BipedalWalker-v3 with binary-weighted continuous actions.

State: 24D continuous (hull angle/angvel, vel_x/y, joint angles/speeds,
       leg contacts, 10 lidar readings).
Action: 4D continuous [-1, 1] (hip1, knee1, hip2, knee2 torques).

Binary decomposition: each action dimension uses k bits with weights {1, 2, 4}.
  12 bit-predicates total, each a PredProg term.
  Composite action_d = 2 * sum(weight_i * bit_i) / max_sum - 1.

Commands:
  collect_states  — run episodes with current bit-predicates, return visited states
  score_bit       — score candidate predicates for one bit position (coordinate descent)
  score           — standard chain-compatible scoring (for validation)

Protocol mirrors other Synthex oracles (JSON over temp files).
"""

import sys
import json
import numpy as np
import gymnasium as gym
from multiprocessing import Pool, cpu_count

NUM_DIMS = 24
BITS_PER_DIM = 3
N_ACTION_DIMS = 4
N_BITS = BITS_PER_DIM * N_ACTION_DIMS  # 12
MAX_STEPS = 1600
WEIGHTS = [2**i for i in range(BITS_PER_DIM)]
MAX_SUM = sum(WEIGHTS)


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


def bits_to_action(bit_values):
    actions = np.zeros(N_ACTION_DIMS)
    for d in range(N_ACTION_DIMS):
        s = 0
        for i in range(BITS_PER_DIM):
            s += WEIGHTS[i] * bit_values[d * BITS_PER_DIM + i]
        actions[d] = 2.0 * s / MAX_SUM - 1.0
    return actions


def bit_policy_action(bit_preds, obs):
    """Evaluate all bit predicates and return continuous action."""
    bits = [1 if eval_pred(p, obs) else 0 for p in bit_preds]
    return bits_to_action(bits)


def chain_action(chain, default, obs):
    """Standard chain evaluation for compatibility."""
    for pred, action in chain:
        if eval_pred(pred, obs):
            return action
    return default


def _run_episode_bits(args):
    bit_preds, seed, max_steps = args
    env = gym.make("BipedalWalker-v3")
    obs, _ = env.reset(seed=seed)
    total_r = 0.0
    for _ in range(max_steps):
        action = bit_policy_action(bit_preds, obs)
        obs, r, term, trunc, _ = env.step(action)
        total_r += r
        if term or trunc:
            break
    env.close()
    return total_r


def run_episodes_bits(bit_preds, seeds, max_steps=MAX_STEPS):
    total = 0.0
    survived = 0
    for s in seeds:
        r = _run_episode_bits((bit_preds, s, max_steps))
        total += r
        if r > 0:
            survived += 1
    return total, survived


def collect_states_bits(bit_preds, seeds, max_steps=MAX_STEPS):
    all_states = []
    n_survived = 0
    for seed in seeds:
        env = gym.make("BipedalWalker-v3")
        obs, _ = env.reset(seed=seed)
        ep_r = 0.0
        for _ in range(max_steps):
            all_states.append(obs.tolist())
            action = bit_policy_action(bit_preds, obs)
            obs, r, term, trunc, _ = env.step(action)
            ep_r += r
            if term or trunc:
                break
        env.close()
        if ep_r > 0:
            n_survived += 1
    return all_states, n_survived


def _score_bit_one(args):
    idx, candidate, bit_preds, target_bit, seeds, max_steps = args
    test_preds = list(bit_preds)
    test_preds[target_bit] = candidate
    reward, survived = run_episodes_bits(test_preds, seeds, max_steps)
    return {"idx": idx, "reward": reward, "landings": survived}


def score_bit_batch(candidates, bit_preds, target_bit, seeds,
                    max_steps=MAX_STEPS):
    args_list = [
        (i, cand, bit_preds, target_bit, seeds, max_steps)
        for i, cand in enumerate(candidates)
    ]
    if not args_list:
        return []
    n_workers = min(cpu_count(), len(args_list), 8)
    if len(args_list) <= 4:
        return [_score_bit_one(a) for a in args_list]
    with Pool(processes=n_workers) as pool:
        return pool.map(_score_bit_one, args_list,
                        chunksize=max(1, len(args_list) // (n_workers * 4)))


def _run_episode_chain(args):
    """Standard chain-based episode for compatibility."""
    chain, default, seed, max_steps = args
    env = gym.make("BipedalWalker-v3")
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


def main():
    with open(sys.argv[1]) as f:
        request = json.load(f)
    cmd = request["cmd"]

    if cmd == "collect_states":
        bit_preds = request.get("bit_predicates")
        if bit_preds is not None:
            seeds = request.get("seeds", list(range(40)))
            max_steps = request.get("max_steps", MAX_STEPS)
            states, n_survived = collect_states_bits(
                bit_preds, seeds, max_steps)
            result = {"states": states, "n_landings": n_survived,
                      "n_episodes": len(seeds)}
        else:
            chain = [(p, a) for p, a in request.get("chain", [])]
            default = request["default"]
            seeds = request.get("seeds", list(range(40)))
            max_steps = request.get("max_steps", MAX_STEPS)
            # For chain-mode collect, bit_preds all falsep
            bp = ["falsep"] * N_BITS
            states, n_survived = collect_states_bits(bp, seeds, max_steps)
            result = {"states": states, "n_landings": n_survived,
                      "n_episodes": len(seeds)}

    elif cmd == "score_bit":
        candidates = request["candidates"]
        bit_preds = request["bit_predicates"]
        target_bit = request["target_bit"]
        seeds = request.get("seeds", list(range(30)))
        max_steps = request.get("max_steps", MAX_STEPS)

        baseline_reward, baseline_survived = run_episodes_bits(
            bit_preds, seeds, max_steps)
        scores = score_bit_batch(
            candidates, bit_preds, target_bit, seeds, max_steps)
        result = {"scores": scores, "baseline_reward": baseline_reward,
                  "baseline_landings": baseline_survived}

    elif cmd == "score":
        candidates = request["candidates"]
        stage_action = request["stage_action"]
        default = request["default"]
        chain_so_far = [(p, a) for p, a in request.get("chain_so_far", [])]
        chain_after = [(p, a) for p, a in request.get("chain_after", [])]
        seeds = request.get("seeds", list(range(30)))
        max_steps = request.get("max_steps", MAX_STEPS)

        baseline_chain = chain_so_far + chain_after
        total = 0.0
        wins = 0
        for s in seeds:
            r = _run_episode_chain(
                (baseline_chain, default, s, max_steps))
            total += r
            if r > 0:
                wins += 1
        result = {"scores": [], "baseline_reward": total,
                  "baseline_landings": wins}
    else:
        result = {"error": f"Unknown command: {cmd}"}

    with open(sys.argv[2], 'w') as f:
        json.dump(result, f)


if __name__ == "__main__":
    main()
