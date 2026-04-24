#!/usr/bin/env python3
"""Gymnasium adapter for ALE/Pong-v5 with ranking synthesis support.

Uses RAM observations to extract a compact state vector:
  [ball_x, ball_y, player_y, ball_vy]

Ball velocity is derived from consecutive frames. The enemy paddle
is part of the environment dynamics (adversary is transparent).

Actions: UP(2), NOOP(0), DOWN(3)
  Mapped to synthesis indices: 0=UP, 1=NOOP, 2=DOWN

Commands:
    collect_states — run episodes, return raw states visited
    score          — score a batch of candidate predicates
"""

import sys
import json
import numpy as np
import gymnasium as gym
import ale_py
from multiprocessing import Pool, cpu_count

gym.register_envs(ale_py)

NUM_DIMS = 6  # ball_x, ball_y, player_y, ball_vx, ball_vy, enemy_y
NUM_ACTIONS = 3

# Synthesis action index → ALE action
ACTION_TO_ALE = {0: 2, 1: 0, 2: 3}  # UP, NOOP, DOWN
ACTION_NAMES = {0: "up", 1: "noop", 2: "down"}

# Pong score: game ends at 21 points for either side.
# Reward: +1 per point won, -1 per point lost.
MAX_STEPS_PER_EPISODE = 10000


def extract_state(env, prev_ball_x, prev_ball_y):
    """Extract [ball_x, ball_y, player_y, ball_vx, ball_vy, enemy_y] from RAM."""
    ram = env.unwrapped.ale.getRAM()
    bx = float(ram[49])
    by = float(ram[54])
    py = float(ram[51])
    ey = float(ram[50])

    if prev_ball_y is not None and by > 0 and by < 200 and prev_ball_y > 0:
        vx = bx - prev_ball_x
        vy = by - prev_ball_y
    else:
        vx, vy = 0.0, 0.0

    return [bx, by, py, vx, vy, ey], bx, by


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


def collect_states(chain, default, seeds, max_steps=MAX_STEPS_PER_EPISODE):
    """Run episodes, return raw states visited."""
    all_states = []
    n_wins = 0
    for seed in seeds:
        env = gym.make("ALE/Pong-v5", obs_type="ram")
        env.reset(seed=seed)
        prev_bx, prev_by = None, None
        ep_reward = 0.0
        for _ in range(max_steps):
            state, prev_bx, prev_by = extract_state(env, prev_bx, prev_by)
            all_states.append(state)
            action_idx = chain_action(chain, default, state)
            ale_action = ACTION_TO_ALE[action_idx]
            _, reward, term, trunc, _ = env.step(ale_action)
            ep_reward += reward
            if term or trunc:
                break
        env.close()
        if ep_reward > 0:
            n_wins += 1
    return all_states, n_wins


def _run_episode(args):
    """Run a single episode, return (total_reward, won?)."""
    chain, default, seed, max_steps = args
    env = gym.make("ALE/Pong-v5", obs_type="ram")
    env.reset(seed=seed)
    prev_bx, prev_by = None, None
    ep_reward = 0.0
    for _ in range(max_steps):
        state, prev_bx, prev_by = extract_state(env, prev_bx, prev_by)
        action_idx = chain_action(chain, default, state)
        ale_action = ACTION_TO_ALE[action_idx]
        _, reward, term, trunc, _ = env.step(ale_action)
        ep_reward += reward
        if term or trunc:
            break
    env.close()
    return ep_reward


def run_episodes(chain, default, seeds, max_steps=MAX_STEPS_PER_EPISODE):
    """Run episodes sequentially, return (total_reward, n_wins).
    No inner Pool — outer score_batch handles parallelism."""
    total = 0.0
    wins = 0
    for s in seeds:
        r = _run_episode((chain, default, s, max_steps))
        total += r
        if r > 0:
            wins += 1
    return total, wins


def _score_one(args):
    idx, candidate, chain_so_far, stage_action, default, seeds, \
        chain_after, max_steps = args
    test_chain = chain_so_far + [(candidate, stage_action)] + chain_after
    reward, wins = run_episodes(test_chain, default, seeds, max_steps)
    return {"idx": idx, "reward": reward, "landings": wins}


def score_batch(candidates, stage_action, default, chain_so_far, seeds,
                chain_after=None, max_steps=MAX_STEPS_PER_EPISODE):
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
    n_workers = min(cpu_count(), n_cands, 8)
    if n_cands <= 4:
        return [_score_one(a) for a in args_list]
    with Pool(processes=n_workers) as pool:
        results = pool.map(
            _score_one, args_list,
            chunksize=max(1, n_cands // (n_workers * 4)))
    return results


def main():
    req_file = sys.argv[1]
    resp_file = sys.argv[2]

    with open(req_file) as f:
        request = json.load(f)

    cmd = request["cmd"]

    if cmd == "collect_states":
        chain = [(p, a) for p, a in request.get("chain", [])]
        default = request["default"]
        seeds = request.get("seeds", list(range(10)))
        max_steps = request.get("max_steps", MAX_STEPS_PER_EPISODE)
        states, n_wins = collect_states(chain, default, seeds, max_steps)
        result = {
            "states": states,
            "n_landings": n_wins,
            "n_episodes": len(seeds),
        }

    elif cmd == "score":
        candidates = request["candidates"]
        stage_action = request["stage_action"]
        default = request["default"]
        chain_so_far = [(p, a) for p, a in request.get("chain_so_far", [])]
        chain_after = [(p, a) for p, a in request.get("chain_after", [])]
        seeds = request.get("seeds", list(range(10)))
        max_steps = request.get("max_steps", MAX_STEPS_PER_EPISODE)
        baseline_chain = chain_so_far + chain_after
        baseline_reward, baseline_wins = run_episodes(
            baseline_chain, default, seeds, max_steps)
        scores = score_batch(
            candidates, stage_action, default, chain_so_far, seeds,
            chain_after, max_steps)
        result = {
            "scores": scores,
            "baseline_reward": baseline_reward,
            "baseline_landings": baseline_wins,
        }

    else:
        result = {"error": f"Unknown command: {cmd}"}

    with open(resp_file, 'w') as f:
        json.dump(result, f)


if __name__ == "__main__":
    main()
