#!/usr/bin/env python3
"""Thin Gymnasium adapter for Pendulum-v1.

All learning logic (features, CEGAR, counterexamples) lives in Synthex.
This script ONLY interacts with the environment and reports observations.

Commands:
    collect_states — run episodes, return raw states visited
    explore        — run episodes with per-step all-action lookahead
    score          — score a batch of candidate predicates
    profile        — per-state all-action reward profiling for ranking synthesis
    collect_anchors — collect initial anchor states from random episodes
    profile_anchors — profile specific anchor states under a given policy
    oracle_verify   — verify candidate predicates via self-consistent rollout
    find_cex        — find counterexample states where ranking disagrees
"""

import sys
import json
import math
import numpy as np
import gymnasium as gym
from multiprocessing import Pool, cpu_count

ACTION_MAP = {0: np.array([-2.0]),   # torque_neg
              1: np.array([0.0]),     # no_torque
              2: np.array([2.0])}     # torque_pos

NUM_DIMS = 3  # cos θ, sin θ, ω
NUM_ACTIONS = 3


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


def _state_to_theta_omega(state):
    cos_t, sin_t, omega = state[0], state[1], state[2]
    theta = math.atan2(sin_t, cos_t)
    return theta, omega


def _state_penalty(obs):
    """State penalty: θ² + 0.1·ω² (0 at equilibrium, positive elsewhere)."""
    theta = math.atan2(obs[1], obs[0])
    omega = obs[2]
    return theta * theta + 0.1 * omega * omega


def _ranking_from_terminal(action_terminal_penalties):
    """Rank actions by terminal state quality: the action whose trajectory
    ends at the lowest-penalty state ranks highest. This is the coinductive
    criterion — what matters is where you end up, because that terminal
    state is the continuation point for the next coinductive step."""
    return sorted(action_terminal_penalties.keys(),
                  key=lambda a: action_terminal_penalties[a])


def _policy_action(state, preds_rankings, default_ranking):
    """Exclusive multi-predicate policy: first matching predicate wins."""
    for pred, ranking in preds_rankings:
        if eval_pred(pred, state):
            return ranking[0]
    return default_ranking[0]


def _rollout_action(sim, aid, pred, r_true, r_false, theta, omega, lookahead):
    """Roll out one action from (theta, omega) using single-pred policy.
    Returns terminal state penalty."""
    return _rollout_action_multi(
        sim, aid, [(pred, r_true)], r_false, theta, omega, lookahead)


def _rollout_action_multi(sim, aid, preds_rankings, default_ranking, theta, omega, lookahead):
    """Roll out one action using multi-predicate exclusive policy.
    Returns terminal state penalty."""
    sim.state = np.array([theta, omega])
    test_obs, _, _, _, _ = sim.step(ACTION_MAP[aid])
    for _ in range(lookahead - 1):
        s = test_obs[:NUM_DIMS].tolist()
        follow_action = _policy_action(s, preds_rankings, default_ranking)
        test_obs, _, _, _, _ = sim.step(ACTION_MAP[follow_action])
    return _state_penalty(test_obs)


# ── Environment interaction ─────────────────────────────────────

def collect_states(chain, default, seeds, max_steps=200):
    """Run episodes, return raw states visited. No learning logic."""
    env = gym.make("Pendulum-v1")
    all_states = []
    n_stabilized = 0

    for seed in seeds:
        obs, _ = env.reset(seed=seed)
        upright_steps = 0
        for _ in range(max_steps):
            state = obs[:NUM_DIMS].tolist()
            all_states.append(state)
            action_id = chain_action(chain, default, state)
            obs, _, terminated, truncated, _ = env.step(ACTION_MAP[action_id])
            if obs[0] > 0.95:
                upright_steps += 1
            if terminated or truncated:
                break
        if upright_steps >= 100:
            n_stabilized += 1

    env.close()
    return all_states, n_stabilized


def explore_episodes(chain, default, seeds, max_steps=200, lookahead=20):
    """Run episodes with multi-step lookahead at sampled steps."""
    env = gym.make("Pendulum-v1")
    sim = gym.make("Pendulum-v1").unwrapped
    steps_data = []
    n_stabilized = 0
    n_total = len(seeds)

    for seed in seeds:
        obs, _ = env.reset(seed=seed)
        upright_steps = 0
        for step_i in range(max_steps):
            state = obs[:NUM_DIMS].tolist()
            chosen = chain_action(chain, default, state)

            if step_i % 5 == 0:
                theta_now, omega_now = env.unwrapped.state.copy()
                alt_rewards = {}
                for aid, torque in ACTION_MAP.items():
                    sim.state = np.array([theta_now, omega_now])
                    test_obs, r_sum, _, _, _ = sim.step(torque)
                    for _ in range(lookahead - 1):
                        s = test_obs[:NUM_DIMS].tolist()
                        a = chain_action(chain, default, s)
                        test_obs, r, _, _, _ = sim.step(ACTION_MAP[a])
                        r_sum += r
                    alt_rewards[str(aid)] = round(float(r_sum), 4)

                steps_data.append([state, chosen, alt_rewards])

            obs, _, terminated, truncated, _ = env.step(ACTION_MAP[chosen])

            if obs[0] > 0.95:
                upright_steps += 1
            if terminated or truncated:
                break

        if upright_steps >= 100:
            n_stabilized += 1

    env.close()
    sim.close()
    return steps_data, n_stabilized, n_total


def run_episodes(chain, default, seeds, max_steps=200):
    env = gym.make("Pendulum-v1")
    total_reward = 0.0
    stabilized_count = 0
    for seed in seeds:
        obs, _ = env.reset(seed=seed)
        ep_reward = 0.0
        upright_steps = 0
        for _ in range(max_steps):
            state = obs[:NUM_DIMS].tolist()
            action_id = chain_action(chain, default, state)
            obs, reward, terminated, truncated, _ = env.step(ACTION_MAP[action_id])
            ep_reward += reward
            if obs[0] > 0.95:
                upright_steps += 1
        total_reward += ep_reward
        if upright_steps >= 100:
            stabilized_count += 1
    env.close()
    return total_reward, stabilized_count


# ── Action profiling for ranking synthesis ───────────────────────

def _profile_seed(args):
    seed, chain, default, max_steps, lookahead = args
    env = gym.make("Pendulum-v1")
    sim = gym.make("Pendulum-v1").unwrapped
    profiles = []

    obs, _ = env.reset(seed=seed)
    for _ in range(max_steps):
        state = obs[:NUM_DIMS].tolist()
        theta_now, omega_now = env.unwrapped.state.copy()

        action_rewards = {}
        for aid, torque in ACTION_MAP.items():
            sim.state = np.array([theta_now, omega_now])
            test_obs, r_sum, _, _, _ = sim.step(torque)
            for _ in range(lookahead - 1):
                s = test_obs[:NUM_DIMS].tolist()
                a = chain_action(chain, default, s)
                test_obs, r, _, _, _ = sim.step(ACTION_MAP[a])
                r_sum += r
            action_rewards[str(aid)] = round(float(r_sum), 4)

        profiles.append([state, action_rewards])

        chosen = chain_action(chain, default, state)
        obs, _, terminated, truncated, _ = env.step(ACTION_MAP[chosen])
        if terminated or truncated:
            break

    env.close()
    sim.close()
    return profiles


def profile_actions(chain, default, seeds, max_steps=500, lookahead=20):
    """Profile all actions at every state along policy trajectories."""
    args_list = [(seed, chain, default, max_steps, lookahead) for seed in seeds]
    n_seeds = len(args_list)
    n_workers = min(cpu_count(), n_seeds)
    if n_seeds <= 4:
        results = [_profile_seed(a) for a in args_list]
    else:
        with Pool(processes=n_workers) as pool:
            results = pool.map(_profile_seed, args_list)
    all_profiles = []
    for profiles in results:
        all_profiles.extend(profiles)
    return all_profiles


# ── Batch candidate scoring ─────────────────────────────────────

def _score_one(args):
    idx, candidate, chain_so_far, stage_action, default, seeds, chain_after, max_steps = args
    test_chain = chain_so_far + [(candidate, stage_action)] + chain_after
    reward, stabilized = run_episodes(test_chain, default, seeds, max_steps)
    return {"idx": idx, "reward": reward, "stabilized": stabilized}


def score_batch(candidates, stage_action, default, chain_so_far, seeds, chain_after=None, max_steps=300):
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


# ── CSHRL anchor-based oracle ────────────────────────────────────

def collect_anchor_states(seeds, max_steps, n_per_episode=5):
    """Run episodes with random actions, sample representative states."""
    env = gym.make("Pendulum-v1")
    all_states = []
    for seed in seeds:
        obs, _ = env.reset(seed=seed)
        episode_states = []
        for _ in range(max_steps):
            state = obs[:NUM_DIMS].tolist()
            episode_states.append(state)
            action = env.action_space.sample()
            obs, _, terminated, truncated, _ = env.step(action)
            if terminated or truncated:
                break
        step = max(1, len(episode_states) // n_per_episode)
        sampled = episode_states[::step][:n_per_episode]
        all_states.extend(sampled)
    env.close()
    return all_states


def profile_anchor_states(anchors, chain, default, lookahead):
    """Profile specific anchor states under a given policy.
    Returns per-anchor ranking by terminal state penalty."""
    sim = gym.make("Pendulum-v1").unwrapped
    results = []
    for state in anchors:
        theta, omega = _state_to_theta_omega(state)
        terminal_penalties = {}
        for aid in range(NUM_ACTIONS):
            sim.state = np.array([theta, omega])
            test_obs, _, _, _, _ = sim.step(ACTION_MAP[aid])
            for _ in range(lookahead - 1):
                s = test_obs[:NUM_DIMS].tolist()
                a = chain_action(chain, default, s)
                test_obs, _, _, _, _ = sim.step(ACTION_MAP[a])
            terminal_penalties[aid] = _state_penalty(test_obs)
        results.append(_ranking_from_terminal(terminal_penalties))
    sim.close()
    return results


def _verify_candidate(args):
    """Verify one candidate at all anchors using its OWN policy as follow-up."""
    cand, anchors, lookahead = args
    pred = cand["pred"]
    r_true = cand["r_true"]
    r_false = cand["r_false"]
    sim = gym.make("Pendulum-v1").unwrapped
    anchor_rankings = []
    for state in anchors:
        theta, omega = _state_to_theta_omega(state)
        terminal_penalties = {}
        for aid in range(NUM_ACTIONS):
            terminal_penalties[aid] = _rollout_action(sim, aid, pred, r_true, r_false,
                                                       theta, omega, lookahead)
        anchor_rankings.append(_ranking_from_terminal(terminal_penalties))
    sim.close()
    return anchor_rankings


def oracle_verify_batch(candidates, anchors, lookahead):
    """For each candidate, verify self-consistent ranking at all anchors.
    Uses multiprocessing for parallelism."""
    args_list = [(cand, anchors, lookahead) for cand in candidates]
    n = len(args_list)
    n_workers = min(cpu_count(), n)
    if n <= 4:
        all_rankings = [_verify_candidate(a) for a in args_list]
    else:
        with Pool(processes=n_workers) as pool:
            all_rankings = pool.map(_verify_candidate, args_list,
                                     chunksize=max(1, n // (n_workers * 4)))
    return [{"rankings": r} for r in all_rankings]


def _find_cex_seed(args):
    """Find counterexample states in one episode."""
    seed, policy_pred, r_true, r_false, max_steps, lookahead, max_cex = args
    env = gym.make("Pendulum-v1")
    sim = gym.make("Pendulum-v1").unwrapped
    cex = []
    obs, _ = env.reset(seed=seed)
    for step in range(max_steps):
        if len(cex) >= max_cex:
            break
        state = obs[:NUM_DIMS].tolist()
        if step % 10 == 0:
            theta, omega = _state_to_theta_omega(state)
            terminal_penalties = {}
            for aid in range(NUM_ACTIONS):
                terminal_penalties[aid] = _rollout_action(sim, aid, policy_pred, r_true, r_false,
                                                           theta, omega, lookahead)
            ranking = _ranking_from_terminal(terminal_penalties)
            expected = r_true if eval_pred(policy_pred, state) else r_false
            if ranking != expected:
                cex.append(state)
        if eval_pred(policy_pred, state):
            action_id = r_true[0]
        else:
            action_id = r_false[0]
        obs, _, terminated, truncated, _ = env.step(ACTION_MAP[action_id])
        if terminated or truncated:
            break
    env.close()
    sim.close()
    return cex


def find_cex_states(policy_pred, r_true, r_false, seeds, max_steps, lookahead, max_cex):
    """Deploy policy, find states where self-consistent ranking disagrees."""
    per_seed_max = max(5, max_cex // len(seeds))
    args_list = [(s, policy_pred, r_true, r_false, max_steps, lookahead, per_seed_max)
                 for s in seeds]
    n = len(args_list)
    n_workers = min(cpu_count(), n)
    if n <= 4:
        results = [_find_cex_seed(a) for a in args_list]
    else:
        with Pool(processes=n_workers) as pool:
            results = pool.map(_find_cex_seed, args_list)
    all_cex = []
    for cex in results:
        all_cex.extend(cex)
    return all_cex[:max_cex]


def _verify_candidate_multi(args):
    """Verify one multi-predicate candidate at all anchors."""
    cand, anchors, lookahead = args
    preds_rankings = [(p["pred"], p["ranking"]) for p in cand["preds"]]
    default_ranking = cand["default_ranking"]
    sim = gym.make("Pendulum-v1").unwrapped
    anchor_rankings = []
    for state in anchors:
        theta, omega = _state_to_theta_omega(state)
        terminal_penalties = {}
        for aid in range(NUM_ACTIONS):
            terminal_penalties[aid] = _rollout_action_multi(
                sim, aid, preds_rankings, default_ranking,
                theta, omega, lookahead)
        anchor_rankings.append(_ranking_from_terminal(terminal_penalties))
    sim.close()
    return anchor_rankings


def oracle_verify_multi_batch(candidates, anchors, lookahead):
    """Verify multi-predicate candidates via self-consistent rollout."""
    args_list = [(cand, anchors, lookahead) for cand in candidates]
    n = len(args_list)
    n_workers = min(cpu_count(), n)
    if n <= 4:
        all_rankings = [_verify_candidate_multi(a) for a in args_list]
    else:
        with Pool(processes=n_workers) as pool:
            all_rankings = pool.map(_verify_candidate_multi, args_list,
                                     chunksize=max(1, n // (n_workers * 4)))
    return [{"rankings": r} for r in all_rankings]


def _find_cex_multi_seed(args):
    """Find CEX states for a multi-predicate policy in one episode."""
    seed, preds_rankings_ser, default_ranking, max_steps, lookahead, max_cex = args
    preds_rankings = [(p[0], p[1]) for p in preds_rankings_ser]
    env = gym.make("Pendulum-v1")
    sim = gym.make("Pendulum-v1").unwrapped
    cex = []
    obs, _ = env.reset(seed=seed)
    for step in range(max_steps):
        if len(cex) >= max_cex:
            break
        state = obs[:NUM_DIMS].tolist()
        if step % 10 == 0:
            theta, omega = _state_to_theta_omega(state)
            terminal_penalties = {}
            for aid in range(NUM_ACTIONS):
                terminal_penalties[aid] = _rollout_action_multi(
                    sim, aid, preds_rankings, default_ranking,
                    theta, omega, lookahead)
            ranking = _ranking_from_terminal(terminal_penalties)
            expected = default_ranking
            for pred, r in preds_rankings:
                if eval_pred(pred, state):
                    expected = r
                    break
            if ranking != expected:
                cex.append(state)
        action_id = _policy_action(state, preds_rankings, default_ranking)
        obs, _, terminated, truncated, _ = env.step(ACTION_MAP[action_id])
        if terminated or truncated:
            break
    env.close()
    sim.close()
    return cex


def find_cex_multi(preds_rankings, default_ranking, seeds, max_steps, lookahead, max_cex):
    """Find CEX states for multi-predicate policy."""
    per_seed_max = max(5, max_cex // len(seeds))
    preds_ser = [(p, r) for p, r in preds_rankings]
    args_list = [(s, preds_ser, default_ranking, max_steps, lookahead, per_seed_max)
                 for s in seeds]
    n = len(args_list)
    n_workers = min(cpu_count(), n)
    if n <= 4:
        results = [_find_cex_multi_seed(a) for a in args_list]
    else:
        with Pool(processes=n_workers) as pool:
            results = pool.map(_find_cex_multi_seed, args_list)
    all_cex = []
    for c in results:
        all_cex.extend(c)
    return all_cex[:max_cex]


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
        max_steps = request.get("max_steps", 200)
        states, n_stab = collect_states(chain, default, seeds, max_steps)
        result = {"states": states, "n_stabilized": n_stab, "n_episodes": len(seeds)}

    elif cmd == "explore":
        chain = [(p, a) for p, a in request.get("chain", [])]
        default = request["default"]
        seeds = request.get("seeds", list(range(50)))
        max_steps = request.get("max_steps", 200)
        lookahead = request.get("lookahead", 20)
        steps_data, n_stab, n_total = explore_episodes(chain, default, seeds, max_steps, lookahead)
        result = {
            "steps": steps_data,
            "n_stabilized": n_stab,
            "n_episodes": n_total,
        }

    elif cmd == "score":
        candidates = request["candidates"]
        stage_action = request["stage_action"]
        default = request["default"]
        chain_so_far = [(p, a) for p, a in request.get("chain_so_far", [])]
        chain_after = [(p, a) for p, a in request.get("chain_after", [])]
        seeds = request.get("seeds", list(range(30)))
        max_steps = request.get("max_steps", 300)
        baseline_chain = chain_so_far + chain_after
        baseline_reward, baseline_stab = run_episodes(baseline_chain, default, seeds, max_steps)
        scores = score_batch(candidates, stage_action, default, chain_so_far, seeds, chain_after, max_steps)
        result = {
            "scores": scores,
            "baseline_reward": baseline_reward,
            "baseline_landings": baseline_stab,
        }

    elif cmd == "profile":
        chain = [(p, a) for p, a in request.get("chain", [])]
        default = request["default"]
        seeds = request.get("seeds", list(range(50)))
        max_steps = request.get("max_steps", 500)
        lookahead = request.get("lookahead", 20)
        profiles = profile_actions(chain, default, seeds, max_steps, lookahead)
        result = {"profiles": profiles, "n_states": len(profiles)}

    elif cmd == "collect_anchors":
        seeds = request.get("seeds", list(range(20)))
        max_steps = request.get("max_steps", 100)
        n_per_episode = request.get("n_per_episode", 5)
        states = collect_anchor_states(seeds, max_steps, n_per_episode)
        result = {"anchors": states}

    elif cmd == "profile_anchors":
        anchors = request["anchors"]
        chain = [(p, a) for p, a in request.get("chain", [])]
        default = request["default"]
        lookahead = request.get("lookahead", 20)
        rankings = profile_anchor_states(anchors, chain, default, lookahead)
        result = {"rankings": rankings}

    elif cmd == "oracle_verify":
        candidates = request["candidates"]
        anchors = request["anchors"]
        lookahead = request.get("lookahead", 20)
        results_list = oracle_verify_batch(candidates, anchors, lookahead)
        result = {"results": results_list}

    elif cmd == "find_cex":
        pred = request["pred"]
        r_true = request["r_true"]
        r_false = request["r_false"]
        seeds = request.get("seeds", list(range(20)))
        max_steps = request.get("max_steps", 500)
        lookahead = request.get("lookahead", 20)
        max_cex = request.get("max_cex", 50)
        cex = find_cex_states(pred, r_true, r_false, seeds, max_steps, lookahead, max_cex)
        result = {"cex_states": cex}

    elif cmd == "oracle_verify_multi":
        candidates = request["candidates"]
        anchors = request["anchors"]
        lookahead = request.get("lookahead", 20)
        results_list = oracle_verify_multi_batch(candidates, anchors, lookahead)
        result = {"results": results_list}

    elif cmd == "find_cex_multi":
        preds_rankings = [(p["pred"], p["ranking"]) for p in request["preds"]]
        default_ranking = request["default_ranking"]
        seeds = request.get("seeds", list(range(20)))
        max_steps = request.get("max_steps", 500)
        lookahead = request.get("lookahead", 20)
        max_cex = request.get("max_cex", 50)
        cex = find_cex_multi(preds_rankings, default_ranking, seeds,
                              max_steps, lookahead, max_cex)
        result = {"cex_states": cex}

    else:
        result = {"error": f"Unknown command: {cmd}"}

    with open(resp_file, 'w') as f:
        json.dump(result, f)


if __name__ == "__main__":
    main()
