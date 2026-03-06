#!/usr/bin/env python3
"""
Empirical HP lattice-folding learning curve with CEGIS-style refinement.

Protocol:
  - Choose a peptide sequence (default: HHPHHHPHHPHH).
  - Build an oracle from exact lookahead on the finite search tree.
  - Stream pairwise action-ranking observations from oracle states.
  - After each observation, fold the whole peptide with the current
    synthesized ranking model and record achieved energy.

Outputs:
  - CSV: observations vs achieved energy
  - Summary on stdout
"""

from __future__ import annotations

from dataclasses import dataclass
from functools import lru_cache
from itertools import combinations
from pathlib import Path
import csv
import argparse


ACTIONS = ("L", "S", "R")
ACTION_ORDER = {"S": 0, "L": 1, "R": 2}
DIRS = ((1, 0), (0, 1), (-1, 0), (0, -1))  # E, N, W, S
NEI4 = ((1, 0), (-1, 0), (0, 1), (0, -1))


@dataclass(frozen=True)
class State:
    positions: tuple[tuple[int, int], ...]
    heading: int
    next_idx: int


def turn(heading: int, action: str) -> int:
    if action == "L":
        return (heading + 1) % 4
    if action == "R":
        return (heading - 1) % 4
    return heading


def addp(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
    return (a[0] + b[0], a[1] + b[1])


def is_adjacent(a: tuple[int, int], b: tuple[int, int]) -> bool:
    return abs(a[0] - b[0]) + abs(a[1] - b[1]) == 1


def full_contacts(seq: str, positions: tuple[tuple[int, int], ...]) -> int:
    # Count each H-H contact once: i<j, non-consecutive, Manhattan-adjacent.
    n = len(seq)
    c = 0
    for i in range(n):
        if seq[i] != "H":
            continue
        for j in range(i + 2, n):
            if seq[j] == "H" and is_adjacent(positions[i], positions[j]):
                c += 1
    return c


def build_env(seq: str):
    n = len(seq)

    @lru_cache(maxsize=None)
    def step_info(state: State, action: str):
        if state.next_idx >= n:
            return None
        new_heading = turn(state.heading, action)
        delta = DIRS[new_heading]
        new_pos = addp(state.positions[-1], delta)
        if new_pos in state.positions:
            return None

        new_positions = state.positions + (new_pos,)
        i = state.next_idx

        gain = 0
        if seq[i] == "H":
            # New contacts with earlier non-consecutive H residues.
            for j in range(0, i - 1):
                if seq[j] == "H" and is_adjacent(new_pos, new_positions[j]):
                    gain += 1

        nxt = State(new_positions, new_heading, i + 1)
        return (nxt, gain)

    @lru_cache(maxsize=None)
    def best_contacts(state: State) -> int:
        if state.next_idx >= n:
            return 0
        best = None
        for a in ACTIONS:
            info = step_info(state, a)
            if info is None:
                continue
            nxt, gain = info
            val = gain + best_contacts(nxt)
            if best is None or val > best:
                best = val
        return 0 if best is None else best

    @lru_cache(maxsize=None)
    def action_values(state: State):
        vals = {}
        for a in ACTIONS:
            info = step_info(state, a)
            if info is None:
                continue
            nxt, gain = info
            vals[a] = gain + best_contacts(nxt)
        return vals

    @lru_cache(maxsize=None)
    def state_ctx(state: State):
        vals = action_values(state)
        x, y = state.positions[-1]
        md = abs(x) + abs(y)
        placed = len(state.positions)
        next_is_h = state.next_idx < n and seq[state.next_idx] == "H"

        out = {
            "next-is-h": next_is_h,
            "idx-even": (state.next_idx % 2 == 0),
            "idx-ge-half": (state.next_idx * 2 >= n),
            "x-pos": (x > 0),
            "x-neg": (x < 0),
            "y-pos": (y > 0),
            "y-neg": (y < 0),
            "md-le2": (md <= 2),
            "md-ge4": (md >= 4),
            "h-e": (state.heading == 0),
            "h-n": (state.heading == 1),
            "h-w": (state.heading == 2),
            "h-s": (state.heading == 3),
            "placed-ge-6": (placed >= 6),
            "placed-ge-10": (placed >= 10),
            "legal-L": ("L" in vals),
            "legal-S": ("S" in vals),
            "legal-R": ("R" in vals),
            "gain-L": ("L" in vals and vals["L"] > 0),
            "gain-S": ("S" in vals and vals["S"] > 0),
            "gain-R": ("R" in vals and vals["R"] > 0),
        }
        return out

    return step_info, best_contacts, action_values, state_ctx


class Prog:
    __slots__ = ("kind", "args")

    def __init__(self, kind: str, *args):
        self.kind = kind
        self.args = args

    def ev(self, ctx: dict[str, bool]) -> bool:
        if self.kind == "T":
            return True
        if self.kind == "F":
            return False
        if self.kind == "feat":
            return ctx[self.args[0]]
        if self.kind == "neg":
            return not self.args[0].ev(ctx)
        if self.kind == "and":
            return self.args[0].ev(ctx) and self.args[1].ev(ctx)
        if self.kind == "or":
            return self.args[0].ev(ctx) or self.args[1].ev(ctx)
        raise ValueError(f"Unknown kind {self.kind}")


def build_version_space(feature_names: list[str]):
    vs = [Prog("T"), Prog("F")]
    lits = [Prog("feat", f) for f in feature_names]
    vs.extend(lits)
    vs.extend([Prog("neg", p) for p in lits])
    for a, b in combinations(lits, 2):
        vs.append(Prog("and", a, b))
        vs.append(Prog("or", a, b))
    return vs


def refine(vs, ctx: dict[str, bool], expected: bool):
    return [p for p in vs if p.ev(ctx) == expected]


def unanimous(vs, ctx: dict[str, bool]):
    if not vs:
        return None
    v0 = vs[0].ev(ctx)
    for p in vs[1:]:
        if p.ev(ctx) != v0:
            return None
    return v0


def pair_key(a: str, b: str):
    return tuple(sorted((a, b)))


def fold_with_model(seq: str, step_info, state_ctx, pair_vses):
    # Standard anchored start for lattice HP:
    # residue 0 at (0,0), residue 1 at (1,0), heading East.
    state = State(((0, 0), (1, 0)), 0, 2)
    while state.next_idx < len(seq):
        vals = []
        legal = []
        for a in ACTIONS:
            info = step_info(state, a)
            if info is not None:
                legal.append(a)
                vals.append((a, info))
        if not legal:
            break
        if len(legal) == 1:
            chosen = legal[0]
        else:
            ctx = state_ctx(state)
            scores = {a: 0.0 for a in legal}
            for a, b in combinations(legal, 2):
                k = pair_key(a, b)
                u = unanimous(pair_vses[k], ctx)
                # pair_vses[k] models (k[0] >= k[1]).
                if u is None:
                    scores[a] += 0.5
                    scores[b] += 0.5
                elif u:
                    scores[k[0]] += 1.0
                else:
                    scores[k[1]] += 1.0
            chosen = max(legal, key=lambda x: (scores[x], -ACTION_ORDER[x]))
        state = step_info(state, chosen)[0]
    contacts = full_contacts(seq, state.positions)
    return state, contacts, -contacts


def enumerate_observations(seq: str, action_values):
    start = State(((0, 0), (1, 0)), 0, 2)
    seen = set()
    obs = []

    def dfs(state: State):
        if state in seen:
            return
        seen.add(state)
        vals = action_values(state)
        legal = sorted(vals.keys(), key=lambda a: ACTION_ORDER[a])
        for a, b in combinations(legal, 2):
            # Observation means "a is at least as good as b".
            obs.append((state, a, b, vals[a] >= vals[b]))
        for a in legal:
            nxt = step_info(state, a)[0]
            dfs(nxt)

    step_info, _, _, _ = build_env(seq)
    dfs(start)
    # Stable order: earlier prefixes first.
    obs.sort(key=lambda t: (t[0].next_idx, len(t[0].positions), t[1], t[2]))
    return obs


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--sequence",
        default="HHPHHHPHHPHH",
        help="HP sequence (default: HHPHHHPHHPHH)",
    )
    parser.add_argument(
        "--output",
        default="protein_folding_learning_curve.csv",
        help="CSV output path",
    )
    parser.add_argument(
        "--max-observations",
        type=int,
        default=0,
        help="Limit observations (0 means all)",
    )
    args = parser.parse_args()

    seq = args.sequence.strip().upper()
    if len(seq) < 3 or any(c not in {"H", "P"} for c in seq):
        raise ValueError("Sequence must be >=3 chars and only contain H/P")

    step_info, best_contacts, action_values, state_ctx = build_env(seq)
    obs = enumerate_observations(seq, action_values)
    if args.max_observations > 0:
        obs = obs[: args.max_observations]

    feature_names = list(state_ctx(State(((0, 0), (1, 0)), 0, 2)).keys())
    base_vs = build_version_space(feature_names)
    pair_vses = {
        ("L", "S"): list(base_vs),
        ("L", "R"): list(base_vs),
        ("R", "S"): list(base_vs),
    }

    out_path = Path(args.output)
    if not out_path.is_absolute():
        out_path = Path(__file__).resolve().parent / out_path
    out_path.parent.mkdir(parents=True, exist_ok=True)

    start = State(((0, 0), (1, 0)), 0, 2)
    oracle_opt_contacts = best_contacts(start)

    rows = []
    best_so_far = None
    final_state, contacts, energy = fold_with_model(seq, step_info, state_ctx, pair_vses)
    best_so_far = energy
    rows.append(
        {
            "observations": 0,
            "contacts": contacts,
            "energy": energy,
            "best_energy_so_far": best_so_far,
            "oracle_best_contacts": oracle_opt_contacts,
            "oracle_best_energy": -oracle_opt_contacts,
            "placed_residues": len(final_state.positions),
            "trajectory_complete": int(final_state.next_idx >= len(seq)),
        }
    )

    for i, (state, a, b, outcome) in enumerate(obs, start=1):
        ctx = state_ctx(state)
        k = pair_key(a, b)
        expected = outcome if (a, b) == k else (not outcome)
        pair_vses[k] = refine(pair_vses[k], ctx, expected)

        final_state, contacts, energy = fold_with_model(seq, step_info, state_ctx, pair_vses)
        if energy < best_so_far:
            best_so_far = energy
        rows.append(
            {
                "observations": i,
                "contacts": contacts,
                "energy": energy,
                "best_energy_so_far": best_so_far,
                "oracle_best_contacts": oracle_opt_contacts,
                "oracle_best_energy": -oracle_opt_contacts,
                "placed_residues": len(final_state.positions),
                "trajectory_complete": int(final_state.next_idx >= len(seq)),
            }
        )

    with out_path.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(
            f,
            fieldnames=[
                "observations",
                "contacts",
                "energy",
                "best_energy_so_far",
                "oracle_best_contacts",
                "oracle_best_energy",
                "placed_residues",
                "trajectory_complete",
            ],
        )
        w.writeheader()
        w.writerows(rows)

    best_seen = min(r["energy"] for r in rows)
    print(f"Sequence: {seq} (n={len(seq)})")
    print(f"Observations used: {len(obs)}")
    print(f"Version-space size per pair (init): {len(base_vs)}")
    print(f"Oracle best contacts: {oracle_opt_contacts} (energy {-oracle_opt_contacts})")
    print(f"Initial synthesized energy: {rows[0]['energy']}")
    print(f"Best synthesized energy seen: {best_seen}")
    print(f"CSV written: {out_path}")


if __name__ == "__main__":
    main()
