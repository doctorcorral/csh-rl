defmodule Synthex.PermutationGym do
  @moduledoc """
  Predicate-guided action ranking synthesis for regulation tasks.

  A predicate p partitions the continuous state space into two regions.
  Each region is assigned a complete **ranking** (total order) over all
  actions — e.g. `torque_pos > no_torque > torque_neg`. The agent
  always executes the top-ranked action for its current region.

  This is grounded in the CSHRL coinductive framework:

    - The predicate defines a 2-state abstract system.
    - Each abstract state carries a full action ranking.
    - CoindHomo verifies that the ranking pair is self-consistent
      with the system dynamics for all time (coinductively).
    - The ranking — not just the top action — is what gets formally
      verified, because it encodes the complete preference structure.

  With one predicate and k actions there are (k!)² ranking pairs,
  but pairs sharing the same top actions are observationally equivalent,
  so the search collapses to (k × (k−1)) distinct executable policies.
  The full ranking is recovered for the winning pair and reported for
  formal verification.
  """

  alias Synthex.GymOracle
  alias Synthex.CEGIS

  @doc """
  Synthesize a single-predicate ranking policy.

  ## Arguments
    - `actions` — list of action atoms in default order

  ## Options
    - `:env`          — environment atom (required)
    - `:max_steps`    — max steps per episode (required)
    - `:depth`        — max boolean depth (default 1)
    - `:max_coeff`    — max diagonal coefficient (default 5)
    - `:n_episodes`   — episodes per candidate scoring (default 200)
    - `:top_k`        — depth-0 atoms kept for depth-1 (default 30)
    - `:cegar_rounds` — max CEGAR rounds (default 3)
    - `:top_pairs`    — ranking pairs carried to depth 1 (default 3)
  """
  def solve(actions, opts \\ []) do
    env = Keyword.fetch!(opts, :env)
    max_steps = Keyword.fetch!(opts, :max_steps)
    depth = Keyword.get(opts, :depth, 1)
    max_coeff = Keyword.get(opts, :max_coeff, 5)
    n_episodes = Keyword.get(opts, :n_episodes, 200)
    top_k = Keyword.get(opts, :top_k, 30)
    cegar_rounds = Keyword.get(opts, :cegar_rounds, 3)
    top_pairs = Keyword.get(opts, :top_pairs, 3)

    all_rankings = permutations(actions)
    ranking_pairs = for r1 <- all_rankings, r2 <- all_rankings,
                        hd(r1) != hd(r2), do: {r1, r2}
    val_seeds = Enum.to_list(10_000..10_499)

    IO.puts("══════════════════════════════════════════════════════")
    IO.puts("  Ranking Synthesis — Single Predicate")
    IO.puts("  Env: #{env}")
    IO.puts("  Actions: #{inspect(actions)}")
    IO.puts("  Rankings: #{length(all_rankings)}, Pairs: #{length(ranking_pairs)}")
    IO.puts("  Depth: #{depth}, Episodes: #{n_episodes}, TopK: #{top_k}")
    IO.puts("  CEGAR rounds: #{cegar_rounds}")
    IO.puts("  max_steps: #{max_steps}")
    IO.puts("══════════════════════════════════════════════════════\n")

    IO.puts("  Collecting trajectory states from Gymnasium...")
    {states, _} = GymOracle.get_trajectory_states([], hd(actions),
      env: env, seeds: Enum.to_list(0..39), max_steps: max_steps)
    IO.puts("  #{length(states)} states collected")

    IO.puts("  Generating features in Synthex...")
    features = GymOracle.generate_features(states, env: env, max_coeff: max_coeff)
    IO.puts("  #{length(features)} initial features\n")

    initial_best = {nil, nil, nil, -999_999.0, 0}

    {_final_features, final_best} =
      Enum.reduce(1..cegar_rounds, {features, initial_best}, fn round, {feats, best} ->
        IO.puts("\n████████ CEGAR Round #{round}/#{cegar_rounds} — #{length(feats)} features ████████")

        seed_offset = (round - 1) * n_episodes
        seeds = Enum.to_list(seed_offset..(seed_offset + n_episodes - 1))
        atoms = CEGIS.enumerate(feats, 0)

        # Rankings that share the same top action are observationally equivalent
        # with a single predicate, so we group by (top_true, top_false).
        executable_pairs = ranking_pairs
          |> Enum.uniq_by(fn {r1, r2} -> {hd(r1), hd(r2)} end)

        IO.puts("  #{length(atoms)} predicates × #{length(executable_pairs)} executable ranking pairs\n")

        # ── Depth 0: score all predicates for each executable pair ──
        d0_results =
          Enum.map(executable_pairs, fn {r_true, r_false} ->
            score_ranking_pair(atoms, r_true, r_false, seeds, env, max_steps)
          end)

        {d0_pred, d0_rt, d0_rf, d0_reward, d0_count} = best_from_results(d0_results, atoms)

        IO.puts("\n  ── Best depth-0 predicate: #{format_pred(d0_pred, env)}")
        IO.puts("     p true  → #{format_ranking(d0_rt)}")
        IO.puts("     p false → #{format_ranking(d0_rf)}")
        IO.puts("     reward=#{Float.round(d0_reward, 1)}")

        # ── Depth 1: refine with compound predicates ──
        {round_pred, round_rt, round_rf, _round_reward, _round_count} =
          if depth >= 1 do
            search_depth_1(d0_results, d0_pred, d0_rt, d0_rf, d0_reward, d0_count,
                           atoms, top_k, top_pairs, seeds, env, max_steps)
          else
            {d0_pred, d0_rt, d0_rf, d0_reward, d0_count}
          end

        # ── Validate on held-out seeds ──
        {new_best, feats} =
          if round_pred != nil do
            {val_reward, val_count} = validate_policy(round_pred, round_rt, round_rf, val_seeds, env, max_steps)
            IO.puts("\n  ▸ Validation: reward=#{Float.round(val_reward, 1)} successes=#{val_count}/#{length(val_seeds)}")

            {_, _, _, prev_val, _} = best
            updated_best = if val_reward > prev_val do
              IO.puts("  ★ New best!")
              {round_pred, round_rt, round_rf, val_reward, val_count}
            else
              best
            end

            feats = if round < cegar_rounds do
              cegar_refine(round_pred, round_rt, round_rf, feats, env, max_coeff, max_steps)
            else
              feats
            end

            {updated_best, feats}
          else
            {best, feats}
          end

        {feats, new_best}
      end)

    {best_pred, best_rt, best_rf, best_val, best_stab} = final_best
    print_summary(best_pred, best_rt, best_rf, best_val, best_stab, val_seeds, env)
    {best_pred, best_rt, best_rf}
  end

  # ── Scoring a ranking pair ───────────────────────────────────

  defp score_ranking_pair(candidates, r_true, r_false, seeds, env, max_steps) do
    a_true = hd(r_true)
    a_false = hd(r_false)
    IO.puts("  >> p → #{format_ranking(r_true)},  ¬p → #{format_ranking(r_false)}")

    {scored, baseline, _} =
      GymOracle.score_candidates(candidates, a_true, a_false, [],
        seeds: seeds, chain_after: [], env: env, max_steps: max_steps)

    best = Enum.max_by(scored, fn {_i, r, _l} -> r end, fn -> nil end)

    case best do
      nil ->
        IO.puts("     (no candidates)")
        {r_true, r_false, scored, baseline, nil, nil}

      {idx, reward, count} ->
        delta = Float.round(reward - baseline, 1)
        IO.puts("     Baseline: #{Float.round(baseline, 1)}  Best: #{Float.round(reward, 1)} (Δ=#{delta})  count=#{count}")
        {r_true, r_false, scored, baseline, idx, reward}
    end
  end

  defp best_from_results(results, candidates) do
    results
    |> Enum.filter(fn {_, _, _, _, idx, _} -> idx != nil end)
    |> Enum.max_by(fn {_, _, _, _, _, reward} -> reward end, fn -> nil end)
    |> case do
      nil -> {nil, nil, nil, -999_999.0, 0}
      {r_true, r_false, scored, _, idx, reward} ->
        pred = Enum.at(candidates, idx)
        count = case Enum.find(scored, fn {i, _, _} -> i == idx end) do
          {_, _, c} -> c
          _ -> 0
        end
        {pred, r_true, r_false, reward, count}
    end
  end

  # ── Depth-1 search ──────────────────────────────────────────

  defp search_depth_1(d0_results, d0_pred, d0_rt, d0_rf, d0_reward, d0_count,
                       atoms, top_k, top_pairs_n, seeds, env, max_steps) do
    ranked_pairs =
      d0_results
      |> Enum.filter(fn {_, _, _, _, idx, _} -> idx != nil end)
      |> Enum.sort_by(fn {_, _, _, _, _, r} -> -r end)

    # Global top_k: best atoms across ALL pairs, not per-pair
    top_atoms =
      ranked_pairs
      |> Enum.flat_map(fn {_, _, scored, _, _, _} -> scored end)
      |> Enum.sort_by(fn {_idx, r, _l} -> -r end)
      |> Enum.uniq_by(fn {idx, _r, _l} -> idx end)
      |> Enum.take(top_k)
      |> Enum.map(fn {idx, _r, _l} -> Enum.at(atoms, idx) end)

    negations = Enum.map(top_atoms, fn p -> {:not, p} end)

    d1_candidates =
      (for p <- top_atoms, q <- top_atoms, p != q, do: {:and, p, q}) ++
      (for p <- top_atoms, q <- top_atoms, p != q, do: {:or, p, q}) ++
      (for p <- negations, q <- top_atoms, do: {:and, p, q}) ++
      (for p <- negations, q <- top_atoms, do: {:or, p, q})
      |> Enum.uniq()

    # Greedy: score depth-1 for the single best ranking pair only
    best_pair = hd(ranked_pairs)
    {bp_rt, bp_rf, _, _, _, _} = best_pair

    IO.puts("\n  Depth 1: #{length(d1_candidates)} predicates × best pair only")

    d1_results = [score_ranking_pair(d1_candidates, bp_rt, bp_rf, seeds, env, max_steps)]

    {d1_pred, d1_rt, d1_rf, d1_reward, d1_count} = best_from_results(d1_results, d1_candidates)

    if d1_pred != nil and d1_reward > d0_reward do
      IO.puts("\n  ── Best depth-1 predicate: #{format_pred(d1_pred, env)}")
      IO.puts("     p true  → #{format_ranking(d1_rt)}")
      IO.puts("     p false → #{format_ranking(d1_rf)}")
      IO.puts("     reward=#{Float.round(d1_reward, 1)}")
      {d1_pred, d1_rt, d1_rf, d1_reward, d1_count}
    else
      IO.puts("\n  ── Depth-1 did not improve over depth-0")
      {d0_pred, d0_rt, d0_rf, d0_reward, d0_count}
    end
  end

  # ── Validation ──────────────────────────────────────────────

  defp validate_policy(pred, r_true, r_false, val_seeds, env, max_steps) do
    a_true = hd(r_true)
    a_false = hd(r_false)
    chain = [{pred, a_true}]
    serialized = GymOracle.serialize_chain(chain, env)
    default_int = GymOracle.serialize_action(a_false, env)

    request = %{
      "cmd" => "score",
      "candidates" => [],
      "stage_action" => 0,
      "default" => default_int,
      "chain_so_far" => serialized,
      "chain_after" => [],
      "seeds" => val_seeds,
      "max_steps" => max_steps
    }

    result = call_python(request, env)
    {result["baseline_reward"], result["baseline_landings"] || result["n_stabilized"] || 0}
  end

  # ── CEGAR refinement ───────────────────────────────────────

  defp cegar_refine(pred, r_true, r_false, feats, env, max_coeff, max_steps) do
    IO.puts("\n  ─── CEGAR: refining abstraction ───")
    a_true = hd(r_true)
    a_false = hd(r_false)
    chain = [{pred, a_true}]

    {new_feats, _cex_data, n_cex, n_succ, n_fail} =
      GymOracle.find_counterexamples(chain, a_false, feats,
        env: env, max_coeff: max_coeff, max_steps: max_steps)

    IO.puts("  StateCEGAR: #{n_cex} counterexample states")
    IO.puts("  Policy: #{n_succ} successes, #{n_fail} failures")
    IO.puts("  New features: #{length(new_feats)}")

    if length(new_feats) == 0 do
      IO.puts("  No new features — CEGAR converged!")
      feats
    else
      expanded = feats ++ new_feats
      IO.puts("  Feature pool: #{length(feats)} → #{length(expanded)}")
      expanded
    end
  end

  # ── Python bridge ──────────────────────────────────────────

  defp call_python(request, env) do
    script = GymOracle.oracle_script(env)
    uid = :erlang.unique_integer([:positive])
    tmp_dir = System.tmp_dir!()
    req_file = Path.join(tmp_dir, "synthex_rank_#{uid}.json")
    resp_file = Path.join(tmp_dir, "synthex_rank_resp_#{uid}.json")

    File.write!(req_file, Jason.encode!(request))

    {_output, _exit_code} =
      System.cmd("python3", ["-u", script, req_file, resp_file],
        stderr_to_stdout: true,
        cd: Path.expand("../../..", __DIR__)
      )

    result = Jason.decode!(File.read!(resp_file))
    File.rm(req_file)
    File.rm(resp_file)
    result
  end

  # ── Permutations ───────────────────────────────────────────

  defp permutations([]), do: [[]]
  defp permutations(list) do
    for elem <- list,
        rest <- permutations(list -- [elem]),
        do: [elem | rest]
  end

  # ── Pretty-printing ───────────────────────────────────────

  defp format_ranking(ranking) do
    ranking |> Enum.map(&inspect/1) |> Enum.join(" > ")
  end

  @pend_dims %{0 => "cosθ", 1 => "sinθ", 2 => "ω"}
  @ll_dims %{0 => "x", 1 => "y", 2 => "vx", 3 => "vy", 4 => "θ", 5 => "ω"}

  defp dim_name(:pendulum, d), do: @pend_dims[d] || "d#{d}"
  defp dim_name(_, d), do: @ll_dims[d] || "d#{d}"

  defp format_pred(nil, _env), do: "∅"
  defp format_pred(:truep, _env), do: "⊤"
  defp format_pred(:falsep, _env), do: "⊥"
  defp format_pred({:feat, ["axis", d, t]}, env), do: "#{dim_name(env, d)}<#{t}"
  defp format_pred({:feat, ["diag", i, j, c]}, env), do: "#{c}·#{dim_name(env, i)}+#{dim_name(env, j)}<0"
  defp format_pred({:not, p}, env), do: "¬(#{format_pred(p, env)})"
  defp format_pred({:and, p, q}, env), do: "(#{format_pred(p, env)} ∧ #{format_pred(q, env)})"
  defp format_pred({:or, p, q}, env), do: "(#{format_pred(p, env)} ∨ #{format_pred(q, env)})"
  defp format_pred(other, _env), do: inspect(other)

  @pend_py %{0 => "cos_theta", 1 => "sin_theta", 2 => "omega"}
  @ll_py %{0 => "x", 1 => "y", 2 => "vx", 3 => "vy", 4 => "theta", 5 => "omega"}

  defp dim_py(:pendulum, d), do: @pend_py[d] || "obs[#{d}]"
  defp dim_py(_, d), do: @ll_py[d] || "obs[#{d}]"

  defp print_summary(nil, _, _, _, _, _, _) do
    IO.puts("\n══════════════════════════════════════════════════════")
    IO.puts("  SYNTHESIS COMPLETE — no improving predicate found")
    IO.puts("══════════════════════════════════════════════════════")
  end

  defp print_summary(pred, r_true, r_false, val, stab, val_seeds, env) do
    IO.puts("\n══════════════════════════════════════════════════════")
    IO.puts("  SYNTHESIS COMPLETE")
    IO.puts("  Best validation: reward=#{Float.round(val, 1)} successes=#{stab}/#{length(val_seeds)}")
    IO.puts("══════════════════════════════════════════════════════")

    IO.puts("\nFinal ranking policy (predicate p = #{format_pred(pred, env)}):")
    IO.puts("  p true  → #{format_ranking(r_true)}")
    IO.puts("  p false → #{format_ranking(r_false)}")

    IO.puts("\n=== DEPLOYABLE POLICY ===")
    obs_line = case env do
      :pendulum -> "    cos_theta, sin_theta, omega = obs[:3]"
      _ -> "    x, y, vx, vy, theta, omega = obs[:6]"
    end
    IO.puts("def policy(obs):")
    IO.puts(obs_line)
    IO.puts("    if #{fmt_py(pred, env)}: return #{inspect(hd(r_true))}  # #{format_ranking(r_true)}")
    IO.puts("    return #{inspect(hd(r_false))}  # #{format_ranking(r_false)}")

    IO.puts("\n=== FOR AGDA VERIFICATION ===")
    IO.puts("Predicate: #{format_pred(pred, env)}")
    IO.puts("Ranking when p:  #{format_ranking(r_true)}")
    IO.puts("Ranking when ¬p: #{format_ranking(r_false)}")
  end

  defp fmt_py({:feat, ["axis", d, t]}, env), do: "#{dim_py(env, d)} < #{t}"
  defp fmt_py({:feat, ["diag", i, j, c]}, env), do: "#{c}*#{dim_py(env, i)} + #{dim_py(env, j)} < 0"
  defp fmt_py({:not, p}, env), do: "not (#{fmt_py(p, env)})"
  defp fmt_py({:and, p, q}, env), do: "(#{fmt_py(p, env)}) and (#{fmt_py(q, env)})"
  defp fmt_py({:or, p, q}, env), do: "(#{fmt_py(p, env)}) or (#{fmt_py(q, env)})"
  defp fmt_py(other, _env), do: inspect(other)
end
