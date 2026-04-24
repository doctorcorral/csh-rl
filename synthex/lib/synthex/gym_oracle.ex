defmodule Synthex.GymOracle do
  @moduledoc """
  Bridge to Python Gymnasium adapters + all learning logic for Gym-in-the-loop synthesis.

  Python scripts are thin adapters that only interact with the environment.
  All feature generation, CEGAR counterexample detection, and abstraction
  refinement logic lives here in Synthex.
  """

  @lunarlander_actions %{
    do_nothing: 0,
    fire_left: 1,
    fire_main: 2,
    fire_right: 3
  }

  @pendulum_actions %{
    torque_neg: 0,
    no_torque: 1,
    torque_pos: 2
  }

  @pong_actions %{
    up: 0,
    noop: 1,
    down: 2
  }

  @cartpole_actions %{
    left: 0,
    right: 1
  }

  @acrobot_actions %{
    torque_neg: 0,
    no_torque: 1,
    torque_pos: 2
  }

  @mountaincar_actions %{
    push_left: 0,
    no_push: 1,
    push_right: 2
  }

  @breakout_actions %{
    right: 0,
    noop: 1,
    left: 2
  }

  @cliffwalking_actions %{
    up: 0,
    right: 1,
    down: 2,
    left: 3
  }

  @bipedal_actions %{
    bit_off: 0,
    bit_on: 1
  }

  @tetris_actions %{
    left: 0,
    right: 1,
    rotate: 2,
    down: 3,
    noop: 4
  }

  def action_map(:lunarlander), do: @lunarlander_actions
  def action_map(:pendulum), do: @pendulum_actions
  def action_map(:pong), do: @pong_actions
  def action_map(:cartpole), do: @cartpole_actions
  def action_map(:acrobot), do: @acrobot_actions
  def action_map(:mountaincar), do: @mountaincar_actions
  def action_map(:breakout), do: @breakout_actions
  def action_map(:cliffwalking), do: @cliffwalking_actions
  def action_map(:bipedal), do: @bipedal_actions
  def action_map(:tetris), do: @tetris_actions
  def action_map(_), do: @lunarlander_actions

  def oracle_script(:lunarlander),
    do: Path.expand("../../../scripts/gym_lunarlander_ranking_oracle.py", __DIR__)
  def oracle_script(:pendulum),
    do: Path.expand("../../../scripts/gym_pendulum_oracle.py", __DIR__)
  def oracle_script(:pong),
    do: Path.expand("../../../scripts/gym_pong_oracle.py", __DIR__)
  def oracle_script(:cartpole),
    do: Path.expand("../../../scripts/gym_cartpole_oracle.py", __DIR__)
  def oracle_script(:acrobot),
    do: Path.expand("../../../scripts/gym_acrobot_oracle.py", __DIR__)
  def oracle_script(:mountaincar),
    do: Path.expand("../../../scripts/gym_mountaincar_oracle.py", __DIR__)
  def oracle_script(:breakout),
    do: Path.expand("../../../scripts/gym_breakout_oracle.py", __DIR__)
  def oracle_script(:cliffwalking),
    do: Path.expand("../../../scripts/gym_cliffwalking_oracle.py", __DIR__)
  def oracle_script(:bipedal),
    do: Path.expand("../../../scripts/gym_bipedal_oracle.py", __DIR__)
  def oracle_script(:tetris),
    do: Path.expand("../../../scripts/gym_tetris_oracle.py", __DIR__)
  def oracle_script(_), do: oracle_script(:lunarlander)

  def num_dims(:pendulum), do: 3
  def num_dims(:lunarlander), do: 6
  def num_dims(:pong), do: 6
  def num_dims(:cartpole), do: 4
  def num_dims(:acrobot), do: 6
  def num_dims(:mountaincar), do: 2
  def num_dims(:breakout), do: 5
  def num_dims(:cliffwalking), do: 2
  def num_dims(:bipedal), do: 24
  def num_dims(:tetris), do: 8
  def num_dims(_), do: 6

  # ── Public API: Environment Interaction ────────────────────────

  @doc "Run episodes in Gymnasium, return raw states visited."
  def get_trajectory_states(chain, default_action, opts \\ []) do
    env = Keyword.get(opts, :env, :lunarlander)
    seeds = Keyword.get(opts, :seeds, Enum.to_list(0..39))
    max_steps = Keyword.get(opts, :max_steps, 300)

    request = %{
      "cmd" => "collect_states",
      "chain" => serialize_chain(chain, env),
      "default" => serialize_action(default_action, env),
      "seeds" => seeds,
      "max_steps" => max_steps
    }

    result = call_python(request, env)
    {result["states"], result["n_stabilized"] || result["n_landings"] || 0}
  end

  @doc """
  Run episodes with multi-step lookahead (Pendulum only).
  At sampled steps, tries each action then follows the policy for
  `lookahead` steps total. Returns per-step [state, chosen, %{aid => N-step reward}].
  """
  def explore(chain, default_action, opts \\ []) do
    env = Keyword.get(opts, :env, :pendulum)
    seeds = Keyword.get(opts, :seeds, Enum.to_list(0..49))
    max_steps = Keyword.get(opts, :max_steps, 200)
    lookahead = Keyword.get(opts, :lookahead, 20)

    request = %{
      "cmd" => "explore",
      "chain" => serialize_chain(chain, env),
      "default" => serialize_action(default_action, env),
      "seeds" => seeds,
      "max_steps" => max_steps,
      "lookahead" => lookahead
    }

    result = call_python(request, env)
    {result["steps"], result["n_stabilized"], result["n_episodes"]}
  end

  @doc "Score candidate predicates against Gymnasium."
  def score_candidates(candidates, stage_action, default_action, chain_so_far, opts \\ []) do
    env = Keyword.get(opts, :env, :lunarlander)
    seeds = Keyword.get(opts, :seeds, Enum.to_list(0..29))
    chain_after = Keyword.get(opts, :chain_after, [])
    max_steps = Keyword.get(opts, :max_steps, 300)

    serialized_candidates = Enum.map(candidates, &serialize_pred/1)

    request = %{
      "cmd" => "score",
      "candidates" => serialized_candidates,
      "stage_action" => serialize_action(stage_action, env),
      "default" => serialize_action(default_action, env),
      "chain_so_far" => serialize_chain(chain_so_far, env),
      "chain_after" => serialize_chain(chain_after, env),
      "seeds" => seeds,
      "max_steps" => max_steps
    }

    result = call_python(request, env)

    scored =
      Enum.map(result["scores"], fn s ->
        {s["idx"], s["reward"], s["stabilized"] || s["landings"] || 0}
      end)

    {scored, result["baseline_reward"], result["baseline_landings"]}
  end

  # ── Learning Logic: Feature Generation ─────────────────────────

  @doc """
  Generate features from raw trajectory states.
  Axis features at percentile thresholds + near-zero band, plus diagonal features.
  """
  def generate_features(states, opts \\ []) do
    env = Keyword.get(opts, :env, :lunarlander)
    max_coeff = Keyword.get(opts, :max_coeff, 5)
    n_dims = num_dims(env)

    axis_feats = generate_axis_features(states, n_dims)
    diag_feats = generate_diag_features(n_dims, max_coeff)
    sq_diag_feats = generate_sq_diag_features(n_dims, max_coeff)
    prod_feats = generate_product_features(states, n_dims)

    axis_feats ++ diag_feats ++ sq_diag_feats ++ prod_feats
  end

  defp generate_axis_features(states, n_dims) do
    for dim <- 0..(n_dims - 1),
        t <- axis_thresholds(states, dim) do
      ["axis", dim, t]
    end
  end

  defp axis_thresholds(states, dim) do
    vals = Enum.map(states, fn s -> Enum.at(s, dim) end)
    percentiles = percentile_values(vals, Enum.to_list(0..100//2))
    near_zero = for i <- -15..15, do: i / 100.0

    ([0.0] ++ percentiles ++ near_zero)
    |> Enum.map(&Float.round(&1 * 1.0, 6))
    |> Enum.uniq()
    |> Enum.sort()
  end

  defp generate_diag_features(n_dims, max_coeff) do
    coeffs = for c <- 1..max_coeff, v <- [c, -c], do: v

    for i <- 0..(n_dims - 1),
        j <- 0..(n_dims - 1),
        i != j,
        c <- coeffs do
      ["diag", i, j, c]
    end
  end

  defp generate_sq_diag_features(n_dims, max_coeff) do
    coeffs =
      for c <- [0.01, 0.05, 0.1, 0.2, 0.5] ++ Enum.to_list(1..max_coeff),
          v <- [c, -c], do: v

    for i <- 0..(n_dims - 1),
        j <- 0..(n_dims - 1),
        i != j,
        c <- coeffs do
      ["sq_diag", i, j, c]
    end
  end

  defp generate_product_features(states, n_dims) when n_dims < 2, do: []
  defp generate_product_features(states, n_dims) do
    pairs = for i <- 0..(n_dims - 2), j <- (i + 1)..(n_dims - 1), do: {i, j}

    Enum.flat_map(pairs, fn {i, j} ->
      products = Enum.map(states, fn s -> Enum.at(s, i) * Enum.at(s, j) end)
      thresholds = percentile_values(products, Enum.to_list(0..100//5))
      near_zero = for k <- -10..10, do: k / 20.0

      ts =
        ([0.0] ++ thresholds ++ near_zero)
        |> Enum.map(&Float.round(&1 * 1.0, 6))
        |> Enum.uniq()
        |> Enum.sort()

      Enum.map(ts, fn t -> ["prod", i, j, t] end)
    end)
  end

  # ── Learning Logic: CEGAR Feature Refinement ──────────────────

  @doc """
  Generic CEGAR feature refinement: run the current policy, collect
  trajectory states, generate new features from regions the policy visits.
  Works for any environment — no explore/state-restore required.

  Returns {new_features, n_successes, n_failures}.
  """
  def refine_features(chain, default_action, existing_features, opts \\ []) do
    env = Keyword.get(opts, :env, :lunarlander)
    max_coeff = Keyword.get(opts, :max_coeff, 5)
    n_dims = num_dims(env)
    seeds = Keyword.get(opts, :cegar_seeds, Enum.to_list(0..49))

    {states, n_succ} = get_trajectory_states(chain, default_action,
      env: env, seeds: seeds, max_steps: Keyword.get(opts, :max_steps, 300))

    existing_set = MapSet.new(existing_features, fn f -> List.to_tuple(f) end)

    new_axis = generate_axis_features(states, n_dims)
      |> Enum.reject(fn f -> MapSet.member?(existing_set, List.to_tuple(f)) end)

    new_diag = generate_diag_features(n_dims, max_coeff)
      |> Enum.reject(fn f -> MapSet.member?(existing_set, List.to_tuple(f)) end)

    new_features = Enum.uniq(new_axis ++ new_diag)
    {new_features, n_succ, length(seeds) - n_succ}
  end

  @doc """
  StateCEGAR for environments with multi-step lookahead (explore).
  Uses per-state regret to find counterexamples, generates targeted
  features around those states, AND returns CEX data for hard filtering.

  Returns {new_features, cex_data, n_cex, n_successes, n_failures}.
  """
  def find_counterexamples(chain, default_action, existing_features, opts \\ []) do
    env = Keyword.get(opts, :env, :pendulum)
    max_coeff = Keyword.get(opts, :max_coeff, 5)
    n_dims = num_dims(env)
    regret_threshold = Keyword.get(opts, :regret_threshold, 0.5)
    max_cex = Keyword.get(opts, :max_cex, 100)

    {steps_data, n_stab, n_episodes} = explore(chain, default_action, opts)

    cex_with_regret =
      steps_data
      |> Enum.map(fn [state, chosen, rewards_map] ->
        chosen_reward = Map.get(rewards_map, to_string(chosen), 0.0)
        best_reward = rewards_map |> Map.values() |> Enum.max()
        {state, best_reward - chosen_reward}
      end)
      |> Enum.filter(fn {_state, regret} -> regret > regret_threshold end)
      |> Enum.sort_by(fn {_state, regret} -> -regret end)

    cex_states = cex_with_regret |> Enum.take(max_cex) |> Enum.map(fn {s, _} -> s end)

    existing_set = MapSet.new(existing_features, fn f -> List.to_tuple(f) end)

    cex_axis =
      for dim <- 0..(n_dims - 1),
          state <- cex_states,
          offset <- [-0.02, -0.01, 0.0, 0.01, 0.02],
          t = Float.round(Enum.at(state, dim) + offset, 6),
          feat = ["axis", dim, t],
          not MapSet.member?(existing_set, List.to_tuple(feat)) do
        feat
      end
      |> Enum.uniq()

    diag_new =
      generate_diag_features(n_dims, max_coeff)
      |> Enum.reject(fn f -> MapSet.member?(existing_set, List.to_tuple(f)) end)

    new_features = Enum.uniq(cex_axis ++ diag_new)

    # Extract CEX oracle data for principled hard filtering
    cex_data = extract_cex_data(steps_data, env, max_cex: max_cex, regret_threshold: regret_threshold)

    IO.puts("  Top regrets: #{inspect(Enum.take(cex_with_regret, 5) |> Enum.map(fn {_, r} -> Float.round(r, 1) end))}")

    {new_features, cex_data, length(cex_with_regret), n_stab, n_episodes - n_stab}
  end

  # ── Local predicate evaluation (pure Elixir, no Python) ─────

  def eval_pred(:truep, _state), do: true
  def eval_pred(:falsep, _state), do: false
  def eval_pred({:feat, ["axis", dim, t]}, state), do: Enum.at(state, dim) < t
  def eval_pred({:feat, ["diag", i, j, c]}, state), do: c * Enum.at(state, i) + Enum.at(state, j) < 0
  def eval_pred({:feat, ["sq_diag", i, j, c]}, state), do: c * Enum.at(state, i) * Enum.at(state, i) + Enum.at(state, j) < 0
  def eval_pred({:feat, ["prod", i, j, t]}, state), do: Enum.at(state, i) * Enum.at(state, j) < t
  def eval_pred({:not, p}, state), do: not eval_pred(p, state)
  def eval_pred({:and, p, q}, state), do: eval_pred(p, state) and eval_pred(q, state)
  def eval_pred({:or, p, q}, state), do: eval_pred(p, state) or eval_pred(q, state)

  def eval_chain([], default, _state), do: default
  def eval_chain([{pred, action} | rest], default, state) do
    if eval_pred(pred, state), do: action, else: eval_chain(rest, default, state)
  end

  # ── Hard consistency filter (principled StateCEGAR viable_on?) ──

  @doc """
  Filter candidates by consistency with the oracle at CEX states.
  A candidate is viable if the chain (with this candidate inserted)
  produces the optimal action at ≥ threshold fraction of CEX states.

  Mirrors the original StateCEGAR's `viable_on?` hard constraint.
  """
  def filter_viable(candidates, action, before, after_chain, default, cex_data, threshold \\ 1.0) do
    n_cex = length(cex_data)
    min_ok = ceil(threshold * n_cex)

    Enum.filter(candidates, fn pred ->
      chain = before ++ [{pred, action}] ++ after_chain
      n_ok = Enum.count(cex_data, fn {state, rewards_map} ->
        chosen = eval_chain(chain, default, state)
        {best_action, _} = Enum.max_by(rewards_map, fn {_a, r} -> r end)
        chosen == best_action
      end)
      n_ok >= min_ok
    end)
  end

  @doc """
  Progressive relaxation: try strict consistency first, then relax
  until viable candidates are found. Degrades gracefully to no filter.
  """
  def filter_viable_relaxed(candidates, action, before, after_chain, default, cex_data) do
    thresholds = [1.0, 0.9, 0.8, 0.7, 0.5]

    result = Enum.reduce_while(thresholds, nil, fn threshold, _acc ->
      viable = filter_viable(candidates, action, before, after_chain, default, cex_data, threshold)
      if length(viable) > 0 do
        pct = round(threshold * 100)
        IO.puts("    CEX filter: #{length(candidates)} → #{length(viable)} viable (#{pct}% consistency)")
        {:halt, viable}
      else
        {:cont, nil}
      end
    end)

    case result do
      nil ->
        IO.puts("    CEX filter: no viable at any threshold, using all #{length(candidates)}")
        candidates
      viable -> viable
    end
  end

  def reverse_action_map(env) do
    action_map(env) |> Enum.map(fn {k, v} -> {v, k} end) |> Map.new()
  end

  defp extract_cex_data(steps_data, env, opts) do
    rev_map = reverse_action_map(env)
    max_cex = Keyword.get(opts, :max_cex, 100)
    threshold = Keyword.get(opts, :regret_threshold, 0.5)

    steps_data
    |> Enum.map(fn [state, chosen, rewards] ->
      chosen_r = Map.get(rewards, to_string(chosen), 0.0)
      best_r = rewards |> Map.values() |> Enum.max()
      {state, chosen, rewards, best_r - chosen_r}
    end)
    |> Enum.filter(fn {_, _, _, regret} -> regret > threshold end)
    |> Enum.sort_by(fn {_, _, _, regret} -> -regret end)
    |> Enum.take(max_cex)
    |> Enum.map(fn {state, _chosen, rewards, _regret} ->
      atom_rewards =
        rewards
        |> Enum.map(fn {k, v} -> {Map.get(rev_map, String.to_integer(k)), v} end)
        |> Map.new()
      {state, atom_rewards}
    end)
  end

  # ── Utilities ──────────────────────────────────────────────────

  defp percentile_values(vals, percentiles) do
    sorted = Enum.sort(vals)
    n = length(sorted)
    if n == 0 do
      []
    else
      Enum.map(percentiles, fn p ->
        idx = min(round(p / 100.0 * (n - 1)), n - 1)
        Enum.at(sorted, idx)
      end)
    end
  end

  # ── Python bridge ──────────────────────────────────────────────

  defp call_python(request, env) do
    script = oracle_script(env)
    uid = :erlang.unique_integer([:positive])
    tmp_dir = System.tmp_dir!()
    req_file = Path.join(tmp_dir, "synthex_req_#{uid}.json")
    resp_file = Path.join(tmp_dir, "synthex_resp_#{uid}.json")

    File.write!(req_file, Jason.encode!(request))

    {_output, exit_code} =
      System.cmd("python3", ["-u", script, req_file, resp_file],
        stderr_to_stdout: true,
        cd: Path.expand("../../..", __DIR__)
      )

    if exit_code != 0 do
      IO.puts("  [GymOracle] Python exited with code #{exit_code}")
    end

    result = Jason.decode!(File.read!(resp_file))
    File.rm(req_file)
    File.rm(resp_file)
    result
  end

  # ── Serialization ──────────────────────────────────────────────

  def serialize_pred(:truep), do: "truep"
  def serialize_pred(:falsep), do: "falsep"
  def serialize_pred({:feat, f}) when is_list(f), do: ["feat", f]
  def serialize_pred({:feat, {:axis, d, t}}), do: ["feat", ["axis", d, t]]
  def serialize_pred({:feat, {:diag, i, j, c}}), do: ["feat", ["diag", i, j, c]]
  def serialize_pred({:not, p}), do: ["not", serialize_pred(p)]
  def serialize_pred({:and, p, q}), do: ["and", serialize_pred(p), serialize_pred(q)]
  def serialize_pred({:or, p, q}), do: ["or", serialize_pred(p), serialize_pred(q)]

  def serialize_action(a, env \\ :lunarlander) do
    Map.fetch!(action_map(env), a)
  end

  def serialize_chain(chain, env \\ :lunarlander) do
    Enum.map(chain, fn {pred, action} ->
      [serialize_pred(pred), serialize_action(action, env)]
    end)
  end
end
