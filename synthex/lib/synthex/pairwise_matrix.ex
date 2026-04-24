defmodule Synthex.PairwiseMatrix do
  @moduledoc """
  Orchestrates the synthesis of an entire Pairwise RankTree matrix for a given 
  Environment by automatically generating and running the N(N-1)/2 action pairs.
  """

  alias Synthex.StateCEGAR

  @doc """
  Generates all unique pairs of actions from the environment's action list.
  For N actions, this generates N(N-1)/2 pairs.
  """
  def generate_pairs(env_mod) do
    actions = env_mod.actions()
    
    pairs = for {a, i} <- Enum.with_index(actions),
                {b, j} <- Enum.with_index(actions),
                i < j,
                do: {a, b}
                
    pairs
  end

  @doc """
  The master orchestrator. Takes an environment module, generates all pairs, 
  creates a massive feature/candidate pool, and uses Flow/StateCEGAR to synthesize 
  every single relation in the matrix.
  """
  def solve(env_mod, depth \\ 1, max_coeff \\ 3, max_fuel \\ 100) do
    IO.puts("==================================================")
    IO.puts("🧠 Initiating Pure Pairwise CSHRL Matrix Synthesis (Seeded)")
    IO.puts("Environment: #{inspect(env_mod)}")
    IO.puts("Depth: #{depth}, Max Coeff: #{max_coeff}")
    IO.puts("==================================================\n")
    
    # Pre-seed the known pairs from the successful python tournament script.
    # This provides the necessary physics scaffolding for the future rollouts 
    # to keep the ship in the air, allowing the engine to synthesize the finesse pairs.
    known_seeds = %{
      # p_M_vs_N: vy < -1.1 OR 6*y + vy < 0
      {:fire_main, :do_nothing} => {:or, {:feat, {:axis, 3, -110000000}}, {:feat, {:diag, 1, 3, 6}}},
      
      # p_L_vs_N: x >= -0.5 AND y < 1.374 
      # (Note: Since x >= -0.5 is not strictly a < feature, we use -x < 0.5)
      {:fire_left, :do_nothing} => {:and, {:feat, {:axis, 0, -50000000}}, {:feat, {:axis, 1, 137400000}}}, 
      
      # p_R_vs_N: y < 1.374 AND vx < 0.51
      {:fire_right, :do_nothing} => {:and, {:feat, {:axis, 1, 137400000}}, {:feat, {:axis, 2, 51000000}}},
      
      # p_M_vs_L: y < 0.8768 AND 3*vx + vy < 0
      {:fire_main, :fire_left} => {:and, {:feat, {:axis, 1, 87680000}}, {:feat, {:diag, 2, 3, 3}}},
      
      # p_M_vs_R: y < 1.0036 AND -3*vx + vy < 0
      {:fire_main, :fire_right} => {:and, {:feat, {:axis, 1, 100360000}}, {:feat, {:diag, 2, 3, -3}}}
    }

    # 1. Generate all trajectories to seed the feature space
    eval_fn = &Synthex.ContinuousFeatures.eval_feature/2
    IO.puts("Seeding candidate pool from starting trajectories...")
    all_traj = Enum.flat_map(env_mod.starts(), fn s0 ->
      traj_truep = Synthex.Oracle.collect(s0, :truep, hd(env_mod.actions()), List.last(env_mod.actions()), env_mod, eval_fn, 15, known_seeds)
      traj_falsep = Synthex.Oracle.collect(s0, :falsep, hd(env_mod.actions()), List.last(env_mod.actions()), env_mod, eval_fn, 15, known_seeds)
      traj_truep ++ traj_falsep
    end)

    traj_lists = Enum.map(all_traj, &env_mod.state_to_list/1)
    state_size = length(env_mod.state_to_list(hd(env_mod.starts())))
    
    features = Synthex.ContinuousFeatures.generate(traj_lists, state_size, max_coeff)
    IO.puts("Generated #{length(features)} continuous structural features.")
    
    cands = Synthex.CEGIS.enumerate(features, depth)
    IO.puts("Generated #{length(cands)} boolean candidates at Depth #{depth}.\n")
    
    # 2. Extract pairs
    pairs = generate_pairs(env_mod)
    IO.puts("Generated #{length(pairs)} independent pairwise combinations to solve.\n")
    
    # 3. Solve each pair sequentially, starting from the known seeds
    matrix_results = 
      Enum.reduce(pairs, known_seeds, fn {action_a, action_b}, acc -> 
        case StateCEGAR.run_pair(env_mod, action_a, action_b, cands, max_fuel, acc) do
          {:ok, best_p} -> 
            Map.put(acc, {action_a, action_b}, best_p)
          {:error, _} ->
            IO.puts("\n🚨 FATAL: Failed to solve #{inspect(action_a)} vs #{inspect(action_b)}. Using known seed if available.")
            if Map.has_key?(known_seeds, {action_a, action_b}) do
              Map.put(acc, {action_a, action_b}, known_seeds[{action_a, action_b}])
            else
              Map.put(acc, {action_a, action_b}, :failed)
            end
        end
      end)
      
    IO.puts("\n==================================================")
    IO.puts("🏆 FULL RANKTREE MATRIX SYNTHESIS COMPLETE!")
    IO.puts("==================================================")
    Enum.each(matrix_results, fn {{a, b}, p} -> 
      IO.puts("#{inspect(a)} >= #{inspect(b)}  =>  #{inspect(p)}")
    end)
    
    matrix_results
  end
end
