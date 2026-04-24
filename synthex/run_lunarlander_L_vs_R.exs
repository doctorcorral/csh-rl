defmodule Synthex.RunLunarLander do
  def run() do
    env_mod = Synthex.Envs.LunarLander
    eval_fn = &Synthex.ContinuousFeatures.eval_feature/2
    IO.puts("Seeding candidate pool from starting trajectories...")
    all_traj = Enum.flat_map(env_mod.starts(), fn s0 ->
      traj_truep = Synthex.Oracle.collect(s0, :truep, :fire_left, :fire_right, env_mod, eval_fn, 30)
      traj_falsep = Synthex.Oracle.collect(s0, :falsep, :fire_left, :fire_right, env_mod, eval_fn, 30)
      traj_truep ++ traj_falsep
    end)
    traj_lists = Enum.map(all_traj, &env_mod.state_to_list/1)
    state_size = length(env_mod.state_to_list(hd(env_mod.starts())))
    
    depth = 1
    max_coeff = 3

    features = Synthex.ContinuousFeatures.generate(traj_lists, state_size, max_coeff)
    IO.puts("Generated #{length(features)} continuous structural features.")
    
    cands = Synthex.CEGIS.enumerate(features, depth)
    IO.puts("Generated #{length(cands)} boolean candidates at Depth #{depth}.\n")
    
    Synthex.StateCEGAR.run_pair(env_mod, :fire_left, :fire_right, cands, 100)
  end
end

Synthex.RunLunarLander.run()
