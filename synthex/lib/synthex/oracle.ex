defmodule Synthex.Oracle do
  @moduledoc """
  A generic pairwise oracle that evaluates rollouts for any environment.
  It answers the question: "Is action_a better than action_b?"
  """

  @doc "Evaluates the candidate predicate for a specific independent pair."
  def pol_pairwise(p, state, action_a, action_b, env_mod, eval_fn) do
    if Synthex.PredProg.eval(p, env_mod.state_to_list(state), eval_fn) do
      action_a
    else
      action_b
    end
  end

  @doc "Rolls out a trajectory and accumulates the penalty."
  def penalty_rollout(_state, _action, _p, _action_a, _action_b, _env_mod, _eval_fn, 0), do: 0
  def penalty_rollout(state, action, p, action_a, action_b, env_mod, eval_fn, k) do
    if env_mod.terminal?(state) do
      # Let the environment decide if this terminal state warrants a crash penalty
      env_mod.penalty(state)
    else
      s_prime = env_mod.step(state, action)
      next_action = pol_pairwise(p, s_prime, action_a, action_b, env_mod, eval_fn)
      env_mod.penalty(state) + penalty_rollout(s_prime, next_action, p, action_a, action_b, env_mod, eval_fn, k - 1)
    end
  end

  @doc "Returns true if action_a is strictly better than (or equal to) action_b."
  def oracle_predict(p, s, action_a, action_b, env_mod, eval_fn) do
    k = env_mod.oracle_horizon()
    penalty_a = penalty_rollout(s, action_a, p, action_a, action_b, env_mod, eval_fn, k)
    penalty_b = penalty_rollout(s, action_b, p, action_a, action_b, env_mod, eval_fn, k)
    
    penalty_a <= penalty_b
  end

  @doc "Computes the sum score across all starting states for a candidate predicate."
  def sum_score(p, action_a, action_b, env_mod, eval_fn) do
    h = env_mod.score_horizon()
    
    Enum.reduce(env_mod.starts(), 0, fn s0, acc -> 
      acc + penalty_score(s0, p, action_a, action_b, env_mod, eval_fn, h)
    end)
  end

  defp penalty_score(_state, _p, _action_a, _action_b, _env_mod, _eval_fn, 0), do: 0
  defp penalty_score(state, p, action_a, action_b, env_mod, eval_fn, k) do
    if env_mod.terminal?(state) do
      # If terminal and penalized heavily, score is 0. Else perfect score.
      if env_mod.penalty(state) >= env_mod.crash_penalty() do
        0
      else
        env_mod.max_penalty()
      end
    else
      action = pol_pairwise(p, state, action_a, action_b, env_mod, eval_fn)
      s_prime = env_mod.step(state, action)
      
      step_score = env_mod.max_penalty() - env_mod.penalty(state)
      step_score + penalty_score(s_prime, p, action_a, action_b, env_mod, eval_fn, k - 1)
    end
  end

  @doc "Collects a trajectory under the current pairwise policy."
  def collect(_state, _p, _action_a, _action_b, _env_mod, _eval_fn, 0), do: []
  def collect(state, p, action_a, action_b, env_mod, eval_fn, n) do
    if env_mod.terminal?(state) do
      []
    else
      action = pol_pairwise(p, state, action_a, action_b, env_mod, eval_fn)
      s_prime = env_mod.step(state, action)
      [state | collect(s_prime, p, action_a, action_b, env_mod, eval_fn, n - 1)]
    end
  end
end
