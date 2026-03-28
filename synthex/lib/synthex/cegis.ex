defmodule Synthex.CEGIS do
  @moduledoc """
  The parallel Counter-Example Guided Inductive Synthesis (CEGIS) loop.
  """

  alias Synthex.PredProg

  @doc """
  Enumerates the version space up to a given boolean depth.
  """
  def enumerate(features, 0) do
    [:truep, :falsep] ++ Enum.map(features, fn f -> {:feat, f} end)
  end

  def enumerate(features, depth) when depth > 0 do
    prev = enumerate(features, depth - 1)
    negations = Enum.map(prev, fn p -> {:not, p} end)

    # We use a comprehension for Cartesian products to generate combinations
    ands = for p1 <- prev, p2 <- prev, do: {:and, p1, p2}
    ors = for p1 <- prev, p2 <- prev, do: {:or, p1, p2}
    neg_ands = for p1 <- negations, p2 <- prev, do: {:and, p1, p2}
    neg_ors = for p1 <- negations, p2 <- prev, do: {:or, p1, p2}

    prev ++ negations ++ ands ++ ors ++ neg_ands ++ neg_ors
    |> Enum.uniq() # Simple deduplication
  end

  @doc """
  Filters the version space concurrently.
  Only keeps programs that are consistent with ALL observations.
  """
  def refine(version_space, observations, eval_feat_fn) do
    # Task.async_stream is the magic here. It automatically partitions the 
    # version_space list across available CPU cores for concurrent evaluation.
    version_space
    |> Task.async_stream(fn prog ->
      is_consistent =
        Enum.all?(observations, fn {state, target_bool} ->
          PredProg.eval(prog, state, eval_feat_fn) == target_bool
        end)
      
      {prog, is_consistent}
    end, ordered: false) # ordered: false makes it faster as we don't care about output order
    |> Enum.filter(fn {:ok, {_prog, is_consistent}} -> is_consistent end)
    |> Enum.map(fn {:ok, {prog, _is_consistent}} -> prog end)
  end
end
