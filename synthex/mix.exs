defmodule Synthex.MixProject do
  use Mix.Project

  def project do
    [
      app: :synthex,
      version: "0.1.0",
      elixir: "~> 1.18",
      start_permanent: Mix.env() == :prod,
      deps: deps()
    ]
  end

  def application do
    [
      extra_applications: [:logger]
    ]
  end

  defp deps do
    [
      {:flow, "~> 1.2"},
      {:jason, "~> 1.4"}
    ]
  end
end
