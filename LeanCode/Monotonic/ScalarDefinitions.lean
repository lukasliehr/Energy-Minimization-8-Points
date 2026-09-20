import LeanCode.Monotonic.Basic

noncomputable section
namespace SquareAntiprismCounterexample

def g1 (t : ℝ) : ℝ := -1 / ((n : ℝ) + t)^2
def g2 (t : ℝ) : ℝ := 2 / ((n : ℝ) + t)^3
def h1 (t : ℝ) : ℝ := -((n : ℝ) / t) * (dStar / t)^n
def h2 (t : ℝ) : ℝ := ((n : ℝ) * ((n : ℝ) + 1) / t^2) * (dStar / t)^n
def f1 (t : ℝ) : ℝ := g1 t + lambda * h1 t
def f2 (t : ℝ) : ℝ := g2 t + lambda * h2 t

end SquareAntiprismCounterexample
