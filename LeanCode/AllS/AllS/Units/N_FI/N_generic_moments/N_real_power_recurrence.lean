import Blueprint.FiniteDefinitions
import Blueprint.Target

/-! Clean proof port from Energy-Minimization-8-Points,
commit 50d14bc06bd41f61573eb6a36eedb8d00759af8f,
Logarithmic/Thomson8/Kernels.lean:21-24. Target Point is the supplied EuclideanSpace.
No legacy Data, certificate, or fixed-exponent target is imported. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Blueprint.Thomson.GenericMoments

theorem real_power_recurrence (w : ℂ) (k : ℕ) : (w ^ (k + 2)).re = 2 * w.re * (w ^ (k + 1)).re - Complex.normSq w * (w ^ k).re := by
  simp only [pow_succ, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

end Blueprint.Thomson.GenericMoments
namespace Blueprint.Thomson.Finite
theorem generic_moments_real_power_recurrence (w : ℂ) (k : ℕ) : (w ^ (k + 2)).re = 2 * w.re * (w ^ (k + 1)).re - Complex.normSq w * (w ^ k).re :=
  GenericMoments.real_power_recurrence w k
#check generic_moments_real_power_recurrence
#print axioms generic_moments_real_power_recurrence
end Blueprint.Thomson.Finite

