import Blueprint.FiniteDefinitions
import Blueprint.Target

/-! Clean proof port from Energy-Minimization-8-Points,
commit 50d14bc06bd41f61573eb6a36eedb8d00759af8f,
Logarithmic/Thomson8/Kernels.lean:35-40. Target Point is the supplied EuclideanSpace.
No legacy Data, certificate, or fixed-exponent target is imported. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Blueprint.Thomson.GenericMoments

theorem complex_power_gram (z w : ℂ) (k : ℕ) : ((z * star w) ^ k).re = (z ^ k).re * (w ^ k).re + (z ^ k).im * (w ^ k).im := by
  change ((z * (starRingEnd ℂ) w) ^ k).re = _
  rw [mul_pow, ← map_pow]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

end Blueprint.Thomson.GenericMoments
namespace Blueprint.Thomson.Finite
theorem generic_moments_complex_power_gram (z w : ℂ) (k : ℕ) : ((z * star w) ^ k).re = (z ^ k).re * (w ^ k).re + (z ^ k).im * (w ^ k).im :=
  GenericMoments.complex_power_gram z w k
#check generic_moments_complex_power_gram
#print axioms generic_moments_complex_power_gram
end Blueprint.Thomson.Finite

