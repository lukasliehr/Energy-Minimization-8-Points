import Blueprint.FiniteDefinitions
import Blueprint.Target

/-! Clean proof port from Energy-Minimization-8-Points,
commit 50d14bc06bd41f61573eb6a36eedb8d00759af8f,
Logarithmic/Thomson8/SphereFrame.lean:24-28. Target Point is the supplied EuclideanSpace.
No legacy Data, certificate, or fixed-exponent target is imported. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Blueprint.Thomson.GenericMoments

theorem inner_frame (b : OrthonormalBasis (Fin 3) ℝ Point) (y z : Point) : inner ℝ y z = inner ℝ (b 0) y * inner ℝ (b 0) z + inner ℝ (b 1) y * inner ℝ (b 1) z + inner ℝ (b 2) y * inner ℝ (b 2) z := by
  have h := b.sum_inner_mul_inner y z
  simpa [Fin.sum_univ_succ, real_inner_comm, add_assoc] using h.symm

end Blueprint.Thomson.GenericMoments
namespace Blueprint.Thomson.Finite
theorem generic_moments_inner_frame (b : OrthonormalBasis (Fin 3) ℝ Point) (y z : Point) : inner ℝ y z = inner ℝ (b 0) y * inner ℝ (b 0) z + inner ℝ (b 1) y * inner ℝ (b 1) z + inner ℝ (b 2) y * inner ℝ (b 2) z :=
  GenericMoments.inner_frame b y z
#check generic_moments_inner_frame
#print axioms generic_moments_inner_frame
end Blueprint.Thomson.Finite

