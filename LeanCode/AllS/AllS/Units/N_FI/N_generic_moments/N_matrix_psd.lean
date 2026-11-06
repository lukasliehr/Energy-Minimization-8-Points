import AllS.Units.N_FI.N_generic_moments.N_moment_entry
import AllS.Units.N_FI.N_generic_moments.N_spherical_kernel_psd
import Blueprint.FiniteDefinitions
import Blueprint.Target

/-! Clean generic proof port from upstream commit
50d14bc06bd41f61573eb6a36eedb8d00759af8f, Logarithmic/Thomson8.
Source declarations: MomentMatrices.momentMatrix_posSemidef.
Only target type aliases and explicit real symEval replace legacy interfaces. -/
noncomputable section
open scoped BigOperators InnerProductSpace
open Blueprint.Thomson.Finite (Configuration)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Blueprint.Thomson.GenericMoments

theorem momentMatrix_posSemidef (m k : ℕ) (y : Configuration) (hy : ∀ i, ‖y i‖=1) :
    (momentMatrix m k y).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro i _
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (sphericalKernel_posSemidef (y i) (hy i) y hy k).mul_mul_conjTranspose_same
      (powerFeatures m (y i) y)

end Blueprint.Thomson.GenericMoments
namespace Blueprint.Thomson.Finite
open GenericMoments
theorem generic_moments_matrix_psd (m k : ℕ) (y : Configuration) (hy : ∀ i, ‖y i‖=1) :
    (momentMatrix m k y).PosSemidef :=
  GenericMoments.momentMatrix_posSemidef m k y hy
#check generic_moments_matrix_psd
#print axioms generic_moments_matrix_psd
end Blueprint.Thomson.Finite
