import AllS.Units.N_FI.N_generic_moments.N_complex_power_gram
import AllS.Units.N_FI.N_generic_moments.N_kernelQ_complex
import AllS.Units.N_FI.N_generic_moments.N_tangent_normSq
import AllS.Units.N_FI.N_generic_moments.N_tangent_re
import Blueprint.FiniteDefinitions
import Blueprint.Target

/-! Clean generic proof port from upstream commit
50d14bc06bd41f61573eb6a36eedb8d00759af8f, Logarithmic/Thomson8.
Source declarations: SphereFrame.spherical_kernel_features.
Only target type aliases and explicit real symEval replace legacy interfaces. -/
noncomputable section
open scoped BigOperators InnerProductSpace
open Blueprint.Thomson.Finite (Configuration)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Blueprint.Thomson.GenericMoments

theorem spherical_kernel_features (b : OrthonormalBasis (Fin 3) ℝ Point)
    (y z : Point) (hy : ‖y‖=1) (hz : ‖z‖=1) (k : ℕ) :
    kernelQ k ⟪b 0,y⟫_ℝ ⟪b 0,z⟫_ℝ ⟪y,z⟫_ℝ =
      ((tangentComplex b y)^k).re*((tangentComplex b z)^k).re +
      ((tangentComplex b y)^k).im*((tangentComplex b z)^k).im := by
  rw [kernelQ_complex k _ _ _ (tangentComplex b y * star (tangentComplex b z))
    (tangent_re b y z)]
  · exact complex_power_gram _ _ _
  · simp [Complex.normSq_mul,Complex.star_def,Complex.normSq_conj,tangent_normSq b y hy,
      tangent_normSq b z hz]

end Blueprint.Thomson.GenericMoments
namespace Blueprint.Thomson.Finite
open GenericMoments
theorem generic_moments_frame_features (b : OrthonormalBasis (Fin 3) ℝ Point)
    (y z : Point) (hy : ‖y‖=1) (hz : ‖z‖=1) (k : ℕ) :
    kernelQ k ⟪b 0,y⟫_ℝ ⟪b 0,z⟫_ℝ ⟪y,z⟫_ℝ =
      ((tangentComplex b y)^k).re*((tangentComplex b z)^k).re +
      ((tangentComplex b y)^k).im*((tangentComplex b z)^k).im :=
  GenericMoments.spherical_kernel_features b y z hy hz k
#check generic_moments_frame_features
#print axioms generic_moments_frame_features
end Blueprint.Thomson.Finite
