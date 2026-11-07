import AllS.Units.N_FI.N_generic_moments.N_inner_frame
import AllS.Units.N_FI.N_generic_moments.N_tangent_re
import Blueprint.FiniteDefinitions
import Blueprint.Target

/-! Clean generic proof port from upstream commit
50d14bc06bd41f61573eb6a36eedb8d00759af8f, Logarithmic/Thomson8.
Source declarations: SphereFrame.tangent_normSq.
Only target type aliases and explicit real symEval replace legacy interfaces. -/
noncomputable section
open scoped BigOperators InnerProductSpace
open Blueprint.Thomson.Finite (Configuration)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Blueprint.Thomson.GenericMoments

theorem tangent_normSq (b : OrthonormalBasis (Fin 3) ℝ Point) (y : Point) (hy : ‖y‖=1) :
    Complex.normSq (tangentComplex b y) = 1-⟪b 0,y⟫_ℝ^2 := by
  have h := inner_frame b y y
  rw [real_inner_self_eq_norm_sq,hy] at h
  simp [tangentComplex,Complex.normSq_apply]
  nlinarith

end Blueprint.Thomson.GenericMoments
namespace Blueprint.Thomson.Finite
open GenericMoments
theorem generic_moments_tangent_normSq (b : OrthonormalBasis (Fin 3) ℝ Point) (y : Point) (hy : ‖y‖=1) :
    Complex.normSq (tangentComplex b y) = 1-⟪b 0,y⟫_ℝ^2 :=
  GenericMoments.tangent_normSq b y hy
#check generic_moments_tangent_normSq
#print axioms generic_moments_tangent_normSq
end Blueprint.Thomson.Finite
