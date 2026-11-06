import AllS.Units.N_FI.N_generic_moments.N_inner_frame
import Blueprint.FiniteDefinitions
import Blueprint.Target

/-! Clean generic proof port from upstream commit
50d14bc06bd41f61573eb6a36eedb8d00759af8f, Logarithmic/Thomson8.
Source declarations: SphereFrame.tangentComplex, SphereFrame.tangent_re.
Only target type aliases and explicit real symEval replace legacy interfaces. -/
noncomputable section
open scoped BigOperators InnerProductSpace
open Blueprint.Thomson.Finite (Configuration)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Blueprint.Thomson.GenericMoments

noncomputable def tangentComplex (b : OrthonormalBasis (Fin 3) ℝ Point) (y : Point) : ℂ :=
  ⟨⟪b 1,y⟫_ℝ,⟪b 2,y⟫_ℝ⟩

theorem tangent_re (b : OrthonormalBasis (Fin 3) ℝ Point) (y z : Point) :
    (tangentComplex b y * star (tangentComplex b z)).re =
      ⟪y,z⟫_ℝ - ⟪b 0,y⟫_ℝ * ⟪b 0,z⟫_ℝ := by
  rw [inner_frame b y z]
  simp [tangentComplex,Complex.mul_re,Complex.star_def]
  ring

end Blueprint.Thomson.GenericMoments
namespace Blueprint.Thomson.Finite
open GenericMoments
theorem generic_moments_tangent_re (b : OrthonormalBasis (Fin 3) ℝ Point) (y z : Point) :
    (tangentComplex b y * star (tangentComplex b z)).re =
      ⟪y,z⟫_ℝ - ⟪b 0,y⟫_ℝ * ⟪b 0,z⟫_ℝ :=
  GenericMoments.tangent_re b y z
#check generic_moments_tangent_re
#print axioms generic_moments_tangent_re
end Blueprint.Thomson.Finite
