import AllS.Units.N_FI.N_generic_moments.N_frame_features
import AllS.Units.N_FI.N_generic_moments.N_two_feature_square
import AllS.Units.N_FI.N_generic_moments.N_unit_frame
import Blueprint.FiniteDefinitions
import Blueprint.Target

/-! Clean generic proof port from upstream commit
50d14bc06bd41f61573eb6a36eedb8d00759af8f, Logarithmic/Thomson8.
Source declarations: KernelPositivity.spherical_kernel_nonneg.
Only target type aliases and explicit real symEval replace legacy interfaces. -/
noncomputable section
open scoped BigOperators InnerProductSpace
open Blueprint.Thomson.Finite (Configuration)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Blueprint.Thomson.GenericMoments

theorem spherical_kernel_nonneg {ι : Type*} [Fintype ι] (x : Point) (hx : ‖x‖=1)
    (y : ι → Point) (hy : ∀ i, ‖y i‖=1) (k : ℕ) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i*c j*kernelQ k ⟪x,y i⟫_ℝ ⟪x,y j⟫_ℝ ⟪y i,y j⟫_ℝ := by
  obtain ⟨b,hb⟩ := unit_frame x hx
  simp_rw [←hb,spherical_kernel_features b _ _ (hy _) (hy _)]
  rw [two_feature_square]
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

end Blueprint.Thomson.GenericMoments
namespace Blueprint.Thomson.Finite
open GenericMoments
theorem generic_moments_spherical_kernel_nonneg {ι : Type*} [Fintype ι] (x : Point) (hx : ‖x‖=1)
    (y : ι → Point) (hy : ∀ i, ‖y i‖=1) (k : ℕ) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i*c j*kernelQ k ⟪x,y i⟫_ℝ ⟪x,y j⟫_ℝ ⟪y i,y j⟫_ℝ :=
  GenericMoments.spherical_kernel_nonneg x hx y hy k c
#check generic_moments_spherical_kernel_nonneg
#print axioms generic_moments_spherical_kernel_nonneg
end Blueprint.Thomson.Finite
