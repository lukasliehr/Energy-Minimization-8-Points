import AllS.Units.N_FI.N_generic_moments.N_kernelQ_swap
import AllS.Units.N_FI.N_generic_moments.N_spherical_kernel_nonneg
import Blueprint.FiniteDefinitions
import Blueprint.Target

/-! Clean generic proof port from upstream commit
50d14bc06bd41f61573eb6a36eedb8d00759af8f, Logarithmic/Thomson8.
Source declarations: KernelPositivity.sphericalKernel_symmetric, KernelPositivity.sphericalKernel_posSemidef.
Only target type aliases and explicit real symEval replace legacy interfaces. -/
noncomputable section
open scoped BigOperators InnerProductSpace
open Blueprint.Thomson.Finite (Configuration)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Blueprint.Thomson.GenericMoments

theorem sphericalKernel_symmetric {ι : Type*} (x : Point) (y : ι → Point) (k : ℕ) :
    (sphericalKernel x y k).IsHermitian := by
  ext i j
  simp only [sphericalKernel,Matrix.conjTranspose_apply,star_trivial]
  rw [real_inner_comm (y j) (y i),kernelQ_swap]

theorem sphericalKernel_posSemidef {ι : Type*} [Fintype ι] (x : Point) (hx : ‖x‖=1)
    (y : ι → Point) (hy : ∀ i, ‖y i‖=1) (k : ℕ) :
    (sphericalKernel x y k).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (sphericalKernel_symmetric x y k)
  intro c
  simpa only [sphericalKernel,Matrix.mulVec,dotProduct,star_trivial,Finset.mul_sum,
    mul_assoc,mul_comm,mul_left_comm] using spherical_kernel_nonneg x hx y hy k c

end Blueprint.Thomson.GenericMoments
namespace Blueprint.Thomson.Finite
open GenericMoments
theorem generic_moments_spherical_kernel_psd {ι : Type*} [Fintype ι] (x : Point) (hx : ‖x‖=1)
    (y : ι → Point) (hy : ∀ i, ‖y i‖=1) (k : ℕ) :
    (sphericalKernel x y k).PosSemidef :=
  GenericMoments.sphericalKernel_posSemidef x hx y hy k
#check generic_moments_spherical_kernel_psd
#print axioms generic_moments_spherical_kernel_psd
end Blueprint.Thomson.Finite
