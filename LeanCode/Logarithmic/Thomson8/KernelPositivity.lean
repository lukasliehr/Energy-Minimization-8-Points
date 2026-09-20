import Thomson8.SphereFrame
import Thomson8.Positivity

namespace Thomson8

open scoped InnerProductSpace

theorem two_feature_square {ι : Type*} [Fintype ι] (c a b : ι → ℝ) :
    (∑ i, ∑ j, c i*c j*(a i*a j+b i*b j)) =
      (∑ i, c i*a i)^2+(∑ i, c i*b i)^2 := by
  simp only [pow_two,Finset.sum_mul,Finset.mul_sum,mul_add,Finset.sum_add_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

theorem spherical_kernel_nonneg {ι : Type*} [Fintype ι] (x : Point) (hx : ‖x‖=1)
    (y : ι → Point) (hy : ∀ i, ‖y i‖=1) (k : ℕ) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i*c j*kernelQ k ⟪x,y i⟫_ℝ ⟪x,y j⟫_ℝ ⟪y i,y j⟫_ℝ := by
  obtain ⟨b,hb⟩ := unit_frame x hx
  simp_rw [←hb,spherical_kernel_features b _ _ (hy _) (hy _)]
  rw [two_feature_square]
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem kernelQ_swap (k : ℕ) (u v t : ℝ) : kernelQ k u v t = kernelQ k v u t := by
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => simp [kernelQ,mul_comm]
  | more k hk hk1 => simp [kernelQ,hk,hk1,mul_comm,mul_left_comm,mul_assoc]

noncomputable def sphericalKernel {ι : Type*} (x : Point) (y : ι → Point) (k : ℕ) :
    Matrix ι ι ℝ := fun i j => kernelQ k ⟪x,y i⟫_ℝ ⟪x,y j⟫_ℝ ⟪y i,y j⟫_ℝ

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

#print axioms sphericalKernel_posSemidef

end Thomson8
