import Blueprint.Target

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

/-- Ordered coordinate tensor; every ordered coordinate tuple occurs once. -/
def oddMoment (r : ℕ) (Y : Fin 8 → Point) (α : Fin r → Fin 3) : ℝ :=
  ∑ i, ∏ j, (Y i) (α j)

theorem inner_pow_coordinates (r : ℕ) (x y : Point) :
    (inner ℝ x y)^r = ∑ α : Fin r → Fin 3, (∏ j, x (α j))*(∏ j, y (α j)) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro α _
  rw [Finset.prod_mul_distrib]
  ring

theorem oddMoment_contraction (r : ℕ) (Y : Fin 8 → Point) (x : Point) :
    ∑ i, (inner ℝ x (Y i))^r =
      ∑ α : Fin r → Fin 3, (∏ j, x (α j))*oddMoment r Y α := by
  simp_rw [inner_pow_coordinates]
  rw [Finset.sum_comm]
  simp [oddMoment, Finset.mul_sum]

theorem oddMoment_square_identity (r : ℕ) (Y : Fin 8 → Point) :
    ∑ i, ∑ j, (inner ℝ (Y i) (Y j))^r =
      ∑ α : Fin r → Fin 3, (oddMoment r Y α)^2 := by
  simp_rw [oddMoment_contraction]
  rw [Finset.sum_comm]
  simp [oddMoment, Finset.sum_mul, pow_two]

theorem oddMoment_multicontraction (r : ℕ) (Y : Fin 8 → Point) (x : Fin r → Point) :
    (∑ i, ∏ j, inner ℝ (x j) (Y i)) =
      ∑ α : Fin r → Fin 3, (∏ j, (x j) (α j))*oddMoment r Y α := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
  simp_rw [Fintype.prod_sum,Finset.prod_mul_distrib]
  rw [Finset.sum_comm]
  simp [oddMoment,Finset.mul_sum,mul_comm]

theorem zero_tensors_norm_square_identity (Y : Fin 8 → Point) :
    (∑ i, ∑ j, inner ℝ (Y i) (Y j)) = ‖∑ i, Y i‖^2 ∧
    (∑ i, ∑ j, (inner ℝ (Y i) (Y j))^3) =
      ∑ α : Fin 3 → Fin 3, (oddMoment 3 Y α)^2 := by
  constructor
  · simp_rw [← inner_sum]
    rw [← sum_inner, real_inner_self_eq_norm_sq]
  · exact oddMoment_square_identity 3 Y

#check zero_tensors_norm_square_identity
#print axioms zero_tensors_norm_square_identity
end Blueprint.Thomson.Finite
