import AllS.Units.N_A.N_interval_semantics

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def CorrectionWeightedQuadraticStatement : Prop :=
  ∀ {n : ℕ} (E M : Matrix (Fin n) (Fin n) ℝ) (w : Fin n→ℝ) (γ : ℝ),
    (∀ i j, E i j=E j i) → (∀ i j, M i j=M j i) →
    (∀ i j, 0 ≤ M i j) → (∀ i j, |E i j| ≤ M i j) →
    (∀ i, 0<w i) → 0 ≤ γ → (∀ i, ∑ j, M i j*w j/w i ≤ γ) →
    QuadraticBound E γ

theorem weighted_pair (x y u v : ℝ) (hu : 0<u) (hv : 0<v) :
    2* |x| * |y| ≤ (v/u)*x^2+(u/v)*y^2 := by
  have hid : (v/u)*x^2+(u/v)*y^2=(v^2*x^2+u^2*y^2)/(u*v) := by
    field_simp
    <;> ring
  rw [hid]
  apply (le_div_iff₀ (mul_pos hu hv)).mpr
  nlinarith only [sq_nonneg (v* |x|-u* |y|), sq_abs x, sq_abs y]

theorem weighted_row_quadratic_bound {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (w v : Fin n→ℝ) (hsym : ∀ i j, M i j=M j i)
    (hM : ∀ i j, 0 ≤ M i j) (hw : ∀ i, 0<w i) :
    (∑ i, ∑ j, M i j* |v i| * |v j|) ≤
      ∑ i, (∑ j, M i j*w j/w i)*v i^2 := by
  have hp : 2*(∑ i, ∑ j, M i j* |v i| * |v j|) ≤
      ∑ i, ∑ j, (M i j*(w j/w i)*v i^2+M i j*(w i/w j)*v j^2) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    have h := mul_le_mul_of_nonneg_left (weighted_pair (v i) (v j) (w i) (w j) (hw i) (hw j)) (hM i j)
    convert h using 1 <;> ring
  have hswap : (∑ i, ∑ j, M i j*(w i/w j)*v j^2)=
      ∑ i, ∑ j, M i j*(w j/w i)*v i^2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsym j i]
  have hfirst : (∑ i, ∑ j, M i j*(w j/w i)*v i^2)=
      ∑ i, (∑ j, M i j*w j/w i)*v i^2 := by
    simp only [Finset.sum_mul, mul_div_assoc]
  simp only [Finset.sum_add_distrib] at hp
  rw [hswap,hfirst] at hp
  linarith

theorem correction_bounds_weighted_quadratic : CorrectionWeightedQuadraticStatement := by
  intro n E M w γ hE hM hMpos hbound hw hγ hrow
  refine ⟨hγ, ?_⟩
  intro v
  have hentry : |quadratic E v| ≤ ∑ i, ∑ j, M i j* |v i| * |v j| := by
    unfold quadratic
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j _
    simp only [abs_mul]
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hbound i j) (abs_nonneg (v i))) (abs_nonneg (v j))
    convert h using 1 <;> ring
  calc
    _ ≤ ∑ i, ∑ j, M i j* |v i| * |v j| := hentry
    _ ≤ ∑ i, (∑ j, M i j*w j/w i)*v i^2 := weighted_row_quadratic_bound M w v hM hMpos hw
    _ ≤ ∑ i, γ*v i^2 := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg (v i))
    _ = γ*squaredEuclidean v := by simp [squaredEuclidean, Finset.mul_sum]

#check correction_bounds_weighted_quadratic
#print CorrectionWeightedQuadraticStatement
#print axioms correction_bounds_weighted_quadratic
end Blueprint.CAP
