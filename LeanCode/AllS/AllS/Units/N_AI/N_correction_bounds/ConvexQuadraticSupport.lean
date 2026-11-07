import AllS.Units.N_AI.N_correction_bounds.FloorSupport

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

theorem quadratic_smul {n : ℕ} (c : ℝ) (M : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) : quadratic (c • M) v = c * quadratic M v := by
  simp only [quadratic,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem quadratic_sum {ι : Type*} [Fintype ι] {n : ℕ}
    (M : ι → Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    quadratic (∑ i, M i) v = ∑ i, quadratic (M i) v := by
  classical
  simp only [quadratic,Matrix.sum_apply,Finset.mul_sum,Finset.sum_mul]
  calc
    _ = ∑ x : Fin n, ∑ i : ι, ∑ y : Fin n, v x * M i x y * v y := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

theorem quadraticBound_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (γ η : ℝ) (hA : QuadraticBound A γ) (hB : QuadraticBound B η) :
    QuadraticBound (A+B) (γ+η) := by
  refine ⟨add_nonneg hA.1 hB.1, fun v => ?_⟩
  rw [quadratic_add]
  calc
    |quadratic A v + quadratic B v| ≤ |quadratic A v| + |quadratic B v| := abs_add_le _ _
    _ ≤ γ*squaredEuclidean v + η*squaredEuclidean v := add_le_add (hA.2 v) (hB.2 v)
    _ = (γ+η)*squaredEuclidean v := by ring

theorem quadraticBound_convex {ι : Type*} [Fintype ι] {n : ℕ}
    (w : ι → ℝ) (M : ι → Matrix (Fin n) (Fin n) ℝ) (γ : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hM : ∀ i, QuadraticBound (M i) γ) :
    QuadraticBound (∑ i, w i • M i) γ := by
  classical
  have hγ : 0 ≤ γ := by
    have h : 0 ≤ ∑ i, w i * γ := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hM i).1)
    simpa only [←Finset.sum_mul,hsum,one_mul] using h
  refine ⟨hγ, fun v => ?_⟩
  rw [quadratic_sum]
  simp_rw [quadratic_smul]
  calc
    |∑ i, w i * quadratic (M i) v| ≤ ∑ i, |w i * quadratic (M i) v| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, w i * |quadratic (M i) v| := by
      simp_rw [abs_mul, abs_of_nonneg (hw _)]
    _ ≤ ∑ i, w i * (γ*squaredEuclidean v) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left ((hM i).2 v) (hw i))
    _ = γ*squaredEuclidean v := by rw [←Finset.sum_mul,hsum,one_mul]

#print axioms quadraticBound_add
#print axioms quadraticBound_convex
end Blueprint.CAP
