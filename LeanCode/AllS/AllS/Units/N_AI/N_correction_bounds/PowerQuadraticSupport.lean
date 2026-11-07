import AllS.Units.N_AI.N_correction_bounds.ConvexQuadraticSupport

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

theorem quadraticBound_smul {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (γ c : ℝ)
    (hM : QuadraticBound M γ) : QuadraticBound (c • M) (|c| * γ) := by
  refine ⟨mul_nonneg (abs_nonneg _) hM.1, fun v => ?_⟩
  rw [quadratic_smul,abs_mul]
  calc
    |c| * |quadratic M v| ≤ |c| * (γ*squaredEuclidean v) :=
      mul_le_mul_of_nonneg_left (hM.2 v) (abs_nonneg _)
    _ = (|c| * γ)*squaredEuclidean v := by ring

theorem quadraticBound_sum {ι : Type*} [Fintype ι] {n : ℕ}
    (M : ι → Matrix (Fin n) (Fin n) ℝ) (γ : ι → ℝ)
    (hM : ∀ i, QuadraticBound (M i) (γ i)) :
    QuadraticBound (∑ i, M i) (∑ i, γ i) := by
  classical
  refine ⟨Finset.sum_nonneg (fun i _ => (hM i).1), fun v => ?_⟩
  rw [quadratic_sum]
  calc
    |∑ i, quadratic (M i) v| ≤ ∑ i, |quadratic (M i) v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, γ i * squaredEuclidean v := Finset.sum_le_sum (fun i _ => (hM i).2 v)
    _ = (∑ i, γ i) * squaredEuclidean v := (Finset.sum_mul ..).symm

theorem quadraticBound_mono {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (γ η : ℝ)
    (hM : QuadraticBound M γ) (hle : γ ≤ η) : QuadraticBound M η := by
  refine ⟨hM.1.trans hle, fun v => (hM.2 v).trans ?_⟩
  apply mul_le_mul_of_nonneg_right hle
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem quadraticBound_sum_smul_of_abs_le_one {ι : Type*} [Fintype ι] {n : ℕ}
    (w : ι → ℝ) (M : ι → Matrix (Fin n) (Fin n) ℝ) (γ : ι → ℝ)
    (hw : ∀ i, |w i| ≤ 1) (hM : ∀ i, QuadraticBound (M i) (γ i)) :
    QuadraticBound (∑ i, w i • M i) (∑ i, γ i) := by
  apply quadraticBound_sum
  intro i
  apply quadraticBound_mono _ _ _ (quadraticBound_smul (M i) (γ i) (w i) (hM i))
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (hw i) (hM i).1

#print axioms quadraticBound_smul
#print axioms quadraticBound_sum
#print axioms quadraticBound_mono
#print axioms quadraticBound_sum_smul_of_abs_le_one
end Blueprint.CAP
