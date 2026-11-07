import AllS.Units.N_AI.N_correction_bounds.FloorSupport
import AllS.Units.N_AI.N_gram_replay.N_uncorrected_floor

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def ShortMetricFloorSupportStatement : Prop :=
  ∀ {n : ℕ} (K Z E : Matrix (Fin n) (Fin n) ℝ) (θ : ℝ),
    E = Z*K-1 → QuadraticBound (E+E.transpose) θ →
    ∀ v, (1-θ)*squaredEuclidean v ≤ quadratic (Z*K*K.transpose*Z.transpose) v

theorem quadratic_one {n : ℕ} (v : Fin n → ℝ) :
    quadratic (1 : Matrix (Fin n) (Fin n) ℝ) v = squaredEuclidean v := by
  classical
  simp [quadratic, squaredEuclidean, Matrix.one_apply, pow_two]

theorem quadratic_square_nonneg {n : ℕ} (E : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) : 0 ≤ quadratic (E*E.transpose) v := by
  rw [quadratic_eq_dotProduct]
  exact (matrix_square_posSemidef E).dotProduct_mulVec_nonneg v

theorem shortMetricFloorSupport : ShortMetricFloorSupportStatement := by
  intro n K Z E θ hE hbound v
  have hproduct : Z*K*K.transpose*Z.transpose =
      1+(E+E.transpose)+E*E.transpose := by
    subst E
    simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_one]
    noncomm_ring
  rw [hproduct, quadratic_add, quadratic_add, quadratic_one]
  have hlow := (abs_le.mp (hbound.2 v)).1
  have hsq := quadratic_square_nonneg E v
  nlinarith

#print ShortMetricFloorSupportStatement
#print axioms shortMetricFloorSupport
end Blueprint.CAP
