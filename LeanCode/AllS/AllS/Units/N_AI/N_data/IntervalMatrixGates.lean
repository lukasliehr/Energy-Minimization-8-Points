import AllS.Units.N_AI.N_data.IntervalExpressionGates
import Mathlib.Data.Matrix.Basic

namespace Blueprint.CAP
open scoped BigOperators

/-- Rational interval checks for every entry of a complete matrix product. -/
def QMatrixProductGate {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) QInterval)
    (B : Matrix (Fin n) (Fin p) QInterval)
    (C : Matrix (Fin m) (Fin p) QInterval) : Prop :=
  ∀ i j, (QInterval.sum fun h => (A i h).mul (B h j)).SubsetGate (C i j)

instance {m n p : ℕ} (A : Matrix (Fin m) (Fin n) QInterval)
    (B : Matrix (Fin n) (Fin p) QInterval)
    (C : Matrix (Fin m) (Fin p) QInterval) : Decidable (QMatrixProductGate A B C) := by
  unfold QMatrixProductGate QInterval.SubsetGate
  infer_instance

/-- A symmetric majorant may use the smaller of the two transposed entry bounds.
The positive weights and complete weighted row sums are checked rationally. -/
def WeightedMajorantGate {n : ℕ} (C : Matrix (Fin n) (Fin n) QInterval)
    (M : Matrix (Fin n) (Fin n) ℚ) (w : Fin n → ℚ) (γ : ℚ) : Prop :=
  (∀ i j, min (C i j).mag (C j i).mag ≤ M i j) ∧
  (∀ i j, M i j = M j i) ∧
  (∀ i j, 0 ≤ M i j) ∧
  (∀ i, 0 < w i) ∧ 0 ≤ γ ∧
  ∀ i, ∑ j, M i j * w j / w i ≤ γ

instance {n : ℕ} (C : Matrix (Fin n) (Fin n) QInterval)
    (M : Matrix (Fin n) (Fin n) ℚ) (w : Fin n → ℚ) (γ : ℚ) :
    Decidable (WeightedMajorantGate C M w γ) := by
  unfold WeightedMajorantGate
  letI : Decidable (∀ i j, min (C i j).mag (C j i).mag ≤ M i j) :=
    @Nat.decidableForallFin n _ (fun i =>
      @Nat.decidableForallFin n _ (fun j => inferInstance))
  letI : Decidable (∀ i j, M i j = M j i) :=
    @Nat.decidableForallFin n _ (fun i =>
      @Nat.decidableForallFin n _ (fun j => inferInstance))
  letI : Decidable (∀ i j, 0 ≤ M i j) :=
    @Nat.decidableForallFin n _ (fun i =>
      @Nat.decidableForallFin n _ (fun j => inferInstance))
  letI : Decidable (∀ i, 0 < w i) := inferInstance
  letI : Decidable (∀ i, ∑ j, M i j * w j / w i ≤ γ) := inferInstance
  infer_instance

end Blueprint.CAP
