import AllS.Units.N_AI.N_data.IntervalExpressionGates

namespace Blueprint.CAP

structure QMatrixModel (N m n : ℕ) where
  coeff : Fin (N+1) → Fin m → Fin n → QInterval
  error : Fin m → Fin n → ℚ

/-- Exact coefficient/error inclusion permits the source's outward conversion
from 256-bit scalar endpoints to 112-bit matrix endpoints. -/
def QMatrixModel.FromScalarsGate {N m n : ℕ}
    (S : Fin m → Fin n → QModel N) (R : QMatrixModel N m n) : Prop :=
  (∀ k i j, ((S i j).coeff k).SubsetGate (R.coeff k i j)) ∧
  (∀ i j, (S i j).error ≤ R.error i j)

end Blueprint.CAP
