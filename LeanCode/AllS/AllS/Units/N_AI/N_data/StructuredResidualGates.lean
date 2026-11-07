import AllS.Units.N_AI.N_data.ScalarLinearGates

namespace Blueprint.CAP
open scoped BigOperators

/-- The shared target errors are deliberately kept outside the coordinate box. -/
def StructuredResidualGate {n t b r : ℕ} (H : Fin t → QModel n)
    (B : Fin b → Fin r → QModel n) (q : Fin r → Fin t → ℚ)
    (R : Fin r → QModel n) : Prop :=
  (∀ i k, ((QInterval.sum fun j => (H j |>.coeff k).scale (q i j)).add
    (QInterval.sum fun j => (B j i |>.coeff k).neg)).SubsetGate ((R i).coeff k)) ∧
  ∀ i, (∑ j, (B j i).error) ≤ (R i).error

end Blueprint.CAP
