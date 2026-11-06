import AllS.Units.N_AI.N_data.StructuredResidualGates

namespace Blueprint.CAP
open scoped BigOperators

def StructuredCenterGate {n r : ℕ} (R : Fin r → QModel n)
    (c : Fin r → Fin (n+1) → ℚ) (E : Fin r → ℚ) : Prop :=
  ∀ i, (∑ k, max |((R i).coeff k).lo-c i k| |((R i).coeff k).hi-c i k|)+
    (R i).error ≤ E i

end Blueprint.CAP
