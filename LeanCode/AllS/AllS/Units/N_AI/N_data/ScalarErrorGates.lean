import AllS.Units.N_AI.N_data.ScalarRecurrenceGates

namespace Blueprint.CAP
open scoped BigOperators

def QModel.variation {n : ℕ} (A : QModel n) : ℚ :=
  ∑ k ∈ Finset.univ.erase (0:Fin (n+1)), (A.coeff k).mag

def QModel.hull {n : ℕ} (A : QModel n) : QInterval :=
  ⟨(A.coeff 0).lo-A.variation-A.error,(A.coeff 0).hi+A.variation+A.error⟩

def qIntegratedDefect {n : ℕ} (A R : QModel n) : ℚ :=
  ∑ k : Fin (2*n), if n ≤ k.val then
    (qWeightedConvolution A.coeff R.coeff (k.val+1)).mag/((k.val+1:ℕ):ℚ) else 0

def QModel.ExpErrorGate {n : ℕ} (A R : QModel n) (E₁ E₂ : ℚ) : Prop :=
  E₁*qIntegratedDefect A R+E₂*A.error ≤ R.error

def QModel.LogErrorGate {n : ℕ} (A R : QModel n) : Prop :=
  0 < A.hull.lo ∧ (qIntegratedDefect R A+A.error)/A.hull.lo ≤ R.error

end Blueprint.CAP
