import AllS.Units.N_AI.N_data.IntervalExpressionGates

namespace Blueprint.CAP
open scoped BigOperators

def QModel.LinearCombinationGate {n m : ℕ} (M : Fin m → QModel n)
    (q : Fin m → ℚ) (R : QModel n) : Prop :=
  (∀ k, (QInterval.sum (fun i => (M i |>.coeff k).scale (q i))).SubsetGate (R.coeff k)) ∧
  (∑ i, |q i| * (M i).error) ≤ R.error

def QModel.ConstantDivisionGate {n : ℕ} (M R : QModel n) (I : QInterval) (μ : ℚ) : Prop :=
  0 < μ ∧ ((0 < I.lo ∧ μ ≤ I.lo) ∨ (I.hi < 0 ∧ μ ≤ -I.hi)) ∧
  (∀ k, ((M.coeff k).mul I.inv).SubsetGate (R.coeff k)) ∧ M.error/μ ≤ R.error

end Blueprint.CAP
