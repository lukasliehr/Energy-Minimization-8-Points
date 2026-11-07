import AllS.Units.N_AI.N_data.IntervalExpressionGates

namespace Blueprint.CAP

def qPrefix {n : ℕ} (b : Fin (n+1) → QInterval) (k : Fin (n+1)) :
    Fin (n+1) → QInterval := fun j => if j.val < k.val then b j else QInterval.point 0

def qWeightedConvolution {n : ℕ} (a b : Fin (n+1) → QInterval) (m : ℕ) : QInterval :=
  QInterval.sum fun i => QInterval.sum fun j =>
    if i.val+j.val=m then ((a i).scale (i.val:ℚ)).mul (b j) else QInterval.point 0

def qWeightedExcept {n : ℕ} (a b : Fin (n+1) → QInterval) (m : Fin (n+1)) : QInterval :=
  QInterval.sum fun i => QInterval.sum fun j =>
    if i ≠ m ∧ i.val+j.val=m.val then ((a i).scale (i.val:ℚ)).mul (b j) else QInterval.point 0

def qExpStep {n : ℕ} (A R : QModel n) (k : Fin (n+1)) : QInterval :=
  (qWeightedConvolution A.coeff (qPrefix R.coeff k) k.val).scale (1/(k.val:ℚ))

def qLogStep {n : ℕ} (A R : QModel n) (k : Fin (n+1)) : QInterval :=
  (((A.coeff k).scale (k.val:ℚ)).add (qWeightedExcept (qPrefix R.coeff k) A.coeff k).neg).mul
    ((A.coeff 0).scale (k.val:ℚ)).inv

def QModel.ExpRecurrenceGate {n : ℕ} (A R : QModel n) : Prop :=
  ∀ k : Fin (n+1), k ≠ 0 → (qExpStep A R k).SubsetGate (R.coeff k)

def QModel.LogRecurrenceGate {n : ℕ} (A R : QModel n) : Prop :=
  0 < (A.coeff 0).lo ∧ ∀ k : Fin (n+1), k ≠ 0 →
    0 < ((A.coeff 0).scale (k.val:ℚ)).lo ∧
    (qLogStep A R k).SubsetGate (R.coeff k)

end Blueprint.CAP
