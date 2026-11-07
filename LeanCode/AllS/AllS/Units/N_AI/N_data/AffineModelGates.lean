import AllS.Units.N_AI.N_data.IntervalExpressionGates

namespace Blueprint.CAP

def qAffineCoefficients (n : ℕ) (c h : ℚ) : Fin (n+2) → ℚ :=
  Fin.cases c (Fin.cases h (fun _ => 0))

def QModel.pointPolynomial {n : ℕ} (a : Fin (n+1) → ℚ) : QModel n :=
  ⟨fun k => QInterval.point (a k),0⟩

def QModel.AffineGate {n : ℕ} (M : QModel (n+1)) (c h : ℚ) : Prop :=
  (∀ k, (M.coeff k).lo ≤ qAffineCoefficients n c h k ∧
    qAffineCoefficients n c h k ≤ (M.coeff k).hi) ∧ 0 ≤ M.error

def QModel.ConstGate {n : ℕ} (M : QModel n) (I : QInterval) : Prop :=
  I.SubsetGate (M.coeff 0) ∧
  (∀ k : Fin (n+1), k ≠ 0 → (M.coeff k).lo ≤ 0 ∧ 0 ≤ (M.coeff k).hi) ∧ 0 ≤ M.error

def QModel.AddGate {n : ℕ} (A B R : QModel n) : Prop :=
  (∀ k, ((A.coeff k).add (B.coeff k)).SubsetGate (R.coeff k)) ∧ A.error+B.error ≤ R.error

def QModel.NegGate {n : ℕ} (A R : QModel n) : Prop :=
  (∀ k, (A.coeff k).neg.SubsetGate (R.coeff k)) ∧ A.error ≤ R.error

def QModel.ScaleGate {n : ℕ} (A R : QModel n) (q : ℚ) : Prop :=
  (∀ k, ((A.coeff k).scale q).SubsetGate (R.coeff k)) ∧ |q| * A.error ≤ R.error

end Blueprint.CAP
