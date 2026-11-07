import Pilot.BalancedProof
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin

namespace Blueprint.CAP
open scoped BigOperators

/-- Exact finite hypotheses for one packed integer matrix-polynomial product.
The length and strict radix bounds make the single integer evaluation injective. -/
def PackedMatrixProductGate {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) (List ℤ))
    (B : Matrix (Fin n) (Fin p) (List ℤ))
    (T : Matrix (Fin m) (Fin p) (List ℤ))
    (L R : ℕ) (MA MB MT H : ℤ) : Prop :=
  1 ≤ L ∧ 1 ≤ R ∧ 0 ≤ MA ∧ 0 ≤ MB ∧ 0 ≤ MT ∧
  (n:ℤ)*(min L R:ℕ)*MA*MB+MT < H ∧
  (∀ i h, (A i h).length=L) ∧ (∀ h j, (B h j).length=R) ∧
  (∀ i j, (T i j).length=L+R-1) ∧
  (∀ i h, (A i h).all (fun a => decide (|a|≤MA)) = true) ∧
  (∀ h j, (B h j).all (fun b => decide (|b|≤MB)) = true) ∧
  (∀ i j, (T i j).all (fun t => decide (|t|≤MT)) = true) ∧
  (∀ i j, (∑ h, BalancedProof.encode (2*H) (A i h)*BalancedProof.encode (2*H) (B h j))=
    BalancedProof.encode (2*H) (T i j))

end Blueprint.CAP
