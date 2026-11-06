import AllS.Units.N_AI.N_data.RationalBernstein
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Field.Rat

/- Pure rational inputs and gates, kept separate from real analytic semantics.
   These structures contain no proof of an analytic enclosure. -/
namespace Blueprint.CAP
open scoped BigOperators

structure QInterval where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq

def QInterval.mid (I : QInterval) : ℚ := (I.lo + I.hi)/2
def QInterval.rad (I : QInterval) : ℚ := (I.hi - I.lo)/2
def QInterval.mag (I : QInterval) : ℚ := max |I.lo| |I.hi|

structure QModel (n : ℕ) where
  coeff : Fin (n+1) → QInterval
  error : ℚ

def QModel.norm {n : ℕ} (M : QModel n) : ℚ := ∑ i, (M.coeff i).mag

def qProductMid {n : ℕ} (A B : QModel n) (k : ℕ) : ℚ :=
  ∑ i, ∑ j, if i.val+j.val=k then (A.coeff i).mid * (B.coeff j).mid else 0

def qProductRad {n : ℕ} (A B : QModel n) (k : ℕ) : ℚ :=
  ∑ i, ∑ j, if i.val+j.val=k then
    |(A.coeff i).mid| * (B.coeff j).rad +
      (A.coeff i).rad * |(B.coeff j).mid| +
      (A.coeff i).rad * (B.coeff j).rad else 0

def qProductTailPower {n : ℕ} (A B : QModel n) : ℚ :=
  ∑ k : Fin (n+1), (|qProductMid A B (n+1+k.val)| + qProductRad A B (n+1+k.val))

def qProductTailControl {n : ℕ} (A B : QModel n) (i : Fin (n+1)) : ℚ :=
  ∑ k : Fin (n+1), rationalBernsteinTransform n i.val k.val * qProductMid A B (n+1+k.val)

def qProductTailRadius {n : ℕ} (A B : QModel n) (i : Fin (n+1)) : ℚ :=
  ∑ k : Fin (n+1), |rationalBernsteinTransform n i.val k.val| * qProductRad A B (n+1+k.val)

def QModel.ProductGate {n : ℕ} (A B R : QModel n) (T : ℚ) : Prop :=
  (∀ k : Fin (n+1), (R.coeff k).lo ≤ qProductMid A B k.val - qProductRad A B k.val ∧
    qProductMid A B k.val + qProductRad A B k.val ≤ (R.coeff k).hi) ∧
  (qProductTailPower A B ≤ T ∨ ∀ i : Fin (n+1),
    |qProductTailControl A B i| + qProductTailRadius A B i ≤ T) ∧
  T + A.error*B.norm + B.error*A.norm + A.error*B.error ≤ R.error

end Blueprint.CAP
