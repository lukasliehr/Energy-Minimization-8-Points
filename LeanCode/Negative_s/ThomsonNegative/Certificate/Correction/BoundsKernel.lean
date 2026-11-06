import ThomsonNegative.Certificate.FactorKernel

/-! Init-only majorants. All quantities are integers with a shared dyadic scale.
The matrix correction is bounded by its polynomial centers and a full error box.
-/
namespace ThomsonNegative.Certificate.Correction

open ThomsonNegative.Certificate

/-- A bounded integer sum; no rational computation occurs in finite leaves. -/
def sumNat (n : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec 0 (fun i acc => Nat.add acc (f i)) n

/-- Absolute numerator of an exactly dyadic metric entry. -/
def metricMagnitude (J : FactorData) (i j : Nat) : Nat :=
  let e := factorEntry J i j
  Nat.add e.1 e.2

/-- Propagate the whole residual error box through one correction entry.
The result has scale `2^(2*S)` when both inputs have scale `2^S`. -/
def errorNumerator (inputs : Nat) (error : Nat → Nat)
    (column : Nat → Nat → Nat → Nat) (u v : Nat) : Nat :=
  sumNat inputs (fun j => Nat.mul (error j) (column u v j))

/-- Absolute congruence by the stored inverse metric. This numerator has
scale `2^(2*S+2*J.bits)`. -/
def congruenceErrorNumerator (n inputs : Nat) (J : FactorData)
    (error : Nat → Nat) (column : Nat → Nat → Nat → Nat) (i j : Nat) : Nat :=
  sumNat n (fun u => sumNat n (fun v =>
    Nat.mul (Nat.mul (metricMagnitude J i u)
      (errorNumerator inputs error column u v)) (metricMagnitude J j v)))

/-- Upward dyadic division. -/
def ceilShift (s x : Nat) : Nat :=
  ThomsonNegative.Compact.Packed.cdiv s x

/-- Combined center and error majorant at scale `2^S`. -/
def entryMajorant (S n inputs centers : Nat) (J : FactorData)
    (centerBound : Nat → Nat → Nat → Nat)
    (error : Nat → Nat) (column : Nat → Nat → Nat → Nat) (i j : Nat) : Nat :=
  Nat.add (sumNat centers (fun k => centerBound k i j))
    (ceilShift (Nat.add S (Nat.mul 2 J.bits))
      (congruenceErrorNumerator n inputs J error column i j))

/-- A uniform `1/3` correction bound leaves room below the `1/2` floor.
Weights are arbitrary positive integers supplied by an untrusted search. -/
def rowCheckAt (S n : Nat) (majorant : Nat → Nat → Nat) (weight : Nat → Nat) (i : Nat) : Bool :=
  Nat.blt 0 (weight i) &&
    Nat.ble (Nat.mul 3 (sumNat n (fun j => Nat.mul (majorant i j) (weight j))))
      (Nat.mul (Nat.pow 2 S) (weight i))

def rowCheck (S n : Nat) (majorant : Nat → Nat → Nat) (weight : Nat → Nat) : Bool :=
  allBelow n (rowCheckAt S n majorant weight)

end ThomsonNegative.Certificate.Correction

namespace ThomsonNegative.Certificate.Correction
open ThomsonNegative.Certificate

/-- Cached raw error contractions avoid repeating the 68-column dot product
inside every metric congruence entry. The equality is checked once per row. -/
def congruenceFromRaw (n : Nat) (J : FactorData)
    (raw : Nat → Nat → Nat) (i j : Nat) : Nat :=
  sumNat n (fun u => sumNat n (fun v =>
    Nat.mul (Nat.mul (metricMagnitude J i u) (raw u v)) (metricMagnitude J j v)))

def entryMajorantFromRaw (S n centers : Nat) (J : FactorData)
    (centerBound : Nat → Nat → Nat → Nat) (raw : Nat → Nat → Nat) (i j : Nat) : Nat :=
  Nat.add (sumNat centers (fun k => centerBound k i j))
    (ceilShift (Nat.add S (Nat.mul 2 J.bits)) (congruenceFromRaw n J raw i j))

end ThomsonNegative.Certificate.Correction
