/-!
# Packed RF records: decoding only (Init-only; imported by data and leaf modules)

A rational kernel coefficient is `(Σ numₖ aᵏ / scaleN) / (Σ denₖ aᵏ / scaleD)` with integer lists; the old
catalogue literal coefficients are exactly `numₖ / scaleN` and `denₖ / scaleD`. Denominators are shared
(the 557 D12 records use 28 distinct denominator polynomials), so a table has

* numerator records: `lenN, scaleN, denIdx, num (biased by 2^25) …` (fixed `R` slots of 26 bits),
* denominator records: `lenD, scaleD, den (biased) …` (fixed `R'` slots of 26 bits),

stored in hex `Nat` chunks of `per` records. Python mirror: `CoeffMap/gen/rf_d12.py` (`decode_rec`).
-/

namespace ThomsonCompact.CoeffMap

/-- The first `n` base-`2^W` digits of `x` (structural recursion, explicit `Nat` primitives). -/
def slots (W : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, x => Nat.land x (Nat.sub (Nat.shiftLeft 1 W) 1) :: slots W n (Nat.shiftRight x W)

/-- Digit `i` of `x` in base `2^W`. -/
def slotAt (W x i : Nat) : Nat := Nat.land (Nat.shiftRight x (Nat.mul W i)) (Nat.sub (Nat.shiftLeft 1 W) 1)

/-- Biased 26-bit signed integer. -/
def unbias (v : Nat) : Int := Int.subNatNat v 33554432

/-- `(Σ numₖ aᵏ / scaleN) / (Σ denₖ aᵏ / scaleD)`. -/
structure RFRec where
  num : List Int
  scaleN : Nat
  den : List Int
  scaleD : Nat

/-- Slots `lenN, scaleN, denIdx, num…` ↦ `(num, scaleN, denIdx)`. -/
def numOfSlots : List Nat → List Int × Nat × Nat
  | lenN :: sc :: d :: rest => ((rest.take lenN).map unbias, sc, d)
  | _ => ([], 1, 0)

/-- Slots `lenD, scaleD, den…` ↦ `(den, scaleD)`. -/
def denOfSlots : List Nat → List Int × Nat
  | lenD :: sc :: rest => ((rest.take lenD).map unbias, sc)
  | _ => ([], 1)

/-- Fixed-size record `k` (`R` slots of width `W`) of a table in chunks of `per` records. -/
def tableSlots (chunk : Nat → Nat) (W R per k : Nat) : List Nat :=
  slots W R (Nat.shiftRight (chunk (k / per)) (Nat.mul (Nat.mul W R) (k % per)))

/-- Record `k` of a numerator table with its shared denominator. -/
def tableRec (numChunk denChunk : Nat → Nat) (W R per R' per' k : Nat) : RFRec :=
  let n := numOfSlots (tableSlots numChunk W R per k)
  let d := denOfSlots (tableSlots denChunk W R' per' n.2.2)
  ⟨n.1, n.2.1, d.1, d.2⟩

end ThomsonCompact.CoeffMap
