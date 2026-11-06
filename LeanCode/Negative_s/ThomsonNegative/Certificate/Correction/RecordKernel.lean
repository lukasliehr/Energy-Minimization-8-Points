import ThomsonNegative.Certificate.FactorKernel
import ThomsonNegative.Structure.Packed.PolyKernel

/-! Evaluate the exact same polynomial records used by the structural proof.
Only the Horner arithmetic is rounded; decoding remains integer arithmetic.
-/
namespace ThomsonNegative.Certificate.Correction
open ThomsonNegative.Compact.Packed

/-- Rational coefficient arguments of a biased-slot polynomial record. -/
def recordArgs (x denominator : Nat) : List (Bool × Nat × Nat) :=
  let width := Nat.land (Nat.shiftRight x 20) 4095
  let length := Nat.land (Nat.shiftRight x 12) 255
  let payload := Nat.shiftRight x 32
  let bias := Nat.pow 2 (Nat.sub width 1)
  ((List.range length).map (fun k => differenceArg
    (ThomsonNegative.Structure.Exact.fld payload (Nat.mul width k) width, bias)
    denominator)).reverse

def recordTM (c : Ctx) (A : TM) (x denominator : Nat) : TM :=
  hornerRefresh c A (recordArgs x denominator)

end ThomsonNegative.Certificate.Correction
