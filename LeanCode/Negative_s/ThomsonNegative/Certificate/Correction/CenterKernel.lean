import ThomsonNegative.Certificate.Correction.RatioKernel
import ThomsonNegative.Structure.Packed.IdentityKernel

/-! Centers are extracted from the verified residual model itself. There is
no center rounding and no separately trusted coefficient table. -/
namespace ThomsonNegative.Certificate.Correction
open ThomsonNegative.Compact.Packed

def context : Ctx := mkCtx 0 384 640 1408
def sourceContext : Ctx := mkCtx 10 384 448 1024

/-- Degree-zero polynomial record containing coefficient `k` of a source TM.
The word uses a 1024-bit biased slot, identical to the source model. -/
def coefficientRecord (T : TM) (k : Nat) : Nat :=
  let slot := Nat.land (Nat.shiftRight
    (Nat.land (Nat.add T.v sourceContext.hb) sourceContext.maskK)
    (Nat.mul 1024 k)) sourceContext.maskW
  Nat.add (Nat.shiftLeft slot 32) 0x40001000

/-- Exact simultaneous coefficient contraction at a separating integer radix. -/
noncomputable def centerEquation (numerator : Nat → Nat) (residual : Nat → TM)
    (centerWord radix length width k : Nat) : ThomsonNegative.Structure.Exact.Equation where
  radixBits := radix
  maxLength := length
  maxWidth := width
  terms := 68
  left := numerator
  right := fun j => coefficientRecord (residual j) k
  scale := 0x300201000
  target0 := centerWord
  target1 := 0x300201000
  target2 := 0x300201000

end ThomsonNegative.Certificate.Correction
