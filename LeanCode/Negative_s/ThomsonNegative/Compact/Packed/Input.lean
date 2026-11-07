import ThomsonNegative.Compact.Packed.Core2

namespace ThomsonNegative.Compact.Packed

/-- A positive affine polynomial with an explicit rounding-error allowance. -/
def affineInput (c : Ctx) (a0 a1 e : Nat) : TM :=
  ofPQ c (Nat.add a0 (Nat.shiftLeft a1 c.W)) 0 e

end ThomsonNegative.Compact.Packed
