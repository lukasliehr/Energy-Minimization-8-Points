import Blueprint.Tail
import Lean_Code.ContactComponents
import Lean_Code.PackingMaximum

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

abbrev ContactAdj := SquareAntiprismVerification.ContactAdj
abbrev ContactReachable := SquareAntiprismVerification.ContactReachable
abbrev ContactReachableWithout := SquareAntiprismVerification.ContactReachableWithout
abbrev PackingInnerBound := SquareAntiprismVerification.PackingInnerBound
abbrev PackingIrreducible := SquareAntiprismVerification.PackingIrreducible
abbrev packingContacts := SquareAntiprismVerification.packingContacts
abbrev packingMaxInner := SquareAntiprismVerification.packingMaxInner

theorem setup_aliases (Y : Fin 8 → Point) (c : ℝ) (i j : Fin 8) :
    ContactAdj Y c i j ↔ i ≠ j ∧ inner ℝ (Y i) (Y j) = c := Iff.rfl

end Blueprint.Thomson.Tail.Implementation
