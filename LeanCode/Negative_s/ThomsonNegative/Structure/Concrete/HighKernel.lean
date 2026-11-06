import ThomsonNegative.Structure.Packed.IdentityKernel
import ThomsonNegative.Certificate.Bridges.RawData
namespace ThomsonNegative.Structure.Concrete.HighKernel
open ThomsonNegative.Structure.Exact
open ThomsonNegative.Certificate.Bridges
def pivot : Nat → Nat | 0 => 82 | 1 => 101 | _ => 68
def positive : Nat → Nat → Nat
 | 0, 2 => 4
 | 1, 2 => 1
 | 2, 0 => 125
 | 4, 2 => 2
 | 7, 0 => 55
 | 8, 0 => 165
 | 9, 0 => 33
 | 12, 0 => 44
 | 13, 0 => 11
 | 15, 0 => 1
 | 16, 1 => 21
 | 17, 1 => 12
 | 18, 1 => 8
 | 20, 1 => 24
 | 21, 1 => 234
 | 23, 1 => 28
 | 26, 1 => 105
 | 27, 1 => 252
 | 28, 1 => 42
 | 31, 1 => 54
 | 32, 1 => 12
 | 34, 1 => 1
 | _, _ => 0
def negative : Nat → Nat → Nat
 | 0, 0 => 55
 | 2, 2 => 4
 | 3, 0 => 8
 | 4, 0 => 15
 | 5, 0 => 125
 | 6, 0 => 95
 | 10, 0 => 77
 | 11, 0 => 77
 | 14, 0 => 11
 | 19, 1 => 120
 | 22, 1 => 36
 | 24, 1 => 240
 | 25, 1 => 180
 | 29, 1 => 112
 | 30, 1 => 96
 | 33, 1 => 12
 | _, _ => 0
noncomputable def positiveTerm (b h r s j : Nat) : Nat :=
  Nat.add (Nat.mul (positive h j) (RawData.positiveSlot b (pivot j) r s))
    (Nat.mul (negative h j) (RawData.negativeSlot b (pivot j) r s))
noncomputable def negativeTerm (b h r s j : Nat) : Nat :=
  Nat.add (Nat.mul (positive h j) (RawData.negativeSlot b (pivot j) r s))
    (Nat.mul (negative h j) (RawData.positiveSlot b (pivot j) r s))
noncomputable def entryCheck (b h r s : Nat) : Bool :=
  Nat.beq
    (Nat.add (RawData.positiveSlot b (Nat.add 67 h) r s)
      (Nat.add (negativeTerm b h r s 0) (Nat.add (negativeTerm b h r s 1) (negativeTerm b h r s 2))))
    (Nat.add (RawData.negativeSlot b (Nat.add 67 h) r s)
      (Nat.add (positiveTerm b h r s 0) (Nat.add (positiveTerm b h r s 1) (positiveTerm b h r s 2))))
noncomputable def blockCheck (b : Nat) : Bool :=
  allBelow 35 (fun h => allBelow (RawData.size b) (fun r =>
    allBelow (RawData.size b) (fun s => entryCheck b h r s)))
end ThomsonNegative.Structure.Concrete.HighKernel
