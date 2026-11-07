import ThomsonNegative.Structure.Packed.IdentityKernel

namespace ThomsonNegative.Structure.Exact

structure EncodedMatrix (m n : Nat) where
  numerator : Nat → Nat → Nat
  denominator : Nat

def zeroRecord : Nat := 0x100000
def oneRecord : Nat := 0x300201000

noncomputable def EncodedMatrix.identity (n : Nat) : EncodedMatrix n n where
  numerator := fun i j => if Nat.beq i j then oneRecord else zeroRecord
  denominator := oneRecord

noncomputable def EncodedMatrix.zero (m n : Nat) : EncodedMatrix m n where
  numerator := fun _ _ => zeroRecord
  denominator := oneRecord

noncomputable def EncodedMatrix.rows {m n : Nat} (A : EncodedMatrix m n)
    (r : Nat) (idx : Nat → Nat) : EncodedMatrix r n :=
  ⟨fun i j => A.numerator (idx i) j,A.denominator⟩

noncomputable def EncodedMatrix.cols {m n : Nat} (A : EncodedMatrix m n)
    (r : Nat) (idx : Nat → Nat) : EncodedMatrix m r :=
  ⟨fun i j => A.numerator i (idx j),A.denominator⟩

noncomputable def productEquation {m n p : Nat} (A : EncodedMatrix m n)
    (B : EncodedMatrix n p) (C : EncodedMatrix m p)
    (R L W i j : Nat) : Equation where
  radixBits := R
  maxLength := L
  maxWidth := W
  terms := n
  left := A.numerator i
  right := fun k => B.numerator k j
  scale := C.denominator
  target0 := C.numerator i j
  target1 := A.denominator
  target2 := B.denominator

noncomputable def productColumnCheck {m n p : Nat} (A : EncodedMatrix m n)
    (B : EncodedMatrix n p) (C : EncodedMatrix m p) (R L W j : Nat) : Bool :=
  allBelow m (fun i => (productEquation A B C R L W i j).check)

end ThomsonNegative.Structure.Exact
