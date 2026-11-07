import ThomsonNegative.Structure.Packed.PolyKernel

/-! Init-only exact polynomial product identities. Hot arithmetic uses Nat only. -/

namespace ThomsonNegative.Structure.Exact

abbrev Signed := Bool × Nat
abbrev Accumulator := Nat × Nat

noncomputable def signedMul (x y : Signed) : Signed :=
  (xor x.1 y.1, Nat.mul x.2 y.2)

noncomputable def addSigned (s : Accumulator) (x : Signed) : Accumulator :=
  Bool.rec (Nat.add s.1 x.2, s.2) (s.1, Nat.add s.2 x.2) x.1

noncomputable def scaleAccumulator (x : Signed) (s : Accumulator) : Accumulator :=
  Bool.rec (Nat.mul x.2 s.1, Nat.mul x.2 s.2)
    (Nat.mul x.2 s.2, Nat.mul x.2 s.1) x.1

noncomputable def sumProducts (R : Nat) (left right : Nat → Nat) (n : Nat) : Accumulator :=
  Nat.rec (motive := fun _ => Accumulator) (0,0)
    (fun k s => addSigned s (signedMul (polyVal R (left k)) (polyVal R (right k)))) n

noncomputable def equalsSigned (s : Accumulator) (x : Signed) : Bool :=
  Bool.rec (Nat.beq s.1 (Nat.add s.2 x.2))
    (Nat.beq (Nat.add s.1 x.2) s.2) x.1

noncomputable def allBelow (n : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k h => h && p k) n

def recordOk (L W x : Nat) : Bool :=
  Nat.ble 1 (fld x 20 12) && Nat.ble (fld x 20 12) W && Nat.ble (fld x 12 8) L

structure Equation where
  radixBits : Nat
  maxLength : Nat
  maxWidth : Nat
  terms : Nat
  left : Nat → Nat
  right : Nat → Nat
  scale : Nat
  target0 : Nat
  target1 : Nat
  target2 : Nat

def Equation.coefficientBound (e : Equation) : Nat :=
  Nat.mul e.maxLength (Nat.shiftLeft 1 (Nat.sub e.maxWidth 1))

noncomputable def Equation.headers (e : Equation) : Bool :=
  recordOk e.maxLength e.maxWidth e.scale &&
  recordOk e.maxLength e.maxWidth e.target0 &&
  recordOk e.maxLength e.maxWidth e.target1 &&
  recordOk e.maxLength e.maxWidth e.target2 &&
  allBelow e.terms (fun k => recordOk e.maxLength e.maxWidth (e.left k) &&
    recordOk e.maxLength e.maxWidth (e.right k))

noncomputable def Equation.arithmetic (e : Equation) : Bool :=
  equalsSigned
    (scaleAccumulator (polyVal e.radixBits e.scale)
      (sumProducts e.radixBits e.left e.right e.terms))
    (signedMul (signedMul (polyVal e.radixBits e.target0) (polyVal e.radixBits e.target1))
      (polyVal e.radixBits e.target2))

def Equation.separation (e : Equation) : Bool :=
  Nat.ble 1 e.radixBits &&
    Nat.blt (Nat.mul 2 (Nat.mul (Nat.add e.terms 1)
      (Nat.mul e.coefficientBound (Nat.mul e.coefficientBound e.coefficientBound))))
      (Nat.shiftLeft 1 e.radixBits)

noncomputable def Equation.check (e : Equation) : Bool :=
  e.headers && e.separation && e.arithmetic

end ThomsonNegative.Structure.Exact
