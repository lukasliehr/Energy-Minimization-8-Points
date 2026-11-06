import ThomsonNegative.Structure.Packed.IdentityKernel
namespace ThomsonNegative.Structure.Exact

noncomputable def sumWeightedProducts (R : Nat) (weight : Nat → Signed)
    (left right : Nat → Nat) (n : Nat) : Accumulator :=
  Nat.rec (motive := fun _ => Accumulator) (0,0)
    (fun k s => addSigned s (signedMul (weight k)
      (signedMul (polyVal R (left k)) (polyVal R (right k))))) n

structure WeightedEquation extends Equation where
  weight : Nat → Signed
  maxWeight : Nat

noncomputable def WeightedEquation.headers (e : WeightedEquation) : Bool :=
  e.toEquation.headers && allBelow e.terms (fun k => Nat.ble (e.weight k).2 e.maxWeight)

noncomputable def WeightedEquation.arithmetic (e : WeightedEquation) : Bool :=
  equalsSigned
    (scaleAccumulator (polyVal e.radixBits e.scale)
      (sumWeightedProducts e.radixBits e.weight e.left e.right e.terms))
    (signedMul (signedMul (polyVal e.radixBits e.target0) (polyVal e.radixBits e.target1))
      (polyVal e.radixBits e.target2))

def WeightedEquation.separation (e : WeightedEquation) : Bool :=
  Nat.ble 1 e.radixBits &&
    Nat.blt (Nat.mul 2 (Nat.mul (Nat.add (Nat.mul e.terms e.maxWeight) 1)
      (Nat.mul e.coefficientBound (Nat.mul e.coefficientBound e.coefficientBound))))
      (Nat.shiftLeft 1 e.radixBits)

noncomputable def WeightedEquation.check (e : WeightedEquation) : Bool :=
  e.headers && e.separation && e.arithmetic
end ThomsonNegative.Structure.Exact
