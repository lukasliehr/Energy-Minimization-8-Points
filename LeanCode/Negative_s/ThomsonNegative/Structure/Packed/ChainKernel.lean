import ThomsonNegative.Structure.Packed.MatrixKernel

namespace ThomsonNegative.Structure.Exact

structure ProductChain where
  length : Nat
  node : Nat → Nat
  factor : Nat → Nat
  radixBits : Nat
  maxLength : Nat
  maxWidth : Nat

noncomputable def ProductChain.equation (c : ProductChain) (k : Nat) : Equation where
  radixBits := c.radixBits
  maxLength := c.maxLength
  maxWidth := c.maxWidth
  terms := 1
  left := fun _ => c.node k
  right := fun _ => c.factor k
  scale := oneRecord
  target0 := c.node (Nat.add k 1)
  target1 := oneRecord
  target2 := oneRecord

noncomputable def ProductChain.check (c : ProductChain) : Bool :=
  allBelow c.length (fun k => (c.equation k).check)

end ThomsonNegative.Structure.Exact
