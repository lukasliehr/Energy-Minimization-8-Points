import ThomsonNegative.Certificate.MatrixKernel
import ThomsonNegative.Certificate.RFKernel

/-! Exact integer square factors. Products use only small Nat arithmetic. -/
namespace ThomsonNegative.Certificate
open ThomsonNegative.Compact.Packed

abbrev NatPair := Nat × Nat

def differenceArg (z : NatPair) (d : Nat) : Bool × Nat × Nat :=
  (Nat.blt z.1 z.2, Nat.add (Nat.sub z.1 z.2) (Nat.sub z.2 z.1), d)

def pairMul (a b : NatPair) : NatPair :=
  (Nat.add (Nat.mul a.1 b.1) (Nat.mul a.2 b.2),
    Nat.add (Nat.mul a.1 b.2) (Nat.mul a.2 b.1))

def pairAdd (a b : NatPair) : NatPair := (Nat.add a.1 b.1, Nat.add a.2 b.2)

def dotNat (f g : Nat → NatPair) (n : Nat) : NatPair :=
  Nat.rec (0,0) (fun k acc => pairAdd acc (pairMul (f k) (g k))) n

/-- A square factor stored by flattened sign-split integer slots. -/
structure FactorData where
  order : Nat
  bits : Nat
  width : Nat
  positive : Nat
  negative : Nat

def factorEntry (F : FactorData) (i j : Nat) : NatPair :=
  let shift := Nat.mul F.width (Nat.add (Nat.mul i F.order) j)
  let mask := Nat.sub (Nat.pow 2 F.width) 1
  (Nat.land (Nat.shiftRight F.positive shift) mask,
    Nat.land (Nat.shiftRight F.negative shift) mask)

def allBelow (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec true (fun k acc => acc && f k) n

def inverseEntryCheck (n : Nat) (F G : FactorData) (i j : Nat) : Bool :=
  let z := dotNat (fun k => factorEntry F i k) (fun k => factorEntry G k j) n
  let expected := cond (Nat.beq i j) (Nat.pow 2 (Nat.add F.bits G.bits)) 0
  Nat.beq z.1 (Nat.add z.2 expected)

def inverseCheck (n : Nat) (F G : FactorData) : Bool :=
  allBelow n (fun i => allBelow n (fun j => inverseEntryCheck n F G i j))

def squareEntryTM (c : Ctx) (F : FactorData) (i j : Nat) : TM :=
  rationalTM c (differenceArg
    (dotNat (fun k => factorEntry F i k) (fun k => factorEntry F j k) F.order)
    (Nat.pow 2 (Nat.mul 2 F.bits)))

def powerTM (c : Ctx) (A : TM) (n : Nat) : TM :=
  Nat.rec (rationalTM c (false,1,1)) (fun _ acc => refresh c (mul c acc A)) n

def chooseN (n k : Nat) : Nat :=
  cond (Nat.ble k n) (Nat.div (fact n) (Nat.mul (fact k) (fact (Nat.sub n k)))) 0

def bernsteinTM (c : Ctx) (N i : Nat) (T : TM) : TM :=
  let one := rationalTM c (false,1,1)
  let half := rationalTM c (false,1,2)
  let plus := refresh c (mul c half (add c one T))
  let minus := refresh c (mul c half (add c one (neg c T)))
  let r := refresh c (mul c (rationalTM c (false,chooseN N i,1))
    (mul c (powerTM c plus i) (powerTM c minus (Nat.sub N i))))
  ⟨r.v,r.a,r.s,r.e,r.ok && plus.ok && minus.ok⟩

def blockEntryTM (c : Ctx) (degree count : Nat) (T : TM) (K : FactorData)
    (F : Nat → FactorData) (i j : Nat) : TM :=
  let floor := mul c (rationalTM c (false,1,2)) (squareEntryTM c K i j)
  let main := sumTM c (fun r => mul c (bernsteinTM c degree r T) (squareEntryTM c (F r) i j)) count
  refresh c (add c floor main)

def blockTM (c : Ctx) (order degree count : Nat) (T : TM) (K : FactorData)
    (F : Nat → FactorData) : TMMatrix :=
  tabulate order order (blockEntryTM c degree count T K F)

end ThomsonNegative.Certificate
