import ThomsonNegative.Compact.Packed.Core2

/-! Compact rational-function records and their uniform packed evaluation. -/
namespace ThomsonNegative.Certificate
open ThomsonNegative.Compact.Packed

/-- Integer coefficients are sign-split into fixed-width slots. A common
positive denominator is shared by the whole coefficient list. -/
structure PolyData where
  width : Nat
  length : Nat
  positive : Nat
  negative : Nat
  denominator : Nat

def polyArg (p : PolyData) (k : Nat) : Bool × Nat × Nat :=
  let mask := Nat.sub (Nat.pow 2 p.width) 1
  let a := Nat.land (Nat.shiftRight p.positive (Nat.mul p.width k)) mask
  let b := Nat.land (Nat.shiftRight p.negative (Nat.mul p.width k)) mask
  (Nat.blt a b, Nat.add (Nat.sub a b) (Nat.sub b a), p.denominator)

def polyArgs (p : PolyData) : List (Bool × Nat × Nat) :=
  (List.range p.length).map (polyArg p)

def rationalTM (c : Ctx) (a : Bool × Nat × Nat) : TM :=
  constTM c a.1 (ratMag c a.2.1 a.2.2) 1

def hornerRefresh (c : Ctx) (A : TM) : List (Bool × Nat × Nat) → TM
  | [] => zeroTM
  | a :: rest => refresh c (add c (mul c (hornerRefresh c A rest) A) (rationalTM c a))

def polynomialTM (c : Ctx) (A : TM) (p : PolyData) : TM :=
  hornerRefresh c A (polyArgs p)

/-- The denominator is supplied as exact factors, already shifted about the
same height anchor as the numerator. Their product identity is a separate,
shared exact polynomial obligation. Repeated factors occur repeatedly. -/
structure RFData where
  numerator : PolyData
  unitInverse : Bool × Nat × Nat
  factors : List PolyData

def inverseFactors (c : Ctx) (fuel tolerance : Nat) (A : TM) : List PolyData → TM → TM
  | [], acc => acc
  | p :: rest, acc =>
      inverseFactors c fuel tolerance A rest
        (refresh c (mul c acc (invN c fuel tolerance (polynomialTM c A p))))

def rationalFunctionTM (c : Ctx) (fuel tolerance : Nat) (A : TM) (r : RFData) : TM :=
  let numerator := polynomialTM c A r.numerator
  let inverse := inverseFactors c fuel tolerance A r.factors (rationalTM c r.unitInverse)
  refresh c (mul c numerator inverse)

/-- Enclose a model by a constant polynomial and one radius, using the same
dyadic scale in a new context. The proposed center can be arbitrary. -/
def collapseAt (c d : Ctx) (ng : Bool) (mag : Nat) (A : TM) : TM :=
  let delta := addC c (!ng) mag 0 A
  let r := constTM d ng mag (rangeX c delta)
  ⟨r.v,r.a,r.s,r.e,r.ok && delta.ok⟩

end ThomsonNegative.Certificate
