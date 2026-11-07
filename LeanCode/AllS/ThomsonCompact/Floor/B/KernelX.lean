import ThomsonCompact.Floor.B.Kernel

/-!
# F3f kernel (Init only): the two x-halves of a cell (two-piece correction)

A cell `x ∈ [-1,1]` is split into `x = (y - 1)/2` (left) and `x = (y + 1)/2` (right), `y ∈ [-1,1]`.

* `pieceHeight c A neg`: the height TM of a half, `A ∘ ((y ∓ 1)/2)` (Horner at the exact affine TM, plus `A`'s
  error);
* `reexpOk`: the centre polynomials of a half, re-expanded exactly: coordinate `r` of the half has the integer
  coefficients `b_k` (scale `2^-(Sc+N)`) of `Σ_j a_j 2^(N-j) (y ∓ 1)^j` (`a_j` at scale `2^-Sc`), checked by an
  integer Taylor shift (`tshift`).
-/

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Packed
open ThomsonCompact.Floor (mask slot)

/-! ## Height TM of a half -/

/-- the coefficients of `A` as constants `±c_k / 2^S` (increasing degree) -/
def tmCoefsQ (c : Ctx) (A : TM) : List (Bool × Nat × Nat) :=
  (List.range c.m).map fun k =>
    let d := Nat.land (Nat.shiftRight (Nat.land (Nat.add A.v c.hb) c.maskK) (Nat.mul c.W k)) c.maskW
    (Nat.blt d c.hW, Nat.add (Nat.sub d c.hW) (Nat.sub c.hW d), c.twoS)

/-- the exact affine TM `(y ∓ 1)/2` -/
def halfU (c : Ctx) (neg : Bool) : TM := tmAff c neg (Nat.pow 2 (Nat.sub c.S 1)) (Nat.pow 2 (Nat.sub c.S 1))

/-- the height TM of the half: `A((y ∓ 1)/2)` (left: `neg = true`) -/
def pieceHeight (c : Ctx) (A : TM) (neg : Bool) : TM := widen (hornerQ c (halfU c neg) (tmCoefsQ c A)) A.e

/-! ## Exact re-expansion of the centres -/

/-- `(y + σ) Q(y)` (`σ = -1` if `neg`), coefficient lists in increasing degree -/
def mulLin (neg : Bool) : List Int → List Int
  | [] => []
  | q :: Q => (cond neg (Int.neg q) q) :: mulLinAux neg q Q
where
  /-- the tail of `(y + σ) (p :: Q)` after its constant term -/
  mulLinAux (neg : Bool) (p : Int) : List Int → List Int
    | [] => [p]
    | q :: Q => (Int.add p (cond neg (Int.neg q) q)) :: mulLinAux neg q Q

/-- add `a` to the constant term -/
def addConst (a : Int) : List Int → List Int
  | [] => [a]
  | q :: Q => (Int.add a q) :: Q

/-- Taylor shift: the coefficients of `Σ_j c_j (y + σ)^j` (Horner from the top) -/
def tshift (neg : Bool) : List Int → List Int
  | [] => []
  | a :: cs => addConst a (mulLin neg (tshift neg cs))

/-- the integers `a_j 2^(N-j)` of a centre numeral (`N+1` sign-magnitude slots of width `wc`) -/
def centreInts (N wc cm : Nat) : List Int :=
  (List.range (Nat.succ N)).map fun j =>
    let z := smDec (slot wc cm j)
    cond z.1 (Int.neg (Int.ofNat (Nat.mul z.2 (Nat.pow 2 (Nat.sub N j)))))
      (Int.ofNat (Nat.mul z.2 (Nat.pow 2 (Nat.sub N j))))

/-- the integers `b_k` of a re-expanded centre numeral -/
def pieceInts (N wcP cmP : Nat) : List Int :=
  (List.range (Nat.succ N)).map fun k =>
    let z := smDec (slot wcP cmP k)
    cond z.1 (Int.neg (Int.ofNat z.2)) (Int.ofNat z.2)

/-- **Re-expansion leaf**: for the coordinates `i0 … i0+n-1`, the half's centre numerals `cmP i` are the exact
re-expansions of the cell's `cm i` -/
def reexpOk (N wc wcP : Nat) (neg : Bool) (cm cmP : Nat → Nat) (i0 n : Nat) : Bool :=
  (List.range n).all fun i => decide (tshift neg (centreInts N wc (cm (Nat.add i0 i))) = pieceInts N wcP (cmP (Nat.add i0 i)))

end ThomsonCompact.Floor.B
