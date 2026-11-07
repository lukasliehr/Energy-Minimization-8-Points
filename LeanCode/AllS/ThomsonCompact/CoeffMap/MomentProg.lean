/-!
# Computable mirror of the moment pivot polynomials `momentP k i a` (Init only)

Polynomials over `ℚ(√2)` in the height `a`: `⟨r, s⟩ ↦ r(a) + √2 · s(a)` with coefficient lists in increasing
degree. `mP k i` mirrors the definition of `momentP` (contacts `a`, `2a-1`, `-a ± (1-a)/√2`; the even-binomial
sums `momentR`), with `√2·√2 = 2` in `q2mul`. Soundness (`ev2 (mP k i) a = momentP k i a`) is in
`CoeffMap.MomentSound`; for the D12 pivots the `√2` part vanishes identically (checked there) and the rational
part is fed to `hornerQ` through `toQL`.
-/

namespace ThomsonCompact.CoeffMap

/-- Sum of coefficient lists. -/
def qadd : List Rat → List Rat → List Rat
  | [], b => b
  | a :: as, [] => a :: as
  | x :: as, y :: bs => (x + y) :: qadd as bs

def qscale (x : Rat) : List Rat → List Rat
  | [] => []
  | y :: ys => (x * y) :: qscale x ys

/-- Product of coefficient lists (schoolbook). -/
def qmul : List Rat → List Rat → List Rat
  | [], _ => []
  | x :: as, b => qadd (qscale x b) (0 :: qmul as b)

/-- `r(a) + √2 · s(a)`. -/
structure Q2P where
  r : List Rat
  s : List Rat

def q2add (p q : Q2P) : Q2P := ⟨qadd p.r q.r, qadd p.s q.s⟩

def q2mul (p q : Q2P) : Q2P :=
  ⟨qadd (qmul p.r q.r) (qscale 2 (qmul p.s q.s)), qadd (qmul p.r q.s) (qmul p.s q.r)⟩

def q2smul (x : Rat) (p : Q2P) : Q2P := ⟨qscale x p.r, qscale x p.s⟩

def q2one : Q2P := ⟨[1], []⟩
def q2zero : Q2P := ⟨[], []⟩
def q2X : Q2P := ⟨[0, 1], []⟩

def q2pow (p : Q2P) : Nat → Q2P
  | 0 => q2one
  | n + 1 => q2mul (q2pow p n) p

/-- Binomial coefficients (Pascal; `= Nat.choose`, proved in `MomentSound`). -/
def chooseI : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => chooseI n k + chooseI n (k + 1)

/-- One term `C(k,j) c^(k-j) d^j (-1)^(j/2) a^((k-j-k%2)/2)` of `momentR`. -/
def mRterm (k : Nat) (c d : Q2P) (j : Nat) : Q2P :=
  q2mul (q2smul ((chooseI k j : Rat) * (if (j / 2) % 2 = 0 then 1 else -1))
    (q2mul (q2pow c (k - j)) (q2pow d j))) (q2pow q2X ((k - j - k % 2) / 2))

/-- Sum of `mRterm` over a list of indices. -/
def mRsum (k : Nat) (c d : Q2P) : List Nat → Q2P
  | [] => q2zero
  | j :: js => q2add (mRterm k c d j) (mRsum k c d js)

/-- `momentR k c d a` (sum over even `j ≤ k`). -/
def mR (k : Nat) (c d : Q2P) : Q2P := mRsum k c d ((List.range (k + 1)).filter (fun j => j % 2 = 0))

/-- The contacts `a, 2a - 1, -a + (1-a)/√2, -a - (1-a)/√2`. -/
def cA : Q2P := q2X
def cB : Q2P := ⟨[-1, 2], []⟩
def cC : Q2P := ⟨[0, -1], [1/2, -1/2]⟩
def cD : Q2P := ⟨[0, -1], [-1/2, 1/2]⟩

/-- Mirror of `momentP k i a`. -/
def mP (k i : Nat) : Q2P :=
  if k = 0 then
    q2add (q2add (q2add (q2add q2one (q2smul 2 (q2pow cA i))) (q2pow cB i)) (q2smul 2 (q2pow cC i)))
      (q2smul 2 (q2pow cD i))
  else
    q2add (q2add (q2add (q2mul (q2smul ((Nat.pow 2 k : Nat) : Rat) (q2pow q2X (k / 2))) (q2pow cB i))
      (q2smul 2 (q2mul (q2pow cA i) (mR k q2one q2one))))
      (q2smul 2 (q2mul (q2pow cC i) (mR k ⟨[-1], [-1/2]⟩ ⟨[0], [1/2]⟩))))
      (q2smul 2 (q2mul (q2pow cD i) (mR k ⟨[-1], [1/2]⟩ ⟨[0], [1/2]⟩)))

/-- All coefficients are zero. -/
def qAllZero : List Rat → Bool
  | [] => true
  | x :: xs => (x == 0) && qAllZero xs

/-- Rational coefficients as `hornerQ` triples `(neg?, |num|, den)`. -/
def toQL (L : List Rat) : List (Bool × Nat × Nat) :=
  L.map fun q => (decide (q < 0), q.num.natAbs, q.den)

end ThomsonCompact.CoeffMap

namespace ThomsonCompact.CoeffMap
/-- D12 pivots `[0,3,2,1,0,0]` and the `√2`-free check for every D12 pair `(k, i)`, `i ≤ 6 - k`. -/
def momPivotD12 (k : Nat) : Nat := [0, 3, 2, 1, 0, 0].getD k 0

def momRationalD12 : Bool :=
  (List.range 6).all fun k => (List.range (7 - k)).all fun i => qAllZero (mP k i).s
end ThomsonCompact.CoeffMap
