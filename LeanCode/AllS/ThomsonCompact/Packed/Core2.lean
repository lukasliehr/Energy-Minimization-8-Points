import ThomsonCompact.Packed.Core

/-!
# Packed Taylor models, part 2: kernel code for F1b (Init only)

`refresh` (exact magnitude reset), `hornerQ` (fixed polynomial with rational coefficients at a TM),
division by in-kernel Newton steps (`divN`) or a supplied witness (`divW`), `expTM` (series + squaring),
`log1pSeries`/`logTM` (series + verified constant `log c`), `powTM` (`d^(-s/2) = exp(-(s/2)·log d)`).
-/

namespace ThomsonCompact.Packed

/-- the zero TM -/
def zeroTM : TM := ⟨0, 0, 0, 0, true⟩

/-- the constant `±mag·2^-S` (`dq` = distance to the intended constant, in units) -/
def constTM (c : Ctx) (ng : Bool) (mag dq : Nat) : TM := addC c ng mag dq zeroTM

/-- keep the polynomial, drop the error (for witnesses: only the polynomial matters) -/
def polyOnly (A : TM) : TM := ⟨A.v, A.a, A.s, 0, A.ok⟩

/-- widen the error by `δ` units -/
def widen (A : TM) (δ : Nat) : TM := ⟨A.v, A.a, A.s, Nat.add A.e δ, A.ok⟩

/-- reset the magnitude bounds to the exact magnitudes (sees cancellation; O(1) bignum operations) -/
def refresh (c : Ctx) (A : TM) : TM :=
  let a := pabs c A
  ⟨A.v, a, ssum c a, A.e, A.ok⟩

/-- `⌊n·2^S/d⌋`: dyadic magnitude of `n/d` (error `< 1` unit) -/
def ratMag (c : Ctx) (n d : Nat) : Nat := Nat.div (Nat.mul n c.twoS) d

/-- `p(G)` for `p(x) = Σⱼ ±(nⱼ/dⱼ) xʲ` (list in increasing degree), Horner -/
def hornerQ (c : Ctx) (G : TM) : List (Bool × Nat × Nat) → TM
  | [] => zeroTM
  | [a] => constTM c a.1 (ratMag c a.2.1 a.2.2) 1
  | a :: b :: rest => addC c a.1 (ratMag c a.2.1 a.2.2) 1 (mul c (hornerQ c G (b :: rest)) G)

/-! ## Division -/

/-- constant coefficient of `A` as (negative?, magnitude) -/
def coef0 (c : Ctx) (A : TM) : Bool × Nat :=
  let d := Nat.land (Nat.land (Nat.add A.v c.hb) c.maskK) c.maskW
  (Nat.blt d c.hW, Nat.add (Nat.sub d c.hW) (Nat.sub c.hW d))

/-- initial reciprocal guess `1/d₀` as a constant -/
def inv0 (c : Ctx) (D : TM) : TM :=
  let d := coef0 c D
  constTM c d.1 (Nat.div (Nat.mul c.twoS c.twoS) d.2) 0

/-- Newton step `R ↦ R + R·E`, `E = 1 - R·D` with refreshed magnitudes; iterates carry no error
(they are witnesses: only the final `recip` check matters) -/
def newtonStep (c : Ctx) (D R : TM) : TM :=
  polyOnly (add c R (mul c R (refresh c (addC c false c.twoS 0 (neg c (mul c R D))))))

/-- at most `k` Newton steps; stops when the polynomial part of the defect `E = 1 - R·D` is below
`E.e/8 + tol` (further steps cannot improve the certified bound). The last defect is shared with `recip`. -/
def newton (c : Ctx) (D : TM) (tol : Nat) : Nat → TM → TM
  | 0, R => R
  | k + 1, R =>
    let E := addC c false c.twoS 0 (neg c (mul c R D))
    cond (Nat.ble (Nat.mul 8 (rangeX c E)) (Nat.add (Nat.mul 9 E.e) (Nat.mul 8 tol))) R
      (newton c D tol k (newtonStep c D R))

/-- `1/d` by in-kernel Newton steps from `1/d₀` (no stored witness), verified by `recip` -/
def invN (c : Ctx) (k tol : Nat) (D : TM) : TM := recip c D (newton c D tol k (inv0 c D))

/-- `f/d` by in-kernel Newton steps, verified by `recip` -/
def divN (c : Ctx) (k tol : Nat) (F D : TM) : TM := mul c F (invN c k tol D)

/-- `f/d` with a supplied witness `R ≈ 1/d` (any TM, e.g. `ofPQ` data) -/
def divW (c : Ctx) (F D R : TM) : TM := mul c F (recip c D R)

/-- `f/g` by the residual lemma: `Q = refresh (polyOnly (F·Rc))` for any enclosure `Rc` of `1/g` (e.g. `invN`),
error `‖f - g q‖·‖1/g‖`. No truncation of `1/g` enters: use it when the quotient is smoother than `1/g`
(divided differences, rational functions with a nearby pole). -/
def divR (c : Ctx) (F G Rc : TM) : TM :=
  let F' := refresh c F
  let Q := refresh c (polyOnly (mul c F' Rc))
  let E := add c F' (neg c (mul c G Q))
  ⟨Q.v, Q.a, Q.s, cdiv c.S (Nat.mul (rangeX c E) (rangeX c Rc)), Q.ok && E.ok && Rc.ok⟩

/-- rational function `p(g)/q(g)` of a TM, fixed rational coefficient lists, Newton division -/
def rfTM (c : Ctx) (k tol : Nat) (G : TM) (num den : List (Bool × Nat × Nat)) : TM :=
  divN c k tol (hornerQ c G num) (hornerQ c G den)

/-! ## exp and log -/

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => Nat.mul (n + 1) (fact n)

/-- `1/i!` for `i < n` -/
def expCoeffs (n : Nat) : List (Bool × Nat × Nat) := (List.range n).map (fun i => (false, 1, fact i))

/-- `exp G` for `‖G‖ ≤ 1`: `n`-term series plus the Lagrange remainder `|x|ⁿ (n+1)/(n!·n)`
(the argument is refreshed first, so the bound `r = Σ|cₖ| + e` is exact) -/
def expSeries (c : Ctx) (n : Nat) (G0 : TM) : TM :=
  let G := refresh c G0
  let P := hornerQ c G (expCoeffs n)
  let r := Nat.add G.s G.e
  let D := Nat.mul (Nat.mul (Nat.pow c.twoS (Nat.sub n 1)) (fact n)) n
  let rem := Nat.div (Nat.add (Nat.mul (Nat.pow r n) (Nat.add n 1)) (Nat.sub D 1)) D
  ⟨P.v, P.a, P.s, Nat.add P.e rem, P.ok && G.ok && Nat.ble r c.twoS && Nat.blt 0 n⟩

/-- `j` squarings -/
def sqIter (c : Ctx) : Nat → TM → TM
  | 0, H => H
  | j + 1, H => sqIter c j (mul c H H)

/-- `exp F = (exp (F/2^j))^(2^j)` (range reduction by squaring; needs `j ≤ S`) -/
def expTM (c : Ctx) (n j : Nat) (F : TM) : TM :=
  let R := sqIter c j (expSeries c n (smul c false (Nat.pow 2 (Nat.sub c.S j)) 0 F))
  ⟨R.v, R.a, R.s, R.e, R.ok && Nat.ble j c.S⟩

/-- `(-1)^i/(i+1)` for `i < n` -/
def log1pCoeffs (n : Nat) : List (Bool × Nat × Nat) :=
  (List.range n).map (fun i => (Nat.beq (Nat.mod i 2) 1, 1, i + 1))

/-- `log(1+U)` for `‖U‖ < 1`: `U·Σ_{i<n} (-U)^i/(i+1)` plus the remainder `|x|^(n+1)/(1-|x|)` -/
def log1pSeries (c : Ctx) (n : Nat) (U0 : TM) : TM :=
  let U := refresh c U0
  let P := mul c U (hornerQ c U (log1pCoeffs n))
  let r := Nat.add U.s U.e
  let D := Nat.mul (Nat.pow c.twoS (Nat.sub n 1)) (Nat.sub c.twoS r)
  let rem := Nat.div (Nat.add (Nat.pow r (Nat.add n 1)) (Nat.sub D 1)) D
  ⟨P.v, P.a, P.s, Nat.add P.e rem, P.ok && Nat.blt r c.twoS && Nat.blt 0 n⟩

/-- verified constant: for `c₀ = cmag·2^-S` and `L = ±Lmag·2^-S`, `(ok, δ)` with
`|log c₀ - L| ≤ δ·2^-S` when `ok` (checked through `exp L`: `|exp L - c₀| ≤ η` gives `η/(c₀ - η)`) -/
def logConst (c : Ctx) (nE jE cmag : Nat) (Lng : Bool) (Lmag : Nat) : Bool × Nat :=
  let A := addC c true cmag 0 (expTM c nE jE (constTM c Lng Lmag 0))
  let eta := rangeX c A
  let den := Nat.sub cmag eta
  (A.ok && Nat.blt eta cmag, Nat.div (Nat.add (Nat.mul eta c.twoS) (Nat.sub den 1)) den)

/-- a table of verified log constants `(cmag, Lng, Lmag, δ)`: checks `logConst` and the claimed `δ` once -/
def logTableOk (c : Ctx) (nE jE : Nat) : List (Nat × Bool × Nat × Nat) → Bool
  | [] => true
  | x :: T => (logConst c nE jE x.1 x.2.1 x.2.2.1).1 && Nat.ble (logConst c nE jE x.1 x.2.1 x.2.2.1).2 x.2.2.2 &&
      logTableOk c nE jE T

/-- `log F = log c₀ + log(1 + (F/c₀ - 1))` for a center `c₀ = cmag·2^-S` and a constant `L` with
`|log c₀ - L| ≤ δ·2^-S` (from `logConst`, or from a table verified once) -/
def logTMc (c : Ctx) (n cmag : Nat) (Lng : Bool) (Lmag δ : Nat) (F : TM) : TM :=
  let U := addC c true c.twoS 0 (smul c false (Nat.div (Nat.mul c.twoS c.twoS) cmag) 1 F)
  let R := addC c Lng Lmag δ (log1pSeries c n U)
  ⟨R.v, R.a, R.s, R.e, R.ok && Nat.blt 0 cmag⟩

/-- `log F` with the constant `log c₀` verified in place -/
def logTM (c : Ctx) (n nE jE cmag : Nat) (Lng : Bool) (Lmag : Nat) (F : TM) : TM :=
  let k := logConst c nE jE cmag Lng Lmag
  let R := logTMc c n cmag Lng Lmag k.2 F
  ⟨R.v, R.a, R.s, R.e, R.ok && k.1⟩

/-- `exp(-(s/2)·l)` for TMs `Sv ≈ s` and `Lg ≈ l` (with `l = log d` this is `d^(-s/2)`) -/
def powL (c : Ctx) (nX jX : Nat) (Lg Sv : TM) : TM :=
  let R := expTM c nX jX (neg c (mul c (smul c false (Nat.pow 2 (Nat.sub c.S 1)) 0 Sv) Lg))
  ⟨R.v, R.a, R.s, R.e, R.ok && Nat.ble 1 c.S⟩

/-- `d^(-s/2) = exp(-(s/2)·log d)` for TMs `D` (positive) and `Sv` (e.g. affine `s`) -/
def powTM (c : Ctx) (n nE jE cmag : Nat) (Lng : Bool) (Lmag : Nat) (nX jX : Nat) (D Sv : TM) : TM :=
  powL c nX jX (logTM c n nE jE cmag Lng Lmag D) Sv

/-! ## Packing coefficient boxes (reverse bridge data path; `Rat` is in `Init`) -/

/-- `⌊q·2^S⌋` (`twoS = 2^S`) -/
def qFloor (twoS : Nat) (q : Rat) : Int := (q.num * (twoS : Int)) / (q.den : Int)

/-- `⌈q·2^S⌉` -/
def qCeil (twoS : Nat) (q : Rat) : Int := -((-(q.num * (twoS : Int))) / (q.den : Int))

/-- `Σ dₖ 2^(W k)` -/
def packD (W : Nat) : List Nat → Nat
  | [] => 0
  | d :: L => Nat.add d (Nat.shiftLeft (packD W L) W)

/-- all `|zₖ| < twoB` -/
def allSmall (twoB : Nat) : List Int → Bool
  | [] => true
  | z :: L => Nat.blt z.natAbs twoB && allSmall twoB L

/-- `Σ (⌈hiₖ 2^S⌉ - ⌊loₖ 2^S⌋)⁺` -/
def boxErr (twoS : Nat) : List (Rat × Rat) → Nat
  | [] => 0
  | b :: L => Nat.add (Int.toNat (qCeil twoS b.2 - qFloor twoS b.1)) (boxErr twoS L)

/-- packed TM from coefficient boxes and an error bound (outward rounding to the grid) -/
def ofBoxes (c : Ctx) (L : List (Rat × Rat)) (err : Rat) : TM :=
  let cl := L.map (fun b => qFloor c.twoS b.1)
  let T := ofPQ c (packD c.W (cl.map Int.toNat)) (packD c.W (cl.map (fun z => Int.toNat (-z))))
    (Nat.add (Int.toNat (qCeil c.twoS err)) (boxErr c.twoS L))
  ⟨T.v, T.a, T.s, T.e, T.ok && allSmall c.twoB cl && Nat.ble L.length c.m⟩

end ThomsonCompact.Packed
