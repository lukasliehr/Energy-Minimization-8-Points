/-!
# Packed Taylor models: kernel code (Init only)

A Taylor model (TM) of order `N` at scale `2^-S` represents a function `f : ℝ → ℝ` on `[-1,1]` by integer
coefficients `cᵢ` (`i ≤ N`) and an error `e`:  `|f t - Σ cᵢ 2^-S tⁱ| ≤ e·2^-S`  (semantics in `Packed.Sound`).

Packed representation in slots of `W` bits (`X = 2^W`, `m = N+1`, `K = W·(2N+1)`):
* `v = Σ cᵢ Xⁱ mod 2^K`        signed coefficients (ring homomorphism ℤ → ℤ/2^K, so products are exact);
* `a = Σ αᵢ Xⁱ`                 coefficient magnitude bounds `|cᵢ| ≤ αᵢ` (nonnegative digits);
* `s = Σ αᵢ`                    cached digit sum, invariant `s < 2^B` (this excludes every slot overflow);
* `e`                           error bound in units `2^-S`;
* `ok`                          conjunction of all numeric side conditions checked while building the TM.

Every operation is a fixed number of big-number kernel operations (independent of `N`):
products by one `Nat.mul`, slot-wise floor/ceil rounding by one mask and one shift, slot sums by casting out
`2^W - 1` (one `Nat.mod`). Written with explicit `Nat` primitives for kernel speed.
-/

namespace ThomsonNegative.Compact.Packed

/-- `Σ_{i<n} 2^(W i)` -/
def ones (W n : Nat) : Nat := Nat.div (Nat.sub (Nat.pow 2 (Nat.mul W n)) 1) (Nat.sub (Nat.pow 2 W) 1)

/-- Parameters and derived constants. Only `mkCtx` builds contexts. -/
structure Ctx where
  N : Nat
  S : Nat
  B : Nat
  W : Nat
  m : Nat
  K : Nat
  wm : Nat
  maskK : Nat
  modW : Nat
  maskWm : Nat
  maskW : Nat
  biasP : Nat
  hb : Nat
  rmask : Nat
  ceilAdd : Nat
  unb : Nat
  hiPat : Nat
  twoK : Nat
  twoB : Nat
  twoS : Nat
  hW : Nat

/-- `N` order, `S` scale bits, `B` coefficient-sum bound bits, `W` slot width
(soundness needs `2B + 2 ≤ W`, `S < W`, `N < 2^B`). -/
def mkCtx (N S B W : Nat) : Ctx :=
  let m := Nat.add N 1
  let n2 := Nat.add (Nat.mul 2 N) 1
  let K := Nat.mul W n2
  { N := N, S := S, B := B, W := W, m := m, K := K,
    wm := Nat.mul W m,
    maskK := Nat.sub (Nat.pow 2 K) 1,
    modW := Nat.sub (Nat.pow 2 W) 1,
    maskWm := Nat.sub (Nat.pow 2 (Nat.mul W m)) 1,
    maskW := Nat.sub (Nat.pow 2 W) 1,
    biasP := Nat.mul (Nat.pow 2 (Nat.sub W 1)) (ones W n2),
    hb := Nat.mul (Nat.pow 2 (Nat.sub W 1)) (ones W m),
    rmask := Nat.mul (Nat.sub (Nat.pow 2 W) (Nat.pow 2 S)) (ones W m),
    ceilAdd := Nat.mul (Nat.sub (Nat.pow 2 S) 1) (ones W m),
    unb := Nat.sub (Nat.pow 2 K) (Nat.mul (Nat.pow 2 (Nat.sub (Nat.sub W 1) S)) (ones W m)),
    hiPat := Nat.mul (Nat.sub (Nat.pow 2 W) (Nat.pow 2 B)) (ones W m),
    twoK := Nat.pow 2 K, twoB := Nat.pow 2 B, twoS := Nat.pow 2 S,
    hW := Nat.pow 2 (Nat.sub W 1) }

structure TM where
  v : Nat
  a : Nat
  s : Nat
  e : Nat
  ok : Bool

/-- `⌈x / 2^S⌉` -/
def cdiv (S x : Nat) : Nat := Nat.shiftRight (Nat.add x (Nat.sub (Nat.pow 2 S) 1)) S

/-- digit sum of a packed nonnegative vector (casting out `2^W - 1`; exact when the sum is `< 2^W - 1`) -/
def ssum (c : Ctx) (x : Nat) : Nat := Nat.mod x c.modW

/-- Input TM from sign-split data: `P = Σ max(cᵢ,0) Xⁱ`, `Q = Σ max(-cᵢ,0) Xⁱ` (digits `< 2^B`), error `e`. -/
def ofPQ (c : Ctx) (P Q e : Nat) : TM :=
  let a := Nat.add P Q
  let s := ssum c a
  ⟨Nat.land (Nat.add P (Nat.sub c.twoK Q)) c.maskK, a, s, e,
   Nat.beq (Nat.land P c.hiPat) 0 && Nat.beq (Nat.land Q c.hiPat) 0 &&
   Nat.ble P c.maskWm && Nat.ble Q c.maskWm && Nat.blt s c.twoB⟩

def neg (c : Ctx) (A : TM) : TM := ⟨Nat.land (Nat.sub c.twoK A.v) c.maskK, A.a, A.s, A.e, A.ok⟩

def add (c : Ctx) (A B : TM) : TM :=
  let s := Nat.add A.s B.s
  ⟨Nat.land (Nat.add A.v B.v) c.maskK, Nat.add A.a B.a, s, Nat.add A.e B.e,
   A.ok && B.ok && Nat.blt s c.twoB⟩

/-- add the constant `±mag·2^-S` (`dq` bounds its distance to the intended constant, in units `2^-S`) -/
def addC (c : Ctx) (ng : Bool) (mag dq : Nat) (A : TM) : TM :=
  let s := Nat.add A.s mag
  ⟨Nat.land (Nat.add A.v (cond ng (Nat.sub c.twoK mag) mag)) c.maskK, Nat.add A.a mag, s, Nat.add A.e dq,
   A.ok && Nat.blt s c.twoB⟩

/-- multiply by the scalar `±q·2^-S` (`dq` bounds its distance to the intended scalar, units `2^-S`) -/
def smul (c : Ctx) (ng : Bool) (q dq : Nat) (A : TM) : TM :=
  let p := Nat.land (Nat.add (Nat.mul A.v q) c.biasP) c.maskK
  let v := Nat.land (Nat.add (Nat.shiftRight (Nat.land p c.rmask) c.S) c.unb) c.maskK
  let a := Nat.shiftRight (Nat.land (Nat.add (Nat.mul A.a q) c.ceilAdd) c.rmask) c.S
  let s := ssum c a
  ⟨cond ng (Nat.land (Nat.sub c.twoK v) c.maskK) v, a, s,
   Nat.add (cdiv c.S (Nat.add (Nat.mul q A.e) (Nat.mul dq (Nat.add A.s A.e)))) c.m,
   A.ok && Nat.blt q c.twoB && Nat.blt s c.twoB⟩

/-- product, truncated to degree `N` (tail `Σ_{k>N} (α*β)_k` into the error), floor-rounded to scale `2^-S` -/
def mul (c : Ctx) (A B : TM) : TM :=
  let p := Nat.land (Nat.add (Nat.mul A.v B.v) c.biasP) c.maskK
  let g := Nat.mul A.a B.a
  let a := Nat.shiftRight (Nat.land (Nat.add (Nat.land g c.maskWm) c.ceilAdd) c.rmask) c.S
  let s := ssum c a
  ⟨Nat.land (Nat.add (Nat.shiftRight (Nat.land p c.rmask) c.S) c.unb) c.maskK, a, s,
   Nat.add (Nat.add (cdiv c.S (Nat.add (Nat.add (Nat.mul A.s B.e) (Nat.mul B.s A.e)) (Nat.mul A.e B.e)))
     (cdiv c.S (ssum c (Nat.shiftRight g c.wm)))) c.m,
   A.ok && B.ok && Nat.blt s c.twoB⟩

/-- rigorous range bound from the magnitude bounds: `sup_{[-1,1]} |f| ≤ range A · 2^-S` (O(1)) -/
def range (A : TM) : Nat := Nat.add A.s A.e

/-- packed exact magnitudes: slot `k` holds `|cₖ|` (O(1) bignum operations, no digit loop).
`X` = biased digits `cₖ + H`; `h` = `H` in the slots with `cₖ ≥ 0`; `pm` = full slot mask there. -/
def pabs (c : Ctx) (A : TM) : Nat :=
  let X := Nat.land (Nat.add A.v c.hb) c.maskK
  let h := Nat.land X c.hb
  let pm := Nat.mul (Nat.shiftRight h (Nat.sub c.W 1)) c.maskW
  Nat.add (Nat.sub (Nat.land X pm) h) (Nat.sub (Nat.sub c.hb h) (Nat.land X (Nat.sub c.maskWm pm)))

/-- exact range bound `Σ|cₖ| + e` (packed magnitudes + slot sum); sees cancellation -/
def rangeX (c : Ctx) (A : TM) : Nat :=
  Nat.add (ssum c (pabs c A)) A.e

/-- `1/Q` from a supplied witness `R`: `D = 1 - R·Q`, `ε = rangeX D < 1/2`, then `|1/q - p_R| ≤ ‖p_R‖ ε/(1-ε)` -/
def recip (c : Ctx) (Q R : TM) : TM :=
  let D := addC c false c.twoS 0 (neg c (mul c R Q))
  let eps := rangeX c D
  let den := Nat.sub c.twoS eps
  ⟨R.v, R.a, R.s, Nat.add R.e (Nat.div (Nat.add (Nat.mul R.s eps) (Nat.sub den 1)) den),
   R.ok && D.ok && Nat.blt (Nat.mul 2 eps) c.twoS⟩

end ThomsonNegative.Compact.Packed
