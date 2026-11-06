import ThomsonCompact.CoeffMap.Deg.Codec
import ThomsonCompact.CoeffMap.BSum

/-!
# One-time (per degree) checks of the W0 tables (Init only; F2e)

* `tagOk`: the coordinate tags and the inverse table agree (`ridx (rtag r) = r`; every table entry `r < nc` at code `c`
  has `rtag r = decT c`).
* `clsOk b`: the classes of block `b` partition the pairs `u ≤ v < rdim b`: keys strictly increasing, pairs of a class
  strictly increasing (code `u + 256 v`), every pair's raw spec (scalar blocks: sum tag and standard flags from the raw
  tags; moment blocks: the pair itself) is the class key, and the pair count is `n (n+1) / 2`.
* `grpOk b`: group boundaries `0 = glo 0 ≤ … ≤ glo (nGrp b) = nCls b`.
* `eOk b g r0 r1`: the coefficient lists of pseudo-block `(b, g)` at coordinates `r0 ≤ r < r1` are the nonzero
  coefficients of the class polynomials (`clsPoly`, computed from the definitions: `CoeffMap.Deg.Poly`) at the
  retained tags, read off the dense accumulators `denseAcc` (`W`-bit slots, overflow excluded by `Σ|c| < 2^W`).
-/

namespace ThomsonCompact.CoeffMap.Deg

namespace DegD

variable (L : DegD)

/-- Tag tables agree (`kC` bounds the third component of the inverse table's domain). -/
def tagOk : Bool :=
  (List.range L.nc).all (fun r => Nat.beq (L.ridx (L.rtag r)) r && Nat.blt (L.rtag r).2.2 L.kC &&
      Nat.blt (L.rtag r).1 (Nat.shiftLeft 1 L.aA) && Nat.blt (L.rtag r).2.1 (Nat.shiftLeft 1 L.aB)) &&
  (List.range (Nat.mul (Nat.shiftLeft 1 (Nat.add L.aA L.aB)) L.kC)).all fun c =>
    (fun r => !(Nat.blt r L.nc) || teq (L.rtag r) (decT L.aA L.aB c)) (sAt L.ridxC 16 10 c)

/-- Key of the pair `(u, v)` of block `b`. -/
def pairKey (b u v : Nat) : Nat :=
  cond (Nat.blt b L.dH) (Nat.add u (Nat.shiftLeft v 8))
    ((fun su sv => cond (Nat.beq (famOf (Nat.sub b L.dH)) 2)
        (Nat.add (encT L.aA L.aB (tadd su.2 sv.2))
          (Nat.add (Nat.shiftLeft (cond (su.1 && sv.1) 1 0) 16) (Nat.shiftLeft (cond (su.1 || sv.1) 1 0) 17)))
        (encT L.aA L.aB (tadd su.2 sv.2)))
      (L.stag (Nat.sub b L.dH) u) (L.stag (Nat.sub b L.dH) v))

/-- Pairs of a class: strictly increasing codes `u + 256 v`, `u ≤ v < n`, key `x`; returns the last code + 1. -/
def pairsOk (b n x : Nat) : List (Nat × Nat) → Nat → Bool
  | [], _ => true
  | p :: ps, lo => Nat.ble lo (Nat.add p.1 (Nat.shiftLeft p.2 8)) && Nat.ble p.1 p.2 && Nat.blt p.2 n &&
      Nat.beq (L.pairKey b p.1 p.2) x && pairsOk b n x ps (Nat.add (Nat.add p.1 (Nat.shiftLeft p.2 8)) 1)

/-- The power-sum indices of the parity key `x` are below `nPS`. -/
def keyBound (b x : Nat) : Bool :=
  !(Nat.ble L.dH b && Nat.ble 3 (famOf (Nat.sub b L.dH))) ||
    ((fun t => Nat.blt (Nat.add (Nat.add t.1 t.2.1) 4) L.nPS && Nat.blt (Nat.add t.2.2 2) L.nPS)
      (decT L.aA L.aB (Nat.land x 65535)))

/-- The classes of block `b` partition the pairs `u ≤ v < rdim b`. -/
def clsOk (b : Nat) : Bool :=
  (List.range (L.nCls b)).all (fun k => L.pairsOk b (L.rdim b) (L.clsKey b k) (L.clsPairs b k) 0 &&
    L.keyBound b (L.clsKey b k) &&
    (Nat.ble (L.nCls b) (Nat.add k 1) || Nat.blt (L.clsKey b k) (L.clsKey b (Nat.add k 1)))) &&
  Nat.beq (((List.range (L.nCls b)).map fun k => (L.clsPairs b k).length).foldr Nat.add 0)
    (Nat.shiftRight (Nat.mul (L.rdim b) (Nat.add (L.rdim b) 1)) 1)

/-- Group boundaries of block `b`. -/
def grpOk (b : Nat) : Bool :=
  Nat.beq (L.glo b 0) 0 && Nat.beq (L.glo b (L.nGrp b)) (L.nCls b) && Nat.ble (L.nGrp b) 31 &&
    (List.range (L.nGrp b)).all fun g => Nat.ble (L.glo b g) (L.glo b (Nat.add g 1))

/-- Dense accumulators of the classes of group `g` of block `b` (power sums `P`, `PP` in sign-magnitude form; slot
width `W`). -/
noncomputable def vTab (P PP : List (List (T3 × Bool × Nat))) (W b g : Nat) : List (Nat × Nat × Nat) :=
  mkList (fun i => L.clsAcc P PP W b (L.clsKey b (Nat.add (L.glo b g) i)))
    (Nat.sub (L.glo b (Nat.add g 1)) (L.glo b g))

/-- The expected coefficient list at coordinate `r` from the dense accumulators `V` of classes `k, k+1, …`. -/
def eRow (W r : Nat) : List (Nat × Nat × Nat) → Nat → List (Nat × Bool × Nat)
  | [], _ => []
  | V :: Vs, k => cond (Nat.beq (slotAt W V.1 r) (slotAt W V.2.1 r)) (eRow W r Vs (Nat.add k 1))
      ((k, Nat.blt (slotAt W V.1 r) (slotAt W V.2.1 r),
        Nat.add (Nat.sub (slotAt W V.1 r) (slotAt W V.2.1 r)) (Nat.sub (slotAt W V.2.1 r) (slotAt W V.1 r))) ::
        eRow W r Vs (Nat.add k 1))

/-- `E = eRow W r Vs k`, checked by one simultaneous walk (`Nat` operations only; `eMatch_spec`). -/
noncomputable def eMatch (W r : Nat) : List (Nat × Nat × Nat) → Nat → List (Nat × Bool × Nat) → Bool :=
  List.rec (motive := fun _ => Nat → List (Nat × Bool × Nat) → Bool)
    (fun _ E => List.casesOn (motive := fun _ => Bool) E true (fun _ _ => false))
    (fun V _ ih k E => (fun p n => cond (Nat.beq p n) (ih (Nat.add k 1) E)
        (List.casesOn (motive := fun _ => Bool) E false (fun e E' =>
          Nat.beq e.1 k && cond e.2.1 (Nat.blt p n) (!(Nat.blt p n)) &&
            Nat.beq e.2.2 (Nat.add (Nat.sub p n) (Nat.sub n p)) && ih (Nat.add k 1) E')))
      (slotAt W V.1 r) (slotAt W V.2.1 r))

/-- The coefficient lists of pseudo-block `(b, g)` at coordinates `r0 ≤ r < r1` are the class coefficients. -/
noncomputable def eOk (P PP : List (List (T3 × Bool × Nat))) (W b g r0 r1 : Nat) : Bool :=
  (fun V => V.all (fun v => Nat.blt v.2.2 (Nat.shiftLeft 1 W)) &&
    walkP (fun r E => eMatch W r V (L.glo b g) E) r0 r1 (L.eTab (Nat.add (Nat.mul 32 b) g)) 0)
  (L.vTab P PP W b g)

/-- The one-time check of pseudo-block `(b, g)` with the canonical parameters (power sums of size `nPS`,
32-bit accumulator slots). -/
noncomputable def eOkC (b g r0 r1 : Nat) : Bool :=
  L.eOk ((psTab L.nPS).map smOf) ((ppsTab L.nPS).map smOf) 32 b g r0 r1

end DegD

end ThomsonCompact.CoeffMap.Deg
