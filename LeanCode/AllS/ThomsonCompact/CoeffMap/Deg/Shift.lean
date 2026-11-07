import ThomsonCompact.CoeffMap.Deg.StageZ

/-!
# Re-centred RF records (Init only; F2i)

The scalar rows evaluate the RF records in powers of the height TM `A`. On the cells of large `s` the numerators and
denominators are tiny differences of large power-basis terms, and the TM bounds (sums of absolute values: unrefreshed
Horner magnitudes, truncation terms, propagated height errors) lose up to `2^8` on the W0 sums. A **re-centred table**
`LS` (per degree) holds every record and every shared denominator re-expanded exactly at a dyadic centre
`a₀ = m / 2^k`; the rows evaluate it at the shifted height TM `shT c m k A = A - a₀`, whose magnitude is the
height range of the cell. The moment rows are unchanged.

For a slot body `b` (biased integers, width `w`) of length `n` with scale `M`, the shifted body `b'` (width `w'`)
and scale `M'` satisfy `b'ⱼ - 2^(w'-1) = (ρPⱼ - ρNⱼ) 2^(k j)` and `M' 2^k = M 2^(k n)`, where `ρP`, `ρN` are the
exact homogeneous Taylor shifts `shiftH m k` of the positive and negative parts of `b`; then
`Σ b'ⱼ tʲ / M' = Σ bᵢ (a₀ + t)ⁱ / M` (`CoeffMap.Deg.ShiftSound.bodyShiftOk_eval`). Every operation is a `Nat`
primitive (no `Int`, no division).

* `mulLin`, `addHead`, `shiftH`: exact Taylor shift of `ℕ` coefficient lists;
* `cmpShift`, `bodyShiftOk`, `recShiftOk`, `denShiftOk`, `recShiftRange`, `denShiftAll`: the one-time checks that
  `LS` is the exact shift of `L` (records `[k0, k1)`, all shared denominators);
* `scalarRowC`, `blockRowC`: rows with the re-centred records (records outside the table fall back to `recTMr`);
* `pTC`, `pLookC`, `zStageOkC`, `pSBC`, `pTSC`, `PSC`: the single-stage and staged `P` programs of
  `CoeffMap.Deg.Prog` / `CoeffMap.Deg.StageZ` with these rows (same code, other rows).

Soundness: `CoeffMap.Deg.ShiftSound`. Bit-exact mirror: `CoeffMap/Deg/gen/mirror.py` (`Leaf.shift`).
-/

namespace ThomsonCompact.CoeffMap.Deg

open ThomsonCompact.Packed ThomsonCompact.CoeffMap

/-! ## Exact Taylor shift of `ℕ` coefficient lists -/

/-- `(m + u) · r + p` for a low-first list `r`: `[m r₀ + p, m r₁ + r₀, …, m r_e + r_{e-1}, r_e]`. -/
noncomputable def mulLin (m : Nat) : List Nat → Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun p => [p]) (fun x _ ih p => Nat.add (Nat.mul m x) p :: ih x)

/-- `a + r` (on the constant coefficient). -/
noncomputable def addHead (a : Nat) (r : List Nat) : List Nat :=
  List.casesOn (motive := fun _ => List Nat) r [a] (fun x xs => Nat.add a x :: xs)

/-- **Exact homogeneous Taylor shift**: `(ρ, 2^(k n))` for `w` of length `n`, with
`Σⱼ ρⱼ uʲ = Σᵢ wᵢ 2^(k (n-1-i)) (m + u)ⁱ`; at `u = 2^k y - m` this is `2^(k (n-1)) Σᵢ wᵢ yⁱ`. -/
noncomputable def shiftH (m k : Nat) (w : List Nat) : List Nat × Nat :=
  List.rec (motive := fun _ => List Nat × Nat) ([], 1)
    (fun x _ ih => (addHead (Nat.mul x ih.2) (mulLin m ih.1 0), Nat.shiftLeft ih.2 k)) w

/-- Positive part `v - 2^(w-1)` of a biased `w`-bit slot (truncated). -/
def posW (w v : Nat) : Nat := Nat.sub v (Nat.shiftLeft 1 (Nat.sub w 1))

/-- Negative part `2^(w-1) - v` of a biased `w`-bit slot (truncated). -/
def negW (w v : Nat) : Nat := Nat.sub (Nat.shiftLeft 1 (Nat.sub w 1)) v

/-- `s'ⱼ + ρNⱼ pⱼ = ρPⱼ pⱼ + 2^(w'-1)` for every `j`, with `pⱼ = p 2^(k j)`, and the three lists have the same
length. -/
noncomputable def cmpShift (w' k : Nat) : List Nat → List Nat → List Nat → Nat → Bool :=
  List.rec (motive := fun _ => List Nat → List Nat → Nat → Bool)
    (fun rp rn _ => rp.isEmpty && rn.isEmpty)
    (fun s _ ih rp rn pw => List.casesOn (motive := fun _ => Bool) rp false (fun p rp' =>
      List.casesOn (motive := fun _ => Bool) rn false (fun q rn' =>
        Nat.beq (Nat.add s (Nat.mul q pw)) (Nat.add (Nat.mul p pw) (Nat.shiftLeft 1 (Nat.sub w' 1))) &&
          ih rp' rn' (Nat.shiftLeft pw k))))

/-- The body `b'` (width `w'`, scale `M'`) is the shift of the body `b` (width `w`, scale `M`) at `m / 2^k`. -/
noncomputable def bodyShiftOk (m k w w' : Nat) (b b' : List Nat) (M M' : Nat) : Bool :=
  (fun rP rN => (b.isEmpty || Nat.beq (Nat.shiftLeft M' k) (Nat.mul M rP.2)) && cmpShift w' k b' rP.1 rN.1 1)
    (shiftH m k (b.map (posW w))) (shiftH m k (b.map (negW w)))

namespace DegD

variable (L : DegD)

/-- Numerator record `i` of `LS` is the shift of record `i` of `L` (same shared denominator index `< nDen`). -/
noncomputable def recShiftOk (LS : DegD) (m k i : Nat) : Bool :=
  (fun s s' => Nat.beq (s'.getD 2 0) (s.getD 2 0) && Nat.blt (s.getD 2 0) L.nDen &&
      bodyShiftOk m k L.rfW LS.rfW ((s.drop 3).take (s.getD 0 0)) ((s'.drop 3).take (s'.getD 0 0)) (s.getD 1 1)
        (s'.getD 1 1))
    (L.recSlots i) (LS.recSlots i)

/-- Shared denominator `d` of `LS` is the shift of denominator `d` of `L`. -/
noncomputable def denShiftOk (LS : DegD) (m k d : Nat) : Bool :=
  (fun s s' => bodyShiftOk m k L.rfW LS.rfW ((s.drop 2).take (s.getD 0 0)) ((s'.drop 2).take (s'.getD 0 0))
      (s.getD 1 1) (s'.getD 1 1))
    (L.denSlots d) (LS.denSlots d)

/-- One-time leaf: the records `k0 ≤ i < k1` of `LS` are shifted records of `L`. -/
noncomputable def recShiftRange (LS : DegD) (m k k0 k1 : Nat) : Bool :=
  (List.range k1).all fun i => !(Nat.ble k0 i) || L.recShiftOk LS m k i

/-- One-time leaf: every shared denominator of `LS` is the shifted denominator of `L`. -/
noncomputable def denShiftAll (LS : DegD) (m k : Nat) : Bool :=
  (List.range L.nDen).all fun d => L.denShiftOk LS m k d

end DegD

/-! ## Rows with re-centred records -/

/-- The shifted height TM `A - m/2^k` (exact for `k ≤ S`), with exact magnitudes (`refresh`: the magnitude bound of
`A - a₀` is the height range of the cell, not `|A| + a₀`). -/
def shT (c : Ctx) (m k : Nat) (A : TM) : TM := refresh c (addC c true (Nat.shiftLeft m (Nat.sub c.S k)) 0 A)

namespace DegD

variable (L : DegD)

/-- Row `u` of scalar block `j` with the re-centred records of `LS` at `T = A - a₀` (records outside the table:
`recTMr` at `A`). -/
noncomputable def scalarRowC (LS : DegD) (c : Ctx) (A T : TM) (j u : Nat) : List (Nat × Option TM) :=
  ((List.range (L.gdim (Nat.add L.dH j))).filter fun i => !(Nat.beq (L.colRec j i u) 1)).map fun i =>
    (i, if Nat.beq (L.colRec j i u) 0 then none else
      some (cond (Nat.blt (L.colRec j i u) L.nRec) (LS.recTMr c T (L.colRec j i u)) (L.recTMr c A (L.colRec j i u))))

/-- Rows of block `b` with re-centred scalar records (moment rows as in `blockRow`; if `k > S` or the shifted TM
is not `ok`, the rows of `blockRow`). -/
noncomputable def blockRowC (LS : DegD) (m k : Nat) (c : Ctx) (A : TM) (b : Nat) : Nat → List (Nat × Option TM) :=
  if b < L.dH then momentRowd c A b (L.piv b) (L.gdim b) else
    cond (Nat.ble k c.S && (shT c m k A).ok) (L.scalarRowC LS c A (shT c m k A) (b - L.dH))
      (L.scalarRowr c A (b - L.dH))

/-- The table of `P u v = (K W Kᵀ)ᵤᵥ` with the re-centred rows (`pT`). -/
noncomputable def pTC (LS : DegD) (m k : Nat) (c : Ctx) (A : TM) (WT : Nat → Nat → TM) (b : Nat) :
    List (List TM) :=
  pTabD c (L.blockRowC LS m k c A b)
    (zColsD c (L.blockRowC LS m k c A b) (wRowsD WT (L.gdim b)) (L.gdim b) (L.rdim b)) (L.rdim b)

/-- The single-stage `P` lookup with the re-centred rows (`pLook`). -/
noncomputable def pLookC (LS : DegD) (m k : Nat) (c : Ctx) (A : TM) (WT : Nat → Nat → TM) (b : Nat) :
    Nat → Nat → TM :=
  fun u v => listAt zeroTM (listAt [] (L.pTC LS m k c A WT b) u) v

/-- **Stage-Z leaf** with the re-centred rows (`zStageOk`). -/
noncomputable def zStageOkC (LS : DegD) (m k : Nat) (c : Ctx) (A : TM) (WT : Nat → Nat → TM) (zd : ZData)
    (b v0 v1 i0 i1 : Nat) : Bool :=
  (List.range (L.rdim b)).all fun v => !(Nat.ble v0 v && Nat.blt v v1) ||
    Option.casesOn (motive := fun _ => Bool) (pivotOf (L.blockRowC LS m k c A b v))
      ((List.range (L.gdim b)).all fun i => !(Nat.ble i0 i && Nat.blt i i1) ||
        L.zOk1 c zd b i v (zTMD c (L.blockRowC LS m k c A b) (wRowsD WT (L.gdim b)) i v))
      (fun _ => true)

/-- Entry `P v u` at `(u, v)` from the stored z columns (`pSB`) with the re-centred rows. -/
noncomputable def pSBC (LS : DegD) (m k : Nat) (c : Ctx) (A : TM) (WT : Nat → Nat → TM) (zd : ZData) (b : Nat)
    (u v : Nat) : TM :=
  Option.casesOn (motive := fun _ => TM) (pivotOf (L.blockRowC LS m k c A b u))
    (Option.casesOn (motive := fun _ => TM) (pivotOf (L.blockRowC LS m k c A b v))
      (dotOpt c (zipRow (L.blockRowC LS m k c A b v) (mkList (fun i => L.zDec c zd b i u) (L.gdim b)) 0))
      (fun j => L.zDec c zd b j u))
    (fun i => Option.casesOn (motive := fun _ => TM) (pivotOf (L.blockRowC LS m k c A b v))
      (L.zDec c zd b i v)
      (fun j => WT j i))

/-- The table of all `pSBC u v` (outer index `v`, literal indices). -/
noncomputable def pTSC (LS : DegD) (m k : Nat) (c : Ctx) (A : TM) (WT : Nat → Nat → TM) (zd : ZData) (b : Nat) :
    List (List TM) :=
  mkList (fun v => mkList (fun u => L.pSBC LS m k c A WT zd b u v) (L.rdim b)) (L.rdim b)

/-- **Stage-P `P` lookup** with the re-centred rows (`PS`). -/
noncomputable def PSC (LS : DegD) (m k : Nat) (c : Ctx) (A : TM) (WT : Nat → Nat → TM) (zd : ZData) (b : Nat)
    (u v : Nat) : TM :=
  listAt zeroTM (listAt [] (L.pTSC LS m k c A WT zd b) v) u

end DegD

end ThomsonCompact.CoeffMap.Deg
