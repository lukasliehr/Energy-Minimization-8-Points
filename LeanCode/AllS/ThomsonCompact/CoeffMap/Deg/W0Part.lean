import ThomsonCompact.CoeffMap.Deg.W0LinkD
import ThomsonCompact.CoeffMap.Deg.SumSound

/-!
# The W0 part of the D14/D16/D18 residuals from per-cell leaves: degree-generic core (F2h)

The per-degree inputs are bundled in `DegLink L d p` (table facts `LinkFacts`, the old raw moment tensors with their
substitution lemma and coefficients, the scalar columns from the RF record bridges, and the one-time block checks);
`CoeffMap/Deg/Bridges/D<D>/Link.lean` builds one per degree. Per cell, the inputs are the leaf facts:

* `hA`: the packed height TM encloses `aS ∘ s` on the cell;
* `hden`: `L.denOkD ctx A sd = true` (owner partition; no shared RF denominator vanishes on the cell);
* `hP`: the `P` lookups `PT b h` of the leaves of block `b`, owner part `h` enclose the real `P` tables `PfL`
  (single-stage leaves: `hP_single` from enclosures `WT` of the W0 entries);
* `hpc`: every piece `(b, g, h)` at every coordinate `r` is `ok` and matches its checkpoint (`leafOk_spec` of the
  piece leaves);
* `hsum`: the final sum records pass (`sumOkD` leaves).

Pieces are indexed by `ι = 32 (32 b + g) + h` (`pieceB`, `pieceG`, `pieceH`); invalid pieces (`b ≥ d + 8`,
`g ≥ nGrp b` or `h ≥ np b`) have `B = 0` and `g = 0`. Results: `BP_valid` (the `B_valid` field), `gP_link` (the
`W0_link` field in the generic Gram form), `bsum_valid_gP` (`Bsum_valid`). The interface glue per degree is in
`Bridges/D<D>/Part.lean` (`W0Part14`, `w0Part_of14`, …).
-/

noncomputable section
open scoped BigOperators

namespace ThomsonCompact.CoeffMap.Deg.Link

open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite ThomsonCompact.CoeffMap ThomsonCompact.Packed
open ThomsonCompact.CoeffMap.Deg

/-! ## Per-degree inputs -/

/-- Everything one degree supplies to the W0 link (all checked once per degree). -/
structure DegLink (L : DegD) (d : ℕ) (p : MomentPivots d) where
  facts : LinkFacts L d p
  momQ : (k : Fin d) → Matrix (Fin (d - k.val + 1)) (Fin (d - k.val + 1)) Poly3
  hsub : ∀ k u v, invariantSubst (momQ k u v) = kernelRPoly k.val u.val v.val
  hcoef : ∀ (k : Fin d) (u v : Fin (d - k.val + 1)) (r : ℕ),
    MvPolynomial.coeff (tagExponent (L.rtag r)) (momQ k u v) = L.Cc k.val r u.val v.val
  hcols : ∀ a, physical a → (∀ k, k < L.nRec → (L.rfRec k).toRatFun.DefinedAt a) → ScalarColumnsL L d a
  checks : ∀ b, b < d + 8 → L.BlockChecks b

theorem nGrp_le (L : DegD) (b : ℕ) (h : L.grpOk b = true) : L.nGrp b ≤ 31 := by
  unfold DegD.grpOk at h
  simp only [Bool.and_eq_true, Nat.ble_eq] at h
  exact h.1.2

/-- `DefinedAt` of every record from the nonvanishing shared denominators. -/
theorem definedAt_of (L : DegD) (hden : ∀ k, k < L.nRec → L.denIdx k < L.nDen ∧ 0 < L.denS (L.denIdx k))
    (a : ℝ) (h : ∀ d, d < L.nDen → evalZ (L.denZ d) a ≠ 0) :
    ∀ k, k < L.nRec → (L.rfRec k).toRatFun.DefinedAt a := by
  intro k hk
  rw [RFRec.definedAt_iff]
  obtain ⟨h1, h2⟩ := hden k hk
  show evalZ (L.denZ (L.denIdx k)) a / (L.denS (L.denIdx k) : ℝ) ≠ 0
  exact div_ne_zero (h _ h1) (by exact_mod_cast h2.ne')

/-! ## Piece indexing -/

/-- Block, group and owner part of piece `ι = 32 (32 b + g) + h`. -/
def pieceB (ι : ℕ) : ℕ := ι / 1024
def pieceG (ι : ℕ) : ℕ := ι / 32 % 32
def pieceH (ι : ℕ) : ℕ := ι % 32

theorem sum_pieces (nb : ℕ) (f : ℕ → ℕ → ℕ → ℝ) :
    ∑ ι : Fin (nb * 32 * 32), f (pieceB ι) (pieceG ι) (pieceH ι) =
      ∑ b ∈ Finset.range nb, ∑ g ∈ Finset.range 32, ∑ h ∈ Finset.range 32, f b g h := by
  rw [← Equiv.sum_comp ((finProdFinEquiv.prodCongr (Equiv.refl (Fin 32))).trans finProdFinEquiv)]
  simp only [Fintype.sum_prod_type, Finset.sum_range]
  refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun g _ => Finset.sum_congr rfl (fun h _ => ?_)))
  have hb := b.isLt
  have hg := g.isLt
  have hh := h.isLt
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply, finProdFinEquiv_apply_val]
  unfold pieceB pieceG pieceH
  congr 1 <;> omega

/-! ## The pieces of a cell -/

section Pieces

variable (L : DegD) (sd : SumD) (a : ℝ → ℝ) (data : CellData)

/-- Validity of piece `(b, g, h)`. -/
def pieceValid (b g h : ℕ) : Prop := b < L.dH + 8 ∧ g < L.nGrp b ∧ h < sd.np b

instance (b g h : ℕ) : Decidable (pieceValid L sd b g h) := by unfold pieceValid; infer_instance

/-- Real function of piece `ι` at coordinate `r` (`0` for invalid pieces). -/
def gP (ι r : ℕ) (x : ℝ) : ℝ :=
  if pieceValid L sd (pieceB ι) (pieceG ι) (pieceH ι) then pieceFL L sd a data (pieceB ι) (pieceG ι) (pieceH ι) r x
  else 0

/-- Piece TMs of the leaves: block `b`, group `g`, part `h` (`P` lookup `PT b h`), coordinate `r`. -/
def TP (c : Ctx) (PT : ℕ → ℕ → ℕ → ℕ → TM) (b g h r : ℕ) : TM :=
  L.pieceTM c (PT b h) sd b g (sd.plo b h) (sd.plo b (h + 1)) ((L.eTab (32 * b + g)).getD r [])

/-- The QModel of piece `ι` at coordinate `r` (the zero model for invalid pieces). -/
def BP (c : Ctx) (PT : ℕ → ℕ → ℕ → ℕ → TM) (ι r : ℕ) : QModel c.N :=
  if pieceValid L sd (pieceB ι) (pieceG ι) (pieceH ι) then toQModel c (TP L sd c PT (pieceB ι) (pieceG ι) (pieceH ι) r)
  else toQModel c zeroTM

end Pieces

variable {N S B W : ℕ}

/-- The piece TMs enclose the real piece functions (any `P` lookups enclosing the real `P` tables). -/
theorem TP_encl (L : DegD) (sd : SumD) (a : ℝ → ℝ) (data : CellData) (hg : Good N S B W)
    (PT : ℕ → ℕ → ℕ → ℕ → TM)
    (hP : ∀ b h, b < L.dH + 8 → h < sd.np b → ∀ u v,
      EnclOk (mkCtx N S B W) (PT b h u v) (fun t => PfL L a data b u v t))
    (b g h r : ℕ) (hb : b < L.dH + 8) (hh : h < sd.np b) :
    EnclOk (mkCtx N S B W) (TP L sd (mkCtx N S B W) PT b g h r) (pieceFL L sd a data b g h r) :=
  pieceTM_sound L hg b (hP b h hb hh) sd g _ _ _

/-- **`B_valid`**: every piece model is valid for its real function. -/
theorem BP_valid (L : DegD) (sd : SumD) (a : ℝ → ℝ) (data : CellData) (hg : Good N S B W)
    (PT : ℕ → ℕ → ℕ → ℕ → TM)
    (hP : ∀ b h, b < L.dH + 8 → h < sd.np b → ∀ u v,
      EnclOk (mkCtx N S B W) (PT b h u v) (fun t => PfL L a data b u v t))
    (n : ℕ) (hpc : ∀ b g h r, b < L.dH + 8 → g < L.nGrp b → h < sd.np b → r < L.nc →
      (TP L sd (mkCtx N S B W) PT b g h r).ok = true ∧
        ckOk (mkCtx N S B W) sd.F n (TP L sd (mkCtx N S B W) PT b g h r) (ckRecD sd n b g h r) = true)
    (ι r : ℕ) (hr : r < L.nc) :
    (BP L sd (mkCtx N S B W) PT ι r).asTM.Valid (gP L sd a data ι r) := by
  unfold BP gP
  by_cases hv : pieceValid L sd (pieceB ι) (pieceG ι) (pieceH ι)
  · simp only [if_pos hv]
    obtain ⟨hb, hgr, hh⟩ := hv
    exact Encl.validQ hg (TP_encl L sd a data hg PT hP _ _ _ r hb hh (hpc _ _ _ r hb hgr hh hr).1)
  · simp only [if_neg hv]
    exact Encl.validQ hg zero_sound

/-- The sum of all piece functions is the triple sum over the valid pieces. -/
theorem sum_gP (L : DegD) (sd : SumD) (a : ℝ → ℝ) (data : CellData) (d : ℕ) (hd : L.dH = d)
    (hng : ∀ b, b < d + 8 → L.nGrp b ≤ 32) (hnp : ∀ b, b < d + 8 → sd.np b ≤ 32) (r : ℕ) (x : ℝ) :
    ∑ ι : Fin ((d + 8) * 32 * 32), gP L sd a data ι r x =
      ∑ b ∈ Finset.range (d + 8), ∑ g ∈ Finset.range (L.nGrp b), ∑ h ∈ Finset.range (sd.np b),
        pieceFL L sd a data b g h r x := by
  have e := sum_pieces (d + 8) (fun b g h => if pieceValid L sd b g h then pieceFL L sd a data b g h r x else 0)
  refine e.trans (Finset.sum_congr rfl (fun b hb => ?_))
  have hb' := Finset.mem_range.mp hb
  have hbv : b < L.dH + 8 := by rw [hd]; exact hb'
  rw [← Finset.sum_range_add_sum_Ico _ (hng b hb')]
  rw [Finset.sum_eq_zero (s := Finset.Ico _ _) (fun g hg => by
    have := (Finset.mem_Ico.mp hg).1
    refine Finset.sum_eq_zero (fun h _ => ?_)
    rw [if_neg (fun hv => by have := hv.2.1; omega)]), add_zero]
  refine Finset.sum_congr rfl (fun g hg => ?_)
  have hg' := Finset.mem_range.mp hg
  rw [← Finset.sum_range_add_sum_Ico _ (hnp b hb')]
  rw [Finset.sum_eq_zero (s := Finset.Ico _ _) (fun h hh => by
    have := (Finset.mem_Ico.mp hh).1
    rw [if_neg (fun hv => by have := hv.2.2; omega)]), add_zero]
  refine Finset.sum_congr rfl (fun h hh => ?_)
  rw [if_pos ⟨hbv, hg', Finset.mem_range.mp hh⟩]

/-- **`W0_link` in the generic Gram form**: the retained coordinate `r` of the Gram polynomial of a family with the
literal Gram entries at `x` is the sum of the piece functions. -/
theorem gP_link (L : DegD) (d : ℕ) (hl : 6 ≤ d) (hu : d ≤ 9) (p : MomentPivots d) (hp : ValidMomentPivots p)
    (K : DegLink L d p) (hg : Good N S B W) {A : TM} (s : ℝ → ℝ)
    (hA : Encl (mkCtx N S B W) A (fun x => aS (s x))) (sd : SumD)
    (hden : L.denOkD (mkCtx N S B W) A sd = true) (hnp : ∀ b, b < d + 8 → sd.np b ≤ 32)
    (data : CellData) (x : ℝ) (hx : x ∈ cellDomain) (hs : 0 ≤ s x)
    (W' : GramFamily d) (hW : ∀ b i j, W'.val b i j = litW data (bIdx d b) i.val j.val x)
    (t : RetainedIndex (2 * d)) (r : ℕ) (hr : r < L.nc) (ht : t.val = L.rtag r) :
    retainCompatible (aS (s x)) (2 * d)
        ⟨gramPoly (aS (s x)) d p W', gramPoly_compatible (aS (s x)) (aS_physical _ hs) d hl hu p hp W'⟩ t =
      ∑ ι : Fin ((d + 8) * 32 * 32), gP L sd (fun x => aS (s x)) data ι r x := by
  obtain ⟨hpo, hnz⟩ := denOkD_sound L hg hA sd hden
  have hdef := definedAt_of L K.facts.den_tab (aS (s x)) (fun dd hdd => hnz dd hdd x hx)
  rw [sum_gP L sd _ data d K.facts.dH (fun b hb => (nGrp_le L b (K.checks b hb).grp).trans (by norm_num)) hnp r x]
  exact pieces_link L d hl hu p hp K.facts K.momQ K.hsub K.hcoef K.checks sd hpo data (fun x => aS (s x)) x hx
    (aS_physical _ hs) (K.hcols _ (aS_physical _ hs) hdef) W' hW t r hr ht

/-- **`Bsum_valid`**: the final sum records enclose the sum of the piece functions. -/
theorem bsum_valid_gP (L : DegD) (d : ℕ) (hd : L.dH = d) (hng : ∀ b, b < d + 8 → L.nGrp b ≤ 32)
    (hg : Good N S B W) (sd : SumD) (a : ℝ → ℝ) (data : CellData) (PT : ℕ → ℕ → ℕ → ℕ → TM)
    (hP : ∀ b h, b < L.dH + 8 → h < sd.np b → ∀ u v,
      EnclOk (mkCtx N S B W) (PT b h u v) (fun t => PfL L a data b u v t))
    (hnp : ∀ b, b < d + 8 → sd.np b ≤ 32) (n : ℕ) (hn : n ≤ N)
    (hpc : ∀ b g h r, b < L.dH + 8 → g < L.nGrp b → h < sd.np b → r < L.nc →
      (TP L sd (mkCtx N S B W) PT b g h r).ok = true ∧
        ckOk (mkCtx N S B W) sd.F n (TP L sd (mkCtx N S B W) PT b g h r) (ckRecD sd n b g h r) = true)
    (r : ℕ) (hr : r < L.nc) (hsum : L.sumOkRD sd n r = true) :
    (BsumD n S sd r).asTM.Valid (fun x => ∑ ι : Fin ((d + 8) * 32 * 32), gP L sd a data ι r x) := by
  have h := bsum_validD hg L sd n hn (fun b g h => pieceFL L sd a data b g h r)
    (fun b g h => TP L sd (mkCtx N S B W) PT b g h r) r (fun b hb g hgr h hh => by
      have hpc' := hpc b g h r hb hgr hh hr
      exact ⟨TP_encl L sd a data hg PT hP b g h r hb hh hpc'.1, hpc'.2⟩) hsum
  have e : (fun x => ∑ ι : Fin ((d + 8) * 32 * 32), gP L sd a data ι r x) =
      (fun x => ∑ b ∈ Finset.range (Nat.add L.dH 8), ∑ g ∈ Finset.range (L.nGrp b), ∑ h ∈ Finset.range (sd.np b),
        pieceFL L sd a data b g h r x) := by
    funext x
    rw [sum_gP L sd a data d hd hng hnp r x]
    show _ = ∑ b ∈ Finset.range (L.dH + 8), _
    rw [hd]
  rw [e]
  exact h

/-! ## Single-stage leaves: the `P` lookups of the W0 entries -/

/-- **`hP` for single-stage leaves**: the computed `P` table of block `b` (rows `blockRow`, W0 entry TMs `WT b`)
encloses the real `P` table. -/
theorem hP_single (L : DegD) (d : ℕ) (p : MomentPivots d) (hF : LinkFacts L d p) (hg : Good N S B W) {A : TM}
    {a : ℝ → ℝ} (hA : Encl (mkCtx N S B W) A a) (data : CellData) (WT : ℕ → ℕ → ℕ → TM)
    (hW : ∀ b i j, EnclOk (mkCtx N S B W) (WT b i j) (litW data b i j))
    (hWsym : ∀ b i j, WT b i j = WT b j i) (b : ℕ) (u v : ℕ) :
    EnclOk (mkCtx N S B W) (L.pLook (mkCtx N S B W) A (WT b) b u v) (fun t => PfL L a data b u v t) := by
  have hmom : b < L.dH → L.piv b ≤ L.gdim b ∧ ∀ j, j ≤ L.gdim b → qAllZero (mP b j).s = true := by
    intro hb
    rw [hF.dH] at hb
    have h1 := hF.piv ⟨b, hb⟩
    have hp' := (p ⟨b, hb⟩).isLt
    refine ⟨by rw [h1, hF.gdim_mom ⟨b, hb⟩]; simp only at hp' ⊢; omega, fun j hj => hF.mom_rat ⟨b, hb⟩ j hj⟩
  have hgood : b < L.dH → L.piv b ≤ L.gdim b ∧ L.rdim b = L.gdim b + 1 := by
    intro hb
    refine ⟨(hmom hb).1, ?_⟩
    rw [hF.dH] at hb
    rw [hF.rdim_mom ⟨b, hb⟩, hF.gdim_mom ⟨b, hb⟩]
  exact pLook_sound L hg b (hW b) (fun u => blockRow_ok L hg hA hF.rec0 b hmom u)
    (fun u hu => blockRow_good L _ A b hgood u hu) (hWsym b)
    (fun i j t ht => litW_symm data b i j t ht) u v

#print axioms BP_valid
#print axioms gP_link
#print axioms bsum_valid_gP
#print axioms hP_single

end ThomsonCompact.CoeffMap.Deg.Link
