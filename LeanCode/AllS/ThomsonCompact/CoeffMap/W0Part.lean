import ThomsonCompact.CoeffMap.BPiece
import ThomsonCompact.CoeffMap.KRowsRSound
import ThomsonCompact.CoeffMap.BLeaf
import ThomsonCompact.CoeffMap.GramPackSound

/-!
# The W0 part of `Residual12` from per-cell leaves (F2d; generic over the cell data)

`W0Part s cell blk hord N nb` bundles exactly the fields `B`, `g`, `B_valid`, `W0_link` of
`Interface.D12.Residual12 s m cell blk hord N t nb` (any `m`, `t`). For decoded cell data `d : CellData` (the
exporter's `Cells/<cell>/W0.lean`), literal cell `d.cell` and blocks `blkOf d b = d.block (blockEquiv.symm b)`,
`w0Part_of` builds it with `nb = 112` pieces `(block, pair group) ∈ Fin 14 × Fin 8` (`finProdFinEquiv`) from

* a height TM `A` enclosing `aS ∘ s` on the cell (`hA`, from the old accepted root model),
* `hok`: every piece TM `blockTMgr c A (WTp d c bi) bi g r` (precise rows, `CoeffMap.KRowsR`) has `ok = true` (the
  per-cell leaves),
* `hden`: `denOk c A = true` (the per-cell denominator leaf).

Piece TMs are `toQModel` of `blockTMgr` on the packed W0 entries `WTp` (`WTp_sound`, `blockTMgr_sound`); the pieces of a
block sum to its contribution (`gPiece_sum`), the contributions to the retained Gram coordinates (`W0_link_pk`).
`W0Part.congr` transports along `s = s'` (e.g. between `fun x => c + h * x` and the old `RootAccepted.exponent`).
-/

namespace ThomsonCompact.CoeffMap

open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite ThomsonCompact.Packed
open ThomsonCompact.CoeffMap.D12
open scoped BigOperators

theorem blockOkgr_spec {c : Ctx} {A : TM} {WT : ℕ → ℕ → TM} {bi g0 g1 r0 r1 : ℕ}
    (h : blockOkgr c A WT bi g0 g1 r0 r1 = true) :
    ∀ g, g0 ≤ g → g < g1 → ∀ r, r0 ≤ r → r < r1 → (blockTMg c A WT bi g r).ok = true := by
  induction g1 with
  | zero => intro g _ h1; exact absurd h1 (Nat.not_lt_zero _)
  | succ k ih =>
    intro g h0 h1 r hr0 hr1
    have h' : cond (Nat.ble g0 k) (Nat.rec (motive := fun _ => Bool) true
        (fun r ih2 => cond (Nat.ble r0 r) ((blockTMg c A WT bi k r).ok && ih2) ih2) r1 &&
          blockOkgr c A WT bi g0 k r0 r1) (blockOkgr c A WT bi g0 k r0 r1) = true := h
    rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h2 | h2
    · apply ih _ g h0 h2 r hr0 hr1
      cases hb : Nat.ble g0 k
      · rw [hb] at h'; exact h'
      · rw [hb, cond_true, Bool.and_eq_true] at h'; exact h'.2
    · subst h2
      rw [show Nat.ble g0 g = true from Nat.ble_eq.mpr h0, cond_true, Bool.and_eq_true] at h'
      have hr' := h'.1
      clear h' ih h1 h0 h
      revert hr'
      induction r1 with
      | zero => exact absurd hr1 (Nat.not_lt_zero _)
      | succ m ihm =>
        intro hm
        have hm' : cond (Nat.ble r0 m) ((blockTMg c A WT bi g m).ok && Nat.rec (motive := fun _ => Bool) true
            (fun r ih2 => cond (Nat.ble r0 r) ((blockTMg c A WT bi g r).ok && ih2) ih2) m)
            (Nat.rec (motive := fun _ => Bool) true
              (fun r ih2 => cond (Nat.ble r0 r) ((blockTMg c A WT bi g r).ok && ih2) ih2) m) = true := hm
        rcases Nat.lt_succ_iff_lt_or_eq.mp hr1 with h3 | h3
        · apply ihm h3
          cases hb : Nat.ble r0 m
          · rw [hb] at hm'; exact hm'
          · rw [hb, cond_true, Bool.and_eq_true] at hm'; exact hm'.2
        · subst h3
          rw [show Nat.ble r0 r = true from Nat.ble_eq.mpr hr0, cond_true, Bool.and_eq_true] at hm'
          exact hm'.1

/-- The `Residual12` fields produced by F2 (W0 contributions and their link to the Gram map). -/
structure W0Part (s : ℝ → ℝ) (cell : Literals.Cell) (blk : GramBlock 6 → Literals.Block)
    (hord : ∀ b, (blk b).order = gramBlockDimension 6 b) (N nb : ℕ) where
  B : Fin nb → Fin 100 → QModel N
  g : Fin nb → Fin 100 → ℝ → ℝ
  B_valid : ∀ b r, (B b r).asTM.Valid (g b r)
  W0_link : ∀ (x : ℝ) (hx : x ∈ cellDomain) (hs : 0 ≤ s x) (r : Fin 100),
    retainCompatible (aS (s x)) 12 (ThomsonCompact.Interface.D12.gramMap s x hs
      (ThomsonCompact.Interface.D12.W0 cell blk hord x hx)) (FixedTables.D12.retainedIndex r) = ∑ b, g b r x

/-- Transport of a `W0Part` along an equality of exponent functions. -/
def W0Part.congr {s s' : ℝ → ℝ} {cell : Literals.Cell} {blk : GramBlock 6 → Literals.Block}
    {hord : ∀ b, (blk b).order = gramBlockDimension 6 b} {N nb : ℕ} (P : W0Part s cell blk hord N nb)
    (h : ∀ x, s x = s' x) : W0Part s' cell blk hord N nb :=
  (funext h : s = s') ▸ P

/-- Literal blocks of decoded cell data, indexed by Gram block. -/
noncomputable def blkOf (d : CellData) : GramBlock 6 → Literals.Block := fun b => d.block (blockEquiv.symm b)

theorem litGram_congr' (d : CellData) (t : ℝ) {x y : ℕ} (hxy : x = y) (a b : Fin (d.block x).order)
    (a' b' : Fin (d.block y).order) (ha : a.val = a'.val) (hb : b.val = b'.val) :
    literalGram d.cell (d.block x) t a b = literalGram d.cell (d.block y) t a' b' := by
  subst hxy
  rw [show a = a' from Fin.ext ha, show b = b' from Fin.ext hb]

theorem W0f_litW_of (d : CellData) (hord : ∀ b, (blkOf d b).order = gramBlockDimension 6 b) (bi : Fin 14)
    (i j : ℕ) (t : ℝ) : W0f d.cell (blkOf d) hord (blockEquiv bi) i j t = litW d bi i j t := by
  have hb : ((blockEquiv.symm (blockEquiv bi) : Fin 14) : ℕ) = (bi : ℕ) := by rw [Equiv.symm_apply_apply]
  have hdim : gramBlockDimension 6 (blockEquiv bi) = d.order bi := by
    rw [← hord (blockEquiv bi)]
    show d.order (blockEquiv.symm (blockEquiv bi)) = _
    rw [hb]
  unfold W0f litW
  by_cases h : i < d.order bi ∧ j < d.order bi
  · rw [dif_pos (show i < gramBlockDimension 6 (blockEquiv bi) ∧ j < gramBlockDimension 6 (blockEquiv bi) by
      rw [hdim]; exact h), dif_pos h]
    unfold ThomsonCompact.Interface.D12.W0mat
    rw [Matrix.submatrix_apply]
    exact litGram_congr' d t hb _ _ _ _ rfl rfl
  · rw [dif_neg (show ¬(i < gramBlockDimension 6 (blockEquiv bi) ∧ j < gramBlockDimension 6 (blockEquiv bi)) by
      rw [hdim]; exact h), dif_neg h]

/-- The W0 hypothesis of the block programs: packed entries enclose the literal Gram entries. -/
theorem hW_of {N S B W : ℕ} (hg : Good N S B W) (d : CellData)
    (hord : ∀ b, (blkOf d b).order = gramBlockDimension 6 b) (bi : Fin 14) :
    ∀ i j, EnclOk (mkCtx N S B W) (WTp d (mkCtx N S B W) bi i j) (W0f d.cell (blkOf d) hord (blockEquiv bi) i j) :=
  fun i j => (WTp_sound hg d bi i j).congr (fun t _ => (W0f_litW_of d hord bi i j t).symm)

/-- Pieces as `Fin 112`. -/
def pieceEquiv : Fin 14 × Fin 8 ≃ Fin 112 := finProdFinEquiv

/-- Piece `ι = (block, group)`. -/
def pieceOf (ι : Fin 112) : Fin 14 × Fin 8 := pieceEquiv.symm ι

/-- The 112 contribution TMs (`Residual12.B`). -/
noncomputable def Bpk (d : CellData) (c : Ctx) (A : TM) (ι : Fin 112) (r : Fin 100) : QModel c.N :=
  toQModel c (blockTMgr c A (WTp d c (pieceOf ι).1) (pieceOf ι).1 (pieceOf ι).2 r)

/-- Their real functions (`Residual12.g`). -/
noncomputable def gpk (s : ℝ → ℝ) (d : CellData) (hord : ∀ b, (blkOf d b).order = gramBlockDimension 6 b)
    (ι : Fin 112) (r : Fin 100) (x : ℝ) : ℝ :=
  gPiece s d.cell (blkOf d) hord (pieceOf ι).1 (D12G.gmap (pieceOf ι).1) 8 (pieceOf ι).2 r x

theorem gpk_piece (s : ℝ → ℝ) (d : CellData) (hord : ∀ b, (blkOf d b).order = gramBlockDimension 6 b)
    (bi : Fin 14) (g : Fin 8) (r : Fin 100) (x : ℝ) :
    gpk s d hord (pieceEquiv (bi, g)) r x = gPiece s d.cell (blkOf d) hord bi (D12G.gmap bi) 8 g r x := by
  unfold gpk
  rw [show pieceOf (pieceEquiv (bi, g)) = (bi, g) from Equiv.symm_apply_apply _ _]

/-- **The W0 part of `Residual12` from the leaves of a cell** (`nb = 112`). -/
noncomputable def w0Part_of {N S B W : ℕ} (hg : Good N S B W) (d : CellData) (s : ℝ → ℝ) {A : TM}
    (hA : Encl (mkCtx N S B W) A (fun x => aS (s x)))
    (hord : ∀ b, (blkOf d b).order = gramBlockDimension 6 b)
    (hok : ∀ (bi : Fin 14) (g : Fin 8) (r : Fin 100),
      (blockTMgr (mkCtx N S B W) A (WTp d (mkCtx N S B W) bi) bi g r).ok = true)
    (hden : denOk (mkCtx N S B W) A = true) : W0Part s d.cell (blkOf d) hord N 112 where
  B := Bpk d (mkCtx N S B W) A
  g := gpk s d hord
  B_valid := fun ι r => Encl.validQ hg (blockTMgr_sound hg s hA d.cell (blkOf d) hord _ (pieceOf ι).1
    (hW_of hg d hord _) (pieceOf ι).2 (pieceOf ι).2.isLt r (hok _ _ r))
  W0_link := fun x hx hs r => by
    rw [D12RF.W0_link_pk s d.cell (blkOf d) hord
      (fun x hx _ dd hdd => denOk_sound hg hA hden dd hdd x hx) x hx hs r]
    calc ∑ bi : Fin 14, g12 s D12RF.Kpk d.cell (blkOf d) hord bi r x
        = ∑ bi : Fin 14, ∑ g : Fin 8, gpk s d hord (pieceEquiv (bi, g)) r x := by
          refine Finset.sum_congr rfl (fun bi _ => ?_)
          rw [← gPiece_sum s d.cell (blkOf d) hord bi (D12G.gmap bi) 8 (by norm_num) r x hx,
            ← Fin.sum_univ_eq_sum_range (fun g => gPiece s d.cell (blkOf d) hord bi (D12G.gmap bi) 8 g r x)]
          exact Finset.sum_congr rfl (fun g _ => (gpk_piece s d hord bi g r x).symm)
      _ = ∑ ι, gpk s d hord ι r x :=
          (Fintype.sum_prod_type (fun p => gpk s d hord (pieceEquiv p) r x)).symm.trans
            (Fintype.sum_equiv pieceEquiv (fun p => gpk s d hord (pieceEquiv p) r x) (fun ι => gpk s d hord ι r x)
              (fun _ => rfl))

/-- `hord` from the 14 decoded block orders (`decide`). -/
theorem hord_of_data (d : CellData)
    (h : ((List.range 6).all fun k => Nat.beq (d.order k) (6 - k)) &&
      ((List.range 8).all fun j => Nat.beq (d.order (6 + j)) (sDimN j)) = true) :
    ∀ b, (blkOf d b).order = gramBlockDimension 6 b := by
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Nat.beq_eq, decide_eq_true_eq] at h
  refine ThomsonCompact.Interface.D12.hord_of_orders (blkOf d) (fun k => ?_) (fun b => ?_)
  · show d.order (blockEquiv.symm (.inl k)) = 6 - k.val
    rw [symm_inl]
    exact h.1 k k.isLt
  · show d.order (blockEquiv.symm (.inr b)) = ThomsonCompact.Interface.D12.scalarOrder b
    rw [symm_inr]
    have := h.2 (D12RF.bIdx b) (by cases b <;> decide)
    rw [this]
    cases b <;> rfl

#print axioms blockOkgr_spec
#print axioms w0Part_of
#print axioms hord_of_data

end ThomsonCompact.CoeffMap
