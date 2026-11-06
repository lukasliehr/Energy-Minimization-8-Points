import ThomsonCompact.CoeffMap.BPiece
import ThomsonCompact.CoeffMap.KRowsR

/-!
# Soundness of the precise rows (F2d)

`recTMr_sound`, `rhoTMr_sound`: the residual-lemma entries enclose the same real entries as the old ones (the RF
record values, the moment pivot ratios), by F1's `divR_sound` (with `invN_sound` for the enclosure of `1/q`) and
`refresh_sound`. Hence `blockRowr_ok` (same real rows `blockRowF`) and `blockTMgr_sound` (same real piece
functions `gPiece` as `blockTMg_sound`).
-/

namespace ThomsonCompact.CoeffMap

open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite ThomsonCompact.Packed
open ThomsonCompact.CoeffMap.D12
open scoped BigOperators

variable {N S B W : ℕ}

theorem denInvAt_eq (c : Ctx) (A : TM) (d : ℕ) : denInvAt c A d = invN c 8 0 (hornerQ c A (denQ d)) := by
  unfold denInvAt
  by_cases hd : d < D12RF.nDen
  · rw [show Nat.blt d D12RF.nDen = true from Nat.blt_eq.mpr hd, cond_true]
    unfold denInvTab
    exact listAt_mkList _ _ hd
  · rw [show Nat.blt d D12RF.nDen = false from by
      cases h : Nat.blt d D12RF.nDen
      · rfl
      · exact absurd (Nat.blt_eq.mp h) hd, cond_false]

theorem refresh_ok' (c : Ctx) (X : TM) : (refresh c X).ok = X.ok := rfl

/-- `ok` of a residual-lemma division gives `ok` of its three inputs. -/
theorem divR_ok_inputs {c : Ctx} {F G Rc : TM} (h : (divR c F G Rc).ok = true) :
    F.ok = true ∧ G.ok = true ∧ Rc.ok = true := by
  have e : (divR c F G Rc).ok = ((refresh c (polyOnly (mul c (refresh c F) Rc))).ok &&
      (add c (refresh c F) (neg c (mul c G (refresh c (polyOnly (mul c (refresh c F) Rc)))))).ok && Rc.ok) := rfl
  rw [e] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hF : F.ok = true := (mul_ok (show (mul c (refresh c F) Rc).ok = true from h1)).1
  have hG : G.ok = true := (mul_ok (show (mul c G (refresh c (polyOnly (mul c (refresh c F) Rc)))).ok = true from
    (add_ok h2).2)).1
  exact ⟨hF, hG, h3⟩

/-- **Precise records** enclose the RF record values. -/
theorem recTMr_sound (hg : Good N S B W) {A : TM} {a : ℝ → ℝ} (hA : Encl (mkCtx N S B W) A a) (k : ℕ) :
    EnclOk (mkCtx N S B W) (recTMr (mkCtx N S B W) A k) (fun t => (D12RF.rec k).value (a t)) := by
  intro hok
  unfold recTMr at hok ⊢
  rw [denInvAt_eq] at hok ⊢
  have h0 : (divR (mkCtx N S B W) (hornerQ (mkCtx N S B W) A (numQN k))
      (hornerQ (mkCtx N S B W) A (denQ (D12RF.denIdx k)))
      (invN (mkCtx N S B W) 8 0 (hornerQ (mkCtx N S B W) A (denQ (D12RF.denIdx k))))).ok = true := hok
  obtain ⟨hFo, hGo, hRo⟩ := divR_ok_inputs h0
  have hF := hornerQ_sound hg hA (numQN k) hFo
  have hG := hornerQ_sound hg hA (denQ (D12RF.denIdx k)) hGo
  obtain ⟨hg0, hR⟩ := invN_sound hg hG 8 0 hRo
  have h := refresh_sound hg (divR_sound hg hF hG hR hg0 h0)
  refine h.congr (fun t _ => ?_)
  rw [numQN_eq, evalQ_numQ, evalQ_denQ, RFRec.value, D12RF.rec_den, D12RF.rec_scaleD]

theorem scalarRowr_ok (hg : Good N S B W) {A : TM} {a : ℝ → ℝ} (hA : Encl (mkCtx N S B W) A a) (bi d u : ℕ) :
    RowOk (mkCtx N S B W) (scalarRowr (mkCtx N S B W) A bi d u) (scalarRowF a bi d u) := by
  unfold RowOk scalarRowr scalarRowF
  refine forall₂_map_same _ (fun i _ => ⟨rfl, ?_⟩)
  by_cases h0 : D12RF.colRec bi i u = 0
  · have hb : Nat.beq (D12RF.colRec bi i u) 0 = true := by simp [h0]
    simp only [hb, if_true, EntryOk]
    intro t _
    rw [h0, rec0_value]
  · have hb : Nat.beq (D12RF.colRec bi i u) 0 = false :=
      Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
    simp only [hb, Bool.false_eq_true, if_false, EntryOk]
    exact recTMr_sound hg hA _

/-- **Precise pivot ratios** enclose the moment pivot ratios. -/
theorem rhoTMr_sound (hg : Good N S B W) {A : TM} {a : ℝ → ℝ} (hA : Encl (mkCtx N S B W) A a) (k p i : ℕ)
    (hk : k < 6) (hsa : sA p i < 7 - k) (hp : p < 7 - k) :
    EnclOk (mkCtx N S B W) (rhoTMr (mkCtx N S B W) A k p i) (fun t => -(momentP k (sA p i) (a t) / momentP k p (a t))) := by
  intro hok
  have h0 : (divR (mkCtx N S B W) (hornerQ (mkCtx N S B W) A (momQ k (sA p i))) (hornerQ (mkCtx N S B W) A (momQ k p))
      (invN (mkCtx N S B W) 8 0 (hornerQ (mkCtx N S B W) A (momQ k p)))).ok = true := hok
  obtain ⟨hFo, hGo, hRo⟩ := divR_ok_inputs h0
  have hF := hornerQ_sound hg hA (momQ k (sA p i)) hFo
  have hG := hornerQ_sound hg hA (momQ k p) hGo
  obtain ⟨hg0, hR⟩ := invN_sound hg hG 8 0 hRo
  have h := refresh_sound hg (neg_sound (divR_sound hg hF hG hR hg0 h0))
  refine h.congr (fun t _ => ?_)
  simp only [momQ]
  rw [← momentP_D12 k (sA p i) hk hsa, ← momentP_D12 k p hk hp]

theorem momentRowr_ok (hg : Good N S B W) {A : TM} {a : ℝ → ℝ} (hA : Encl (mkCtx N S B W) A a)
    (k p d r : ℕ) (hk : k < 6) (hpd : p ≤ d) (hd : d = 6 - k) :
    RowOk (mkCtx N S B W) (momentRowr (mkCtx N S B W) A k p d r) (momentRowF a k p d r) := by
  unfold RowOk momentRowr momentRowF
  by_cases hr : r = p
  · simp only [hr, if_true]
    refine forall₂_map_same _ (fun i hi => ⟨rfl, ?_⟩)
    have hi' : i < d := List.mem_range.mp hi
    have hsa : sA p i < 7 - k := by unfold sA; split_ifs <;> omega
    exact rhoTMr_sound hg hA k p i hk hsa (by omega)
  · simp only [hr, if_false]
    exact List.Forall₂.cons ⟨rfl, fun t _ => rfl⟩ List.Forall₂.nil

theorem blockRowr_ok (hg : Good N S B W) {A : TM} {a : ℝ → ℝ} (hA : Encl (mkCtx N S B W) A a) (bi : Fin 14)
    (u : ℕ) : RowOk (mkCtx N S B W) (blockRowr (mkCtx N S B W) A bi u) (blockRowF a bi u) := by
  unfold blockRowr blockRowF
  by_cases h : bi.val < 6
  · simp only [h, if_true]
    have hp : pivN bi ≤ 6 - bi := by fin_cases bi <;> simp_all [pivN]
    exact momentRowr_ok hg hA bi (pivN bi) (6 - bi) u h hp rfl
  · simp only [h, if_false]
    exact scalarRowr_ok hg hA _ _ _

/-- **B soundness for one piece with the precise rows** (same real piece function as `blockTMg_sound`). -/
theorem blockTMgr_sound (hg : Good N S B W) {A : TM} (s : ℝ → ℝ)
    (hA : Encl (mkCtx N S B W) A (fun t => aS (s t))) (cell : Literals.Cell)
    (blk : GramBlock 6 → Literals.Block) (hord : ∀ b, (blk b).order = gramBlockDimension 6 b)
    (WT : ℕ → ℕ → TM) (bi : Fin 14)
    (hW : ∀ i j, EnclOk (mkCtx N S B W) (WT i j) (W0f cell blk hord (blockEquiv bi) i j)) (g : ℕ) (hg8 : g < 8)
    (r : Fin 100) :
    EnclOk (mkCtx N S B W) (blockTMgr (mkCtx N S B W) A WT bi g r) (gPiece s cell blk hord bi (D12G.gmap bi) 8 g r) := by
  unfold blockTMgr
  rw [eTabG_eq bi bi.isLt g hg8 r r.isLt, eTab_eq bi bi.isLt r r.isLt]
  unfold gPiece
  refine gTMz_sound hg hW (blockRowr_ok hg hA bi) (fun i j t ht => W0f_symm cell blk hord _ i j t ht) _ _ _ _ ?_
  intro e he
  have he' := (List.mem_filter.mp he).1
  rw [eList_eq bi r r.isLt] at he'
  rw [eSize_eq bi]
  exact symEntries_range _ _ e he'

#print axioms recTMr_sound
#print axioms blockTMgr_sound

end ThomsonCompact.CoeffMap
