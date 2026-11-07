import ThomsonCompact.CoeffMap.BSound
import ThomsonCompact.CoeffMap.ETab

/-!
# Soundness of the W0 block pieces on the grouped tables (F2c)

* `blockTMg_sound`: every piece TM `blockTMg c A WT bi g r` (grouped coefficient lists `EDataG`, tabled
  contraction, faster records) with `ok = true` encloses `gPiece … bi (D12G.gmap bi) 8 g r`; the 8 pieces of a
  block sum to its contribution `g12` (`gPiece_sum`).
* `blockOkg_spec`: a leaf `blockOkg c A WT bi g0 g1 = true` gives `ok = true` of its pieces.
* `denOk_sound`: `denOk c A = true` gives the per-cell denominator facts of `W0_link_pk`.
-/

namespace ThomsonCompact.CoeffMap

open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite ThomsonCompact.Packed
open ThomsonCompact.CoeffMap.D12
open scoped BigOperators

variable {N S B W : ℕ}

theorem blockOkg_spec {c : Ctx} {A : TM} {WT : ℕ → ℕ → TM} {bi g0 g1 : ℕ} (h : blockOkg c A WT bi g0 g1 = true) :
    ∀ g, g0 ≤ g → g < g1 → ∀ r, r < 100 → (blockTMg c A WT bi g r).ok = true := by
  induction g1 with
  | zero => intro g _ h1; exact absurd h1 (Nat.not_lt_zero _)
  | succ k ih =>
    intro g h0 h1 r hr
    have h' : cond (Nat.ble g0 k) (Nat.rec (motive := fun _ => Bool) true
        (fun r ih2 => (blockTMg c A WT bi k r).ok && ih2) 100 && blockOkg c A WT bi g0 k) (blockOkg c A WT bi g0 k) = true := h
    rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h2 | h2
    · apply ih _ g h0 h2 r hr
      cases hb : Nat.ble g0 k
      · rw [hb] at h'; exact h'
      · rw [hb, cond_true, Bool.and_eq_true] at h'; exact h'.2
    · subst h2
      rw [show Nat.ble g0 g = true from Nat.ble_eq.mpr h0, cond_true, Bool.and_eq_true] at h'
      have hr' := h'.1
      clear h' ih h1 h0 h
      revert hr'
      generalize 100 = m at hr ⊢
      induction m with
      | zero => exact absurd hr (Nat.not_lt_zero _)
      | succ m ihm =>
        intro hm
        have hm' : ((blockTMg c A WT bi g m).ok && Nat.rec (motive := fun _ => Bool) true
            (fun r ih2 => (blockTMg c A WT bi g r).ok && ih2) m) = true := hm
        rw [Bool.and_eq_true] at hm'
        rcases Nat.lt_succ_iff_lt_or_eq.mp hr with h3 | h3
        · exact ihm h3 hm'.2
        · rw [h3]; exact hm'.1

/-- **B soundness for one piece of the grouped tables.** -/
theorem blockTMg_sound (hg : Good N S B W) {A : TM} (s : ℝ → ℝ)
    (hA : Encl (mkCtx N S B W) A (fun t => aS (s t))) (cell : Literals.Cell)
    (blk : GramBlock 6 → Literals.Block) (hord : ∀ b, (blk b).order = gramBlockDimension 6 b)
    (WT : ℕ → ℕ → TM) (bi : Fin 14)
    (hW : ∀ i j, EnclOk (mkCtx N S B W) (WT i j) (W0f cell blk hord (blockEquiv bi) i j)) (g : ℕ) (hg8 : g < 8)
    (r : Fin 100) :
    EnclOk (mkCtx N S B W) (blockTMg (mkCtx N S B W) A WT bi g r) (gPiece s cell blk hord bi (D12G.gmap bi) 8 g r) := by
  unfold blockTMg
  rw [eTabG_eq bi bi.isLt g hg8 r r.isLt, eTab_eq bi bi.isLt r r.isLt]
  exact blockTMf_sound hg s hA cell blk hord WT bi hW (D12G.gmap bi) 8 g r

theorem invN_ok_D {c : Ctx} {k tol : ℕ} {D : TM} (h : (invN c k tol D).ok = true) : D.ok = true :=
  (mul_ok (recip_ok h).2).2

/-- **Per-cell denominator facts** (the hypothesis of `W0_link_pk`) from `denOk`. -/
theorem denOk_sound (hg : Good N S B W) {A : TM} {a : ℝ → ℝ} (hA : Encl (mkCtx N S B W) A a)
    (h : denOk (mkCtx N S B W) A = true) :
    ∀ d, d < D12RF.nDen → ∀ t ∈ Set.Icc (-1 : ℝ) 1, evalZ (D12RF.denPoly d) (a t) ≠ 0 := by
  intro d hd t ht hz
  unfold denOk at h
  rw [List.all_eq_true] at h
  have hok := h d (List.mem_range.mpr hd)
  have hD := hornerQ_sound hg hA (denQ d) (invN_ok_D hok)
  have hne := (invN_sound hg hD 8 0 hok).1 t ht
  apply hne
  show evalQ (denQ d) (a t) = 0
  rw [evalQ_denQ, hz, zero_div]

#print axioms blockTMg_sound
#print axioms denOk_sound

end ThomsonCompact.CoeffMap
