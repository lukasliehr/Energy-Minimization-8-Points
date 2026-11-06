import ThomsonCompact.CoeffMap.Deg.StageZ
import ThomsonCompact.CoeffMap.Deg.ProgSound

/-!
# Soundness of the stored z columns (F2g)

* `zDec_eq`: if the stage-Z check `zOk1 … T` passes, the decoded stored entry **is** `refresh c T` (the decoder needs no
  semantics: the check compares the decoded value and error fields with `T`'s).
* `zStageOk_spec`: a stage-Z leaf gives `ZFacts` for its tile of dense rows `v` and rows `i`; tiles join
  (`ZFacts.join_v`, `ZFacts.join_i`) to the whole block (`ZFacts.full`).
* `PS_sound`: with the stage-Z facts of block `b`, the stage-P lookup `PS` encloses the real `P` table
  `pLF Wf rowF (rdim b)` (same real function as the single-stage `pLook_sound`), using only the real symmetry of
  the Gram entries (`pF_symm`).
-/

namespace ThomsonCompact.CoeffMap.Deg

open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite ThomsonCompact.Packed ThomsonCompact.CoeffMap
open scoped BigOperators

variable {N S B W : ℕ}

/-! ## Stored entries -/

theorem refresh_fields (c : Ctx) (T : TM) (v e : ℕ) (hv : T.v = v) (he : T.e = e) (hok : T.ok = true) :
    refresh c ⟨v, 0, 0, e, true⟩ = refresh c T := by
  obtain ⟨tv, ta, ts, te, tok⟩ := T
  simp only at hv he hok
  subst hv he hok
  rfl

theorem zOk1_fields (L : DegD) (c : Ctx) (zd : ZData) (b i v : ℕ) (T : TM) (h : L.zOk1 c zd b i v T = true) :
    T.ok = true ∧ T.v = decZV c (zd.zw b) (L.zRec c zd b i v) ∧
      T.e = decZE c (zd.zw b) (zd.ew b) (L.zRec c zd b i v) := by
  unfold DegD.zOk1 at h
  dsimp only at h
  simp only [Bool.and_eq_true, Nat.beq_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **A checked stored entry is the refreshed computed TM.** -/
theorem zDec_eq (L : DegD) (c : Ctx) (zd : ZData) (b i v : ℕ) (T : TM) (h : L.zOk1 c zd b i v T = true) :
    L.zDec c zd b i v = refresh c T := by
  obtain ⟨hok, hv, he⟩ := zOk1_fields L c zd b i v T h
  exact refresh_fields c T _ _ hv he hok

theorem zDec_encl (hg : Good N S B W) (L : DegD) (zd : ZData) (b i v : ℕ) {T : TM} {f : ℝ → ℝ}
    (hT : EnclOk (mkCtx N S B W) T f) (h : L.zOk1 (mkCtx N S B W) zd b i v T = true) :
    EnclOk (mkCtx N S B W) (L.zDec (mkCtx N S B W) zd b i v) f := by
  intro _
  rw [zDec_eq L _ zd b i v T h]
  exact refresh_sound hg (hT (zOk1_fields L _ zd b i v T h).1)

/-! ## Stage-Z leaves -/

/-- The stage-Z facts of the dense rows `v0 ≤ v < v1` and the rows `i0 ≤ i < i1` of block `b`. -/
def ZFacts (L : DegD) (c : Ctx) (A : TM) (WT : ℕ → ℕ → TM) (zd : ZData) (b v0 v1 i0 i1 : ℕ) : Prop :=
  ∀ v, v0 ≤ v → v < v1 → v < L.rdim b → pivotOf (L.blockRow c A b v) = none →
    ∀ i, i0 ≤ i → i < i1 → i < L.gdim b →
      L.zOk1 c zd b i v (zTMD c (L.blockRow c A b) (wRowsD WT (L.gdim b)) i v) = true

/-- **Stage-Z leaf spec.** -/
theorem zStageOk_spec (L : DegD) {c : Ctx} {A : TM} {WT : ℕ → ℕ → TM} {zd : ZData} {b v0 v1 i0 i1 : ℕ}
    (h : L.zStageOk c A WT zd b v0 v1 i0 i1 = true) : ZFacts L c A WT zd b v0 v1 i0 i1 := by
  intro v hv0 hv1 hvn hp i hi0 hi1 hin
  unfold DegD.zStageOk at h
  rw [List.all_eq_true] at h
  have h1 := h v (List.mem_range.mpr hvn)
  have hb1 : (Nat.ble v0 v && Nat.blt v v1) = true := by
    rw [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]; exact ⟨hv0, hv1⟩
  rw [hb1, hp] at h1
  dsimp only at h1
  simp only [Bool.not_true, Bool.false_or, List.all_eq_true, List.mem_range] at h1
  have h2 := h1 i hin
  have hb2 : (Nat.ble i0 i && Nat.blt i i1) = true := by
    rw [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq]; exact ⟨hi0, hi1⟩
  rw [hb2] at h2
  simpa using h2

theorem ZFacts.join_v {L : DegD} {c : Ctx} {A : TM} {WT : ℕ → ℕ → TM} {zd : ZData} {b v0 v1 v2 i0 i1 : ℕ}
    (h1 : ZFacts L c A WT zd b v0 v1 i0 i1) (h2 : ZFacts L c A WT zd b v1 v2 i0 i1) :
    ZFacts L c A WT zd b v0 v2 i0 i1 := by
  intro v hv0 hv2 hvn hp i hi0 hi1 hin
  by_cases hv : v < v1
  · exact h1 v hv0 hv hvn hp i hi0 hi1 hin
  · exact h2 v (by omega) hv2 hvn hp i hi0 hi1 hin

theorem ZFacts.join_i {L : DegD} {c : Ctx} {A : TM} {WT : ℕ → ℕ → TM} {zd : ZData} {b v0 v1 i0 i1 i2 : ℕ}
    (h1 : ZFacts L c A WT zd b v0 v1 i0 i1) (h2 : ZFacts L c A WT zd b v0 v1 i1 i2) :
    ZFacts L c A WT zd b v0 v1 i0 i2 := by
  intro v hv0 hv1 hvn hp i hi0 hi2 hin
  by_cases hi : i < i1
  · exact h1 v hv0 hv1 hvn hp i hi0 hi hin
  · exact h2 v hv0 hv1 hvn hp i (by omega) hi2 hin

theorem ZFacts.full {L : DegD} {c : Ctx} {A : TM} {WT : ℕ → ℕ → TM} {zd : ZData} {b v1 i1 : ℕ}
    (h : ZFacts L c A WT zd b 0 v1 0 i1) (hv : L.rdim b ≤ v1) (hi : L.gdim b ≤ i1) :
    ∀ v, v < L.rdim b → pivotOf (L.blockRow c A b v) = none → ∀ i, i < L.gdim b →
      L.zOk1 c zd b i v (zTMD c (L.blockRow c A b) (wRowsD WT (L.gdim b)) i v) = true :=
  fun v hvn hp i hin => h v (Nat.zero_le _) (by omega) hvn hp i (Nat.zero_le _) (by omega) hin

/-! ## The real `P` table is symmetric -/

theorem list_sum_comm {α β : Type*} (L : List α) (M : List β) (f : α → β → ℝ) :
    (L.map fun a => (M.map fun b => f a b).sum).sum = (M.map fun b => (L.map fun a => f a b).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    rw [List.sum_map_add]

theorem pF_symm {Wf : ℕ → ℕ → ℝ → ℝ} {rowF : ℕ → List (ℕ × (ℝ → ℝ))}
    (hWs : ∀ i j, ∀ t ∈ Set.Icc (-1 : ℝ) 1, Wf i j t = Wf j i t) (u v : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    pF Wf rowF u v t = pF Wf rowF v u t := by
  unfold pF zF
  simp_rw [← List.sum_map_mul_left]
  rw [list_sum_comm]
  congr 1
  apply List.map_congr_left
  intro q _
  congr 1
  apply List.map_congr_left
  intro q' _
  rw [hWs _ _ t ht]
  ring

theorem rowF_pivot {c : Ctx} {r : List (ℕ × Option TM)} {rf : List (ℕ × (ℝ → ℝ))} (hr : RowOk c r rf) {j : ℕ}
    (hp : pivotOf r = some j) : ∃ κ : ℝ → ℝ, rf = [(j, κ)] ∧ ∀ t ∈ Set.Icc (-1 : ℝ) 1, κ t = 1 := by
  rw [pivotOf_some hp] at hr
  rcases hr with _ | ⟨⟨hjq, hκ⟩, hnil⟩
  rename_i q rest
  cases hnil
  obtain ⟨q1, q2⟩ := q
  simp only at hjq
  subst hjq
  exact ⟨q2, rfl, hκ⟩

theorem zF_pivot {Wf : ℕ → ℕ → ℝ → ℝ} {rowF : ℕ → List (ℕ × (ℝ → ℝ))} {v j : ℕ} {κ : ℝ → ℝ}
    (hrf : rowF v = [(j, κ)]) (hκ : ∀ t ∈ Set.Icc (-1 : ℝ) 1, κ t = 1) (i : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) : zF Wf rowF i v t = Wf i j t := by
  unfold zF
  rw [hrf]
  simp [hκ t ht]

theorem pF_pivot {Wf : ℕ → ℕ → ℝ → ℝ} {rowF : ℕ → List (ℕ × (ℝ → ℝ))} {u i : ℕ} {κ : ℝ → ℝ}
    (hrf : rowF u = [(i, κ)]) (hκ : ∀ t ∈ Set.Icc (-1 : ℝ) 1, κ t = 1) (v : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) : pF Wf rowF u v t = zF Wf rowF i v t := by
  unfold pF
  rw [hrf]
  simp [hκ t ht]

/-! ## The stage-P lookup -/

section PS

variable (L : DegD) (hg : Good N S B W) {A : TM} {WT : ℕ → ℕ → TM} {Wf : ℕ → ℕ → ℝ → ℝ}
  {rowF : ℕ → List (ℕ × (ℝ → ℝ))} (zd : ZData) (b : ℕ)
  (hW : ∀ i j, EnclOk (mkCtx N S B W) (WT i j) (Wf i j))
  (hWs : ∀ i j, ∀ t ∈ Set.Icc (-1 : ℝ) 1, Wf i j t = Wf j i t)
  (hrow : ∀ u, RowOk (mkCtx N S B W) (L.blockRow (mkCtx N S B W) A b u) (rowF u))
  (hgood : ∀ u, u < L.rdim b → RowGood (L.gdim b) (L.blockRow (mkCtx N S B W) A b u))
  (hz : ∀ v, v < L.rdim b → pivotOf (L.blockRow (mkCtx N S B W) A b v) = none → ∀ i, i < L.gdim b →
    L.zOk1 (mkCtx N S B W) zd b i v
      (zTMD (mkCtx N S B W) (L.blockRow (mkCtx N S B W) A b) (wRowsD WT (L.gdim b)) i v) = true)
include hg hW hWs hrow hgood hz

theorem zDec_sound {i w : ℕ} (hi : i < L.gdim b) (hw : w < L.rdim b)
    (hp : pivotOf (L.blockRow (mkCtx N S B W) A b w) = none) :
    EnclOk (mkCtx N S B W) (L.zDec (mkCtx N S B W) zd b i w) (zF Wf rowF i w) :=
  zDec_encl hg L zd b i w (zTMD_sound hg hW hrow hgood hi hw) (hz w hw hp i hi)

/-- The tabled entry `pSB u v` encloses the real `P u v` (inside the block). -/
theorem pSB_sound {u v : ℕ} (huv : u < L.rdim b ∧ v < L.rdim b) :
    EnclOk (mkCtx N S B W) (L.pSB (mkCtx N S B W) A WT zd b u v) (pF Wf rowF u v) := by
  unfold DegD.pSB
  cases hpu : pivotOf (L.blockRow (mkCtx N S B W) A b u) with
  | none =>
    cases hpv : pivotOf (L.blockRow (mkCtx N S B W) A b v) with
    | none =>
      show EnclOk _ (dotOpt _ (zipRow (L.blockRow _ A b v) (mkList (fun i => L.zDec _ zd b i u) (L.gdim b)) 0)) _
      rw [zipRow_full (hgood v huv.2)]
      refine (dotRow_sound hg hW hrow hgood huv.2 (fun i => L.zDec _ zd b i u) (fun i => zF Wf rowF i u)
        (fun i hi => zDec_sound L hg zd b hW hWs hrow hgood hz hi huv.1 hpu)).congr (fun t ht => ?_)
      rw [pF_symm hWs u v t ht]
      rfl
    | some j =>
      show EnclOk _ (L.zDec _ zd b j u) _
      obtain ⟨κ, hrf, hκ⟩ := rowF_pivot (hrow v) hpv
      have hgv := hgood v huv.2
      rw [pivotOf_some hpv] at hgv
      have hj : j < L.gdim b := hgv.2 _ (List.mem_singleton_self _)
      refine (zDec_sound L hg zd b hW hWs hrow hgood hz hj huv.1 hpu).congr (fun t ht => ?_)
      unfold zF pF
      apply congrArg List.sum
      apply List.map_congr_left
      intro q _
      rw [show zF Wf rowF q.1 v t = Wf q.1 j t from zF_pivot hrf hκ q.1 t ht, hWs _ _ t ht]
  | some i =>
    obtain ⟨κu, hrfu, hκu⟩ := rowF_pivot (hrow u) hpu
    have hgu := hgood u huv.1
    rw [pivotOf_some hpu] at hgu
    have hi : i < L.gdim b := hgu.2 _ (List.mem_singleton_self _)
    cases hpv : pivotOf (L.blockRow (mkCtx N S B W) A b v) with
    | none =>
      show EnclOk _ (L.zDec _ zd b i v) _
      refine (zDec_sound L hg zd b hW hWs hrow hgood hz hi huv.2 hpv).congr (fun t ht => ?_)
      rw [pF_pivot hrfu hκu v t ht]
    | some j =>
      show EnclOk _ (WT j i) _
      obtain ⟨κv, hrfv, hκv⟩ := rowF_pivot (hrow v) hpv
      refine (hW j i).congr (fun t ht => ?_)
      rw [pF_pivot hrfu hκu v t ht, zF_pivot hrfv hκv i t ht, hWs _ _ t ht]

/-- **The stage-P lookup encloses the real `P` table** (given the stage-Z facts of the block). -/
theorem PS_sound (u v : ℕ) :
    EnclOk (mkCtx N S B W) (L.PS (mkCtx N S B W) A WT zd b u v) (pLF Wf rowF (L.rdim b) u v) := by
  unfold DegD.PS DegD.pTS
  by_cases huv : u < L.rdim b ∧ v < L.rdim b
  · rw [listAt_mkList _ _ huv.2, listAt_mkList _ _ huv.1]
    exact (pSB_sound L hg zd b hW hWs hrow hgood hz huv).congr (fun t _ => by unfold pLF; rw [if_pos huv])
  · have hz0 : listAt zeroTM (listAt [] (mkList (fun v => mkList (fun u => L.pSB (mkCtx N S B W) A WT zd b u v)
        (L.rdim b)) (L.rdim b)) v) u = zeroTM := by
      by_cases hv : v < L.rdim b
      · rw [listAt_mkList _ _ hv, listAt_mkList_ge _ _ (by omega)]
      · rw [listAt_mkList_ge _ _ (by omega)]; rfl
    rw [hz0]
    exact zero_enclOk.congr (fun t _ => by unfold pLF; rw [if_neg huv])

end PS

#print axioms zDec_eq
#print axioms zStageOk_spec
#print axioms PS_sound

end ThomsonCompact.CoeffMap.Deg
