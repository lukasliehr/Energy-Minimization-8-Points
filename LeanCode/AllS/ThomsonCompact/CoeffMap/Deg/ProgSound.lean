import ThomsonCompact.CoeffMap.Deg.Prog
import ThomsonCompact.CoeffMap.Contract
import ThomsonCompact.CoeffMap.Rep
import ThomsonCompact.CoeffMap.RFCore
import ThomsonCompact.CoeffMap.MomentSound
import ThomsonCompact.CoeffMap.Deg.BDotSound

/-!
# Soundness of the degree-generic W0 piece programs (F2f)

Structural TM soundness of `CoeffMap.Deg.Prog` for any per-degree data `L : DegD`, any per-cell `SumD` and any
real rows: the kernel programs are mirrored by real functions with the same lookups (`pLF`, `qSumF`, `qTabF`,
`qTabE`, `pieceF`), so that no semantic fact about the tables is needed here (those are in `CoeffMap.Deg.RepSound`).

* `pieceTM_sound`: Gram TMs enclosing `Wf` (symmetric on the cell) and rows matching real rows (`RowOk`) give
  `EnclOk (pieceTM …) (pieceF …)`.
* `leafOk_spec`: a leaf `leafOk … = true` gives `ok` and `ckOk` of each of its pieces.
* rows: `recTMr_sound` (residual-lemma RF records), `scalarRowr_ok`, `rhoTMd_sound`, `momentRowd_ok`, `blockRow_ok`
  (real rows `blockRowF`; the RF record `0` is the constant `1`, the moment pivot polynomials are rational).
* `denOkD_sound`: the per-cell check gives the owner partition and the nonvanishing of every shared denominator.
-/

namespace ThomsonCompact.CoeffMap.Deg

open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite ThomsonCompact.Packed ThomsonCompact.CoeffMap
open scoped BigOperators

variable {N S B W : ℕ}

/-! ## Real mirrors of the lookups -/

/-- The real `P` table: `pF` inside `[0, n)²`, zero outside (mirror of the `pT` lookup). -/
noncomputable def pLF (Wf : ℕ → ℕ → ℝ → ℝ) (rowF : ℕ → List (ℕ × (ℝ → ℝ))) (n u v : ℕ) (t : ℝ) : ℝ :=
  if u < n ∧ v < n then pF Wf rowF u v t else 0

/-- `Σ_{p ∈ ps} m(p) P p.1 p.2` (`m = 1` on the diagonal, `2` off it). -/
noncomputable def qSumF (P : ℕ → ℕ → ℝ) (ps : List (ℕ × ℕ)) : ℝ :=
  (ps.map fun p => (if p.1 = p.2 then (1 : ℝ) else 2) * P p.1 p.2).sum

namespace DegD

variable (L : DegD)

/-- Size of the chunked `Q` table of group `g` of block `b` (`16 (⌊len/16⌋ + 1)`). -/
def qLen (b g : ℕ) : ℕ := 16 * (Nat.add (Nat.shiftRight (Nat.sub (L.glo b (Nat.add g 1)) (L.glo b g)) 4) 1)

/-- Real `Q` table entry `i` of group `g` (mirror of `qAt`). -/
noncomputable def qTabF (sd : SumD) (P : ℕ → ℕ → ℝ) (b g lo hi i : ℕ) : ℝ :=
  if i < L.qLen b g then qSumF P (L.clsPart sd b (Nat.add (L.glo b g) i) lo hi) else 0

/-- Empty flag of `Q` table entry `i` (mirror of `qAt`). -/
def qTabE (sd : SumD) (b g lo hi i : ℕ) : Bool :=
  if i < L.qLen b g then (L.clsPart sd b (Nat.add (L.glo b g) i) lo hi).isEmpty else true

/-- The real piece function (mirror of `pieceTM`). -/
noncomputable def pieceF (sd : SumD) (P : ℕ → ℕ → ℝ) (b g lo hi : ℕ) (E : List (ℕ × Bool × ℕ)) : ℝ :=
  (E.map fun e => (if L.qTabE sd b g lo hi (Nat.sub e.1 (L.glo b g)) = true then 0 else
    qval (e.2.1, e.2.2, L.bden b)) * L.qTabF sd P b g lo hi (Nat.sub e.1 (L.glo b g))).sum

theorem qTabF_zero (sd : SumD) (P : ℕ → ℕ → ℝ) (b g lo hi i : ℕ) (h : L.qTabE sd b g lo hi i = true) :
    L.qTabF sd P b g lo hi i = 0 := by
  unfold DegD.qTabE at h
  unfold DegD.qTabF
  split_ifs at h ⊢ with hi
  · rw [List.isEmpty_iff.mp h]; simp [qSumF]
  · rfl

end DegD

theorem listAt_nil' {α : Type} (d : α) (i : ℕ) : listAt d [] i = d := rfl

theorem shr4_land15 (i : ℕ) : Nat.add (Nat.mul 16 (Nat.shiftRight i 4)) (Nat.land i 15) = i := by
  rw [show Nat.shiftRight i 4 = i / 16 from Nat.shiftRight_eq_div_pow i 4,
    show Nat.land i 15 = i % 16 from Nat.and_two_pow_sub_one_eq_mod i 4]
  exact Nat.div_add_mod i 16

theorem qAt_eq (L : DegD) (c : Ctx) (PT : ℕ → ℕ → TM) (sd : SumD) (b g lo hi i : ℕ) :
    L.qAt c PT sd b g lo hi i =
      if i < L.qLen b g then L.qEnt c PT sd b (Nat.add (L.glo b g) i) lo hi else (true, zeroTM) := by
  unfold DegD.qAt DegD.qTab DegD.qLen
  have hl : Nat.land i 15 < 16 := by
    rw [show Nat.land i 15 = i % 16 from Nat.and_two_pow_sub_one_eq_mod i 4]; exact Nat.mod_lt _ (by norm_num)
  have h16 := shr4_land15 i
  have h16' : 16 * Nat.shiftRight i 4 + Nat.land i 15 = i := h16
  by_cases hi : Nat.shiftRight i 4 < Nat.add (Nat.shiftRight (Nat.sub (L.glo b (Nat.add g 1)) (L.glo b g)) 4) 1
  · rw [listAt_mkList _ _ hi, listAt_mkList _ _ hl, if_pos (by
      have h2 : Nat.shiftRight i 4 + 1 ≤ Nat.shiftRight (Nat.sub (L.glo b (Nat.add g 1)) (L.glo b g)) 4 + 1 := hi
      show i < 16 * (Nat.shiftRight (Nat.sub (L.glo b (Nat.add g 1)) (L.glo b g)) 4 + 1)
      have h3 : Nat.land i 15 < 16 := hl
      omega), h16]
  · rw [listAt_mkList_ge _ _ (Nat.le_of_not_lt hi), if_neg (by
      have h2 : ¬ Nat.shiftRight i 4 + 1 ≤ Nat.shiftRight (Nat.sub (L.glo b (Nat.add g 1)) (L.glo b g)) 4 + 1 :=
        fun h => hi h
      show ¬ i < 16 * (Nat.shiftRight (Nat.sub (L.glo b (Nat.add g 1)) (L.glo b g)) 4 + 1)
      omega)]
    rfl

/-! ## Row walks -/

theorem drop_headD {α : Type} (d : α) : ∀ (L : List α) (n : ℕ), (L.drop n).headD d = L.getD n d
  | [], n => by cases n <;> rfl
  | a :: L, 0 => rfl
  | a :: L, n + 1 => by rw [List.drop_succ_cons, drop_headD d L n, List.getD_cons_succ]

theorem zipRow_spec : ∀ (row : List (ℕ × Option TM)) (full : List TM) (k : ℕ), (∀ p ∈ row, k ≤ p.1) →
    (row.map Prod.fst).Pairwise (· < ·) →
    zipRow row (full.drop k) k = row.map fun p => (p.2, full.getD p.1 zeroTM)
  | [], _, _, _, _ => rfl
  | p :: ps, full, k, hk, hs => by
    have hp : k ≤ p.1 := hk p (List.mem_cons_self ..)
    rw [List.map_cons, List.pairwise_cons] at hs
    show (fun ws' => (p.2, ws'.headD zeroTM) :: zipRow ps ws'.tail (Nat.add p.1 1)) ((full.drop k).drop (Nat.sub p.1 k)) = _
    rw [List.drop_drop, show k + Nat.sub p.1 k = p.1 by show k + (p.1 - k) = p.1; omega]
    dsimp only
    rw [drop_headD, List.tail_drop, zipRow_spec ps full (p.1 + 1) (fun q hq => by
      have := hs.1 q.1 (List.mem_map_of_mem hq); omega) hs.2, List.map_cons]

/-- Row indices strictly increasing and below `n`. -/
def RowGood (n : ℕ) (row : List (ℕ × Option TM)) : Prop :=
  (row.map Prod.fst).Pairwise (· < ·) ∧ ∀ p ∈ row, p.1 < n

theorem zipRow_full {n : ℕ} {row : List (ℕ × Option TM)} (h : RowGood n row) (f : ℕ → TM) :
    zipRow row (mkList f n) 0 = row.map fun p => (p.2, f p.1) := by
  rw [show mkList f n = (mkList f n).drop 0 from rfl, zipRow_spec row _ 0 (fun _ _ => Nat.zero_le _) h.1]
  apply List.map_congr_left
  intro p hp
  rw [← listAt_eq, listAt_mkList _ _ (h.2 p hp)]

theorem pT_lookup (L : DegD) (c : Ctx) (A : TM) (WT : ℕ → ℕ → TM) (b u v : ℕ) :
    listAt zeroTM (listAt [] (L.pT c A WT b) u) v =
      if u < L.rdim b ∧ v < L.rdim b then
        pTMD c (L.blockRow c A b) (zColsD c (L.blockRow c A b) (wRowsD WT (L.gdim b)) (L.gdim b) (L.rdim b)) u v
      else zeroTM := by
  unfold DegD.pT pTabD
  by_cases hu : u < L.rdim b
  · rw [listAt_mkList _ _ hu]
    by_cases hv : v < L.rdim b
    · rw [listAt_mkList _ _ hv, if_pos ⟨hu, hv⟩]
    · rw [listAt_mkList_ge _ _ (Nat.le_of_not_lt hv), if_neg (fun h => hv h.2)]
  · rw [listAt_mkList_ge _ _ (Nat.le_of_not_lt hu), if_neg (fun h => hu h.1)]
    rfl

theorem forall₂_and_mem {α β : Type*} {P : α → β → Prop} {Q : α → Prop} : ∀ {L : List α} {M : List β},
    List.Forall₂ P L M → (∀ a ∈ L, Q a) → List.Forall₂ (fun a b => P a b ∧ Q a) L M
  | [], [], List.Forall₂.nil, _ => List.Forall₂.nil
  | a :: _, _ :: _, List.Forall₂.cons h hL, hq =>
    List.Forall₂.cons ⟨h, hq a (List.mem_cons_self ..)⟩ (forall₂_and_mem hL (fun x hx => hq x (List.mem_cons_of_mem _ hx)))

theorem bdot_ok_of {c : Ctx} {as : List TM} {Bs : List (List TM)} {n i : ℕ} (hi : i < n)
    (h : (listAt zeroTM (bdot c as Bs n) i).ok = true) : bdotOk c as Bs = true := by
  unfold bdot at h
  rw [listAt_mkList _ _ hi] at h
  have e : (dotFin c (slotAt (bsp c) (bdotAcc (bsp c) as Bs).1 i, slotAt (bsp c) (bdotAcc (bsp c) as Bs).2.1 i,
      slotAt (bsp c) (bdotAcc (bsp c) as Bs).2.2.1 i, slotAt (bsp c) (bdotAcc (bsp c) as Bs).2.2.2 i,
      bdotOk c as Bs)).ok = (bdotOk c as Bs && _ && _) := rfl
  rw [e] at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1

theorem list_eq_mkList (d : TM) (Lt : List TM) : Lt = mkList (fun i => listAt d Lt i) Lt.length := by
  rw [mkList_eq]
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, listAt_eq]
    rw [List.getD_eq_getElem _ _ h1]

section Contract

variable (hg : Good N S B W) {WT : ℕ → ℕ → TM} {Wf : ℕ → ℕ → ℝ → ℝ}
  {row : ℕ → List (ℕ × Option TM)} {rowF : ℕ → List (ℕ × (ℝ → ℝ))} {n m : ℕ}
  (hW : ∀ i j, EnclOk (mkCtx N S B W) (WT i j) (Wf i j))
  (hrow : ∀ u, RowOk (mkCtx N S B W) (row u) (rowF u))
  (hgood : ∀ u, u < m → RowGood n (row u))
include hg hW hrow hgood

theorem dotRow_sound {v : ℕ} (hv : v < m) (X : ℕ → TM) (Xf : ℕ → ℝ → ℝ)
    (hX : ∀ j, j < n → EnclOk (mkCtx N S B W) (X j) (Xf j)) :
    EnclOk (mkCtx N S B W) (dotOpt (mkCtx N S B W) ((row v).map fun p => (p.2, X p.1)))
      (fun t => ((rowF v).map fun q => q.2 t * Xf q.1 t).sum) := by
  unfold dotOpt
  rw [List.map_map]
  have hF := forall₂_and_mem (hrow v) (hgood v hv).2
  have h := dotTM_sound hg (forall₂_map (R := fun a b => EnclOk (mkCtx N S B W) a.1 b.1 ∧ EnclOk (mkCtx N S B W) a.2 b.2)
    (f := fun p => (entTM (mkCtx N S B W) p.2, X p.1)) (g := fun q => (q.2, Xf q.1))
    (fun p q hpq => by
      refine ⟨entTM_sound hg hpq.1.2, ?_⟩
      show EnclOk _ (X p.1) (Xf q.1)
      rw [hpq.1.1]
      exact hX q.1 (hpq.1.1 ▸ hpq.2)) hF)
  exact h.congr (fun t _ => by simp [List.map_map, Function.comp_def])

theorem zTMD_sound {i v : ℕ} (hi : i < n) (hv : v < m) :
    EnclOk (mkCtx N S B W) (zTMD (mkCtx N S B W) row (wRowsD WT n) i v) (zF Wf rowF i v) := by
  unfold zTMD
  have hwr : listAt [] (wRowsD WT n) i = mkList (fun j => WT i j) n := listAt_mkList _ _ hi
  cases hp : pivotOf (row v) with
  | none =>
    show EnclOk _ (dotOpt _ (zipRow (row v) (listAt [] (wRowsD WT n) i) 0)) _
    rw [hwr, zipRow_full (hgood v hv)]
    exact (dotRow_sound hg hW hrow hgood hv (fun j => WT i j) (fun j => Wf i j) (fun j _ => hW i j)).congr
      (fun t _ => rfl)
  | some j =>
    show EnclOk _ (listAt zeroTM (listAt [] (wRowsD WT n) i) j) _
    have hr := hrow v
    have hgv := hgood v hv
    rw [pivotOf_some hp] at hr hgv
    have hj : j < n := hgv.2 _ (List.mem_singleton_self _)
    rw [hwr, listAt_mkList _ _ hj]
    generalize hrf : rowF v = rf at hr
    rcases hr with _ | ⟨⟨hjq, hκ⟩, hnil⟩
    rename_i q rest
    cases hnil
    refine (hW i j).congr (fun t ht => ?_)
    unfold zF
    rw [hrf]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [hκ t ht, one_mul]
    simp only at hjq
    rw [hjq]

theorem zcol_len (hWsym : ∀ i j, WT i j = WT j i) {v : ℕ} (hv : v < m) :
    (listAt [] (zColsD (mkCtx N S B W) row (wRowsD WT n) n m) v).length = n := by
  unfold zColsD
  rw [listAt_mkList _ _ hv]
  unfold zColD
  cases hp : pivotOf (row v) with
  | none =>
    show (mkList (fun i => zTMD _ row (wRowsD WT n) i v) n).length = n
    rw [mkList_eq, List.length_map, List.length_range]
  | some j =>
    show (listAt [] (wRowsD WT n) j).length = n
    have hgv := hgood v hv
    rw [pivotOf_some hp] at hgv
    have hj : j < n := hgv.2 _ (List.mem_singleton_self _)
    unfold wRowsD
    rw [listAt_mkList _ _ hj, mkList_eq, List.length_map, List.length_range]

theorem zc_sound (hWsym : ∀ i j, WT i j = WT j i) {i v : ℕ} (hi : i < n) (hv : v < m) :
    EnclOk (mkCtx N S B W) (listAt zeroTM (listAt [] (zColsD (mkCtx N S B W) row (wRowsD WT n) n m) v) i)
      (zF Wf rowF i v) := by
  unfold zColsD
  rw [listAt_mkList _ _ hv]
  unfold zColD
  have hwr : ∀ j, j < n → listAt [] (wRowsD WT n) j = mkList (fun i => WT j i) n := fun j hj => listAt_mkList _ _ hj
  cases hp : pivotOf (row v) with
  | none =>
    show EnclOk _ (listAt zeroTM (mkList (fun i => zTMD _ row (wRowsD WT n) i v) n) i) _
    rw [listAt_mkList _ _ hi]
    exact zTMD_sound hg hW hrow hgood hi hv
  | some j =>
    show EnclOk _ (listAt zeroTM (listAt [] (wRowsD WT n) j) i) _
    have hr := hrow v
    have hgv := hgood v hv
    rw [pivotOf_some hp] at hr hgv
    have hj : j < n := hgv.2 _ (List.mem_singleton_self _)
    rw [hwr j hj, listAt_mkList _ _ hi, hWsym]
    generalize hrf : rowF v = rf at hr
    rcases hr with _ | ⟨⟨hjq, hκ⟩, hnil⟩
    rename_i q rest
    cases hnil
    refine (hW i j).congr (fun t ht => ?_)
    unfold zF
    rw [hrf]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [hκ t ht, one_mul]
    simp only at hjq
    rw [hjq]

theorem pTMD_sound (hWsym : ∀ i j, WT i j = WT j i) (hWs : ∀ i j, ∀ t ∈ Set.Icc (-1 : ℝ) 1, Wf i j t = Wf j i t)
    {u v : ℕ} (hu : u < m) (hv : v < m) :
    EnclOk (mkCtx N S B W) (pTMD (mkCtx N S B W) row (zColsD (mkCtx N S B W) row (wRowsD WT n) n m) u v)
      (pF Wf rowF u v) := by
  unfold pTMD
  cases hp : pivotOf (row v) with
  | none =>
    cases hq : pivotOf (row u) with
    | none =>
      show EnclOk _ (dotOpt _ (zipRow (row u) (listAt [] (zColsD (mkCtx N S B W) row (wRowsD WT n) n m) v) 0)) _
      rw [list_eq_mkList zeroTM (listAt [] (zColsD (mkCtx N S B W) row (wRowsD WT n) n m) v),
        zcol_len hg hW hrow hgood hWsym hv, zipRow_full (hgood u hu)]
      exact (dotRow_sound hg hW hrow hgood hu _ (fun i => zF Wf rowF i v)
        (fun i hi => zc_sound hg hW hrow hgood hWsym hi hv)).congr (fun t _ => rfl)
    | some i =>
      show EnclOk _ (listAt zeroTM (listAt [] (zColsD (mkCtx N S B W) row (wRowsD WT n) n m) v) i) _
      have hr := hrow u
      have hgu := hgood u hu
      rw [pivotOf_some hq] at hr hgu
      have hi : i < n := hgu.2 _ (List.mem_singleton_self _)
      generalize hrf : rowF u = rf at hr
      rcases hr with _ | ⟨⟨hiq, hκ⟩, hnil⟩
      rename_i q rest
      cases hnil
      refine (zc_sound hg hW hrow hgood hWsym hi hv).congr (fun t ht => ?_)
      unfold pF
      rw [hrf]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [hκ t ht, one_mul]
      simp only at hiq
      rw [hiq]
  | some j =>
    show EnclOk _ (listAt zeroTM (listAt [] (zColsD (mkCtx N S B W) row (wRowsD WT n) n m) u) j) _
    have hr := hrow v
    have hgv := hgood v hv
    rw [pivotOf_some hp] at hr hgv
    have hj : j < n := hgv.2 _ (List.mem_singleton_self _)
    generalize hrf : rowF v = rf at hr
    rcases hr with _ | ⟨⟨hjq, hκ⟩, hnil⟩
    rename_i q rest
    cases hnil
    refine (zc_sound hg hW hrow hgood hWsym hj hu).congr (fun t ht => ?_)
    have hz : ∀ i, zF Wf rowF i v t = Wf i j t := by
      intro i
      unfold zF
      rw [hrf]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [hκ t ht, one_mul]
      simp only at hjq
      rw [hjq]
    unfold zF pF
    apply congrArg List.sum
    apply List.map_congr_left
    intro q _
    rw [hz, hWs _ _ t ht]

end Contract

theorem qTab_lookup (L : DegD) (c : Ctx) (PT : ℕ → ℕ → TM) (sd : SumD) (b g lo hi i : ℕ) :
    L.qAt c PT sd b g lo hi i =
      if i < L.qLen b g then L.qEnt c PT sd b (Nat.add (L.glo b g) i) lo hi else (true, zeroTM) :=
  qAt_eq L c PT sd b g lo hi i

/-! ## The piece program -/

section Piece

variable (L : DegD) (hg : Good N S B W) {A : TM} {WT : ℕ → ℕ → TM} {Wf : ℕ → ℕ → ℝ → ℝ}
  {rowF : ℕ → List (ℕ × (ℝ → ℝ))} (b : ℕ)
  (hW : ∀ i j, EnclOk (mkCtx N S B W) (WT i j) (Wf i j))
  (hrow : ∀ u, RowOk (mkCtx N S B W) (L.blockRow (mkCtx N S B W) A b u) (rowF u))
  (hgood : ∀ u, u < L.rdim b → RowGood (L.gdim b) (L.blockRow (mkCtx N S B W) A b u))
  (hWsym : ∀ i j, WT i j = WT j i)
  (hWs : ∀ i j, ∀ t ∈ Set.Icc (-1 : ℝ) 1, Wf i j t = Wf j i t)
include hg hW hrow hgood hWsym hWs

theorem pT_sound (u v : ℕ) :
    EnclOk (mkCtx N S B W) (listAt zeroTM (listAt [] (L.pT (mkCtx N S B W) A WT b) u) v)
      (pLF Wf rowF (L.rdim b) u v) := by
  rw [pT_lookup]
  by_cases h : u < L.rdim b ∧ v < L.rdim b
  · rw [if_pos h]
    exact (pTMD_sound hg hW hrow hgood hWsym hWs h.1 h.2).congr (fun t _ => by unfold pLF; rw [if_pos h])
  · rw [if_neg h]
    exact zero_enclOk.congr (fun t _ => by unfold pLF; rw [if_neg h])

/-- The computed `P` lookup encloses the real `P` table. -/
theorem pLook_sound (u v : ℕ) :
    EnclOk (mkCtx N S B W) (L.pLook (mkCtx N S B W) A WT b u v) (pLF Wf rowF (L.rdim b) u v) :=
  pT_sound L hg b hW hrow hgood hWsym hWs u v

end Piece

/-! ## The piece programs for any `P` lookup -/

section PieceP

variable (L : DegD) (hg : Good N S B W) {PT : ℕ → ℕ → TM} {Pf : ℕ → ℕ → ℝ → ℝ} (b : ℕ)
  (hP : ∀ u v, EnclOk (mkCtx N S B W) (PT u v) (Pf u v))
include hg hP

theorem qSum_sound (ps : List (ℕ × ℕ)) :
    EnclOk (mkCtx N S B W) (DegD.qSum (mkCtx N S B W) PT ps) (fun t => qSumF (fun u v => Pf u v t) ps) := by
  unfold DegD.qSum
  have h := dotTM_sound hg (forall₂_map_same (R := fun x y => EnclOk (mkCtx N S B W) x.1 y.1 ∧
      EnclOk (mkCtx N S B W) x.2 y.2)
    (f := fun p => (constI (mkCtx N S B W) (cond (Nat.beq p.1 p.2) 1 2),
      PT p.1 p.2))
    (g := fun p => ((fun _ => ((cond (Nat.beq p.1 p.2) 1 2 : ℕ) : ℝ)), Pf p.1 p.2)) ps
    (fun p _ => ⟨constI_sound hg _, hP p.1 p.2⟩))
  refine h.congr (fun t _ => ?_)
  unfold qSumF
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  show ((cond (Nat.beq p.1 p.2) 1 2 : ℕ) : ℝ) * Pf p.1 p.2 t = _
  by_cases hp : p.1 = p.2
  · rw [show Nat.beq p.1 p.2 = true by rw [hp]; exact Nat.beq_refl _, if_pos hp]; simp
  · rw [show Nat.beq p.1 p.2 = false from Bool.eq_false_iff.mpr (fun h' => hp (Nat.eq_of_beq_eq_true h')),
      if_neg hp]; simp

/-- **The piece program encloses the real piece function** (any `P` lookup enclosing a real `P` table). -/
theorem pieceTM_sound (sd : SumD) (g lo hi : ℕ) (E : List (ℕ × Bool × ℕ)) :
    EnclOk (mkCtx N S B W) (L.pieceTM (mkCtx N S B W) PT sd b g lo hi E)
      (fun t => L.pieceF sd (fun u v => Pf u v t) b g lo hi E) := by
  unfold DegD.pieceTM
  have h := dotTM_sound hg (forall₂_map_same (R := fun x y => EnclOk (mkCtx N S B W) x.1 y.1 ∧
      EnclOk (mkCtx N S B W) x.2 y.2)
    (f := fun e => (fun q => (cond q.1 zeroTM (constQ (mkCtx N S B W) e.2.1 e.2.2 (L.bden b)), q.2))
      (L.qAt (mkCtx N S B W) PT sd b g lo hi (Nat.sub e.1 (L.glo b g))))
    (g := fun e => ((fun _ => if L.qTabE sd b g lo hi (Nat.sub e.1 (L.glo b g)) = true then 0 else
      qval (e.2.1, e.2.2, L.bden b)),
      fun t => L.qTabF sd (fun u v => Pf u v t) b g lo hi (Nat.sub e.1 (L.glo b g)))) E
    (fun e _ => by
      dsimp only
      rw [qTab_lookup]
      unfold DegD.qTabE DegD.qTabF
      by_cases hi' : Nat.sub e.1 (L.glo b g) < L.qLen b g
      · simp only [if_pos hi']
        unfold DegD.qEnt
        dsimp only
        refine ⟨?_, qSum_sound hg hP _⟩
        cases (L.clsPart sd b (Nat.add (L.glo b g) (Nat.sub e.1 (L.glo b g))) lo hi).isEmpty
        · exact (constQ_sound hg _ _ _).congr (fun t _ => by simp)
        · exact zero_enclOk.congr (fun t _ => by simp)
      · simp only [if_neg hi']
        exact ⟨zero_enclOk.congr (fun t _ => by simp), zero_enclOk⟩))
  exact h.congr (fun t _ => by simp [DegD.pieceF, List.map_map, Function.comp_def])

end PieceP

#print axioms pieceTM_sound

/-! ## Leaves -/

theorem walkP_specD {α : Type} (p : ℕ → α → Bool) (r0 r1 : ℕ) (d : α) : ∀ (L : List α) (s : ℕ),
    walkP p r0 r1 L s = true → ∀ i, i < L.length → r0 ≤ s + i → s + i < r1 → p (s + i) (L.getD i d) = true
  | [], _, _, i, hi, _, _ => absurd hi (Nat.not_lt_zero _)
  | x :: L, s, h, i, hi, h0, h1 => by
    have h' : cond (Nat.blt s r1) (cond (Nat.ble r0 s) (p s x && walkP p r0 r1 L (s + 1))
        (walkP p r0 r1 L (s + 1))) true = true := h
    rw [show Nat.blt s r1 = true from Nat.blt_eq.mpr (by omega), cond_true] at h'
    cases i with
    | zero =>
      rw [show Nat.ble r0 s = true from Nat.ble_eq.mpr (by omega), cond_true, Bool.and_eq_true] at h'
      simpa using h'.1
    | succ j =>
      have hrest : walkP p r0 r1 L (s + 1) = true := by
        cases hb : Nat.ble r0 s
        · rw [hb, cond_false] at h'; exact h'
        · rw [hb, cond_true, Bool.and_eq_true] at h'; exact h'.2
      have := walkP_specD p r0 r1 d L (s + 1) hrest j (by simp at hi; omega) (by omega) (by omega)
      rw [show s + (j + 1) = s + 1 + j by omega]
      simpa using this

theorem splitL_length {α : Type} : ∀ (lens : List ℕ) (M : List α), (splitL lens M).length = lens.length
  | [], _ => rfl
  | _ :: lens, M => by
    show (splitL lens _).length + 1 = lens.length + 1
    rw [splitL_length lens]

theorem eTab_length (L : DegD) (pb : ℕ) : (L.eTab pb).length = L.nc := by
  unfold DegD.eTab
  rw [splitL_length, mkList_eq, List.length_map, List.length_range]

/-- **Leaf spec**: every piece of a passing leaf is `ok` and matches its checkpoint. -/
theorem leafOk_spec (L : DegD) {c : Ctx} {PT : ℕ → ℕ → TM} {sd : SumD} {n b g0 g1 h r0 r1 : ℕ}
    (hl : L.leafOk c PT sd n b g0 g1 h r0 r1 = true) :
    ∀ g, g0 ≤ g → g < g1 → ∀ r, r0 ≤ r → r < r1 → r < L.nc →
      (L.pieceTM c PT sd b g (sd.plo b h) (sd.plo b (h + 1)) ((L.eTab (32 * b + g)).getD r [])).ok = true ∧
      ckOk c sd.F n (L.pieceTM c PT sd b g (sd.plo b h) (sd.plo b (h + 1)) ((L.eTab (32 * b + g)).getD r []))
        (ckRecD sd n b g h r) = true := by
  induction g1 with
  | zero => intro g _ h1; exact absurd h1 (Nat.not_lt_zero _)
  | succ k ih =>
    intro g h0 h1 r hr0 hr1 hr
    have h' : cond (Nat.ble g0 k) (walkP (L.pieceOk c PT sd b k (sd.plo b h) (sd.plo b (Nat.add h 1))
        (fun r => ckRecD sd n b k h r) sd.F n) r0 r1 (L.eTab (Nat.add (Nat.mul 32 b) k)) 0 &&
          L.leafOk c PT sd n b g0 k h r0 r1) (L.leafOk c PT sd n b g0 k h r0 r1) = true := hl
    rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h2 | h2
    · apply ih _ g h0 h2 r hr0 hr1 hr
      cases hb : Nat.ble g0 k
      · rw [hb] at h'; exact h'
      · rw [hb, cond_true, Bool.and_eq_true] at h'; exact h'.2
    · subst h2
      rw [show Nat.ble g0 g = true from Nat.ble_eq.mpr h0, cond_true, Bool.and_eq_true] at h'
      have hw := walkP_specD _ r0 r1 [] _ 0 h'.1 r (by rw [eTab_length]; exact hr) (by omega) (by omega)
      rw [Nat.zero_add] at hw
      unfold DegD.pieceOk at hw
      simpa only [Bool.and_eq_true, Nat.add_eq, Nat.mul_eq] using hw

#print axioms leafOk_spec

/-! ## Rows -/

theorem qSlotW_eq (w M v : ℕ) : qSlotW w M v = qOfInt M (unbiasW w v) := by
  unfold qSlotW qOfInt unbiasW
  generalize Nat.shiftLeft 1 (Nat.sub w 1) = H
  rw [Int.subNatNat_eq_coe]
  have h1 : decide ((v : ℤ) - (H : ℤ) < 0) = Nat.blt v H := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.blt_eq]
    omega
  have h2 : ((v : ℤ) - (H : ℤ)).natAbs = Nat.add (Nat.sub v H) (Nat.sub H v) := by
    show _ = v - H + (H - v)
    omega
  rw [h1, h2]

namespace DegD

variable (L : DegD)

theorem numQ_eq (k : ℕ) : L.numQ k = (L.numZ k).map (qOfInt (L.numS k)) := by
  unfold DegD.numQ DegD.numZ DegD.numS
  dsimp only
  rw [List.map_map]
  apply List.map_congr_left
  intro v _
  exact qSlotW_eq _ _ _

theorem denQ_eq (d : ℕ) : L.denQ d = (L.denZ d).map (qOfInt (L.denS d)) := by
  unfold DegD.denQ DegD.denZ DegD.denS
  dsimp only
  rw [List.map_map]
  apply List.map_congr_left
  intro v _
  exact qSlotW_eq _ _ _

theorem evalQ_numQ (k : ℕ) (y : ℝ) : evalQ (L.numQ k) y = evalZ (L.numZ k) y / L.numS k := by
  rw [numQ_eq, evalQ_qOfInt]

theorem evalQ_denQ (d : ℕ) (y : ℝ) : evalQ (L.denQ d) y = evalZ (L.denZ d) y / L.denS d := by
  rw [denQ_eq, evalQ_qOfInt]

theorem denGAt_eq (c : Ctx) (A : TM) (d : ℕ) : L.denGAt c A d = hornerQ c A (L.denQ d) := by
  unfold DegD.denGAt
  by_cases hd : d < L.nDen
  · rw [show Nat.blt d L.nDen = true from Nat.blt_eq.mpr hd, cond_true]
    unfold DegD.denGTab
    exact listAt_mkList _ _ hd
  · rw [show Nat.blt d L.nDen = false from Bool.eq_false_iff.mpr (fun h => hd (Nat.blt_eq.mp h)), cond_false]

theorem denInvAt_eq (c : Ctx) (A : TM) (d : ℕ) : L.denInvAt c A d = invN c 8 0 (hornerQ c A (L.denQ d)) := by
  unfold DegD.denInvAt
  by_cases hd : d < L.nDen
  · rw [show Nat.blt d L.nDen = true from Nat.blt_eq.mpr hd, cond_true]
    unfold DegD.denInvTab
    exact listAt_mkList _ _ hd
  · rw [show Nat.blt d L.nDen = false from Bool.eq_false_iff.mpr (fun h => hd (Nat.blt_eq.mp h)), cond_false]

/-- Real rows of scalar block `j` (mirror of `scalarRowr`). -/
noncomputable def scalarRowF (a : ℝ → ℝ) (j u : ℕ) : List (ℕ × (ℝ → ℝ)) :=
  ((List.range (L.gdim (Nat.add L.dH j))).filter fun i => !(Nat.beq (L.colRec j i u) 1)).map fun i =>
    (i, fun t => (L.rfRec (L.colRec j i u)).value (a t))

/-- Real rows of block `b` (mirror of `blockRow`). -/
noncomputable def blockRowF (a : ℝ → ℝ) (b : ℕ) : ℕ → List (ℕ × (ℝ → ℝ)) :=
  if b < L.dH then fun r => if r = L.piv b then
      (List.range (L.gdim b)).map fun i => (i, fun t => -(momentP b (sAb (L.piv b) i) (a t) / momentP b (L.piv b) (a t)))
    else [(if r < L.piv b then r else r - 1, fun _ => 1)]
  else L.scalarRowF a (b - L.dH)

end DegD

theorem divR_ok_inputsD {c : Ctx} {F G Rc : TM} (h : (divR c F G Rc).ok = true) :
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

theorem invN_ok_DD {c : Ctx} {k tol : ℕ} {D : TM} (h : (invN c k tol D).ok = true) : D.ok = true :=
  (mul_ok (recip_ok h).2).2

/-- **Precise records** enclose the RF record values. -/
theorem recTMr_sound (L : DegD) (hg : Good N S B W) {A : TM} {a : ℝ → ℝ} (hA : Encl (mkCtx N S B W) A a) (k : ℕ) :
    EnclOk (mkCtx N S B W) (L.recTMr (mkCtx N S B W) A k) (fun t => (L.rfRec k).value (a t)) := by
  intro hok
  unfold DegD.recTMr at hok ⊢
  rw [L.denInvAt_eq, L.denGAt_eq] at hok ⊢
  have h0 : (divR (mkCtx N S B W) (polyD (mkCtx N S B W) A (L.numQ k))
      (hornerQ (mkCtx N S B W) A (L.denQ (L.denIdx k)))
      (invN (mkCtx N S B W) 8 0 (hornerQ (mkCtx N S B W) A (L.denQ (L.denIdx k))))).ok = true := hok
  obtain ⟨hFo, hGo, hRo⟩ := divR_ok_inputsD h0
  have hF := polyD_sound hg hA (L.numQ k) hFo
  have hG := hornerQ_sound hg hA (L.denQ (L.denIdx k)) hGo
  obtain ⟨hg0, hR⟩ := invN_sound hg hG 8 0 hRo
  have h := refresh_sound hg (divR_sound hg hF hG hR hg0 h0)
  refine h.congr (fun t _ => ?_)
  rw [L.evalQ_numQ, L.evalQ_denQ]
  rfl

theorem scalarRowr_ok (L : DegD) (hg : Good N S B W) {A : TM} {a : ℝ → ℝ} (hA : Encl (mkCtx N S B W) A a)
    (h0 : ∀ y, (L.rfRec 0).value y = 1) (j u : ℕ) :
    RowOk (mkCtx N S B W) (L.scalarRowr (mkCtx N S B W) A j u) (L.scalarRowF a j u) := by
  unfold RowOk DegD.scalarRowr DegD.scalarRowF
  refine forall₂_map_same _ (fun i _ => ⟨rfl, ?_⟩)
  by_cases hc : L.colRec j i u = 0
  · have hb : Nat.beq (L.colRec j i u) 0 = true := by rw [hc]; rfl
    simp only [hb, if_true, EntryOk]
    intro t _
    rw [hc, h0]
  · have hb : Nat.beq (L.colRec j i u) 0 = false :=
      Bool.eq_false_iff.mpr (fun h => hc (Nat.eq_of_beq_eq_true h))
    simp only [hb, Bool.false_eq_true, if_false, EntryOk]
    exact recTMr_sound L hg hA _

/-- `momentP` is the rational mirror polynomial when its `√2` part vanishes. -/
theorem momentP_rat (k j : ℕ) (hz : qAllZero (mP k j).s = true) (y : ℝ) :
    momentP k j y = evalQ (momQd k j) y := by
  rw [momentP_eq, ev2, evq_allZero _ y hz, mul_zero, add_zero, momQd, evalQ_toQL]

/-- **Precise pivot ratios** enclose the moment pivot ratios. -/
theorem rhoTMd_sound (hg : Good N S B W) {A : TM} {a : ℝ → ℝ} (hA : Encl (mkCtx N S B W) A a) (k p i : ℕ)
    (hz1 : qAllZero (mP k (sAb p i)).s = true) (hz2 : qAllZero (mP k p).s = true) :
    EnclOk (mkCtx N S B W) (rhoTMd (mkCtx N S B W) A k p i)
      (fun t => -(momentP k (sAb p i) (a t) / momentP k p (a t))) := by
  intro hok
  have h0 : (divR (mkCtx N S B W) (hornerQ (mkCtx N S B W) A (momQd k (sAb p i)))
      (hornerQ (mkCtx N S B W) A (momQd k p)) (invN (mkCtx N S B W) 8 0 (hornerQ (mkCtx N S B W) A (momQd k p)))).ok =
      true := hok
  obtain ⟨hFo, hGo, hRo⟩ := divR_ok_inputsD h0
  have hF := hornerQ_sound hg hA (momQd k (sAb p i)) hFo
  have hG := hornerQ_sound hg hA (momQd k p) hGo
  obtain ⟨hg0, hR⟩ := invN_sound hg hG 8 0 hRo
  have h := refresh_sound hg (neg_sound (divR_sound hg hF hG hR hg0 h0))
  refine h.congr (fun t _ => ?_)
  rw [momentP_rat k _ hz1, momentP_rat k _ hz2]

theorem sAb_le (p i d : ℕ) (hp : p ≤ d) (hi : i < d) : sAb p i ≤ d := by
  unfold sAb; split_ifs <;> omega

theorem blockRow_ok (L : DegD) (hg : Good N S B W) {A : TM} {a : ℝ → ℝ} (hA : Encl (mkCtx N S B W) A a)
    (h0 : ∀ y, (L.rfRec 0).value y = 1) (b : ℕ)
    (hmom : b < L.dH → L.piv b ≤ L.gdim b ∧ ∀ j, j ≤ L.gdim b → qAllZero (mP b j).s = true) (u : ℕ) :
    RowOk (mkCtx N S B W) (L.blockRow (mkCtx N S B W) A b u) (L.blockRowF a b u) := by
  unfold DegD.blockRow DegD.blockRowF
  by_cases hb : b < L.dH
  · rw [if_pos hb, if_pos hb]
    obtain ⟨hp, hz⟩ := hmom hb
    unfold momentRowd
    by_cases hr : u = L.piv b
    · rw [if_pos hr, if_pos hr]
      refine forall₂_map_same _ (fun i hi => ⟨rfl, ?_⟩)
      have hi' : i < L.gdim b := List.mem_range.mp hi
      exact rhoTMd_sound hg hA b (L.piv b) i (hz _ (sAb_le _ _ _ hp hi')) (hz _ hp)
    · rw [if_neg hr, if_neg hr]
      exact List.Forall₂.cons ⟨rfl, fun t _ => rfl⟩ List.Forall₂.nil
  · rw [if_neg hb, if_neg hb]
    exact scalarRowr_ok L hg hA h0 _ u

#print axioms blockRow_ok

theorem blockRow_good (L : DegD) (c : Ctx) (A : TM) (b : ℕ)
    (hmom : b < L.dH → L.piv b ≤ L.gdim b ∧ L.rdim b = L.gdim b + 1) (u : ℕ) (hu : u < L.rdim b) :
    RowGood (L.gdim b) (L.blockRow c A b u) := by
  unfold DegD.blockRow RowGood
  by_cases hb : b < L.dH
  · rw [if_pos hb]
    obtain ⟨hp, hr⟩ := hmom hb
    unfold momentRowd
    by_cases hup : u = L.piv b
    · rw [if_pos hup]
      refine ⟨?_, ?_⟩
      · rw [List.map_map]
        simpa [Function.comp_def] using List.pairwise_lt_range (n := L.gdim b)
      · intro p hp'
        simp only [List.mem_map, List.mem_range] at hp'
        obtain ⟨i, hi, rfl⟩ := hp'
        exact hi
    · rw [if_neg hup]
      refine ⟨List.pairwise_singleton _ _, ?_⟩
      intro p hp'
      rw [List.mem_singleton] at hp'
      subst hp'
      show (if u < L.piv b then u else u - 1) < L.gdim b
      split_ifs <;> omega
  · rw [if_neg hb]
    unfold DegD.scalarRowr
    have hjb : Nat.add L.dH (b - L.dH) = b := by show L.dH + (b - L.dH) = b; omega
    refine ⟨?_, ?_⟩
    · rw [List.map_map]
      have h1 := (List.pairwise_lt_range (n := L.gdim (Nat.add L.dH (b - L.dH)))).filter
        (fun i => !(Nat.beq (L.colRec (b - L.dH) i u) 1))
      simpa [Function.comp_def] using h1
    · intro p hp'
      simp only [List.mem_map, List.mem_filter, List.mem_range] at hp'
      obtain ⟨i, ⟨hi, _⟩, rfl⟩ := hp'
      rw [hjb] at hi
      exact hi


/-! ## The per-cell check -/

theorem partsOk_spec (L : DegD) (sd : SumD) (h : L.partsOk sd = true) :
    ∀ b, b < Nat.add L.dH 8 → sd.plo b 0 = 0 ∧ 512 ≤ sd.plo b (sd.np b) ∧
      ∀ i, i < sd.np b → sd.plo b i ≤ sd.plo b (i + 1) := by
  intro b hb
  unfold DegD.partsOk at h
  rw [List.all_eq_true] at h
  have h1 := h b (List.mem_range.mpr hb)
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, List.all_eq_true, List.mem_range] at h1
  exact ⟨h1.1.1, h1.1.2, fun i hi => h1.2 i hi⟩

/-- **Per-cell denominator facts** and the owner partition from `denOkD`. -/
theorem denOkD_sound (L : DegD) (hg : Good N S B W) {A : TM} {a : ℝ → ℝ} (hA : Encl (mkCtx N S B W) A a)
    (sd : SumD) (h : L.denOkD (mkCtx N S B W) A sd = true) :
    L.partsOk sd = true ∧ ∀ d, d < L.nDen → ∀ t ∈ Set.Icc (-1 : ℝ) 1, evalZ (L.denZ d) (a t) ≠ 0 := by
  unfold DegD.denOkD at h
  rw [Bool.and_eq_true] at h
  refine ⟨h.1, fun d hd t ht hz => ?_⟩
  have h2 := h.2
  rw [List.all_eq_true] at h2
  have hok := h2 d (List.mem_range.mpr hd)
  have hD := hornerQ_sound hg hA (L.denQ d) (invN_ok_DD hok)
  have hne := (invN_sound hg hD 8 0 hok).1 t ht
  apply hne
  show evalQ (L.denQ d) (a t) = 0
  rw [L.evalQ_denQ, hz, zero_div]

#print axioms denOkD_sound

end ThomsonCompact.CoeffMap.Deg
