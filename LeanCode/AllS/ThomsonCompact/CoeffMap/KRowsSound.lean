import ThomsonCompact.CoeffMap.KRows
import ThomsonCompact.CoeffMap.Rep
import ThomsonCompact.CoeffMap.MomentSound
import ThomsonCompact.CoeffMap.ScalarColumns
import ThomsonCompact.CoeffMap.PackLemmas

/-!
# Soundness of the column-matrix rows (F2b c)

* `recTM_sound`: record TMs enclose the record values `(rec k).value (a t)`; `recTM_den`: their denominators do
  not vanish on the cell (the per-cell `DefinedAt` facts, via `scalarColumns_of_den`).
* `scalarRow_ok`, `scalarRow_rep`: the scalar rows are TM-valid and represent `Kpk`.
* `momentRow_ok`, `momentRow_rep`: the moment rows are TM-valid and represent `momentKernelMatrix`.
-/

namespace ThomsonCompact.CoeffMap

open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite ThomsonCompact.Packed
open scoped BigOperators

variable {N S B W : ℕ}

/-! ## Scalar records -/

theorem qOfIntI_eq : qOfIntI = qOfInt := rfl

theorem evalQ_numQ (k : ℕ) (y : ℝ) : evalQ (numQ k) y = evalZ (D12RF.rec k).num y / (D12RF.rec k).scaleN := by
  rw [numQ, qOfIntI_eq, evalQ_qOfInt]

theorem evalQ_denQ (d : ℕ) (y : ℝ) : evalQ (denQ d) y = evalZ (D12RF.denPoly d) y / D12RF.denScale d := by
  rw [denQ, qOfIntI_eq, evalQ_qOfInt]

theorem recTM_sound (hg : Good N S B W) {A : TM} {a : ℝ → ℝ} (hA : Encl (mkCtx N S B W) A a) (k : ℕ) :
    EnclOk (mkCtx N S B W) (recTM (mkCtx N S B W) A k) (fun t => (D12RF.rec k).value (a t)) := by
  intro hok
  obtain ⟨-, h⟩ := rfTM_sound hg hA 8 0 (numQ k) (denQ (D12RF.denIdx k)) hok
  refine h.congr (fun t _ => ?_)
  rw [evalQ_numQ, evalQ_denQ, RFRec.value, D12RF.rec_den, D12RF.rec_scaleD]

theorem recTM_den (hg : Good N S B W) {A : TM} {a : ℝ → ℝ} (hA : Encl (mkCtx N S B W) A a) (k : ℕ)
    (hok : (recTM (mkCtx N S B W) A k).ok = true) :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1, evalZ (D12RF.denPoly (D12RF.denIdx k)) (a t) ≠ 0 := by
  intro t ht hz
  obtain ⟨h, -⟩ := rfTM_sound hg hA 8 0 (numQ k) (denQ (D12RF.denIdx k)) hok
  exact h t ht (by rw [evalQ_denQ, hz, zero_div])

/-- Records `0` and `1` are the constants `1` and `0`. -/
theorem rec01 : (D12RF.rec 0).num = [1] ∧ (D12RF.rec 0).scaleN = 1 ∧ (D12RF.rec 0).den = [1] ∧
    (D12RF.rec 0).scaleD = 1 ∧ (D12RF.rec 1).num = [] := by decide +kernel

theorem rec0_value (y : ℝ) : (D12RF.rec 0).value y = 1 := by
  obtain ⟨h1, h2, h3, h4, -⟩ := rec01
  simp [RFRec.value, h1, h2, h3, h4, evalZ, horner]

theorem rec1_value (y : ℝ) : (D12RF.rec 1).value y = 0 := by
  simp [RFRec.value, rec01.2.2.2.2, evalZ]

/-! ## Scalar rows -/

/-- Real rows matching `scalarRow`. -/
noncomputable def scalarRowF (a : ℝ → ℝ) (bi d u : ℕ) : List (ℕ × (ℝ → ℝ)) :=
  ((List.range d).filter fun i => !(Nat.beq (D12RF.colRec bi i u) 1)).map fun i =>
    (i, fun t => (D12RF.rec (D12RF.colRec bi i u)).value (a t))

theorem scalarRow_ok (hg : Good N S B W) {A : TM} {a : ℝ → ℝ} (hA : Encl (mkCtx N S B W) A a) (bi d u : ℕ) :
    RowOk (mkCtx N S B W) (scalarRow (mkCtx N S B W) A bi d u) (scalarRowF a bi d u) := by
  unfold RowOk scalarRow scalarRowF
  refine forall₂_map_same _ (fun i _ => ⟨rfl, ?_⟩)
  by_cases h0 : D12RF.colRec bi i u = 0
  · have hb : Nat.beq (D12RF.colRec bi i u) 0 = true := by simp [h0]
    simp only [hb, if_true, EntryOk]
    intro t _
    rw [h0, rec0_value]
  · have hb : Nat.beq (D12RF.colRec bi i u) 0 = false :=
      Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
    simp only [hb, Bool.false_eq_true, if_false, EntryOk]
    exact recTM_sound hg hA _

theorem filter_range_sum (p : ℕ → Bool) (g : ℕ → ℝ) : ∀ d, (∀ i, i < d → p i = false → g i = 0) →
    (((List.range d).filter p).map g).sum = ∑ i ∈ Finset.range d, g i
  | 0, _ => by simp
  | d + 1, h => by
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append,
      filter_range_sum p g d (fun i hi => h i (by omega)), Finset.sum_range_succ]
    by_cases hp : p d
    · simp [hp]
    · simp [hp, h d (by omega) (by simpa using hp)]

theorem scalarRow_rep (a : ℝ → ℝ) (t : ℝ) (b : ScalarBlockName) (d : ℕ)
    (hd : scalarBlockDimension b 6 = d) (u : Fin (D12.rawSize b)) (F : ℕ → ℝ) :
    ((scalarRowF a (D12RF.bIdx b) d u).map fun q => q.2 t * F q.1).sum =
      ∑ i : Fin (scalarBlockDimension b 6), D12RF.Kpk (a t) b u i * F i := by
  unfold scalarRowF
  rw [List.map_map]
  have h := filter_range_sum (fun i => !(Nat.beq (D12RF.colRec (D12RF.bIdx b) i u) 1))
    (fun i => (D12RF.rec (D12RF.colRec (D12RF.bIdx b) i u)).value (a t) * F i) d (by
      intro i _ hp
      have h1 : D12RF.colRec (D12RF.bIdx b) i u = 1 := by simpa using hp
      simp [h1, rec1_value])
  refine h.trans ?_
  subst hd
  rw [← Fin.sum_univ_eq_sum_range]
  rfl

/-! ## Moment rows -/

/-- Real rows matching `momentRow`. -/
noncomputable def momentRowF (a : ℝ → ℝ) (k p d r : ℕ) : List (ℕ × (ℝ → ℝ)) :=
  if r = p then (List.range d).map fun i => (i, fun t => -(momentP k (sA p i) (a t) / momentP k p (a t)))
  else [(if r < p then r else r - 1, fun _ => 1)]

theorem hornerQ_ok_of_divN {c : Ctx} {k tol : ℕ} {F D : TM} (h : (divN c k tol F D).ok = true) :
    F.ok = true ∧ D.ok = true := by
  have h1 := mul_ok h
  have h2 := recip_ok h1.2
  exact ⟨h1.1, (mul_ok h2.2).2⟩

theorem momentRow_ok (hg : Good N S B W) {A : TM} {a : ℝ → ℝ} (hA : Encl (mkCtx N S B W) A a)
    (k p d r : ℕ) (hk : k < 6) (hpd : p ≤ d) (hd : d = 6 - k) :
    RowOk (mkCtx N S B W) (momentRow (mkCtx N S B W) A k p d r) (momentRowF a k p d r) := by
  unfold RowOk momentRow momentRowF
  by_cases hr : r = p
  · simp only [hr, if_true]
    refine forall₂_map_same _ (fun i hi => ⟨rfl, ?_⟩)
    have hi' : i < d := List.mem_range.mp hi
    intro hok
    simp only [rhoTM] at hok
    have hdiv : (divN (mkCtx N S B W) 8 0 (hornerQ (mkCtx N S B W) A (momQ k (sA p i)))
        (hornerQ (mkCtx N S B W) A (momQ k p))).ok = true := hok
    obtain ⟨hF, hD⟩ := hornerQ_ok_of_divN hdiv
    have e1 := hornerQ_sound hg hA (momQ k (sA p i)) hF
    have e2 := hornerQ_sound hg hA (momQ k p) hD
    obtain ⟨-, e3⟩ := divN_sound hg e1 e2 8 0 hdiv
    refine (neg_sound e3).congr (fun t _ => ?_)
    have hsa : sA p i < 7 - k := by unfold sA; split_ifs <;> omega
    simp only [momQ]
    rw [← momentP_D12 k (sA p i) hk hsa, ← momentP_D12 k p hk (by omega)]
  · simp only [hr, if_false]
    exact List.Forall₂.cons ⟨rfl, fun t _ => rfl⟩ List.Forall₂.nil

theorem val_succAbove {d : ℕ} (p : Fin (d + 1)) (i : Fin d) : (p.succAbove i).val = sA p.val i.val := by
  unfold Fin.succAbove sA
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (Fin.lt_def.mp h1) (by simpa using h2)
  · exact absurd (Fin.lt_def.mpr (by simpa using h2)) h1
  · rfl

theorem momentRow_rep (a : ℝ → ℝ) (t : ℝ) (k : Fin 6) (F : ℕ → ℝ) (r : Fin (6 - k.val + 1)) :
    ((momentRowF a k.val (D12.pivots k).val (6 - k.val) r).map fun q => q.2 t * F q.1).sum =
      ∑ i : Fin (6 - k.val), momentKernelMatrix (a t) 6 D12.pivots k r i * F i := by
  have hK : ∀ i : Fin (6 - k.val), momentKernelMatrix (a t) 6 D12.pivots k r i =
      (if r.val = sA (D12.pivots k).val i.val then 1 else 0) -
        (momentP k.val (sA (D12.pivots k).val i.val) (a t) / momentP k.val (D12.pivots k).val (a t)) *
          (if r.val = (D12.pivots k).val then 1 else 0) := by
    intro i
    rw [gram_map_family_and_map.2.2, ← val_succAbove]
    simp only [Fin.ext_iff]
  simp_rw [hK]
  set p := (D12.pivots k).val with hp
  have hpd : p ≤ 6 - k.val := Nat.lt_succ_iff.mp (D12.pivots k).isLt
  have hr := r.isLt
  rw [Fin.sum_univ_eq_sum_range (fun i => ((if r.val = sA p i then 1 else 0) -
    momentP k.val (sA p i) (a t) / momentP k.val p (a t) * (if r.val = p then 1 else 0)) * F i)]
  unfold momentRowF
  by_cases hrp : r.val = p
  · simp only [hrp, if_true, List.map_map]
    rw [list_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    have hne : p ≠ sA p i := by unfold sA; split_ifs <;> omega
    simp [hne]
  · simp only [hrp, if_false, mul_zero, sub_zero, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, one_mul]
    by_cases hlt : r.val < p
    · simp only [hlt, if_true]
      rw [Finset.sum_eq_single r.val]
      · have : r.val = sA p r.val := by unfold sA; simp [hlt]
        simp [← this]
      · intro i _ hne
        have : r.val ≠ sA p i := by unfold sA; split_ifs <;> omega
        simp [this]
      · intro h
        exact absurd (Finset.mem_range.mpr (by omega)) h
    · simp only [hlt, if_false]
      rw [Finset.sum_eq_single (r.val - 1)]
      · have : r.val = sA p (r.val - 1) := by unfold sA; split_ifs <;> omega
        simp [← this]
      · intro i _ hne
        have : r.val ≠ sA p i := by unfold sA; split_ifs <;> omega
        simp [this]
      · intro h
        exact absurd (Finset.mem_range.mpr (by omega)) h

#print axioms recTM_sound
#print axioms scalarRow_rep
#print axioms momentRow_ok
#print axioms momentRow_rep

/-! ## Faster records (F2c): `Nat`-only decode and the shared denominator table -/

theorem qOfIntI_unbias (M v : ℕ) : qOfIntI M (unbias v) = qOfSlot M v := by
  unfold qOfIntI unbias qOfSlot
  rw [Int.subNatNat_eq_coe]
  have h1 : decide ((v : ℤ) - ((33554432 : ℕ) : ℤ) < 0) = Nat.blt v 33554432 := by
    rw [Bool.eq_iff_iff, decide_eq_true_iff, Nat.blt_eq]
    omega
  have h2 : ((v : ℤ) - ((33554432 : ℕ) : ℤ)).natAbs = Nat.add (Nat.sub v 33554432) (Nat.sub 33554432 v) := by
    show _ = v - 33554432 + (33554432 - v)
    omega
  rw [h1, h2]

theorem rec_num (k : ℕ) : (D12RF.rec k).num = (numOfSlots (tableSlots D12RF.recChunk 26 18 34 k)).1 := rfl
theorem rec_scaleN (k : ℕ) : (D12RF.rec k).scaleN = (numOfSlots (tableSlots D12RF.recChunk 26 18 34 k)).2.1 := rfl

theorem numQN_eq (k : ℕ) : numQN k = numQ k := by
  unfold numQN numQ
  rw [rec_num, rec_scaleN]
  generalize tableSlots D12RF.recChunk 26 18 34 k = s
  rcases s with _ | ⟨lenN, _ | ⟨sc, _ | ⟨d, rest⟩⟩⟩
  · rfl
  · rfl
  · rfl
  · show (rest.take lenN).map (qOfSlot sc) = ((rest.take lenN).map unbias).map (qOfIntI sc)
    rw [List.map_map]
    apply List.map_congr_left
    intro v _
    exact (qOfIntI_unbias sc v).symm

/-- **The faster record TM is the record TM.** -/
theorem recTMz_eq (c : Ctx) (A : TM) (k : ℕ) : recTMz c A k = recTM c A k := by
  unfold recTMz recTM rfTM divN
  rw [numQN_eq]
  congr 1
  cases h : Nat.blt (D12RF.denIdx k) D12RF.nDen
  · rfl
  · rw [cond_true, denInvTab, listAt_mkList _ _ (Nat.blt_eq.mp h)]

theorem scalarRowz_eq (c : Ctx) (A : TM) (bi d u : ℕ) : scalarRowz c A bi d u = scalarRow c A bi d u := by
  unfold scalarRowz scalarRow
  simp only [recTMz_eq]

#print axioms recTMz_eq

end ThomsonCompact.CoeffMap
