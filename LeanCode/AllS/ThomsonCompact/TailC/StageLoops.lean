import ThomsonCompact.TailC.StageBasic

/-!
# TailC: specifications of the stage's loops (workstream TC1)

`walk_spec`, `rowsGo_spec` (rows = sums of `e ⊙ pack(c q)`), `scatRow_spec`, `scatAll_spec` (exact digit
scatter, no bounds needed) and `decOut_spec`.
-/

namespace ThomsonCompact.TailC
open Finset

/-- The zero row. -/
abbrev z4 : R4 := (0, 0, 0, 0)

/-! ## Walk -/

theorem walk_nil (Q : R4) (es : List Ent) (pos : ℕ) : walk Q [] es pos = ([], es) := rfl

theorem walk_cons_nil (Q r : R4) (rs : List R4) (pos : ℕ) : walk Q (r :: rs) [] pos = (r :: rs, []) := rfl

theorem walk_cons_cons (Q r : R4) (rs : List R4) (e : Ent) (es : List Ent) (pos : ℕ) :
    walk Q (r :: rs) (e :: es) pos =
      Bool.rec (motive := fun _ => List R4 × List Ent)
        ((r :: (walk Q rs (e :: es) (Nat.add pos 1)).1), (walk Q rs (e :: es) (Nat.add pos 1)).2)
        ((addEnt e Q r :: (walk Q rs es (Nat.add pos 1)).1), (walk Q rs es (Nat.add pos 1)).2)
        (Nat.beq e.1 pos) := rfl

theorem walk_spec (Q : R4) : ∀ (rows : List R4) (es : List Ent) (pos : ℕ), (walk Q rows es pos).2 = [] →
    (walk Q rows es pos).1.length = rows.length ∧ (∀ e ∈ es, pos ≤ e.1 ∧ e.1 < pos + rows.length) ∧
    ∀ i < rows.length, rv ((walk Q rows es pos).1.getD i z4) =
      rv (rows.getD i z4) + (es.map fun e => if e.1 = pos + i then ev e * rv Q else 0).sum
  | [], es, pos, h => by
    rw [walk_nil] at h ⊢; subst h; simp
  | r :: rs, [], pos, _ => by
    rw [walk_cons_nil]; simp
  | r :: rs, e :: es, pos, h => by
    rw [walk_cons_cons, brec, nbeq, nadd] at h ⊢
    by_cases he : e.1 = pos
    · have hd : decide (e.1 = pos) = true := by simpa using he
      rw [if_pos hd] at h ⊢
      obtain ⟨h1, h2, h3⟩ := walk_spec Q rs es (pos + 1) h
      refine ⟨by simp [h1], ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · simp only [List.length_cons]; omega
        · have := h2 x hx; simp only [List.length_cons]; omega
      · intro i hi
        cases i with
        | zero =>
          have hz : (es.map fun x => if x.1 = pos then ev x * rv Q else 0).sum = 0 :=
            lsum_zero _ _ (fun x hx => by have := h2 x hx; rw [if_neg (by omega)])
          simp only [List.getD_cons_zero, List.map_cons, List.sum_cons, rv_addEnt, add_zero, hz, if_pos he]
        | succ j =>
          have hj : j < rs.length := by simp only [List.length_cons] at hi; omega
          have h3j := h3 j hj
          simp only [show pos + 1 + j = pos + (j + 1) by omega] at h3j
          simp only [List.getD_cons_succ, List.map_cons, List.sum_cons, h3j]
          rw [if_neg (by omega), zero_add]
    · have hd : ¬ decide (e.1 = pos) = true := by simpa using he
      rw [if_neg hd] at h ⊢
      obtain ⟨h1, h2, h3⟩ := walk_spec Q rs (e :: es) (pos + 1) h
      refine ⟨by simp [h1], ?_, ?_⟩
      · intro x hx
        have := h2 x hx; simp only [List.length_cons]; omega
      · intro i hi
        cases i with
        | zero =>
          have hz : ((e :: es).map fun x => if x.1 = pos then ev x * rv Q else 0).sum = 0 :=
            lsum_zero _ _ (fun x hx => by have := h2 x hx; rw [if_neg (by omega)])
          simp only [List.getD_cons_zero, add_zero, hz]
        | succ j =>
          have hj : j < rs.length := by simp only [List.length_cons] at hi; omega
          have h3j := h3 j hj
          simp only [show pos + 1 + j = pos + (j + 1) by omega] at h3j
          simp only [List.getD_cons_succ, h3j]

/-! ## Terms -/

theorem isNil_iff {α : Type} (l : List α) : isNil l = true ↔ l = [] := by
  cases l <;> simp [isNil]

theorem idxOk_iff (n : ℕ) : ∀ l : List Ent, idxOk n l = true ↔ ∀ f ∈ l, f.1 < n
  | [] => by simp [idxOk]
  | f :: fs => by
    show (Nat.blt f.1 n && idxOk n fs) = true ↔ _
    rw [Bool.and_eq_true, nblt, decide_eq_true_iff, idxOk_iff n fs]; simp

theorem rowsGo_cons (W n : ℕ) (t : Term) (ts : List Term) (rows : List R4) :
    rowsGo W n (t :: ts) rows =
      ((isNil (walk (packQ W t.2.2 t.2.1) rows t.1 0).2 && idxOk n t.2.1) &&
          (rowsGo W n ts (walk (packQ W t.2.2 t.2.1) rows t.1 0).1).1,
        (rowsGo W n ts (walk (packQ W t.2.2 t.2.1) rows t.1 0).1).2) := rfl

theorem rowsGo_spec (W n : ℕ) : ∀ (ts : List Term) (rows : List R4), (rowsGo W n ts rows).1 = true →
    (rowsGo W n ts rows).2.length = rows.length ∧
    (∀ t ∈ ts, (∀ e ∈ t.1, e.1 < rows.length) ∧ ∀ f ∈ t.2.1, f.1 < n) ∧
    ∀ i < rows.length, rv ((rowsGo W n ts rows).2.getD i z4) = rv (rows.getD i z4) +
      (ts.map fun t => (t.1.map fun e => if e.1 = i then ev e * rv (packQ W t.2.2 t.2.1) else 0).sum).sum
  | [], rows, _ => by
    refine ⟨rfl, by simp, fun i _ => ?_⟩
    show rv (rows.getD i z4) = _
    simp
  | t :: ts, rows, h => by
    rw [rowsGo_cons] at h ⊢
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨hnil, hidx⟩, hrest⟩ := h
    rw [isNil_iff] at hnil
    rw [idxOk_iff] at hidx
    obtain ⟨w1, w2, w3⟩ := walk_spec (packQ W t.2.2 t.2.1) rows t.1 0 hnil
    obtain ⟨g1, g2, g3⟩ := rowsGo_spec W n ts _ hrest
    rw [w1] at g1 g2 g3
    refine ⟨g1, ?_, fun i hi => ?_⟩
    · intro t' ht'
      rcases List.mem_cons.1 ht' with rfl | ht'
      · exact ⟨fun e he => by have := w2 e he; omega, hidx⟩
      · exact g2 t' ht'
    · rw [g3 i hi, w3 i hi, List.map_cons, List.sum_cons, zero_add, add_assoc]

/-! ## Scatter -/

/-- One scatter step (the body of `scatRow`). -/
noncomputable def scatStep (W W2 gw h Xu Xv g : ℕ) (C : R4) : R4 :=
  (Bool.rec (motive := fun _ => Nat)
      (Nat.add C.1 (Nat.shiftLeft (Nat.sub (Nat.land Xu (mask W)) h) (Nat.mul W2 (Nat.land g (mask gw)))))
      C.1 (Nat.blt (Nat.land Xu (mask W)) h),
   Bool.rec (motive := fun _ => Nat) C.2.1
      (Nat.add C.2.1 (Nat.shiftLeft (Nat.sub h (Nat.land Xu (mask W))) (Nat.mul W2 (Nat.land g (mask gw)))))
      (Nat.blt (Nat.land Xu (mask W)) h),
   Bool.rec (motive := fun _ => Nat)
      (Nat.add C.2.2.1 (Nat.shiftLeft (Nat.sub (Nat.land Xv (mask W)) h) (Nat.mul W2 (Nat.land g (mask gw)))))
      C.2.2.1 (Nat.blt (Nat.land Xv (mask W)) h),
   Bool.rec (motive := fun _ => Nat) C.2.2.2
      (Nat.add C.2.2.2 (Nat.shiftLeft (Nat.sub h (Nat.land Xv (mask W))) (Nat.mul W2 (Nat.land g (mask gw)))))
      (Nat.blt (Nat.land Xv (mask W)) h))

theorem scatRow_zero (W W2 gw h Xu Xv g : ℕ) (C : R4) : scatRow W W2 gw h 0 Xu Xv g C = C := rfl

theorem scatRow_succ (W W2 gw h k Xu Xv g : ℕ) (C : R4) :
    scatRow W W2 gw h (k + 1) Xu Xv g C =
      scatRow W W2 gw h k (Nat.shiftRight Xu W) (Nat.shiftRight Xv W) (Nat.shiftRight g gw)
        (scatStep W W2 gw h Xu Xv g C) := rfl

theorem signed_part (d h k : ℕ) (P N : ℕ) :
    ((if d < h then P else P + (d - h) * 2 ^ k : ℕ) : ℤ) - ((if d < h then N + (h - d) * 2 ^ k else N : ℕ) : ℤ) =
      (P : ℤ) - N + ((d : ℤ) - h) * 2 ^ k := by
  by_cases hd : d < h
  · rw [if_pos hd, if_pos hd]; push_cast [Nat.cast_sub hd.le]; ring
  · rw [if_neg hd, if_neg hd]; push_cast [Nat.cast_sub (not_lt.1 hd)]; ring

theorem rv_scatStep (W W2 gw h Xu Xv g : ℕ) (C : R4) :
    rv (scatStep W W2 gw h Xu Xv g C) =
      rv C + (⟨(Xu % 2 ^ W : ℕ) - (h : ℤ), (Xv % 2 ^ W : ℕ) - (h : ℤ)⟩ : ℤ√2) * 2 ^ (W2 * (g % 2 ^ gw)) := by
  obtain ⟨C1, C2, C3, C4⟩ := C
  ext
  · rw [Zsqrtd.re_add, re_mul_two_pow]
    simp only [scatStep, rv, brec, land_mask, nadd, nsub, nmul, nshl, nblt, decide_eq_true_iff]
    exact signed_part _ _ _ C1 C2
  · rw [Zsqrtd.im_add, im_mul_two_pow]
    simp only [scatStep, rv, brec, land_mask, nadd, nsub, nmul, nshl, nblt, decide_eq_true_iff]
    exact signed_part _ _ _ C3 C4

theorem dig_zero (W X : ℕ) : dig W X 0 = X % 2 ^ W := by simp [dig]

theorem dig_div (W X t : ℕ) : dig W (X / 2 ^ W) t = dig W X (t + 1) := by
  simp only [dig, Nat.div_div_eq_div_mul, ← pow_add, Nat.mul_succ, add_comm W]

theorem scatRow_spec (W W2 gw h : ℕ) : ∀ (k Xu Xv g : ℕ) (C : R4),
    rv (scatRow W W2 gw h k Xu Xv g C) = rv C +
      ∑ t ∈ range k, (⟨(dig W Xu t : ℤ) - h, (dig W Xv t : ℤ) - h⟩ : ℤ√2) * 2 ^ (W2 * dig gw g t)
  | 0, Xu, Xv, g, C => by rw [scatRow_zero]; simp
  | k + 1, Xu, Xv, g, C => by
    rw [scatRow_succ, scatRow_spec W W2 gw h k, rv_scatStep, Finset.sum_range_succ', add_assoc]
    congr 1
    rw [add_comm]
    congr 1
    · refine Finset.sum_congr rfl (fun t _ => ?_)
      simp only [nshr, dig_div]
    · simp only [dig_zero]

theorem scatAll_cons (W W2 gw h bs n : ℕ) (gam : ℕ → ℕ) (r : R4) (rs : List R4) (s : ℕ) (C : R4) :
    scatAll W W2 gw h bs n gam (r :: rs) s C =
      scatAll W W2 gw h bs n gam rs (Nat.add s 1)
        (scatRow W W2 gw h n (Nat.sub (Nat.add r.1 bs) r.2.1) (Nat.sub (Nat.add r.2.2.1 bs) r.2.2.2) (gam s) C) :=
  rfl

theorem scatAll_spec (W W2 gw h bs n : ℕ) (gam : ℕ → ℕ) : ∀ (rows : List R4) (s0 : ℕ) (C : R4),
    rv (scatAll W W2 gw h bs n gam rows s0 C) = rv C + ∑ i ∈ range rows.length, ∑ t ∈ range n,
      (⟨(dig W ((rows.getD i z4).1 + bs - (rows.getD i z4).2.1) t : ℤ) - h,
         (dig W ((rows.getD i z4).2.2.1 + bs - (rows.getD i z4).2.2.2) t : ℤ) - h⟩ : ℤ√2) *
        2 ^ (W2 * dig gw (gam (s0 + i)) t)
  | [], s0, C => by simp [scatAll]
  | r :: rs, s0, C => by
    rw [scatAll_cons, scatAll_spec W W2 gw h bs n gam rs, scatRow_spec, List.length_cons,
      Finset.sum_range_succ', add_assoc]
    congr 1
    rw [add_comm]
    simp only [nadd, nsub, List.getD_cons_succ, List.getD_cons_zero, add_zero]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [show s0 + 1 + i = s0 + (i + 1) by omega]

/-! ## Output decoding -/

theorem smv_smd (d h : ℕ) : smv (smd d h) = (d : ℤ) - h := by
  simp only [smd, smv, nblt, nadd, nsub, decide_eq_true_iff]
  by_cases hd : d < h
  · rw [if_pos hd, Nat.sub_eq_zero_of_le hd.le, zero_add, Nat.cast_sub hd.le]; ring
  · rw [if_neg hd, Nat.sub_eq_zero_of_le (not_lt.1 hd), add_zero, Nat.cast_sub (not_lt.1 hd)]

theorem decOut_succ (W2 h2 k γ Yu Yv : ℕ) :
    decOut W2 h2 (k + 1) γ Yu Yv =
      (γ, smd (Nat.land Yu (mask W2)) h2, smd (Nat.land Yv (mask W2)) h2) ::
        decOut W2 h2 k (Nat.add γ 1) (Nat.shiftRight Yu W2) (Nat.shiftRight Yv W2) := rfl

theorem decOut_spec (W2 h2 : ℕ) : ∀ (k γ Yu Yv : ℕ),
    (decOut W2 h2 k γ Yu Yv).map (fun e => (e.1, ev e)) =
      (List.range k).map (fun j => (γ + j, (⟨(dig W2 Yu j : ℤ) - h2, (dig W2 Yv j : ℤ) - h2⟩ : ℤ√2)))
  | 0, γ, Yu, Yv => rfl
  | k + 1, γ, Yu, Yv => by
    rw [decOut_succ, List.map_cons, decOut_spec W2 h2 k, List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1
    · rw [land_mask, land_mask]; simp [ev, smv_smd, dig_zero]
    · refine List.map_congr_left (fun j _ => ?_)
      simp only [Function.comp, nadd, nshr, dig_div]
      congr 1
      omega

end ThomsonCompact.TailC
