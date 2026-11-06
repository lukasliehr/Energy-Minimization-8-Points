import ThomsonCompact.Floor.B.SoundRow

/-!
# Row leaf: the contraction values (F3b)

For a row `r` and channel vectors `zl`, `pval r zl k ch = Σ_idx ê_{idx,k} z_{m_idx,ch}` is the exact contraction;
the kernel's biased contraction results decode to it (`pb_contract`), with the magnitude bound `pval_abs`, and
`Σ_k pval_k u^k = Σ_idx z_idx evalZ(ê_idx)(u)` (`pval_eval`).
-/

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Packed
open ThomsonCompact.Floor (mask slot)
open scoped BigOperators

theorem getD_of_lt {α : Type*} (l : List α) (d : α) {i : ℕ} (h : i < l.length) : l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem getD_of_ge {α : Type*} (l : List α) (d : α) {i : ℕ} (h : l.length ≤ i) : l.getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr h, Option.getD_none]

theorem list_sum_range' {M : Type*} [AddCommMonoid M] (f : ℕ → M) : ∀ n,
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, list_sum_range' f n, Finset.sum_range_succ]; simp

theorem list_sum_range (f : ℕ → ℤ) : ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => by simp
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, list_sum_range f n, Finset.sum_range_succ]; simp

theorem list_sum_rangeR (f : ℕ → ℝ) : ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => by simp
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, list_sum_rangeR f n, Finset.sum_range_succ]; simp

/-- exact contraction value of channel `ch` at power `k` -/
def pval (r : RowT) (zl : ℕ → List ℤ) (k ch : ℕ) : ℤ :=
  ∑ idx ∈ Finset.range r.nms, r.ehat idx k * (zl (r.mAt idx)).getD ch 0

/-- the contraction at power `k` as a packed integer vector of `n` channels -/
def pvec (r : RowT) (zl : ℕ → List ℤ) (n k : ℕ) : List ℤ := (List.range n).map (pval r zl k)

theorem zipWith_slotsL {α : Type*} (w : ℕ) (f : ℕ → ℕ → α) : ∀ (cvs : List ℕ) (t : ℕ),
    List.zipWith f (slotsL w cvs.length t) cvs = (List.range cvs.length).map fun i => f (slot w t i) (cvs.getD i 0)
  | [], t => by simp [slotsL]
  | cv :: cvs, t => by
    rw [show List.zipWith f (slotsL w (cv :: cvs).length t) (cv :: cvs) =
      f (t &&& mask w) cv :: List.zipWith f (slotsL w cvs.length (t >>> w)) cvs from rfl]
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map]
    refine congrArg₂ List.cons ?_ ?_
    · show f (t &&& mask w) cv = f ((t >>> (w * 0)) &&& mask w) cv
      rw [Nat.mul_zero, Nat.shiftRight_zero]
    · rw [zipWith_slotsL w f cvs (t >>> w)]
      apply List.map_congr_left
      intro i _
      simp only [Function.comp_apply, List.getD_cons_succ]
      congr 1
      show ((t >>> w) >>> (w * i)) &&& mask w = (t >>> (w * (i + 1))) &&& mask w
      rw [← Nat.shiftRight_add, show w + w * i = w * (i + 1) by ring]

theorem horner_eq_of_getD (X : ℤ) : ∀ (l1 l2 : List ℤ), (∀ k, l1.getD k 0 = l2.getD k 0) → horner X l1 = horner X l2
  | [], [], _ => rfl
  | [], y :: ys, h => by
    have h0 := h 0
    simp at h0
    have := horner_eq_of_getD X [] ys (fun k => by have := h (k + 1); simpa using this)
    simp [← h0, ← this]
  | x :: xs, [], h => by
    have h0 := h 0
    simp at h0
    have := horner_eq_of_getD X xs [] (fun k => by have := h (k + 1); simpa using this)
    simp [h0, this]
  | x :: xs, y :: ys, h => by
    have h0 := h 0
    simp at h0
    have := horner_eq_of_getD X xs ys (fun k => by have := h (k + 1); simpa using this)
    simp [h0, this]

/-- the row's channel vectors are those of its entries -/
theorem cvs_getD (cvA : List ℕ) (r : RowT) (hlen : r.msL.length = r.nms) (idx : ℕ) (hidx : idx < r.nms) :
    (r.msL.map fun m => cvA.getD m 0).getD idx 0 = cvA.getD (r.mAt idx) 0 := by
  unfold RowT.mAt
  rw [getD_of_lt _ _ (by simp [hlen, hidx]), List.getElem_map, getD_of_lt r.msL 0 (by rw [hlen]; exact hidx)]

/-- **the contraction modulo `2^KC`** -/
theorem contract_mod (cb : CellB) {nI : ℕ} (cvA : List ℕ) (zl : ℕ → List ℤ) (hch : ChanSem nI cb cvA zl) (r : RowT)
    (hlen : r.msL.length = r.nms) (hms : ∀ m ∈ r.msL, m < nI) (hw : 1 ≤ r.w) (k : ℕ) :
    (contractK r.w cb.KC (r.msL.map fun m => cvA.getD m 0) (lsum (r.msL.map fun m => cvA.getD m 0))
      (r.t.getD k 0) : ℤ) % 2 ^ cb.KC = horner (2 ^ cb.WC : ℤ) (pvec r zl cb.nC k) % 2 ^ cb.KC := by
  set cvs := r.msL.map fun m => cvA.getD m 0 with hcvs
  have hcl : cvs.length = r.nms := by rw [hcvs, List.length_map, hlen]
  rw [contractK_mod r.w cb.KC hw cvs (r.t.getD k 0), zipWith_slotsL, hcl]
  -- Σ_idx ê_idx cv_idx ≡ horner (lcomb [(ê_idx, zl m_idx)])
  have hL := lcomb_mod (M := 2 ^ cb.KC) (W := cb.WC)
    ((List.range r.nms).map fun idx => (r.ehat idx k, cvA.getD (r.mAt idx) 0, zl (r.mAt idx)))
    (by
      intro x hx
      obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp hx
      have hm : r.mAt idx < nI := by
        unfold RowT.mAt
        rw [getD_of_lt _ _ (by rw [hlen]; exact List.mem_range.mp hidx)]
        exact hms _ (List.getElem_mem _)
      exact hch.mod _ (by have := hch.cvl; omega))
  have e1 : ((List.range r.nms).map fun i => ((slot r.w (r.t.getD k 0) i : ℤ) - 2 ^ (r.w - 1)) *
      ((cvs.getD i 0 : ℕ) : ℤ)).sum =
      (((List.range r.nms).map fun idx => (r.ehat idx k, cvA.getD (r.mAt idx) 0, zl (r.mAt idx))).map
        fun x => x.1 * (x.2.1 : ℤ)).sum := by
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro idx hidx
    simp only [Function.comp_apply, RowT.ehat]
    rw [hcvs, cvs_getD cvA r hlen idx (List.mem_range.mp hidx)]
  rw [e1, hL]
  congr 1
  apply horner_eq_of_getD
  intro ch
  rw [lcomb_getD, List.map_map, List.map_map]
  unfold pvec
  by_cases hch' : ch < cb.nC
  · rw [getD_of_lt _ _ (by simp [hch']), List.getElem_map, List.getElem_range]
    unfold pval
    rw [← list_sum_range]
    congr 1
  · rw [getD_of_ge _ _ (by simp; omega)]
    rw [show ((List.range r.nms).map _) = (List.range r.nms).map (fun _ => (0 : ℤ)) from ?_]
    · simp
    · apply List.map_congr_left
      intro idx _
      simp only [Function.comp_apply]
      rw [getD_of_ge _ _ (by rw [hch.len]; omega), mul_zero]

/-! ## Magnitudes, decoding, evaluation -/

theorem lsum_eq_sum : ∀ l : List ℕ, lsum l = l.sum
  | [] => rfl
  | x :: l => by show x + lsum l = _; rw [lsum_eq_sum l, List.sum_cons]

theorem ehat_abs (r : RowT) (hw : 1 ≤ r.w) (idx k : ℕ) : |r.ehat idx k| ≤ 2 ^ (r.w - 1) := by
  unfold RowT.ehat
  have h1 : slot r.w (r.t.getD k 0) idx < 2 ^ r.w := by
    rw [slot_eq]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have h2 : ((slot r.w (r.t.getD k 0) idx : ℕ) : ℤ) < 2 ^ r.w := by exact_mod_cast h1
  have h3 : (2 : ℤ) ^ r.w = 2 * 2 ^ (r.w - 1) := by
    conv_lhs => rw [show r.w = (r.w - 1) + 1 by omega]
    exact pow_succ' 2 (r.w - 1)
  have h0 : (0 : ℤ) ≤ ((slot r.w (r.t.getD k 0) idx : ℕ) : ℤ) := Int.natCast_nonneg _
  rw [abs_le]; constructor <;> linarith

theorem zl_abs (cb : CellB) {nI : ℕ} (cvA : List ℕ) (zl : ℕ → List ℤ) (hch : ChanSem nI cb cvA zl) (m ch : ℕ) :
    |(zl m).getD ch 0| ≤ (cb.cmax : ℤ) := by
  by_cases h : ch < (zl m).length
  · rw [getD_of_lt _ _ h]; exact hch.bnd m _ (List.getElem_mem h)
  · rw [getD_of_ge _ _ (by omega)]; simp

/-- the contraction values are bounded by `nms 2^(w-1) cmax` -/
theorem pval_abs (cb : CellB) {nI : ℕ} (cvA : List ℕ) (zl : ℕ → List ℤ) (hch : ChanSem nI cb cvA zl) (r : RowT)
    (hw : 1 ≤ r.w) (k ch : ℕ) : |pval r zl k ch| ≤ r.nms * 2 ^ (r.w - 1) * cb.cmax := by
  unfold pval
  calc |∑ idx ∈ Finset.range r.nms, r.ehat idx k * (zl (r.mAt idx)).getD ch 0|
      ≤ ∑ idx ∈ Finset.range r.nms, |r.ehat idx k * (zl (r.mAt idx)).getD ch 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _idx ∈ Finset.range r.nms, (2 ^ (r.w - 1) * (cb.cmax : ℤ)) := by
        apply Finset.sum_le_sum; intro idx _
        rw [abs_mul]
        exact mul_le_mul (ehat_abs r hw idx k) (zl_abs cb cvA zl hch _ ch) (abs_nonneg _) (by positivity)
    _ = r.nms * 2 ^ (r.w - 1) * cb.cmax := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- the biased contraction result is the digit list of the biased contraction values -/
theorem pb_contract (cb : CellB) {nI : ℕ} (cvA : List ℕ) (zl : ℕ → List ℤ) (hch : ChanSem nI cb cvA zl) (r : RowT)
    (hlen : r.msL.length = r.nms) (hms : ∀ m ∈ r.msL, m < nI) (hw : 1 ≤ r.w) (hWC : 1 ≤ cb.WC) (k : ℕ)
    (hb : r.nms * 2 ^ (r.w - 1) * cb.cmax < 2 ^ (cb.WC - 1)) :
    Nat.land (Nat.add (contractK r.w cb.KC (r.msL.map fun m => cvA.getD m 0)
        (lsum (r.msL.map fun m => cvA.getD m 0)) (r.t.getD k 0)) (pvBias cb.WC cb.nC)) (mask cb.KC) =
      Nat.ofDigits (2 ^ cb.WC) ((pvec r zl cb.nC k).map fun x => (x + 2 ^ (cb.WC - 1)).toNat) := by
  have hz : ∀ x ∈ pvec r zl cb.nC k, |x| < 2 ^ (cb.WC - 1) := by
    intro x hx
    obtain ⟨ch, _, rfl⟩ := List.mem_map.mp hx
    have := pval_abs cb cvA zl hch r hw k ch
    have hb' : ((r.nms * 2 ^ (r.w - 1) * cb.cmax : ℕ) : ℤ) < 2 ^ (cb.WC - 1) := by exact_mod_cast hb
    push_cast at hb'
    linarith
  exact pb_digits hWC (pvec r zl cb.nC k) (by simp [pvec]) hz _ (contract_mod cb cvA zl hch r hlen hms hw k)

/-- `Σ_k f_k t^k` -/
theorem horner_range {R : Type*} [CommSemiring R] (t : R) (f : ℕ → R) : ∀ n,
    horner t ((List.range n).map f) = ∑ k ∈ Finset.range n, f k * t ^ k
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ_eq_map, List.map_cons, horner_cons, List.map_map, Finset.sum_range_succ',
      horner_range t (f ∘ Nat.succ) n, Finset.mul_sum]
    simp only [Function.comp_apply, pow_zero, mul_one, pow_succ]
    rw [add_comm]; congr 1; apply Finset.sum_congr rfl; intro k _; ring

theorem evalZ_range (f : ℕ → ℤ) (n : ℕ) (t : ℝ) :
    evalZ ((List.range n).map f) t = ∑ k ∈ Finset.range n, (f k : ℝ) * t ^ k := by
  unfold evalZ; rw [List.map_map]; exact horner_range t _ n

/-- the contraction evaluates to the channel combination of the re-expanded entries -/
theorem pval_eval (r : RowT) (zl : ℕ → List ℤ) (ch : ℕ) (u : ℝ) :
    ∑ k ∈ Finset.range r.L, (pval r zl k ch : ℝ) * u ^ k =
      ∑ idx ∈ Finset.range r.nms, ((zl (r.mAt idx)).getD ch 0 : ℝ) * evalZ (r.ecoef idx) u := by
  unfold pval RowT.ecoef
  simp only [evalZ_range, Int.cast_sum, Int.cast_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro idx _; apply Finset.sum_congr rfl; intro k _; ring

/-! ## Sums of packed nonnegative vectors -/

theorem list_ext_getD {l1 l2 : List ℕ} (hl : l1.length = l2.length) (h : ∀ i, l1.getD i 0 = l2.getD i 0) :
    l1 = l2 := by
  apply List.ext_getElem hl
  intro i h1 h2
  have := h i
  rwa [getD_of_lt _ _ h1, getD_of_lt _ _ h2] at this

theorem lsum_ofDigits (b n : ℕ) : ∀ (Ls : List (List ℕ)), (∀ l ∈ Ls, l.length = n) →
    lsum (Ls.map (Nat.ofDigits b)) = Nat.ofDigits b ((List.range n).map fun i => (Ls.map fun l => l.getD i 0).sum)
  | [], _ => by
    show 0 = _
    rw [show ((List.range n).map fun i => (([] : List (List ℕ)).map fun l => l.getD i 0).sum) =
      List.replicate n 0 by simp, Nat.ofDigits_replicate_zero]
  | l :: Ls, h => by
    show Nat.ofDigits b l + lsum (Ls.map (Nat.ofDigits b)) = _
    rw [lsum_ofDigits b n Ls (fun x hx => h x (List.mem_cons_of_mem _ hx)), ← ofDigits_addL]
    congr 1
    apply list_ext_getD
    · rw [length_addL, h l (by simp)]; simp
    · intro i
      rw [getD_addL]
      by_cases hi : i < n
      · rw [getD_of_lt ((List.range n).map _) 0 (by simp [hi]), getD_of_lt ((List.range n).map _) 0 (by simp [hi])]
        simp
      · rw [getD_of_ge ((List.range n).map _) 0 (by simp; omega), getD_of_ge ((List.range n).map _) 0 (by simp; omega),
          getD_of_ge l 0 (by rw [h l (by simp)]; omega)]
        simp

/-- slot `i` of a sum of packed nonnegative vectors without carries -/
theorem slot_lsum {W : ℕ} (hW : 0 < W) (n : ℕ) (Ls : List (List ℕ)) (hl : ∀ l ∈ Ls, l.length = n)
    (hb : ∀ i < n, (Ls.map fun l => l.getD i 0).sum < 2 ^ W) (i : ℕ) (hi : i < n) :
    slot W (lsum (Ls.map (Nat.ofDigits (2 ^ W)))) i = (Ls.map fun l => l.getD i 0).sum := by
  rw [lsum_ofDigits _ n Ls hl, slot_ofDigits hW]
  · rw [getD_of_lt _ _ (by simp [hi])]; simp
  · intro d hd
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hd
    exact hb j (List.mem_range.mp hj)

end ThomsonCompact.Floor.B
