import ThomsonCompact.Floor.B.SoundBlockQ
import AllS.Units.N_AI.N_data.OutputInsertionGates

/-!
# Assembly of the whole-centre and error bounds (F3b)

Generic glue from the leaf theorems to the `Active12'` fields:
* `qb_comb`: a nonnegative combination of quadratically bounded matrices;
* `insM_comb`, `congr_comb`: linearity of the block insertion and of the congruence;
* `outIns_eq_insM`: the old `outputInsertion` formula is `insM` on the block rows;
* `centre_assembly`: per-channel congruence bounds + Bernstein weights ⇒ the whole-centre bound;
* `error_assembly`: row error claims ⇒ the error bound.
-/

namespace ThomsonCompact.Floor.B
open Blueprint.CAP
open scoped BigOperators

/-! ## Quadratic bounds of combinations -/

theorem quadratic_comb {n : ℕ} {ι : Type*} (s : Finset ι) (M : ι → Matrix (Fin n) (Fin n) ℝ) (c : ι → ℝ)
    (v : Fin n → ℝ) : quadratic (∑ i ∈ s, c i • M i) v = ∑ i ∈ s, c i * quadratic (M i) v := by
  unfold quadratic
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  calc ∑ a, ∑ b, v a * (∑ i ∈ s, c i * M i a b) * v b
      = ∑ a, ∑ b, ∑ i ∈ s, c i * (v a * M i a b * v b) := by
        apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _
        rw [Finset.mul_sum, Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring
    _ = ∑ a, ∑ i ∈ s, ∑ b, c i * (v a * M i a b * v b) := by
        apply Finset.sum_congr rfl; intro a _; exact Finset.sum_comm
    _ = ∑ i ∈ s, ∑ a, ∑ b, c i * (v a * M i a b * v b) := Finset.sum_comm
    _ = _ := by
        apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro a _; rw [Finset.mul_sum]

theorem qb_comb {n : ℕ} {ι : Type*} (s : Finset ι) (M : ι → Matrix (Fin n) (Fin n) ℝ) (γ c : ι → ℝ) (γ' : ℝ)
    (hM : ∀ i ∈ s, QuadraticBound (M i) (γ i)) (hc : ∀ i ∈ s, 0 ≤ c i) (hγ' : 0 ≤ γ')
    (hsum : ∑ i ∈ s, c i * γ i ≤ γ') : QuadraticBound (∑ i ∈ s, c i • M i) γ' := by
  refine ⟨hγ', fun v => ?_⟩
  rw [quadratic_comb]
  have hE : 0 ≤ squaredEuclidean v := by unfold squaredEuclidean; positivity
  calc |∑ i ∈ s, c i * quadratic (M i) v| ≤ ∑ i ∈ s, |c i * quadratic (M i) v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, c i * (γ i * squaredEuclidean v) := by
        apply Finset.sum_le_sum; intro i hi
        rw [abs_mul, abs_of_nonneg (hc i hi)]
        exact mul_le_mul_of_nonneg_left ((hM i hi).2 v) (hc i hi)
    _ = (∑ i ∈ s, c i * γ i) * squaredEuclidean v := by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring
    _ ≤ γ' * squaredEuclidean v := mul_le_mul_of_nonneg_right hsum hE

/-! ## Linearity -/

theorem insM_comb {ι : Type*} (n nr : ℕ) (uI vI : ℕ → ℕ) (s : Finset ι) (c : ι → ℝ) (w : ι → ℕ → ℝ) :
    insM n nr uI vI (fun i => ∑ k ∈ s, c k * w k i) = ∑ k ∈ s, c k • insM n nr uI vI (w k) := by
  ext a b
  simp only [insM, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro i _
  ring

theorem congr_comb {n : ℕ} {ι : Type*} (Z : Matrix (Fin n) (Fin n) ℝ) (s : Finset ι) (c : ι → ℝ)
    (M : ι → Matrix (Fin n) (Fin n) ℝ) :
    Z * (∑ k ∈ s, c k • M k) * Z.transpose = ∑ k ∈ s, c k • (Z * M k * Z.transpose) := by
  rw [Matrix.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro k _
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-! ## The block insertion of the old output coordinates -/

/-- the old `outputInsertion` formula equals `insM` on the block rows `j0 … j0+nr-1` -/
theorem outIns_eq_insM {nI : ℕ} (coords : Fin nI → String × ℕ × ℕ) (name : String) (n nr j0 : ℕ) (hnr : j0 + nr ≤ nI)
    (uI vI : ℕ → ℕ) (hrow : ∀ i (h : i < nr), coords ⟨j0 + i, by omega⟩ = (name, uI i, vI i))
    (hout : ∀ k : Fin nI, (coords k).1 = name → j0 ≤ k.val ∧ k.val < j0 + nr) (v : Fin nI → ℝ) :
    (Matrix.of fun a b : Fin n => ∑ k : Fin nI, v k * (outputEntryQ coords k name a.val b.val : ℝ)) =
      insM n nr uI vI (fun i => if h : j0 + i < nI then v ⟨j0 + i, h⟩ else 0) := by
  ext a b
  simp only [insM, Matrix.of_apply]
  set G : ℕ → ℝ := fun m => if h : m < nI then v ⟨m, h⟩ * (outputEntryQ coords ⟨m, h⟩ name a.val b.val : ℝ)
    else 0 with hG
  have e1 : ∑ k : Fin nI, v k * (outputEntryQ coords k name a.val b.val : ℝ) = ∑ m ∈ Finset.range nI, G m := by
    rw [← Fin.sum_univ_eq_sum_range G nI]
    apply Finset.sum_congr rfl; intro k _
    simp only [hG, dif_pos k.isLt]
  have e2 : ∑ m ∈ Finset.Ico j0 (j0 + nr), G m = ∑ m ∈ Finset.range nI, G m := by
    apply Finset.sum_subset
    · intro m hm; have := Finset.mem_Ico.mp hm; exact Finset.mem_range.mpr (by omega)
    · intro m hm hm'
      have hm100 := Finset.mem_range.mp hm
      simp only [hG, dif_pos hm100]
      have hne : (coords ⟨m, hm100⟩).1 ≠ name := by
        intro h; have := hout ⟨m, hm100⟩ h; exact hm' (Finset.mem_Ico.mpr this)
      unfold outputEntryQ
      rw [if_neg (by intro h; exact hne h.1.symm)]
      simp
  rw [e1, ← e2, Finset.sum_Ico_eq_sum_range, show j0 + nr - j0 = nr by omega]
  apply Finset.sum_congr rfl; intro i hi
  have hi' := Finset.mem_range.mp hi
  have h100 : j0 + i < nI := by omega
  simp only [hG, dif_pos h100]
  congr 1
  unfold outputEntryQ
  rw [hrow i hi']
  by_cases hc : (a.val = uI i ∧ b.val = vI i) ∨ (a.val = vI i ∧ b.val = uI i)
  · rw [if_pos ⟨rfl, hc⟩, if_pos hc]; norm_num
  · rw [if_neg (fun h => hc h.2), if_neg hc]; norm_num

/-! ## The whole-centre bound at one point -/

theorem insM_congr_vec (n nr : ℕ) (uI vI : ℕ → ℕ) (y y' : ℕ → ℝ) (h : ∀ i < nr, y i = y' i) :
    insM n nr uI vI y = insM n nr uI vI y' := by
  ext a b
  simp only [insM, Matrix.of_apply]
  apply Finset.sum_congr rfl; intro i hi; rw [h i (Finset.mem_range.mp hi)]

/-- **Whole-centre bound** at one point: the row values are Bernstein combinations (weights `bw ≥ 0`, sum 1)
of channel values `F i ch / K`, every channel has a congruence bound `γ ch`, and `γ ch / K ≤ γc`. -/
theorem centre_assembly (n nr : ℕ) (uI vI : ℕ → ℕ) (Z : Matrix (Fin n) (Fin n) ℝ) (Nc : ℕ)
    (bw : ℕ → ℝ) (hbw0 : ∀ ch ≤ Nc, 0 ≤ bw ch) (hbw1 : ∑ ch ∈ Finset.range (Nc + 1), bw ch = 1)
    (y : ℕ → ℝ) (F : ℕ → ℕ → ℝ) (K : ℝ) (hK : 0 < K)
    (hy : ∀ i < nr, y i = ∑ ch ∈ Finset.range (Nc + 1), bw ch * F i ch / K)
    (γ : ℕ → ℝ) (hQ : ∀ ch ≤ Nc, QuadraticBound (Z * insM n nr uI vI (fun i => F i ch) * Z.transpose) (γ ch))
    (γc : ℝ) (hγc : 0 ≤ γc) (hγ : ∀ ch ≤ Nc, γ ch / K ≤ γc) :
    QuadraticBound (Z * insM n nr uI vI y * Z.transpose) γc := by
  rw [insM_congr_vec n nr uI vI y (fun i => ∑ ch ∈ Finset.range (Nc + 1), (bw ch / K) * F i ch)
    (fun i hi => by rw [hy i hi]; apply Finset.sum_congr rfl; intro ch _; ring)]
  rw [insM_comb, congr_comb]
  apply qb_comb _ _ γ _ γc (fun ch hch => hQ ch (by have := Finset.mem_range.mp hch; omega))
    (fun ch hch => div_nonneg (hbw0 ch (by have := Finset.mem_range.mp hch; omega)) hK.le) hγc
  calc ∑ ch ∈ Finset.range (Nc + 1), bw ch / K * γ ch ≤ ∑ ch ∈ Finset.range (Nc + 1), bw ch * γc := by
        apply Finset.sum_le_sum; intro ch hch
        have h1 := hγ ch (by have := Finset.mem_range.mp hch; omega)
        have h0 := hbw0 ch (by have := Finset.mem_range.mp hch; omega)
        calc bw ch / K * γ ch = bw ch * (γ ch / K) := by ring
          _ ≤ bw ch * γc := mul_le_mul_of_nonneg_left h1 h0
    _ = γc := by rw [← Finset.sum_mul, hbw1, one_mul]

/-! ## Row vectors of the inverse table -/

/-- a function vanishing off the row entries sums over the entries -/
theorem sum_msL {nI : ℕ} (r : RowT) (hs : r.msL.Pairwise (· < ·)) (h100 : ∀ m ∈ r.msL, m < nI) (f : ℕ → ℝ)
    (hf : ∀ m < nI, m ∉ r.msL → f m = 0) :
    ∑ m ∈ Finset.range nI, f m = ∑ idx ∈ Finset.range r.nms, f (r.mAt idx) := by
  have hnd : r.msL.Nodup := hs.imp (fun h => Nat.ne_of_lt h)
  rw [← msL_sum, ← List.sum_toFinset f hnd]
  symm
  apply Finset.sum_subset
  · intro m hm; exact Finset.mem_range.mpr (h100 m (List.mem_toFinset.mp hm))
  · intro m hm hm'
    exact hf m (Finset.mem_range.mp hm) (fun h => hm' (List.mem_toFinset.mpr h))

/-- **Row error.** The row `j` of the inverse table applied to a structured target error plus a residual
error is bounded by the row error claim `rowErr`. -/
theorem rowvec_err {nI : ℕ} (cb : CellB) (r : RowT) (H : ℕ → ℝ → ℝ) (dl : ℝ → ℝ) (zl : ℕ → List ℤ) (a : ℝ)
    (hs : r.msL.Pairwise (· < ·)) (h100 : ∀ m ∈ r.msL, m < nI) (hdl : dl a ≠ 0)
    (hzero : ∀ m < nI, m ∉ r.msL → H m a = 0)
    (e : ℕ → ℝ) (he : ∀ tt < cb.nT, |e tt| ≤ (cb.herr tt : ℝ) / 2 ^ 256)
    (q : ℕ → ℕ → ℝ) (hq : ∀ m < nI, ∀ tt < cb.nT, q m tt = ((zl m).getD (cb.N + 1 + tt) 0 : ℝ) / 3)
    (ε : ℕ → ℝ) (hε : ∀ m < nI, |ε m| ≤ (cb.Er m : ℝ) / 2 ^ 256) :
    |∑ m ∈ Finset.range nI, H m a / dl a * (∑ tt ∈ Finset.range cb.nT, e tt * q m tt + ε m)| ≤
      rowErr cb r H dl zl a := by
  have hda : 0 < |dl a| := abs_pos.mpr hdl
  have e1 : ∑ m ∈ Finset.range nI, H m a / dl a * (∑ tt ∈ Finset.range cb.nT, e tt * q m tt + ε m) =
      ∑ tt ∈ Finset.range cb.nT, e tt * (rowS r H zl (cb.N + 1 + tt) a / (3 * dl a)) +
        ∑ idx ∈ Finset.range r.nms, H (r.mAt idx) a / dl a * ε (r.mAt idx) := by
    have e2 : ∑ m ∈ Finset.range nI, H m a / dl a * (∑ tt ∈ Finset.range cb.nT, e tt * q m tt + ε m) =
        ∑ tt ∈ Finset.range cb.nT, e tt * ∑ m ∈ Finset.range nI, H m a / dl a * q m tt +
          ∑ m ∈ Finset.range nI, H m a / dl a * ε m := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro tt _; apply Finset.sum_congr rfl; intro m _; ring
    rw [e2]
    congr 1
    · apply Finset.sum_congr rfl; intro tt htt
      congr 1
      rw [sum_msL r hs h100 _ (fun m hm hm' => by rw [hzero m hm hm']; simp)]
      unfold rowS
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl; intro idx hidx
      have hm : r.mAt idx < nI := by
        apply h100
        unfold RowT.mAt
        rw [getD_of_lt _ _ (by simp [RowT.msL]; exact Finset.mem_range.mp hidx)]
        exact List.getElem_mem _
      rw [hq _ hm tt (Finset.mem_range.mp htt)]
      field_simp
    · exact sum_msL r hs h100 _ (fun m hm hm' => by rw [hzero m hm hm']; simp)
  rw [e1]
  unfold rowErr
  refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
  · refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun tt htt => ?_)
    rw [abs_mul, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    have := he tt (Finset.mem_range.mp htt)
    calc |e tt| * (|rowS r H zl (cb.N + 1 + tt) a| / (3 * |dl a|))
        ≤ (cb.herr tt : ℝ) / 2 ^ 256 * (|rowS r H zl (cb.N + 1 + tt) a| / (3 * |dl a|)) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = _ := by ring
  · refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun idx hidx => ?_)
    have hm : r.mAt idx < nI := by
      apply h100
      unfold RowT.mAt
      rw [getD_of_lt _ _ (by simp [RowT.msL]; exact Finset.mem_range.mp hidx)]
      exact List.getElem_mem _
    rw [abs_mul, abs_div]
    have := hε _ hm
    calc |H (r.mAt idx) a| / |dl a| * |ε (r.mAt idx)| ≤ |H (r.mAt idx) a| / |dl a| * ((cb.Er (r.mAt idx) : ℝ) / 2 ^ 256) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring

end ThomsonCompact.Floor.B
