import ThomsonCompact.Fixed.SoundN
import Mathlib.Tactic.LinearCombination

/-!
# The assembled table identity (workstream F4)

`table_poly`: from the one-time checks (`tabOk`, `gLinkOk`, `kapHdrOk`), the N-link leaves (`colLinkOk` for
every output), the main leaves (`leafOk` for a list of slices covering all columns) and one numeric bound,
the **polynomial identity (T)** holds for all real `t`:

  `Σ_{k<n} N_ik(t) · Γ_k(t) · H_ki'(t) = [i = i'] · s · Q(t)`,

with `N_ik = nC L k i` the canonical polynomials (`SoundN.ncomp`), `Γ_k = gamC G k`, `Q = qC G` (`SoundG`)
and `H_ki' = hC sl k i'` the stored table entries. Together with (G) (`gLinkOk_sound`) this is the
A·H orientation of the paper's Lemma `lem:direct-fixed-table`.
-/

namespace ThomsonCompact.Fixed

open ThomsonCompact.Packed

/-! ## Slices -/

/-- The empty slice. -/
noncomputable def sliceNil : Slice := ⟨0, 0, fun _ _ => 0, fun _ => 0, 0, 0⟩

/-- The (first) slice of `sl` containing column `i`. -/
noncomputable def findSlice (sl : List Slice) (i : Nat) : Slice :=
  (sl.find? fun S => decide (S.i0 ≤ i ∧ i < S.i0 + S.len)).getD sliceNil

theorem findSlice_spec (sl : List Slice) (i : Nat) (h : ∃ S ∈ sl, S.i0 ≤ i ∧ i < S.i0 + S.len) :
    findSlice sl i ∈ sl ∧ (findSlice sl i).i0 ≤ i ∧ i < (findSlice sl i).i0 + (findSlice sl i).len := by
  obtain ⟨S, hS, hi⟩ := h
  unfold findSlice
  cases hf : sl.find? (fun S => decide (S.i0 ≤ i ∧ i < S.i0 + S.len)) with
  | none =>
    have := List.find?_eq_none.mp hf S hS
    simp [hi] at this
  | some S' =>
    have h1 := List.mem_of_find?_eq_some hf
    have h2 := List.find?_some hf
    simp only [decide_eq_true_eq] at h2
    exact ⟨h1, h2⟩

/-- Stored `H` entry `(k, i)` (coefficients). -/
noncomputable def hC (sl : List Slice) (k i : Nat) : List ℤ := hcoef (findSlice sl i) k i

/-- Canonical `N` polynomial of output `k` at row `i`. -/
noncomputable def nC (L : LTab) (k i : Nat) : List ℤ :=
  ncomp L (oBlk L k) (oRow L k) (oCol L k) (oMult L k) (L.rtag i)

/-! ## One-time checks -/

theorem kapHdrOk_spec (L : LTab) (n LK wK mK : Nat) (h : kapHdrOk L n LK wK mK = true) :
    (∀ b r, b < 4 → r < 256 → 1 ≤ polyVecOk LK wK mK (L.kc b r) (L.kn b r) 0 1) ∧ ∀ k, k < n → oBlk L k < 4 := by
  have h' : (Nat.rec (motive := fun _ => Bool) true (fun b ih => ih &&
      Nat.rec (motive := fun _ => Bool) true
        (fun r ih2 => ih2 && Nat.ble 1 (polyVecOk LK wK mK (L.kc b r) (L.kn b r) 0 1)) 256) 4 &&
      Nat.rec (motive := fun _ => Bool) true (fun k ih => ih && Nat.blt (Nat.land (L.oinfo k) 255) 4) n) = true := h
  rw [Bool.and_eq_true] at h'
  have inner : ∀ b m, Nat.rec (motive := fun _ => Bool) true
      (fun r ih2 => ih2 && Nat.ble 1 (polyVecOk LK wK mK (L.kc b r) (L.kn b r) 0 1)) m = true →
      ∀ r, r < m → 1 ≤ polyVecOk LK wK mK (L.kc b r) (L.kn b r) 0 1 := by
    intro b m
    induction m with
    | zero => intro _ r hr; exact absurd hr (Nat.not_lt_zero r)
    | succ m ih =>
      intro hm r hr
      have hm' : (Nat.rec (motive := fun _ => Bool) true
          (fun r ih2 => ih2 && Nat.ble 1 (polyVecOk LK wK mK (L.kc b r) (L.kn b r) 0 1)) m &&
          Nat.ble 1 (polyVecOk LK wK mK (L.kc b m) (L.kn b m) 0 1)) = true := hm
      rw [Bool.and_eq_true] at hm'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
      · exact ih hm'.1 r hr
      · exact Nat.le_of_ble_eq_true hm'.2
  have outer : ∀ m, Nat.rec (motive := fun _ => Bool) true (fun b ih => ih &&
      Nat.rec (motive := fun _ => Bool) true
        (fun r ih2 => ih2 && Nat.ble 1 (polyVecOk LK wK mK (L.kc b r) (L.kn b r) 0 1)) 256) m = true →
      ∀ b r, b < m → r < 256 → 1 ≤ polyVecOk LK wK mK (L.kc b r) (L.kn b r) 0 1 := by
    intro m
    induction m with
    | zero => intro _ b r hb; exact absurd hb (Nat.not_lt_zero b)
    | succ m ih =>
      intro hm b r hb hr
      have hm' : (Nat.rec (motive := fun _ => Bool) true (fun b ih => ih &&
          Nat.rec (motive := fun _ => Bool) true
            (fun r ih2 => ih2 && Nat.ble 1 (polyVecOk LK wK mK (L.kc b r) (L.kn b r) 0 1)) 256) m &&
          Nat.rec (motive := fun _ => Bool) true
            (fun r ih2 => ih2 && Nat.ble 1 (polyVecOk LK wK mK (L.kc m r) (L.kn m r) 0 1)) 256) = true := hm
      rw [Bool.and_eq_true] at hm'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hb | rfl
      · exact ih hm'.1 b r hb hr
      · exact inner b 256 hm'.2 r hr
  have blk : ∀ m, Nat.rec (motive := fun _ => Bool) true
      (fun k ih => ih && Nat.blt (Nat.land (L.oinfo k) 255) 4) m = true → ∀ k, k < m → oBlk L k < 4 := by
    intro m
    induction m with
    | zero => intro _ k hk; exact absurd hk (Nat.not_lt_zero k)
    | succ m ih =>
      intro hm k hk
      have hm' : (Nat.rec (motive := fun _ => Bool) true
          (fun k ih => ih && Nat.blt (Nat.land (L.oinfo k) 255) 4) m &&
          Nat.blt (Nat.land (L.oinfo m) 255) 4) = true := hm
      rw [Bool.and_eq_true] at hm'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact ih hm'.1 k hk
      · exact Nat.blt_eq.mp hm'.2
  exact ⟨fun b r hb hr => outer 4 h'.1 b r hb hr, blk n h'.2⟩

theorem linkOk_spec (T : Tab) (L : LTab) : ∀ (m k0 : Nat), linkOk T L m k0 = true →
    ∀ k, k0 ≤ k → k < k0 + m → colLinkOk T L k = true
  | 0, _, _, k, h1, h2 => by omega
  | m + 1, k0, h, k, h1, h2 => by
    have h' : (colLinkOk T L k0 && linkOk T L m (Nat.add k0 1)) = true := h
    rw [Bool.and_eq_true] at h'
    by_cases hk : k = k0
    · rw [hk]; exact h'.1
    · exact linkOk_spec T L m (Nat.add k0 1) h'.2 k (by rw [nat_add]; omega) (by rw [nat_add]; omega)

/-! ## The radix identity -/

theorem list_sum_range' {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, list_sum_range' f n, Finset.sum_range_succ]
    simp

/-- **(T) at the radix.** -/
theorem table_radix (T : Tab) (G : GTab) (L : LTab) (sl : List Slice) (hR : 0 < T.R)
    (htab : tabOk T = true) (hleaf : ∀ S ∈ sl, leafOk T S = true)
    (hcov : ∀ i, i < T.n → ∃ S ∈ sl, S.i0 ≤ i ∧ i < S.i0 + S.len)
    (hG : gLinkOk T G = true) (hlink : ∀ k, k < T.n → colLinkOk T L k = true)
    (hrtag : ∀ i j, i < T.n → j < T.n → L.rtag i = L.rtag j → i = j)
    (hnr : ∀ i, i < T.n → notRetained L.D (L.rtag i) = false) :
    ∀ i i', i < T.n → i' < T.n →
      ∑ k ∈ Finset.range T.n, horner ((2 : ℤ) ^ T.R) (nC L k i) *
          (horner ((2 : ℤ) ^ T.R) (gamC G k) * horner ((2 : ℤ) ^ T.R) (hC sl k i')) =
        if i = i' then (G.s : ℤ) * horner ((2 : ℤ) ^ T.R) (qC G) else 0 := by
  intro i i' hi hi'
  obtain ⟨g1, g2, -, -, -⟩ := gLinkOk_sound T G hR hG
  obtain ⟨hS, hS1, hS2⟩ := findSlice_spec sl i' (hcov i' hi')
  have hl := (leafOk_sound T _ hR htab (hleaf _ hS)).2 i (i' - (findSlice sl i').i0) hi (by omega)
  rw [show (findSlice sl i').i0 + (i' - (findSlice sl i').i0) = i' by omega] at hl
  rw [g2] at hl
  rw [← hl]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  have hN := colLinkOk_sound T L k hR (hlink k hk') hrtag hnr ((tabOk_spec T htab).2 k hk').2 i hi
  rw [g1 k, hN]
  unfold hC nC
  ring

/-! ## The lift -/

theorem recBound_mono {L w L' w' : Nat} (hL : L ≤ L') (hw : w ≤ w') : recBound L w ≤ recBound L' w' := by
  simp only [recBound, nat_mul, nat_sub, nat_shiftLeft, one_mul]
  exact Nat.mul_le_mul hL (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem l1_conv3 (a b c : List ℤ) : l1 (convL a (convL b c)) ≤ l1 a * (l1 b * l1 c) :=
  (l1_convL _ _).trans (Nat.mul_le_mul_left _ (l1_convL _ _))

/-- **The polynomial table identity (T)** for all real `t`. -/
theorem table_poly (T : Tab) (G : GTab) (L : LTab) (sl : List Slice) (LH wH LK wK mK : Nat) (hR : 0 < T.R)
    (htab : tabOk T = true) (hleaf : ∀ S ∈ sl, leafOk T S = true ∧ S.LH ≤ LH ∧ S.wH ≤ wH)
    (hcov : ∀ i, i < T.n → ∃ S ∈ sl, S.i0 ≤ i ∧ i < S.i0 + S.len)
    (hG : gLinkOk T G = true) (hlink : ∀ k, k < T.n → colLinkOk T L k = true)
    (hkap : kapHdrOk L T.n LK wK mK = true)
    (hrtag : ∀ i j, i < T.n → j < T.n → L.rtag i = L.rtag j → i = j)
    (hnr : ∀ i, i < T.n → notRetained L.D (L.rtag i) = false)
    (hbound : 2 * (T.n * (mK * (mK * (255 * (255 * 65535) * (recBound LK wK * recBound LK wK)))) *
      (recBound G.LG G.wG * recBound LH wH) + G.s * recBound G.LQ G.wQ) < 2 ^ T.R) :
    ∀ i i', i < T.n → i' < T.n → ∀ t : ℝ,
      ∑ k ∈ Finset.range T.n, evalZ (nC L k i) t * (evalZ (gamC G k) t * evalZ (hC sl k i') t) =
        if i = i' then (G.s : ℝ) * evalZ (qC G) t else 0 := by
  intro i i' hi hi' t
  have hrad := table_radix T G L sl hR htab (fun S hS => (hleaf S hS).1) hcov hG hlink hrtag hnr i i' hi hi'
  obtain ⟨-, -, gB, qB, -⟩ := gLinkOk_sound T G hR hG
  obtain ⟨kH, kB⟩ := kapHdrOk_spec L T.n LK wK mK hkap
  obtain ⟨hS, hS1, hS2⟩ := findSlice_spec sl i' (hcov i' hi')
  have hH := (leafOk_sound T _ hR htab (hleaf _ hS).1).1
  -- the polynomial
  set c : ℤ := if i = i' then (G.s : ℤ) else 0 with hc
  have hP0 : horner ((2 ^ T.R : ℕ) : ℤ) (addL (sumL ((List.range T.n).map fun k =>
      convL (nC L k i) (convL (gamC G k) (hC sl k i')))) (scaleL (-c) (qC G))) = 0 := by
    rw [hornerZ_addL, hornerZ_sumL, hornerZ_scaleL, List.map_map, list_sum_range']
    push_cast
    simp only [Function.comp, hornerZ_convL]
    rw [hrad, hc]
    split_ifs <;> ring
  -- ℓ1 bounds
  have hKB : ∀ b r, b < 4 → r < 256 → (∀ u ∈ kapC L b r, l1 u.2 ≤ recBound LK wK) ∧ (kapC L b r).length ≤ mK := by
    intro b r hb hr
    obtain ⟨p1, p2, p3⟩ := polyVecOk_spec T.R _ _ _ _ _ _ _ (kH b r hb hr)
    refine ⟨fun u hu => l1_le_of_coefB (p3 u hu), ?_⟩
    have hlen : (kapC L b r).length = (kapV T.R L b r).length := by
      have h := congrArg List.length (decPolyVec_sv T.R hR (L.kc b r) (L.kn b r) 0)
      simp only [List.length_map] at h
      exact h.symm
    rw [hlen]
    have := (Inc.full (kapV T.R L b r) p1 p2 (Nat.zero_le _)).1
    simp only [kapV] at this ⊢
    omega
  have hNB : ∀ k, k < T.n → l1 (nC L k i) ≤ mK * (mK * (255 * (255 * 65535) * (recBound LK wK * recBound LK wK))) := by
    intro k hk
    have hb := kB k hk
    have hr : oRow L k < 256 := Nat.lt_succ_of_le Nat.and_le_right
    have hcl : oCol L k < 256 := Nat.lt_succ_of_le Nat.and_le_right
    obtain ⟨r1, r2⟩ := hKB _ _ hb hr
    obtain ⟨c1, c2⟩ := hKB _ _ hb hcl
    refine (ncomp_l1 L _ _ _ _ _ (recBound LK wK) Nat.and_le_right r1 c1).trans ?_
    exact Nat.mul_le_mul r2 (Nat.mul_le_mul c2 le_rfl)
  have hl1 : l1 (addL (sumL ((List.range T.n).map fun k =>
      convL (nC L k i) (convL (gamC G k) (hC sl k i')))) (scaleL (-c) (qC G))) ≤
      T.n * (mK * (mK * (255 * (255 * 65535) * (recBound LK wK * recBound LK wK)))) *
        (recBound G.LG G.wG * recBound LH wH) + G.s * recBound G.LQ G.wQ := by
    refine (l1_addL _ _).trans (Nat.add_le_add ?_ ?_)
    · have := l1_sumL_map (fun k => convL (nC L k i) (convL (gamC G k) (hC sl k i')))
        ((mK * (mK * (255 * (255 * 65535) * (recBound LK wK * recBound LK wK)))) *
          (recBound G.LG G.wG * recBound LH wH)) (List.range T.n) (fun k hk => by
        have hk' := List.mem_range.mp hk
        refine (l1_conv3 _ _ _).trans (Nat.mul_le_mul (hNB k hk') (Nat.mul_le_mul (l1_le_of_coefB (gB k)) ?_))
        exact (l1_le_of_coefB (hH k i' hk')).trans (recBound_mono (hleaf _ hS).2.1 (hleaf _ hS).2.2))
      rw [List.length_range] at this
      refine this.trans (le_of_eq ?_)
      ring
    · rw [l1_scaleL, Int.natAbs_neg, hc]
      refine (Nat.mul_le_mul ?_ (l1_le_of_coefB qB)).trans le_rfl
      split_ifs <;> simp
  have hlift := lift (2 ^ T.R) (Nat.one_lt_two_pow (by omega)) _
    (lt_of_le_of_lt (Nat.mul_le_mul_left 2 hl1) hbound) hP0 t
  rw [evalZ_addL, evalZ_sumL, evalZ_scaleL, List.map_map, list_sum_range'] at hlift
  simp only [Function.comp, evalZ_convL] at hlift
  rw [hc] at hlift
  split_ifs at hlift ⊢ <;> push_cast at hlift ⊢ <;> linear_combination hlift

#print axioms table_radix
#print axioms table_poly

end ThomsonCompact.Fixed
