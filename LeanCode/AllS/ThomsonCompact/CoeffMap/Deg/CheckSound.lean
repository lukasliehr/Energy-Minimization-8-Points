import ThomsonCompact.CoeffMap.Deg.DenseSound
import ThomsonCompact.CoeffMap.Deg.ProgSound

/-!
# Soundness of the one-time (per degree) checks (F2f)

* `tagOk_spec`: the coordinate tags and the inverse tag table agree: `ridx (rtag r) = r` and `ridx t = r < nc` only
  for `t = rtag r`; hence `lookup_ridx`: summing the terms with `ridx t = r` is `rawIntegerLookup · (rtag r)`.
* `clsOk_spec`: the classes of block `b` partition the pairs `u ≤ v < rdim b` (`cls_sum`), every pair of class `k`
  has the class key, and the parity keys satisfy the power-sum bounds of `rscZ_eval`.
* `grpOk_spec`, `grp_sum`: the groups split the classes into consecutive ranges.
* `eOk_spec`: the coefficient list of pseudo-block `(b, g)` at a checked coordinate `r` is `eRow` of the class
  accumulators; `eRow_sum`: it represents the class coefficients `cc` (the slot differences).
-/

namespace ThomsonCompact.CoeffMap.Deg

open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite ThomsonCompact.CoeffMap ThomsonCompact.Packed
open scoped BigOperators

/-! ## Tag codes -/

theorem pow_mask (a : ℕ) : Nat.sub (Nat.shiftLeft 1 a) 1 = 2 ^ a - 1 := by
  rw [shl_eq, one_mul]; rfl

theorem land_pow (x w : ℕ) : Nat.land x (2 ^ w - 1) = x % 2 ^ w := Nat.and_two_pow_sub_one_eq_mod x w

theorem encT_eq (aA aB : ℕ) (t : T3) : encT aA aB t = t.1 + (t.2.1 + t.2.2 * 2 ^ aB) * 2 ^ aA := by
  show Nat.add t.1 (Nat.shiftLeft (Nat.add t.2.1 (Nat.shiftLeft t.2.2 aB)) aA) = _
  rw [shl_eq, shl_eq]; rfl

theorem decT_encT (aA aB : ℕ) (t : T3) (h1 : t.1 < 2 ^ aA) (h2 : t.2.1 < 2 ^ aB) : decT aA aB (encT aA aB t) = t := by
  obtain ⟨x, y, z⟩ := t
  simp only at h1 h2
  have hE := encT_eq aA aB (x, y, z)
  simp only at hE
  show (Nat.land (encT aA aB (x, y, z)) (Nat.sub (Nat.shiftLeft 1 aA) 1),
    Nat.land (Nat.shiftRight (encT aA aB (x, y, z)) aA) (Nat.sub (Nat.shiftLeft 1 aB) 1),
    Nat.shiftRight (encT aA aB (x, y, z)) (Nat.add aA aB)) = (x, y, z)
  rw [hE, pow_mask, pow_mask, land_pow, land_pow, shr_eq, shr_eq, Nat.add_eq]
  have e1 : (x + (y + z * 2 ^ aB) * 2 ^ aA) % 2 ^ aA = x := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h1]
  have e2 : (x + (y + z * 2 ^ aB) * 2 ^ aA) / 2 ^ aA = y + z * 2 ^ aB := by
    rw [Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt h1, zero_add]
  have e3 : (y + z * 2 ^ aB) % 2 ^ aB = y := by rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt h2]
  have e4 : (x + (y + z * 2 ^ aB) * 2 ^ aA) / 2 ^ (aA + aB) = z := by
    rw [pow_add, ← Nat.div_div_eq_div_mul, e2, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt h2, zero_add]
  rw [e1, e2, e3, e4]

theorem encT_lt (aA aB kC : ℕ) (t : T3) (h1 : t.1 < 2 ^ aA) (h2 : t.2.1 < 2 ^ aB) (h3 : t.2.2 < kC) :
    encT aA aB t < 2 ^ (aA + aB) * kC := by
  rw [encT_eq]
  have : t.2.1 + t.2.2 * 2 ^ aB < 2 ^ aB * kC := by
    have : t.2.2 * 2 ^ aB + 2 ^ aB ≤ 2 ^ aB * kC := by
      rw [mul_comm, ← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h3
    omega
  calc t.1 + (t.2.1 + t.2.2 * 2 ^ aB) * 2 ^ aA < 2 ^ aA + (t.2.1 + t.2.2 * 2 ^ aB) * 2 ^ aA := by omega
    _ = (t.2.1 + t.2.2 * 2 ^ aB + 1) * 2 ^ aA := by ring
    _ ≤ (2 ^ aB * kC) * 2 ^ aA := Nat.mul_le_mul_right _ this
    _ = 2 ^ (aA + aB) * kC := by rw [pow_add]; ring

namespace DegD

variable (L : DegD)

theorem tagOk_spec (h : L.tagOk = true) :
    (∀ r, r < L.nc → L.ridx (L.rtag r) = r) ∧ (∀ t r, r < L.nc → L.ridx t = r → t = L.rtag r) := by
  unfold DegD.tagOk at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun r hr => ?_, fun t r hr htr => ?_⟩
  · have := h1 r (List.mem_range.mpr hr)
    simp only [Bool.and_eq_true, Nat.beq_eq] at this
    exact this.1.1.1
  · unfold DegD.ridx at htr
    cases hb : (Nat.blt t.1 (Nat.shiftLeft 1 L.aA) && Nat.blt t.2.1 (Nat.shiftLeft 1 L.aB) && Nat.blt t.2.2 L.kC)
    · rw [hb, cond_false] at htr; omega
    · rw [hb, cond_true] at htr
      simp only [Bool.and_eq_true, Nat.blt_eq, shl_eq, one_mul] at hb
      obtain ⟨⟨hb1, hb2⟩, hb3⟩ := hb
      have hc := h2 (encT L.aA L.aB t) (List.mem_range.mpr (by
        rw [show Nat.mul (Nat.shiftLeft 1 (Nat.add L.aA L.aB)) L.kC = 2 ^ (L.aA + L.aB) * L.kC by
          rw [shl_eq, one_mul]; rfl]
        exact encT_lt _ _ _ t hb1 hb2 hb3))
      rw [htr] at hc
      simp only [show Nat.blt r L.nc = true from Nat.blt_eq.mpr hr, Bool.not_true, Bool.false_or] at hc
      rw [teq_eq hc, decT_encT _ _ t hb1 hb2]

/-- Summing the terms with `ridx t = r` is the lookup at the tag of `r`. -/
theorem lookup_ridx (h : L.tagOk = true) (P : SP) (r : ℕ) (hr : r < L.nc) :
    (P.map fun e => if L.ridx e.1 = r then e.2 else 0).sum = rawIntegerLookup P (L.rtag r) := by
  obtain ⟨h1, h2⟩ := L.tagOk_spec h
  unfold rawIntegerLookup
  congr 1
  apply List.map_congr_left
  intro e _
  by_cases he : e.1 = L.rtag r
  · rw [if_pos (by rw [he, h1 r hr]), if_pos he]
  · rw [if_neg (fun h' => he (h2 e.1 r hr h')), if_neg he]

/-! ## Classes -/

theorem pairsOk_spec (b n x : ℕ) : ∀ (ps : List (ℕ × ℕ)) (lo : ℕ), L.pairsOk b n x ps lo = true →
    (∀ p ∈ ps, p.1 ≤ p.2 ∧ p.2 < n ∧ L.pairKey b p.1 p.2 = x ∧ lo ≤ p.1 + 256 * p.2) ∧
      (ps.map fun p => p.1 + 256 * p.2).Pairwise (· < ·)
  | [], _, _ => ⟨fun _ h => absurd h List.not_mem_nil, List.Pairwise.nil⟩
  | p :: ps, lo, h => by
    have h' : (Nat.ble lo (Nat.add p.1 (Nat.shiftLeft p.2 8)) && Nat.ble p.1 p.2 && Nat.blt p.2 n &&
        Nat.beq (L.pairKey b p.1 p.2) x && L.pairsOk b n x ps (Nat.add (Nat.add p.1 (Nat.shiftLeft p.2 8)) 1)) = true := h
    simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.beq_eq] at h'
    obtain ⟨⟨⟨⟨hlo, hle⟩, hn⟩, hk⟩, hrest⟩ := h'
    have hc : Nat.add p.1 (Nat.shiftLeft p.2 8) = p.1 + 256 * p.2 := by
      rw [shl_eq]; show p.1 + p.2 * 2 ^ 8 = _; ring
    rw [hc] at hlo hrest
    simp only [Nat.add_eq] at hrest
    obtain ⟨ih1, ih2⟩ := pairsOk_spec b n x ps _ hrest
    refine ⟨fun q hq => ?_, ?_⟩
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨hle, hn, hk, hlo⟩
      · obtain ⟨a, b', c', d'⟩ := ih1 q hq
        exact ⟨a, b', c', by omega⟩
    · rw [List.map_cons, List.pairwise_cons]
      refine ⟨fun y hy => ?_, ih2⟩
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
      have := (ih1 q hq).2.2.2
      omega

/-- The facts of `clsOk b`. -/
structure ClsFacts (b : ℕ) : Prop where
  pairs : ∀ k, k < L.nCls b → ∀ p ∈ L.clsPairs b k, p.1 ≤ p.2 ∧ p.2 < L.rdim b ∧ L.pairKey b p.1 p.2 = L.clsKey b k
  sorted : ∀ k, k < L.nCls b → ((L.clsPairs b k).map fun p => p.1 + 256 * p.2).Pairwise (· < ·)
  bound : ∀ k, k < L.nCls b → L.keyBound b (L.clsKey b k) = true
  keys : ∀ k, k + 1 < L.nCls b → L.clsKey b k < L.clsKey b (k + 1)
  count : (((List.range (L.nCls b)).map fun k => (L.clsPairs b k).length).foldr Nat.add 0) =
    Nat.shiftRight (Nat.mul (L.rdim b) (Nat.add (L.rdim b) 1)) 1

theorem clsOk_spec (b : ℕ) (h : L.clsOk b = true) : L.ClsFacts b := by
  unfold DegD.clsOk at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have hk : ∀ k, k < L.nCls b → _ := fun k hk => h1 k (List.mem_range.mpr hk)
  refine ⟨fun k hkn p hp => ?_, fun k hkn => ?_, fun k hkn => ?_, fun k hkn => ?_, Nat.eq_of_beq_eq_true h2⟩
  · have := hk k hkn
    simp only [Bool.and_eq_true] at this
    exact ((L.pairsOk_spec b _ _ _ 0 this.1.1).1 p hp).elim fun a hb => ⟨a, hb.1, hb.2.1⟩
  · have := hk k hkn
    simp only [Bool.and_eq_true] at this
    exact (L.pairsOk_spec b _ _ _ 0 this.1.1).2
  · have := hk k hkn
    simp only [Bool.and_eq_true] at this
    exact this.1.2
  · have := hk k (by omega)
    simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq, Nat.blt_eq, Nat.add_eq] at this
    rcases this.2 with h' | h'
    · omega
    · exact h'

theorem sum_map_flatMap' {α β M : Type*} [AddCommMonoid M] (g : α → List β) (F : β → M) : ∀ L : List α,
    ((L.flatMap g).map F).sum = (L.map fun x => ((g x).map F).sum).sum
  | [] => by simp
  | x :: L => by
    rw [List.flatMap_cons, List.map_append, List.sum_append, sum_map_flatMap' g F L, List.map_cons, List.sum_cons]

/-- The pairs `u ≤ v < n`, column by column. -/
def triPairs (n : ℕ) : List (ℕ × ℕ) := (List.range n).flatMap fun v => (List.range (v + 1)).map fun u => (u, v)

theorem mem_triPairs (n : ℕ) (p : ℕ × ℕ) : p ∈ triPairs n ↔ p.1 ≤ p.2 ∧ p.2 < n := by
  unfold triPairs
  simp only [List.mem_flatMap, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨v, hv, u, hu, rfl⟩; exact ⟨by omega, hv⟩
  · intro h; exact ⟨p.2, h.2, p.1, by omega, rfl⟩

theorem triPairs_nodup (n : ℕ) : (triPairs n).Nodup := by
  unfold triPairs
  rw [List.nodup_flatMap]
  refine ⟨fun v _ => (@List.nodup_range (v + 1)).map (fun a b h => by simpa using h), ?_⟩
  refine (@List.nodup_range n).pairwise_of_forall_ne ?_
  intro v _ w _ hvw
  simp only [Function.onFun, List.disjoint_left, List.mem_map, List.mem_range]
  rintro p ⟨u, _, rfl⟩ ⟨u', _, h⟩
  simp only [Prod.mk.injEq] at h
  exact hvw h.2.symm

theorem triPairs_length (n : ℕ) : 2 * (triPairs n).length = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold triPairs at ih ⊢
    rw [List.range_succ, List.flatMap_append, List.length_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_map, List.length_range]
    rw [mul_add, ih]
    ring

/-- **The classes partition the pairs** `u ≤ v < rdim b`. -/
theorem cls_sum {M : Type*} [AddCommMonoid M] (b : ℕ) (hc : L.ClsFacts b) (F : ℕ × ℕ → M) :
    ∑ k ∈ Finset.range (L.nCls b), ((L.clsPairs b k).map F).sum = ((triPairs (L.rdim b)).map F).sum := by
  set Lall := (List.range (L.nCls b)).flatMap (L.clsPairs b) with hLall
  have hkeyinj : ∀ k k', k < L.nCls b → k' < L.nCls b → L.clsKey b k = L.clsKey b k' → k = k' := by
    have hmono : ∀ k j, k + j + 1 < L.nCls b → L.clsKey b k < L.clsKey b (k + j + 1) := by
      intro k j
      induction j with
      | zero => intro h; exact hc.keys k h
      | succ j ih => intro h; exact lt_trans (ih (by omega)) (hc.keys _ (by omega))
    intro k k' hk hk' he
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hl | hl
    · have := hmono k (k' - k - 1) (by omega)
      rw [show k + (k' - k - 1) + 1 = k' by omega] at this; omega
    · have := hmono k' (k - k' - 1) (by omega)
      rw [show k' + (k - k' - 1) + 1 = k by omega] at this; omega
  have hnodup : Lall.Nodup := by
    rw [hLall, List.nodup_flatMap]
    refine ⟨fun k hk => ?_, ?_⟩
    · have hs := hc.sorted k (List.mem_range.mp hk)
      exact List.Nodup.of_map (fun p : ℕ × ℕ => p.1 + 256 * p.2) (hs.imp (fun h => ne_of_lt h) : List.Nodup _)
    · refine (@List.nodup_range (L.nCls b)).pairwise_of_forall_ne ?_
      intro k hk k' hk' hne
      simp only [Function.onFun, List.disjoint_left]
      intro p hp hp'
      have e1 := (hc.pairs k (List.mem_range.mp hk) p hp).2.2
      have e2 := (hc.pairs k' (List.mem_range.mp hk') p hp').2.2
      exact hne (hkeyinj k k' (List.mem_range.mp hk) (List.mem_range.mp hk') (e1.symm.trans e2))
  have hsub : Lall ⊆ triPairs (L.rdim b) := by
    intro p hp
    rw [hLall, List.mem_flatMap] at hp
    obtain ⟨k, hk, hp⟩ := hp
    have := hc.pairs k (List.mem_range.mp hk) p hp
    exact (mem_triPairs _ p).mpr ⟨this.1, this.2.1⟩
  have hlen : Lall.length = (triPairs (L.rdim b)).length := by
    have h1 := hc.count
    have h2 := triPairs_length (L.rdim b)
    rw [hLall, List.length_flatMap]
    have h3 : ((List.range (L.nCls b)).map fun k => (L.clsPairs b k).length).foldr Nat.add 0 =
        ((List.range (L.nCls b)).map fun k => (L.clsPairs b k).length).sum := rfl
    rw [h3, shr_eq] at h1
    show ((List.range (L.nCls b)).map fun k => (L.clsPairs b k).length).sum = _
    rw [h1]
    show L.rdim b * (L.rdim b + 1) / 2 ^ 1 = _
    omega
  have hperm : Lall.Perm (triPairs (L.rdim b)) :=
    (List.subperm_of_subset hnodup hsub).perm_of_length_le hlen.ge
  rw [← (hperm.map F).sum_eq, hLall, sum_map_flatMap', list_sum_range]

/-! ## Groups -/

theorem grpOk_spec (b : ℕ) (h : L.grpOk b = true) :
    L.glo b 0 = 0 ∧ L.glo b (L.nGrp b) = L.nCls b ∧ ∀ g, g < L.nGrp b → L.glo b g ≤ L.glo b (g + 1) := by
  unfold DegD.grpOk at h
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, List.all_eq_true, List.mem_range] at h
  exact ⟨h.1.1.1, h.1.1.2, fun g hg => h.2 g hg⟩

/-- **The groups split the classes**: `Σ_g Σ_{i < glo (g+1) - glo g} f (glo g + i) = Σ_{k < nCls} f k`. -/
theorem grp_sum {M : Type*} [AddCommMonoid M] (b : ℕ) (h : L.grpOk b = true) (f : ℕ → M) :
    ∑ g ∈ Finset.range (L.nGrp b), ∑ i ∈ Finset.range (L.glo b (g + 1) - L.glo b g), f (L.glo b g + i) =
      ∑ k ∈ Finset.range (L.nCls b), f k := by
  obtain ⟨h0, hN, hmono⟩ := L.grpOk_spec b h
  have key : ∀ G, G ≤ L.nGrp b → ∑ g ∈ Finset.range G, ∑ i ∈ Finset.range (L.glo b (g + 1) - L.glo b g),
      f (L.glo b g + i) = ∑ k ∈ Finset.range (L.glo b G), f k := by
    intro G
    induction G with
    | zero => intro _; rw [h0]; simp
    | succ G ih =>
      intro hG
      rw [Finset.sum_range_succ, ih (by omega)]
      have hm := hmono G (by omega)
      rw [← Finset.sum_range_add_sum_Ico _ hm, Finset.sum_Ico_eq_sum_range]
  rw [key _ le_rfl, hN]

/-! ## Coefficient lists -/

/-- Coefficient of the accumulator `V` at slot `r`. -/
def vCoef (W r : ℕ) (V : ℕ × ℕ × ℕ) : ℤ := (slotAt W V.1 r : ℤ) - slotAt W V.2.1 r

theorem qval_slot (p q den : ℕ) :
    qval (Nat.blt p q, Nat.add (Nat.sub p q) (Nat.sub q p), den) = (((p : ℤ) - q : ℤ) : ℝ) / den := by
  unfold qval
  by_cases h : p < q
  · rw [show Nat.blt p q = true from Nat.blt_eq.mpr h, if_pos rfl]
    rw [show Nat.add (Nat.sub p q) (Nat.sub q p) = q - p by show p - q + (q - p) = q - p; omega]
    rw [Nat.cast_sub h.le]; push_cast; ring
  · rw [show Nat.blt p q = false from Bool.eq_false_iff.mpr (fun h' => h (Nat.blt_eq.mp h')), if_neg (by simp)]
    rw [show Nat.add (Nat.sub p q) (Nat.sub q p) = p - q by show p - q + (q - p) = p - q; omega]
    rw [Nat.cast_sub (not_lt.mp h)]; push_cast; ring

/-- **`eRow` represents the class coefficients.** -/
theorem eRow_sum (W r den : ℕ) (F : ℕ → ℝ) : ∀ (Vs : List (ℕ × ℕ × ℕ)) (k : ℕ),
    ((eRow W r Vs k).map fun e => qval (e.2.1, e.2.2, den) * F e.1).sum =
      ∑ i ∈ Finset.range Vs.length, ((vCoef W r (Vs.getD i (0, 0, 0)) : ℝ) / den) * F (k + i)
  | [], _ => by simp [eRow]
  | V :: Vs, k => by
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    have ih := eRow_sum W r den F Vs (k + 1)
    have hE : eRow W r (V :: Vs) k = cond (Nat.beq (slotAt W V.1 r) (slotAt W V.2.1 r)) (eRow W r Vs (k + 1))
        ((k, Nat.blt (slotAt W V.1 r) (slotAt W V.2.1 r),
          Nat.add (Nat.sub (slotAt W V.1 r) (slotAt W V.2.1 r)) (Nat.sub (slotAt W V.2.1 r) (slotAt W V.1 r))) ::
          eRow W r Vs (k + 1)) := rfl
    have hsum : ∑ i ∈ Finset.range Vs.length, ((vCoef W r (Vs.getD i (0, 0, 0)) : ℝ) / den) * F (k + 1 + i) =
        ∑ i ∈ Finset.range Vs.length, ((vCoef W r (Vs.getD i (0, 0, 0)) : ℝ) / den) * F (k + (i + 1)) := by
      apply Finset.sum_congr rfl; intro i _; rw [show k + 1 + i = k + (i + 1) by ring]
    rw [hE]
    by_cases hpq : slotAt W V.1 r = slotAt W V.2.1 r
    · rw [show Nat.beq (slotAt W V.1 r) (slotAt W V.2.1 r) = true from by rw [hpq]; exact Nat.beq_refl _, cond_true]
      have h0 : (vCoef W r V : ℝ) = 0 := by unfold vCoef; rw [hpq]; simp
      rw [ih, hsum, h0, zero_div, zero_mul, add_zero]
    · rw [show Nat.beq (slotAt W V.1 r) (slotAt W V.2.1 r) = false from
        Bool.eq_false_iff.mpr (fun h' => hpq (Nat.eq_of_beq_eq_true h')), cond_false]
      simp only [List.map_cons, List.sum_cons]
      rw [qval_slot, ih, hsum, add_zero, add_comm]
      unfold vCoef
      push_cast
      ring

theorem eMatch_spec (W r : ℕ) : ∀ (Vs : List (ℕ × ℕ × ℕ)) (k : ℕ) (E : List (ℕ × Bool × ℕ)),
    eMatch W r Vs k E = true → E = eRow W r Vs k
  | [], _, E, h => by
    cases E with
    | nil => rfl
    | cons _ _ => exact absurd h (by simp [eMatch])
  | V :: Vs, k, E, h => by
    have h' : (fun p n => cond (Nat.beq p n) (eMatch W r Vs (Nat.add k 1) E)
        (List.casesOn (motive := fun _ => Bool) E false (fun e E' =>
          Nat.beq e.1 k && cond e.2.1 (Nat.blt p n) (!(Nat.blt p n)) &&
            Nat.beq e.2.2 (Nat.add (Nat.sub p n) (Nat.sub n p)) && eMatch W r Vs (Nat.add k 1) E')))
        (slotAt W V.1 r) (slotAt W V.2.1 r) = true := h
    dsimp only at h'
    unfold eRow
    by_cases hpq : slotAt W V.1 r = slotAt W V.2.1 r
    · rw [show Nat.beq (slotAt W V.1 r) (slotAt W V.2.1 r) = true from by rw [hpq]; exact Nat.beq_refl _,
        cond_true] at h' ⊢
      exact eMatch_spec W r Vs _ E h'
    · rw [show Nat.beq (slotAt W V.1 r) (slotAt W V.2.1 r) = false from
        Bool.eq_false_iff.mpr (fun h'' => hpq (Nat.eq_of_beq_eq_true h'')), cond_false] at h' ⊢
      cases E with
      | nil => exact absurd h' (by simp)
      | cons e E' =>
        simp only [Bool.and_eq_true, Nat.beq_eq] at h'
        obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h'
        rw [eMatch_spec W r Vs _ E' h4]
        obtain ⟨k', s, m⟩ := e
        simp only at h1 h2 h3
        subst h1; subst h3
        have hs : s = Nat.blt (slotAt W V.1 r) (slotAt W V.2.1 r) := by
          cases s <;> cases hb : Nat.blt (slotAt W V.1 r) (slotAt W V.2.1 r) <;> simp_all
        rw [hs]

theorem vTab_getD (P PP : List (List (T3 × Bool × ℕ))) (W b g i : ℕ)
    (hi : i < L.glo b (g + 1) - L.glo b g) :
    (L.vTab P PP W b g).getD i (0, 0, 0) = L.clsAcc P PP W b (L.clsKey b (L.glo b g + i)) := by
  unfold DegD.vTab
  rw [← listAt_eq]
  have hi' : i < Nat.sub (L.glo b (Nat.add g 1)) (L.glo b g) := hi
  rw [listAt_mkList _ _ hi']
  simp only [Nat.add_eq]

theorem vTab_length (P PP : List (List (T3 × Bool × ℕ))) (W b g : ℕ) :
    (L.vTab P PP W b g).length = L.glo b (g + 1) - L.glo b g := by
  unfold DegD.vTab; rw [mkList_eq, List.length_map, List.length_range]; rfl

/-- **The coefficient lists are the class coefficients.** -/
theorem eOk_spec (P PP : List (List (T3 × Bool × ℕ))) (W b g r0 r1 : ℕ) (h : L.eOk P PP W b g r0 r1 = true)
    (r : ℕ) (h0 : r0 ≤ r) (h1 : r < r1) (hr : r < L.nc) :
    (L.eTab (32 * b + g)).getD r [] = eRow W r (L.vTab P PP W b g) (L.glo b g) ∧
      ∀ V ∈ L.vTab P PP W b g, V.2.2 < 2 ^ W := by
  unfold DegD.eOk at h
  dsimp only at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨?_, fun V hV => by simpa [Nat.shiftLeft_eq, shl_eq] using h.1 V hV⟩
  have hw := walkP_specD _ r0 r1 [] _ 0 h.2 r (by rw [eTab_length]; exact hr) (by omega) (by omega)
  rw [Nat.zero_add] at hw
  exact eMatch_spec W r _ _ _ (by simpa [Nat.add_eq, Nat.mul_eq] using hw)

end DegD

end ThomsonCompact.CoeffMap.Deg
