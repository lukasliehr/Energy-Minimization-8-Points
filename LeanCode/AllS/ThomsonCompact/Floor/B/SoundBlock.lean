import ThomsonCompact.Floor.B.SoundRowT

/-!
# Block leaf: exact channel-packed congruence (F3b)

The two stages of `blockOk` are exact linear combinations of the packed row payloads (`ckPack`): every
accumulator is a combination `IsComb` with signed coefficients `s` (the congruence coefficients `Tz_pq`) and
absolute coefficients `a` (bounds for `|Tz_pq|`, used for the error part and the overflow checks).
-/

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Packed
open ThomsonCompact.Floor (mask slot)
open scoped BigOperators

/-! ## Combinations of payloads -/

/-- `x` is the combination of the payloads `X i` (`i < nr`, each with `Q = 0`) with signed coefficients `s` and
absolute coefficients `a` -/
structure IsComb (nr : ℕ) (X : ℕ → PAcc) (x : PAcc) (s : ℕ → ℤ) (a : ℕ → ℕ) : Prop where
  ex : ∃ ap an : ℕ → ℕ, (∀ i, (ap i : ℤ) - an i = s i) ∧ (∀ i, ap i + an i = a i) ∧
    x.P = ∑ i ∈ Finset.range nr, ap i * (X i).P ∧ x.Q = ∑ i ∈ Finset.range nr, an i * (X i).P
  E : x.E = ∑ i ∈ Finset.range nr, a i * (X i).E
  H : x.H = ∑ i ∈ Finset.range nr, a i * (X i).H
  A : x.A = ∑ i ∈ Finset.range nr, a i

theorem IsComb.zero (nr : ℕ) (X : ℕ → PAcc) : IsComb nr X PAcc.zero (fun _ => 0) (fun _ => 0) :=
  ⟨⟨fun _ => 0, fun _ => 0, fun _ => by simp, fun _ => by simp, by simp [PAcc.zero], by simp [PAcc.zero]⟩,
    by simp [PAcc.zero], by simp [PAcc.zero], by simp [PAcc.zero]⟩

theorem IsComb.addm {nr : ℕ} {X : ℕ → PAcc} {acc x : PAcc} {s1 s2 : ℕ → ℤ} {a1 a2 : ℕ → ℕ}
    (h1 : IsComb nr X acc s1 a1) (h2 : IsComb nr X x s2 a2) (ng : Bool) (n : ℕ) :
    IsComb nr X (acc.addm ng n x) (fun i => s1 i + sv (ng, n) * s2 i) (fun i => a1 i + n * a2 i) := by
  obtain ⟨ap1, an1, hs1, ha1, hP1, hQ1⟩ := h1.ex
  obtain ⟨ap2, an2, hs2, ha2, hP2, hQ2⟩ := h2.ex
  refine ⟨⟨fun i => ap1 i + n * (cond ng (an2 i) (ap2 i)), fun i => an1 i + n * (cond ng (ap2 i) (an2 i)),
    fun i => ?_, fun i => ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [← hs1 i, ← hs2 i]; unfold sv; cases ng <;> simp <;> ring
  · rw [← ha1 i, ← ha2 i]; cases ng <;> simp <;> ring
  · show acc.P + n * cond ng x.Q x.P = _
    rw [hP1, hQ2, hP2]
    cases ng <;> simp [Finset.mul_sum, ← Finset.sum_add_distrib, add_mul, mul_assoc]
  · show acc.Q + n * cond ng x.P x.Q = _
    rw [hQ1, hQ2, hP2]
    cases ng <;> simp [Finset.mul_sum, ← Finset.sum_add_distrib, add_mul, mul_assoc]
  · show acc.E + n * x.E = _
    rw [h1.E, h2.E, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  · show acc.H + n * x.H = _
    rw [h1.H, h2.H, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro i _; ring
  · show acc.A + n * x.A = _
    rw [h1.A, h2.A, Finset.mul_sum, ← Finset.sum_add_distrib]

/-- folding `addm` over a list of terms -/
theorem IsComb.foldl {β : Type*} {nr : ℕ} {X : ℕ → PAcc} (cf : β → Bool × ℕ) (vf : β → PAcc)
    (sf : β → ℕ → ℤ) (af : β → ℕ → ℕ) : ∀ (l : List β) (acc : PAcc) (s0 : ℕ → ℤ) (a0 : ℕ → ℕ),
    IsComb nr X acc s0 a0 → (∀ x ∈ l, IsComb nr X (vf x) (sf x) (af x)) →
    IsComb nr X (l.foldl (fun acc x => acc.addm (cf x).1 (cf x).2 (vf x)) acc)
      (fun i => s0 i + (l.map fun x => sv (cf x) * sf x i).sum) (fun i => a0 i + (l.map fun x => (cf x).2 * af x i).sum)
  | [], acc, s0, a0, h, _ => by simpa using h
  | x :: l, acc, s0, a0, h, hl => by
    have h1 := h.addm (hl x (by simp)) (cf x).1 (cf x).2
    have h2 := IsComb.foldl cf vf sf af l _ _ _ h1 (fun y hy => hl y (List.mem_cons_of_mem _ hy))
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    convert h2 using 2 <;> ring

/-! ## Payloads -/

/-- one step of the packing fold of `ckPack` -/
def ckStep (LB LE : ℕ) (T : ℕ → TM) (i : ℕ) (a : ℕ × ℕ × Bool × ℕ × ℕ) : ℕ × ℕ × Bool × ℕ × ℕ :=
  (Nat.add (T i).v (Nat.shiftLeft a.1 LB), Nat.add (T i).e (Nat.shiftLeft a.2.1 LE), and (T i).ok a.2.2.1,
    Nat.max (T i).e a.2.2.2.1, Nat.max (T i).s a.2.2.2.2)

theorem ckStep_foldr_succ (LB LE : ℕ) (T : ℕ → TM) (n : ℕ) (init : ℕ × ℕ × Bool × ℕ × ℕ) :
    (List.range (n + 1)).foldr (ckStep LB LE T) init =
      ckStep LB LE T 0 ((List.range n).foldr (ckStep LB LE (fun i => T (i + 1))) init) := by
  rw [List.range_succ_eq_map, List.foldr_cons, List.foldr_map]
  rfl

theorem ckPack_fold (LB LE : ℕ) : ∀ (n : ℕ) (T : ℕ → TM),
    ((List.range n).foldr (ckStep LB LE T) (0, 0, true, 0, 0)).1 = ∑ i ∈ Finset.range n, (T i).v * 2 ^ (LB * i) ∧
    ((List.range n).foldr (ckStep LB LE T) (0, 0, true, 0, 0)).2.1 = ∑ i ∈ Finset.range n, (T i).e * 2 ^ (LE * i) ∧
    (((List.range n).foldr (ckStep LB LE T) (0, 0, true, 0, 0)).2.2.1 = true → ∀ i < n, (T i).ok = true) ∧
    (∀ i < n, (T i).e ≤ ((List.range n).foldr (ckStep LB LE T) (0, 0, true, 0, 0)).2.2.2.1) ∧
    (∀ i < n, (T i).s ≤ ((List.range n).foldr (ckStep LB LE T) (0, 0, true, 0, 0)).2.2.2.2)
  | 0, T => by simp
  | n + 1, T => by
    obtain ⟨h1, h2, h3, h4, h5⟩ := ckPack_fold LB LE n (fun i => T (i + 1))
    rw [ckStep_foldr_succ]
    set R := (List.range n).foldr (ckStep LB LE (fun i => T (i + 1))) (0, 0, true, 0, 0) with hR
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show (T 0).v + R.1 <<< LB = _
      rw [h1, Finset.sum_range_succ', Nat.shiftLeft_eq, Finset.sum_mul, add_comm]
      congr 1
      · apply Finset.sum_congr rfl; intro i _; rw [mul_assoc, ← pow_add]; congr 2
      · simp
    · show (T 0).e + R.2.1 <<< LE = _
      rw [h2, Finset.sum_range_succ', Nat.shiftLeft_eq, Finset.sum_mul, add_comm]
      congr 1
      · apply Finset.sum_congr rfl; intro i _; rw [mul_assoc, ← pow_add]; congr 2
      · simp
    · intro h i hi
      have h' : ((T 0).ok && R.2.2.1) = true := h
      rw [Bool.and_eq_true] at h'
      rcases i with _ | i
      · exact h'.1
      · exact h3 h'.2 i (by omega)
    · intro i hi
      rcases i with _ | i
      · exact Nat.le_max_left _ _
      · exact le_trans (h4 i (by omega)) (Nat.le_max_right _ _)
    · intro i hi
      rcases i with _ | i
      · exact Nat.le_max_left _ _
      · exact le_trans (h5 i (by omega)) (Nat.le_max_right _ _)

/-- the payload of a row: packed checkpoint values and errors of the channels `ch0 …` -/
theorem ckPack_spec (c : Ctx) (Kc wv we LB LE : ℕ) (ck : CkRow) (ch0 nch : ℕ) :
    (ckPack c Kc wv we LB LE ck ch0 nch).1.P =
      ∑ i ∈ Finset.range nch, (ck.tm c Kc wv we (ch0 + i)).v * 2 ^ (LB * i) ∧
    (ckPack c Kc wv we LB LE ck ch0 nch).1.Q = 0 ∧
    (ckPack c Kc wv we LB LE ck ch0 nch).1.E =
      ∑ i ∈ Finset.range nch, (ck.tm c Kc wv we (ch0 + i)).e * 2 ^ (LE * i) ∧
    (ckPack c Kc wv we LB LE ck ch0 nch).1.H = ck.Ej ∧ (ckPack c Kc wv we LB LE ck ch0 nch).1.A = 1 ∧
    ((ckPack c Kc wv we LB LE ck ch0 nch).2.1 = true → ∀ i < nch, (ck.tm c Kc wv we (ch0 + i)).ok = true) ∧
    (∀ i < nch, (ck.tm c Kc wv we (ch0 + i)).e ≤ (ckPack c Kc wv we LB LE ck ch0 nch).2.2.1) ∧
    (∀ i < nch, (ck.tm c Kc wv we (ch0 + i)).s ≤ (ckPack c Kc wv we LB LE ck ch0 nch).2.2.2) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := ckPack_fold LB LE nch (fun i => ck.tm c Kc wv we (ch0 + i))
  exact ⟨h1, rfl, h2, rfl, rfl, h3, h4, h5⟩

/-! ## Touch lists and the two stages -/

theorem sum_filterMap_range {β M : Type*} [AddCommMonoid M] (F : ℕ → Option β) (G : β → M) : ∀ n,
    (((List.range n).filterMap F).map G).sum =
      ∑ i ∈ Finset.range n, (match F i with | some y => G y | none => 0)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.filterMap_append, List.map_append, List.sum_append, sum_filterMap_range F G n,
      Finset.sum_range_succ]
    congr 1
    rcases h : F n with _ | y <;> simp [List.filterMap, h]

/-- the touch list of `u` as row indices -/
def touchIdx (uI vI : ℕ → ℕ) (nr u : ℕ) : List (ℕ × ℕ) :=
  (List.range nr).filterMap fun i => cond (Nat.beq (uI i) u) (some (vI i, i))
    (cond (and (Nat.beq (vI i) u) (Bool.not (Nat.beq (uI i) u))) (some (uI i, i)) none)

theorem touchV_eq {α : Type} (uI vI : ℕ → ℕ) (X : ℕ → α) (nr u : ℕ) :
    touchV ((List.range nr).map fun i => ((uI i, vI i), X i)) u =
      (touchIdx uI vI nr u).map fun x => (x.1, X x.2) := by
  unfold touchV touchIdx
  rw [List.filterMap_map, List.map_filterMap]
  apply List.filterMap_congr
  intro i _
  simp only [Function.comp_apply]
  cases Nat.beq (uI i) u <;> cases Nat.beq (vI i) u <;> rfl

/-- `Zi_pu` as a signed integer -/
def zv (wz zr u : ℕ) : ℤ := sv (zsm wz zr u)

/-- stage-1 coefficients of row `i` in `Y_u` -/
def sY (uI vI : ℕ → ℕ) (wz zq u i : ℕ) : ℤ :=
  (if uI i = u then zv wz zq (vI i) else 0) + (if vI i = u ∧ uI i ≠ u then zv wz zq (uI i) else 0)

def aY (uI vI : ℕ → ℕ) (wz zq u i : ℕ) : ℕ :=
  (if uI i = u then (zsm wz zq (vI i)).2 else 0) + (if vI i = u ∧ uI i ≠ u then (zsm wz zq (uI i)).2 else 0)

theorem isComb_delta (nr : ℕ) (X : ℕ → PAcc) (hQ : ∀ i, (X i).Q = 0) (hA : ∀ i, (X i).A = 1) (i : ℕ) (hi : i < nr) :
    IsComb nr X (X i) (fun i' => if i' = i then 1 else 0) (fun i' => if i' = i then 1 else 0) := by
  refine ⟨⟨fun i' => if i' = i then 1 else 0, fun _ => 0, fun i' => by by_cases h : i' = i <;> simp [h], fun i' => by simp, ?_, ?_⟩,
    ?_, ?_, ?_⟩
  · simp only [ite_mul, one_mul, zero_mul]; rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr hi)]
  · rw [hQ i]; simp
  · simp only [ite_mul, one_mul, zero_mul]; rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr hi)]
  · simp only [ite_mul, one_mul, zero_mul]; rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr hi)]
  · rw [hA i, Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr hi)]

/-- **Stage 1**: `Y_u` is the combination with coefficients `sY`, `aY` -/
theorem stage1_comb (nr : ℕ) (X : ℕ → PAcc) (hQ : ∀ i, (X i).Q = 0) (hA : ∀ i, (X i).A = 1)
    (uI vI : ℕ → ℕ) (wz zq u : ℕ) :
    IsComb nr X (((touchIdx uI vI nr u).map fun x => (x.1, X x.2)).foldl
        (fun acc x => let z := zsm wz zq x.1; acc.addm z.1 z.2 x.2) PAcc.zero)
      (fun i => if i < nr then sY uI vI wz zq u i else 0) (fun i => if i < nr then aY uI vI wz zq u i else 0) := by
  rw [List.foldl_map]
  have h := IsComb.foldl (nr := nr) (X := X) (fun x : ℕ × ℕ => zsm wz zq x.1) (fun x => X x.2)
    (fun x i' => if i' = x.2 then 1 else 0) (fun x i' => if i' = x.2 then 1 else 0) (touchIdx uI vI nr u)
    PAcc.zero (fun _ => 0) (fun _ => 0) (IsComb.zero nr X) (by
      intro x hx
      unfold touchIdx at hx
      obtain ⟨i, hi, hx⟩ := List.mem_filterMap.mp hx
      have hi' := List.mem_range.mp hi
      have : x.2 = i := by
        revert hx; cases Nat.beq (uI i) u <;> cases Nat.beq (vI i) u <;> simp <;> intro h <;> rw [← h]
      rw [this]
      exact isComb_delta nr X hQ hA i hi')
  convert h using 2 with i i
  · rw [zero_add]
    unfold touchIdx
    rw [sum_filterMap_range]
    by_cases hi : i < nr
    · rw [if_pos hi, Finset.sum_eq_single i]
      · unfold sY zv
        by_cases h1 : uI i = u
        · simp [h1, Nat.beq_refl]
        · have h1' : Nat.beq (uI i) u = false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
          by_cases h2 : vI i = u
          · simp [h1, h1', h2, Nat.beq_refl]
          · have h2' : Nat.beq (vI i) u = false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
            simp [h1, h1', h2, h2']
      · intro b _ hb
        cases Nat.beq (uI b) u <;> cases Nat.beq (vI b) u <;> simp [Ne.symm hb]
      · intro h; exact absurd (Finset.mem_range.mpr hi) h
    · rw [if_neg hi]
      symm
      apply Finset.sum_eq_zero
      intro b hb
      have : b ≠ i := by have := Finset.mem_range.mp hb; omega
      cases Nat.beq (uI b) u <;> cases Nat.beq (vI b) u <;> simp [Ne.symm this]
  · rw [zero_add]
    unfold touchIdx
    rw [sum_filterMap_range]
    by_cases hi : i < nr
    · rw [if_pos hi, Finset.sum_eq_single i]
      · unfold aY
        by_cases h1 : uI i = u
        · simp [h1, Nat.beq_refl]
        · have h1' : Nat.beq (uI i) u = false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
          by_cases h2 : vI i = u
          · simp [h1, h1', h2, Nat.beq_refl]
          · have h2' : Nat.beq (vI i) u = false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
            simp [h1, h1', h2, h2']
      · intro b _ hb
        cases Nat.beq (uI b) u <;> cases Nat.beq (vI b) u <;> simp [Ne.symm hb]
      · intro h; exact absurd (Finset.mem_range.mpr hi) h
    · rw [if_neg hi]
      symm
      apply Finset.sum_eq_zero
      intro b hb
      have : b ≠ i := by have := Finset.mem_range.mp hb; omega
      cases Nat.beq (uI b) u <;> cases Nat.beq (vI b) u <;> simp [Ne.symm this]

/-- congruence coefficient of row `i` in `G_pq`: `Zi_p,u Zi_q,v + [u ≠ v] Zi_p,v Zi_q,u` -/
def sG (uI vI : ℕ → ℕ) (wz zp zq i : ℕ) : ℤ :=
  zv wz zp (uI i) * zv wz zq (vI i) + (if uI i ≠ vI i then zv wz zp (vI i) * zv wz zq (uI i) else 0)

def aG (uI vI : ℕ → ℕ) (wz zp zq i : ℕ) : ℕ :=
  (zsm wz zp (uI i)).2 * (zsm wz zq (vI i)).2 +
    (if uI i ≠ vI i then (zsm wz zp (vI i)).2 * (zsm wz zq (uI i)).2 else 0)

theorem stage1_eq (uI vI : ℕ → ℕ) (X : ℕ → PAcc) (nr n wz zq : ℕ) :
    stage1 wz zq ((List.range n).map (touchV ((List.range nr).map fun i => ((uI i, vI i), X i)))) =
      (List.range n).map fun u => ((touchIdx uI vI nr u).map fun x => (x.1, X x.2)).foldl
        (fun acc x => let z := zsm wz zq x.1; acc.addm z.1 z.2 x.2) PAcc.zero := by
  unfold stage1
  rw [List.map_map]
  apply List.map_congr_left
  intro u _
  simp only [Function.comp_apply, touchV_eq]

/-- **Stage 2**: `G_pq` is the combination with the congruence coefficients `sG` (and `aG`) -/
theorem stage2_comb (nr : ℕ) (X : ℕ → PAcc) (hQ : ∀ i, (X i).Q = 0) (hA : ∀ i, (X i).A = 1)
    (uI vI : ℕ → ℕ) (n wz zp zq : ℕ) (huv : ∀ i < nr, uI i < n ∧ vI i < n) :
    IsComb nr X (stage2 wz zp (stage1 wz zq ((List.range n).map (touchV ((List.range nr).map fun i =>
        ((uI i, vI i), X i))))))
      (fun i => if i < nr then sG uI vI wz zp zq i else 0) (fun i => if i < nr then aG uI vI wz zp zq i else 0) := by
  rw [stage1_eq]
  set Yu := fun u => ((touchIdx uI vI nr u).map fun x => (x.1, X x.2)).foldl
    (fun acc x => let z := zsm wz zq x.1; acc.addm z.1 z.2 x.2) PAcc.zero with hYu
  have hzip : ((List.range n).map Yu).zip (List.range ((List.range n).map Yu).length) =
      (List.range n).map fun u => (Yu u, u) := by
    apply List.ext_getElem (by simp)
    intro k h1 h2
    simp
  unfold stage2
  rw [hzip]
  have h := IsComb.foldl (nr := nr) (X := X) (fun x : PAcc × ℕ => zsm wz zp x.2) (fun x => x.1)
    (fun x i => if i < nr then sY uI vI wz zq x.2 i else 0) (fun x i => if i < nr then aY uI vI wz zq x.2 i else 0)
    ((List.range n).map fun u => (Yu u, u)) PAcc.zero (fun _ => 0) (fun _ => 0) (IsComb.zero nr X) (by
      intro x hx
      obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx
      exact stage1_comb nr X hQ hA uI vI wz zq u)
  convert h using 2 with i i
  · rw [zero_add, List.map_map, list_sum_range']
    simp only [Function.comp_apply]
    by_cases hi : i < nr
    · obtain ⟨hu, hv⟩ := huv i hi
      simp only [hi, if_true]
      unfold sY sG
      simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, ite_and]
      rw [Finset.sum_ite_eq, Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr hu), if_pos (Finset.mem_range.mpr hv)]
      unfold zv
      by_cases huv' : uI i = vI i
      · simp [huv']
      · simp [huv', Ne.symm huv', mul_comm]
    · simp [hi]
  · rw [zero_add, List.map_map, list_sum_range']
    simp only [Function.comp_apply]
    by_cases hi : i < nr
    · obtain ⟨hu, hv⟩ := huv i hi
      simp only [hi, if_true]
      unfold aY aG
      simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, ite_and]
      try rw [Finset.sum_ite_eq, Finset.sum_ite_eq, if_pos (Finset.mem_range.mpr hu), if_pos (Finset.mem_range.mpr hv)]
    · simp [hi]

/-! ## Per-channel extraction -/

theorem ofDigits_range (b : ℕ) (d : ℕ → ℕ) : ∀ n,
    Nat.ofDigits b ((List.range n).map d) = ∑ c ∈ Finset.range n, d c * b ^ c
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ_eq_map, List.map_cons, Nat.ofDigits_cons, List.map_map, ofDigits_range b (d ∘ Nat.succ) n,
      Finset.sum_range_succ', Finset.mul_sum]
    simp only [Function.comp_apply, pow_zero, mul_one, pow_succ]
    rw [add_comm]; congr 1; apply Finset.sum_congr rfl; intro c _; ring

theorem slot_packed {LB : ℕ} (hLB : 0 < LB) (nch nr : ℕ) (cf : ℕ → ℕ) (v : ℕ → ℕ → ℕ)
    (hb : ∀ c < nch, ∑ i ∈ Finset.range nr, cf i * v i c < 2 ^ LB) (ch : ℕ) (hch : ch < nch) :
    slot LB (∑ i ∈ Finset.range nr, cf i * ∑ c ∈ Finset.range nch, v i c * 2 ^ (LB * c)) ch =
      ∑ i ∈ Finset.range nr, cf i * v i ch := by
  have e : ∑ i ∈ Finset.range nr, cf i * ∑ c ∈ Finset.range nch, v i c * 2 ^ (LB * c) =
      Nat.ofDigits (2 ^ LB) ((List.range nch).map fun c => ∑ i ∈ Finset.range nr, cf i * v i c) := by
    rw [ofDigits_range]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro c _; apply Finset.sum_congr rfl; intro i _
    rw [← pow_mul]; ring
  rw [e, slot_ofDigits hLB]
  · rw [getD_of_lt _ _ (by simp [hch])]; simp
  · intro d hd
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd
    exact hb c (List.mem_range.mp hc)

theorem IsComb.natAbs_le {nr : ℕ} {X : ℕ → PAcc} {x : PAcc} {s : ℕ → ℤ} {a : ℕ → ℕ} (h : IsComb nr X x s a) (i : ℕ) :
    (s i).natAbs ≤ a i := by
  obtain ⟨ap, an, hs, ha, _, _⟩ := h.ex
  have h1 : ((s i).natAbs : ℤ) ≤ a i := by
    rw [Int.natCast_natAbs, ← hs i, ← ha i]; push_cast
    rw [_root_.abs_le]; constructor <;> linarith [Int.natCast_nonneg (ap i), Int.natCast_nonneg (an i)]
  exact_mod_cast h1

variable {N S B W : ℕ}

/-- **One pair `(p, q)`, one channel**: the kernel's `zfin` of the slots of `G_pq` encloses
`2^-FG Σ_i s_i f_i,ch` -/
theorem pair_encl (hg : Good N S B W) {FG : ℕ} (hF : FG + 1 ≤ W)
    (nr nch LB LE : ℕ) (hLB : 0 < LB) (hLE : 0 < LE) (X : ℕ → PAcc) (T : ℕ → ℕ → TM) (f : ℕ → ℕ → ℝ → ℝ)
    (hXP : ∀ i, (X i).P = ∑ c ∈ Finset.range nch, (T i c).v * 2 ^ (LB * c))
    (hXE : ∀ i, (X i).E = ∑ c ∈ Finset.range nch, (T i c).e * 2 ^ (LE * c))
    (hT : ∀ i < nr, ∀ c < nch, Encl (mkCtx N S B W) (T i c) (f i c))
    (G : PAcc) (s : ℕ → ℤ) (a : ℕ → ℕ) (hG : IsComb nr X G s a)
    (smax emax : ℕ) (hs : ∀ i < nr, ∀ c < nch, (T i c).s ≤ smax) (he : ∀ i < nr, ∀ c < nch, (T i c).e ≤ emax)
    (hovB : G.A * 2 ^ (W * (2 * N + 1)) < 2 ^ LB) (hovE : G.A * emax < 2 ^ LE)
    (okV : Bool) (ch : ℕ) (hch : ch < nch)
    (hok : (zfin (mkCtx N S B W) FG (slot LB G.P ch, slot LB G.Q ch, Nat.mul G.A smax, slot LE G.E ch, okV)).ok = true) :
    Encl (mkCtx N S B W) (zfin (mkCtx N S B W) FG (slot LB G.P ch, slot LB G.Q ch, Nat.mul G.A smax, slot LE G.E ch, okV))
      (fun t => (∑ i ∈ Finset.range nr, (s i : ℝ) * f i ch t) / 2 ^ FG) := by
  obtain ⟨ap, an, hs', ha', hP, hQ⟩ := hG.ex
  have hvK : ∀ i < nr, ∀ c < nch, (T i c).v < 2 ^ (W * (2 * N + 1)) := fun i hi c hc => by
    obtain ⟨_, _, hR, _⟩ := hT i hi c hc; exact hR.v_lt
  have hA := hG.A
  have hbnd : ∀ (cf : ℕ → ℕ), (∀ i, cf i ≤ a i) → ∀ c < nch,
      ∑ i ∈ Finset.range nr, cf i * (T i c).v < 2 ^ LB := by
    intro cf hcf c hc
    calc ∑ i ∈ Finset.range nr, cf i * (T i c).v ≤ ∑ i ∈ Finset.range nr, a i * 2 ^ (W * (2 * N + 1)) :=
          Finset.sum_le_sum (fun i hi => Nat.mul_le_mul (hcf i) (hvK i (Finset.mem_range.mp hi) c hc).le)
      _ = G.A * 2 ^ (W * (2 * N + 1)) := by rw [hA, Finset.sum_mul]
      _ < 2 ^ LB := hovB
  have hPs : slot LB G.P ch = ∑ i ∈ Finset.range nr, ap i * (T i ch).v := by
    rw [hP, Finset.sum_congr rfl (fun i _ => by rw [hXP i])]
    exact slot_packed hLB nch nr ap (fun i c => (T i c).v) (hbnd ap (fun i => by rw [← ha' i]; omega)) ch hch
  have hQs : slot LB G.Q ch = ∑ i ∈ Finset.range nr, an i * (T i ch).v := by
    rw [hQ, Finset.sum_congr rfl (fun i _ => by rw [hXP i])]
    exact slot_packed hLB nch nr an (fun i c => (T i c).v) (hbnd an (fun i => by rw [← ha' i]; omega)) ch hch
  have hEs : slot LE G.E ch = ∑ i ∈ Finset.range nr, a i * (T i ch).e := by
    rw [hG.E, Finset.sum_congr rfl (fun i _ => by rw [hXE i])]
    refine slot_packed hLE nch nr a (fun i c => (T i c).e) (fun c hc => ?_) ch hch
    calc ∑ i ∈ Finset.range nr, a i * (T i c).e ≤ ∑ i ∈ Finset.range nr, a i * emax :=
          Finset.sum_le_sum (fun i hi => Nat.mul_le_mul_left _ (he i (Finset.mem_range.mp hi) c hc))
      _ = G.A * emax := by rw [hA, Finset.sum_mul]
      _ < 2 ^ LE := hovE
  set L : List (ℤ × TM × (ℝ → ℝ)) := (List.range nr).map fun i => (s i, T i ch, f i ch) with hL
  have hz := zfin_sound hg hF L (by
      intro x hx; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx; exact hT i (List.mem_range.mp hi) ch hch)
    (slot LB G.P ch) (slot LB G.Q ch) (Nat.mul G.A smax) (slot LE G.E ch) okV
    (by
      rw [hPs, hQs, hL, List.map_map, list_sum_range']
      push_cast
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i _
      simp only [Function.comp_apply]
      rw [← hs' i]; ring)
    (by
      rw [hL, List.map_map, list_sum_range']
      show _ ≤ G.A * smax
      rw [hA, Finset.sum_mul]
      apply Finset.sum_le_sum; intro i hi
      exact Nat.mul_le_mul (hG.natAbs_le i) (hs i (Finset.mem_range.mp hi) ch hch))
    (by
      rw [hL, List.map_map, list_sum_range', hEs]
      apply Finset.sum_le_sum; intro i _
      exact Nat.mul_le_mul_right _ (hG.natAbs_le i))
    hok
  refine hz.congr (fun t _ => ?_)
  rw [hL, List.map_map, list_sum_range']
  rfl

/-! ## The double fold of `blockOk` -/

/-- the packed row-sum increment of `rsAdd` -/
def rsT (LS p q t : ℕ) (w : List ℕ) : ℕ :=
  t * w.getD q 0 * 2 ^ (LS * p) + (if p = q then 0 else t * w.getD p 0 * 2 ^ (LS * q))

theorem rsAdd_eq (LS p q t : ℕ) (w : List ℕ) (acc : ℕ) : rsAdd LS p q t w acc = acc + rsT LS p q t w := by
  unfold rsAdd rsT
  show acc + (t * w.getD q 0) <<< (LS * p) + cond (Nat.beq p q) 0 ((t * w.getD p 0) <<< (LS * q)) = _
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  by_cases h : p = q
  · subst h; rw [Nat.beq_refl]; simp
  · rw [Bool.eq_false_iff.mpr (fun h' => h (Nat.eq_of_beq_eq_true h'))]; simp [h]; ring

/-- the channel TMs of a pair -/
noncomputable def bTs (c : Ctx) (FG LB LE nch smax : ℕ) (okV : Bool) (G : PAcc) : List TM :=
  (List.range nch).map fun ch => zfin c FG (slot LB G.P ch, slot LB G.Q ch, Nat.mul G.A smax, slot LE G.E ch, okV)

/-- the state update of one pair `p ≤ q` -/
noncomputable def bupd (c : Ctx) (FG LB LE LS ch0 nch smax : ℕ) (okV : Bool) (ws : ℕ → List ℕ) (wE : List ℕ)
    (p q : ℕ) (G : PAcc) (st : List ℕ × ℕ × Bool × ℕ) : List ℕ × ℕ × Bool × ℕ :=
  ((st.1.zip ((bTs c FG LB LE nch smax okV G).zip (List.range nch))).map fun x =>
      rsAdd LS p q (range x.2.1) (ws (Nat.add ch0 x.2.2)) x.1,
    rsAdd LS p q (Packed.cdiv 64 G.H) wE st.2.1,
    and st.2.2.1 ((bTs c FG LB LE nch smax okV G).all fun T => T.ok), Nat.max st.2.2.2 G.A)

theorem bupd_spec (c : Ctx) (FG LB LE LS ch0 nch smax : ℕ) (okV : Bool) (ws : ℕ → List ℕ) (wE : List ℕ)
    (p q : ℕ) (G : PAcc) (st : List ℕ × ℕ × Bool × ℕ) (hst : st.1.length = nch) :
    (bupd c FG LB LE LS ch0 nch smax okV ws wE p q G st).1.length = nch ∧
    (∀ ch < nch, (bupd c FG LB LE LS ch0 nch smax okV ws wE p q G st).1.getD ch 0 =
      st.1.getD ch 0 + rsT LS p q (range ((bTs c FG LB LE nch smax okV G).getD ch zeroTM)) (ws (ch0 + ch))) ∧
    (bupd c FG LB LE LS ch0 nch smax okV ws wE p q G st).2.1 = st.2.1 + rsT LS p q (Packed.cdiv 64 G.H) wE ∧
    ((bupd c FG LB LE LS ch0 nch smax okV ws wE p q G st).2.2.1 = true →
      st.2.2.1 = true ∧ ∀ ch < nch, ((bTs c FG LB LE nch smax okV G).getD ch zeroTM).ok = true) ∧
    st.2.2.2 ≤ (bupd c FG LB LE LS ch0 nch smax okV ws wE p q G st).2.2.2 ∧
    G.A ≤ (bupd c FG LB LE LS ch0 nch smax okV ws wE p q G st).2.2.2 := by
  have hTl : (bTs c FG LB LE nch smax okV G).length = nch := by simp [bTs]
  refine ⟨by simp [bupd, hst, hTl], fun ch hch => ?_, rsAdd_eq _ _ _ _ _ _, fun h => ?_,
    Nat.le_max_left _ _, Nat.le_max_right _ _⟩
  · unfold bupd
    rw [getD_of_lt _ _ (by simp [hst, hTl, hch])]
    simp only [List.getElem_map, List.getElem_zip, List.getElem_range]
    rw [rsAdd_eq, ← getD_of_lt st.1 0 (by rw [hst]; exact hch),
      ← getD_of_lt (bTs c FG LB LE nch smax okV G) zeroTM (by rw [hTl]; exact hch)]
    rfl
  · have h' : (st.2.2.1 && (bTs c FG LB LE nch smax okV G).all fun T => T.ok) = true := h
    rw [Bool.and_eq_true, List.all_eq_true] at h'
    refine ⟨h'.1, fun ch hch => ?_⟩
    rw [getD_of_lt _ _ (by rw [hTl]; exact hch)]
    exact h'.2 _ (List.getElem_mem _)

/-- the inner fold (over `p`, fixed `q`) -/
theorem inner_spec (c : Ctx) (FG LB LE LS ch0 nch smax : ℕ) (okV : Bool) (ws : ℕ → List ℕ) (wE : List ℕ)
    (wz : ℕ) (Ys : List PAcc) (zq : ℕ × ℕ) : ∀ (l : List (ℕ × ℕ)) (st : List ℕ × ℕ × Bool × ℕ), st.1.length = nch →
    let r := l.foldl (fun st' zp => cond (Nat.ble zp.2 zq.2)
      (bupd c FG LB LE LS ch0 nch smax okV ws wE zp.2 zq.2 (stage2 wz zp.1 Ys) st') st') st
    r.1.length = nch ∧
    (∀ ch < nch, r.1.getD ch 0 = st.1.getD ch 0 + (l.map fun zp => if zp.2 ≤ zq.2 then
      rsT LS zp.2 zq.2 (range ((bTs c FG LB LE nch smax okV (stage2 wz zp.1 Ys)).getD ch zeroTM)) (ws (ch0 + ch))
      else 0).sum) ∧
    r.2.1 = st.2.1 + (l.map fun zp => if zp.2 ≤ zq.2 then
      rsT LS zp.2 zq.2 (Packed.cdiv 64 (stage2 wz zp.1 Ys).H) wE else 0).sum ∧
    (r.2.2.1 = true → st.2.2.1 = true ∧ ∀ zp ∈ l, zp.2 ≤ zq.2 → ∀ ch < nch,
      ((bTs c FG LB LE nch smax okV (stage2 wz zp.1 Ys)).getD ch zeroTM).ok = true) ∧
    st.2.2.2 ≤ r.2.2.2 ∧ (∀ zp ∈ l, zp.2 ≤ zq.2 → (stage2 wz zp.1 Ys).A ≤ r.2.2.2)
  | [], st, hst => by simp [hst]
  | zp :: l, st, hst => by
    intro r
    by_cases hpq : zp.2 ≤ zq.2
    · have hb : Nat.ble zp.2 zq.2 = true := Nat.ble_eq.mpr hpq
      obtain ⟨u1, u2, u3, u4, u5, u6⟩ := bupd_spec c FG LB LE LS ch0 nch smax okV ws wE zp.2 zq.2
        (stage2 wz zp.1 Ys) st hst
      obtain ⟨i1, i2, i3, i4, i5, i6⟩ := inner_spec c FG LB LE LS ch0 nch smax okV ws wE wz Ys zq l _ u1
      have hr : r = l.foldl (fun st' zp => cond (Nat.ble zp.2 zq.2)
          (bupd c FG LB LE LS ch0 nch smax okV ws wE zp.2 zq.2 (stage2 wz zp.1 Ys) st') st')
          (bupd c FG LB LE LS ch0 nch smax okV ws wE zp.2 zq.2 (stage2 wz zp.1 Ys) st) := by
        show List.foldl _ (cond (Nat.ble zp.2 zq.2) _ st) l = _
        rw [hb]; rfl
      rw [hr]
      refine ⟨i1, fun ch hch => ?_, ?_, fun h => ?_, ?_, fun zp' hzp' hle => ?_⟩
      · rw [i2 ch hch, u2 ch hch, List.map_cons, List.sum_cons, if_pos hpq]; ring
      · rw [i3, u3, List.map_cons, List.sum_cons, if_pos hpq]; ring
      · obtain ⟨h1, h2⟩ := i4 h
        obtain ⟨h3, h4⟩ := u4 h1
        refine ⟨h3, fun zp' hzp' hle ch hch => ?_⟩
        rcases List.mem_cons.mp hzp' with rfl | hzp'
        · exact h4 ch hch
        · exact h2 zp' hzp' hle ch hch
      · exact le_trans u5 i5
      · rcases List.mem_cons.mp hzp' with rfl | hzp'
        · exact le_trans u6 i5
        · exact i6 zp' hzp' hle
    · have hb : Nat.ble zp.2 zq.2 = false := by
        rw [Bool.eq_false_iff]; intro h; exact hpq (Nat.ble_eq.mp h)
      obtain ⟨i1, i2, i3, i4, i5, i6⟩ := inner_spec c FG LB LE LS ch0 nch smax okV ws wE wz Ys zq l st hst
      have hr : r = l.foldl (fun st' zp => cond (Nat.ble zp.2 zq.2)
          (bupd c FG LB LE LS ch0 nch smax okV ws wE zp.2 zq.2 (stage2 wz zp.1 Ys) st') st') st := by
        show List.foldl _ (cond (Nat.ble zp.2 zq.2) _ st) l = _
        rw [hb]; rfl
      rw [hr]
      refine ⟨i1, fun ch hch => ?_, ?_, fun h => ?_, i5, fun zp' hzp' hle => ?_⟩
      · rw [i2 ch hch, List.map_cons, List.sum_cons, if_neg hpq, zero_add]
      · rw [i3, List.map_cons, List.sum_cons, if_neg hpq, zero_add]
      · obtain ⟨h1, h2⟩ := i4 h
        refine ⟨h1, fun zp' hzp' hle ch hch => ?_⟩
        rcases List.mem_cons.mp hzp' with rfl | hzp'
        · exact absurd hle hpq
        · exact h2 zp' hzp' hle ch hch
      · rcases List.mem_cons.mp hzp' with rfl | hzp'
        · exact absurd hle hpq
        · exact i6 zp' hzp' hle

/-- the outer fold (over `q`) -/
theorem outer_spec (c : Ctx) (FG LB LE LS ch0 nch smax : ℕ) (okV : Bool) (ws : ℕ → List ℕ) (wE : List ℕ)
    (wz : ℕ) (tl : List (List (ℕ × PAcc))) (nz : List (ℕ × ℕ)) :
    ∀ (l : List (ℕ × ℕ)) (st : List ℕ × ℕ × Bool × ℕ), st.1.length = nch →
    let r := l.foldl (fun st zq => nz.foldl (fun st' zp => cond (Nat.ble zp.2 zq.2)
      (bupd c FG LB LE LS ch0 nch smax okV ws wE zp.2 zq.2 (stage2 wz zp.1 (stage1 wz zq.1 tl)) st') st') st) st
    r.1.length = nch ∧
    (∀ ch < nch, r.1.getD ch 0 = st.1.getD ch 0 + (l.map fun zq => (nz.map fun zp => if zp.2 ≤ zq.2 then
      rsT LS zp.2 zq.2 (range ((bTs c FG LB LE nch smax okV (stage2 wz zp.1 (stage1 wz zq.1 tl))).getD ch zeroTM))
        (ws (ch0 + ch)) else 0).sum).sum) ∧
    r.2.1 = st.2.1 + (l.map fun zq => (nz.map fun zp => if zp.2 ≤ zq.2 then
      rsT LS zp.2 zq.2 (Packed.cdiv 64 (stage2 wz zp.1 (stage1 wz zq.1 tl)).H) wE else 0).sum).sum ∧
    (r.2.2.1 = true → st.2.2.1 = true ∧ ∀ zq ∈ l, ∀ zp ∈ nz, zp.2 ≤ zq.2 → ∀ ch < nch,
      ((bTs c FG LB LE nch smax okV (stage2 wz zp.1 (stage1 wz zq.1 tl))).getD ch zeroTM).ok = true) ∧
    st.2.2.2 ≤ r.2.2.2 ∧ (∀ zq ∈ l, ∀ zp ∈ nz, zp.2 ≤ zq.2 → (stage2 wz zp.1 (stage1 wz zq.1 tl)).A ≤ r.2.2.2)
  | [], st, hst => by simp [hst]
  | zq :: l, st, hst => by
    intro r
    obtain ⟨u1, u2, u3, u4, u5, u6⟩ := inner_spec c FG LB LE LS ch0 nch smax okV ws wE wz (stage1 wz zq.1 tl) zq nz st hst
    obtain ⟨i1, i2, i3, i4, i5, i6⟩ := outer_spec c FG LB LE LS ch0 nch smax okV ws wE wz tl nz l _ u1
    refine ⟨i1, fun ch hch => ?_, ?_, fun h => ?_, le_trans u5 i5, fun zq' hzq' zp hzp hle => ?_⟩
    · show List.getD (List.foldl _ (List.foldl _ st nz) l).1 ch 0 = _
      rw [i2 ch hch, u2 ch hch, List.map_cons, List.sum_cons]; ring
    · show (List.foldl _ (List.foldl _ st nz) l).2.1 = _
      rw [i3, u3, List.map_cons, List.sum_cons]; ring
    · obtain ⟨h1, h2⟩ := i4 h
      obtain ⟨h3, h4⟩ := u4 h1
      refine ⟨h3, fun zq' hzq' zp hzp hle ch hch => ?_⟩
      rcases List.mem_cons.mp hzq' with rfl | hzq'
      · exact h4 zp hzp hle ch hch
      · exact h2 zq' hzq' zp hzp hle ch hch
    · rcases List.mem_cons.mp hzq' with rfl | hzq'
      · exact le_trans (u6 zp hzp hle) i5
      · exact i6 zq' hzq' zp hzp hle

/-- the result of the double fold -/
noncomputable def bres (c : Ctx) (wz FG LB LE LS ch0 nch smax : ℕ) (okV : Bool) (ws : ℕ → List ℕ) (wE : List ℕ)
    (zrows : List ℕ) (n : ℕ) (tl : List (List (ℕ × PAcc))) : List ℕ × ℕ × Bool × ℕ :=
  (zrows.zip (List.range n)).foldl (fun st zq => (zrows.zip (List.range n)).foldl (fun st' zp =>
      cond (Nat.ble zp.2 zq.2)
        (bupd c FG LB LE LS ch0 nch smax okV ws wE zp.2 zq.2 (stage2 wz zp.1 (stage1 wz zq.1 tl)) st') st') st)
    (List.replicate nch 0, 0, true, 0)

theorem zip_range_eq (zrows : List ℕ) (n : ℕ) (hz : zrows.length = n) :
    zrows.zip (List.range n) = (List.range n).map fun i => (zrows.getD i 0, i) := by
  apply List.ext_getElem (by simp [hz])
  intro k h1 h2
  have hk : k < n := by simpa using h2
  simp [List.getElem?_eq_getElem (show k < zrows.length by omega)]

/-- **The double fold**: per-channel packed row sums, the error row sums, the `ok` flags and `max |Tz|` -/
theorem bres_spec (c : Ctx) (wz FG LB LE LS ch0 nch smax : ℕ) (okV : Bool) (ws : ℕ → List ℕ) (wE : List ℕ)
    (zrows : List ℕ) (n : ℕ) (tl : List (List (ℕ × PAcc))) (hz : zrows.length = n) :
    let Gp := fun p q => stage2 wz (zrows.getD p 0) (stage1 wz (zrows.getD q 0) tl)
    let res := bres c wz FG LB LE LS ch0 nch smax okV ws wE zrows n tl
    res.1.length = nch ∧
    (∀ ch < nch, res.1.getD ch 0 = ∑ q ∈ Finset.range n, ∑ p ∈ Finset.range n, if p ≤ q then
      rsT LS p q (range ((bTs c FG LB LE nch smax okV (Gp p q)).getD ch zeroTM)) (ws (ch0 + ch)) else 0) ∧
    res.2.1 = ∑ q ∈ Finset.range n, ∑ p ∈ Finset.range n, (if p ≤ q then
      rsT LS p q (Packed.cdiv 64 (Gp p q).H) wE else 0) ∧
    (res.2.2.1 = true → ∀ q < n, ∀ p ≤ q, ∀ ch < nch, ((bTs c FG LB LE nch smax okV (Gp p q)).getD ch zeroTM).ok = true) ∧
    (∀ q < n, ∀ p ≤ q, (Gp p q).A ≤ res.2.2.2) := by
  intro Gp res
  have hnz := zip_range_eq zrows n hz
  obtain ⟨h1, h2, h3, h4, _, h6⟩ := outer_spec c FG LB LE LS ch0 nch smax okV ws wE wz tl (zrows.zip (List.range n))
    (zrows.zip (List.range n)) (List.replicate nch 0, 0, true, 0) (by simp)
  have hres : res = List.foldl _ (List.replicate nch 0, 0, true, 0) (zrows.zip (List.range n)) := rfl
  rw [hnz] at h1 h2 h3 h4 h6 hres
  refine ⟨by rw [hres]; exact h1, fun ch hch => ?_, ?_, fun h q hq p hpq ch hch => ?_, fun q hq p hpq => ?_⟩
  · have h0 : (List.replicate nch 0).getD ch 0 = 0 := by rw [getD_of_lt _ _ (by simp [hch])]; simp
    rw [hres, h2 ch hch, h0, zero_add, List.map_map, list_sum_range']
    apply Finset.sum_congr rfl; intro q _
    simp only [Function.comp_apply, List.map_map, list_sum_range']
    rfl
  · rw [hres, h3, List.map_map, list_sum_range']
    simp only [zero_add, Function.comp_apply, List.map_map, list_sum_range']
    rfl
  · have hp : p < n := by omega
    rw [hres] at h
    exact (h4 h).2 (zrows.getD q 0, q) (List.mem_map.mpr ⟨q, List.mem_range.mpr hq, rfl⟩)
      (zrows.getD p 0, p) (List.mem_map.mpr ⟨p, List.mem_range.mpr hp, rfl⟩) hpq ch hch
  · have hp : p < n := by omega
    rw [hres]
    exact h6 (zrows.getD q 0, q) (List.mem_map.mpr ⟨q, List.mem_range.mpr hq, rfl⟩)
      (zrows.getD p 0, p) (List.mem_map.mpr ⟨p, List.mem_range.mpr hp, rfl⟩) hpq

/-! ## Packed row sums -/

theorem rs_rearrange (LS n : ℕ) (t : ℕ → ℕ → ℕ) (w : List ℕ) :
    ∑ q ∈ Finset.range n, ∑ p ∈ Finset.range n, (if p ≤ q then rsT LS p q (t p q) w else 0) =
      ∑ p ∈ Finset.range n, (∑ q ∈ Finset.range n, t (min p q) (max p q) * w.getD q 0) * 2 ^ (LS * p) := by
  have e1 : ∀ p q, (if p ≤ q then rsT LS p q (t p q) w else 0) =
      (if p ≤ q then t p q * w.getD q 0 * 2 ^ (LS * p) else 0) +
        (if p < q then t p q * w.getD p 0 * 2 ^ (LS * q) else 0) := by
    intro p q; unfold rsT
    by_cases h1 : p ≤ q
    · by_cases h3 : p = q
      · subst h3; simp
      · have h2 : p < q := by omega
        simp [h1, h2, h3]
    · have h2 : ¬ p < q := by omega
      simp [h1, h2]
  simp only [e1, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun q p => if p ≤ q then t p q * w.getD q 0 * 2 ^ (LS * p) else 0)]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro p _
  rw [← Finset.sum_add_distrib, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro q _
  by_cases h : p ≤ q
  · have h2 : ¬ q < p := by omega
    simp [h, h2]
  · have h2 : q < p := by omega
    simp [h, h2, min_eq_right h2.le, max_eq_left h2.le]

theorem slot_rows {LS : ℕ} (hLS : 0 < LS) (n : ℕ) (R : ℕ → ℕ) (hR : ∀ p < n, R p < 2 ^ LS) (p : ℕ) (hp : p < n) :
    slot LS (∑ p ∈ Finset.range n, R p * 2 ^ (LS * p)) p = R p := by
  have e : ∑ p ∈ Finset.range n, R p * 2 ^ (LS * p) = Nat.ofDigits (2 ^ LS) ((List.range n).map R) := by
    rw [ofDigits_range]; apply Finset.sum_congr rfl; intro c _; rw [pow_mul]
  rw [e, slot_ofDigits hLS]
  · rw [getD_of_lt _ _ (by simp [hp])]; simp
  · intro d hd
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd
    exact hR c (List.mem_range.mp hc)

end ThomsonCompact.Floor.B
