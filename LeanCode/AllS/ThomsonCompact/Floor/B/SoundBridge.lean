import ThomsonCompact.Floor.B.BridgeKernel
import ThomsonCompact.Floor.B.SoundRowC

/-!
# Soundness of the F3b bridge checks (re-expanded D12 table against the old literals)

For an old entry `h` (Horner order) at the anchor `a0 = p/2^q`, `σ = 2^-g` (`cg = q - g`):
* `Bridge.reJ`: the exact re-expanded integers `J` with `2^q Σ_k J_k u^k = 2^(q |h|) h((p + 2^cg u)/2^q)`
  (`Bridge.reJ_eval`); the kernel's `reexpP` is `horner (2^W) J mod 2^K` (`Bridge.reexpP_fst`) and
  `Σ |J_k| ≤ reexpM.1` (`Bridge.reJ_natAbs`), so `pvGet` decodes every `J_k` exactly (`Bridge.reexp_decode`);
* `Bridge.entryOk_sound`, `Bridge.magOk_sound`, `Bridge.rowEntries_spec`: entry, magnitude and row-walk checks;
* `rowBridge_sound`, `denOk_sound`: the `RowSem` fields of a row from `rowBridgeOk` and `denOk`.
-/

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Packed
open ThomsonCompact.Floor (mask slot)
open scoped BigOperators

namespace Bridge

/-! ## Boolean, natural-number and sign-magnitude helpers -/

theorem band_true {a b : Bool} (h : and a b = true) : a = true ∧ b = true := by
  revert h; cases a <;> cases b <;> decide

theorem land_mask (a K : ℕ) : Nat.land a (mask K) = a % 2 ^ K := by
  rw [mask_eq]; exact Nat.and_two_pow_sub_one_eq_mod a K

theorem cast_land_mask (a K : ℕ) : ((Nat.land a (mask K) : ℕ) : ℤ) = (a : ℤ) % 2 ^ K := by
  rw [mask_eq]; exact toZ_mod_mask

theorem ndist_cast (a b : ℕ) : ((ndist a b : ℕ) : ℤ) = |(a : ℤ) - (b : ℤ)| := by
  show (((a - b) + (b - a) : ℕ) : ℤ) = _
  rcases le_total a b with h | h
  · rw [Nat.sub_eq_zero_of_le h, zero_add, Nat.cast_sub h, abs_of_nonpos (by omega), neg_sub]
  · rw [Nat.sub_eq_zero_of_le h, add_zero, Nat.cast_sub h, abs_of_nonneg (by omega)]

theorem sv_true (A : ℕ) : sv (true, A) = -(A : ℤ) := rfl

theorem sv_false (A : ℕ) : sv (false, A) = (A : ℤ) := rfl

/-- the kernel's distance of two sign-magnitude numbers -/
theorem cond_dist (s1 s2 : Bool) (A B : ℕ) :
    ((cond (!(xor s1 s2)) (ndist A B) (Nat.add A B) : ℕ) : ℤ) = |sv (s1, A) - sv (s2, B)| := by
  cases s1 <;> cases s2
  · show ((ndist A B : ℕ) : ℤ) = _
    rw [sv_false, sv_false, ndist_cast]
  · show ((A + B : ℕ) : ℤ) = _
    rw [sv_false, sv_true, sub_neg_eq_add, abs_of_nonneg (by omega)]
    omega
  · show ((A + B : ℕ) : ℤ) = _
    rw [sv_true, sv_false, abs_of_nonpos (by omega)]
    omega
  · show ((ndist A B : ℕ) : ℤ) = _
    rw [sv_true, sv_true, ndist_cast, show -(A : ℤ) - -(B : ℤ) = -((A : ℤ) - B) by ring, abs_neg]

theorem cond_dist_le (s1 s2 : Bool) (A B T : ℕ)
    (h : 2 * cond (!(xor s1 s2)) (ndist A B) (Nat.add A B) ≤ T) :
    2 * |sv (s1, A) - sv (s2, B)| ≤ (T : ℤ) := by
  rw [← cond_dist]; exact_mod_cast h

theorem sv_mul (s : Bool) (A c : ℕ) : sv (s, A * c) = sv (s, A) * (c : ℤ) := by
  cases s
  · rw [sv_false, sv_false, Nat.cast_mul]
  · rw [sv_true, sv_true, Nat.cast_mul, neg_mul]

theorem sv_int (x : ℤ) : sv (decide (x < 0), x.natAbs) = x := by
  by_cases hx : x < 0
  · rw [decide_eq_true hx, sv_true, Int.natCast_natAbs, abs_of_neg hx, neg_neg]
  · rw [decide_eq_false hx, sv_false, Int.natCast_natAbs, abs_of_nonneg (not_lt.mp hx)]

theorem sv_slot (s h : ℕ) : sv (Nat.blt s h, ndist s h) = (s : ℤ) - h := by
  by_cases hs : s < h
  · have hb : Nat.blt s h = true := by rw [Nat.blt_eq]; exact hs
    rw [hb, sv_true, ndist_cast, abs_of_neg (by omega), neg_neg]
  · have hb : Nat.blt s h = false :=
      Bool.eq_false_iff.mpr (fun hb => hs (by rw [Nat.blt_eq] at hb; exact hb))
    rw [hb, sv_false, ndist_cast, abs_of_nonneg (by omega)]

/-! ## The exact re-expansion -/

/-- the exact re-expanded integer coefficients `J` (Horner order) of an old entry -/
def reJ (p q cg : ℕ) : List ℤ → List ℤ
  | [] => []
  | x :: rest => addL [x * 2 ^ (q * rest.length)]
      (addL (scaleL (p : ℤ) (reJ p q cg rest)) (0 :: scaleL ((2 : ℤ) ^ cg) (reJ p q cg rest)))

theorem reJ_length (p q cg : ℕ) : ∀ h : List ℤ, (reJ p q cg h).length = h.length
  | [] => rfl
  | x :: rest => by
    simp only [reJ, length_addL, length_scaleL, List.length_cons, List.length_nil, reJ_length p q cg rest]
    omega

theorem reexpP_snd (p q cg W K : ℕ) : ∀ h : List ℤ, (reexpP p q cg W K h).2 = 2 ^ (q * h.length)
  | [] => by show (1 : ℕ) = 2 ^ (q * 0); rw [Nat.mul_zero, pow_zero]
  | x :: rest => by
    show Nat.shiftLeft (reexpP p q cg W K rest).2 q = _
    rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq, reexpP_snd p q cg W K rest, ← pow_add, List.length_cons,
      mul_add_one]

theorem reexpP_cons_fst (p q cg W K : ℕ) (x : ℤ) (rest : List ℤ) :
    (reexpP p q cg W K (x :: rest)).1 =
      Nat.land (cond (decide (x < 0))
        (Nat.add (Nat.add (Nat.mul p (reexpP p q cg W K rest).1)
            (Nat.shiftLeft (reexpP p q cg W K rest).1 (Nat.add W cg)))
          (Nat.sub (Nat.pow 2 K) (Nat.land (Nat.mul (Int.natAbs x) (reexpP p q cg W K rest).2) (mask K))))
        (Nat.add (Nat.add (Nat.mul p (reexpP p q cg W K rest).1)
            (Nat.shiftLeft (reexpP p q cg W K rest).1 (Nat.add W cg)))
          (Nat.mul (Int.natAbs x) (reexpP p q cg W K rest).2))) (mask K) := rfl

/-- one signed accumulation step of `reexpP` (two's complement modulo `2^K`) -/
theorem signed_step (t K P : ℕ) (x : ℤ) :
    ((Nat.land (cond (decide (x < 0))
        (Nat.add t (Nat.sub (Nat.pow 2 K) (Nat.land (Nat.mul (Int.natAbs x) P) (mask K))))
        (Nat.add t (Nat.mul (Int.natAbs x) P))) (mask K) : ℕ) : ℤ) % 2 ^ K =
      ((t : ℤ) + x * (P : ℤ)) % 2 ^ K := by
  rw [cast_land_mask, Int.emod_emod]
  by_cases hx : x < 0
  · rw [decide_eq_true hx, cond_true]
    have hle : Nat.land (Nat.mul (Int.natAbs x) P) (mask K) ≤ Nat.pow 2 K := by
      rw [land_mask]; exact (Nat.mod_lt _ (Nat.two_pow_pos K)).le
    have e : ((Nat.add t (Nat.sub (Nat.pow 2 K) (Nat.land (Nat.mul (Int.natAbs x) P) (mask K))) : ℕ) : ℤ) =
        (t : ℤ) + (2 ^ K - ((x.natAbs * P : ℕ) : ℤ) % 2 ^ K) := by
      rw [Nat.add_eq, Nat.cast_add, Nat.sub_eq, Nat.cast_sub hle, cast_land_mask, Nat.pow_eq, Nat.cast_pow,
        Nat.cast_ofNat, Nat.mul_eq]
    rw [e, mod_helper]
    congr 1
    rw [Nat.cast_mul, Int.natCast_natAbs, abs_of_neg hx]; ring
  · rw [decide_eq_false hx, cond_false, Nat.add_eq, Nat.mul_eq, Nat.cast_add, Nat.cast_mul,
      Int.natCast_natAbs, abs_of_nonneg (not_lt.mp hx)]

/-- the packed `J` of `reexpP` is `horner (2^W) J` modulo `2^K` -/
theorem reexpP_fst (p q cg W K : ℕ) : ∀ h : List ℤ,
    ((reexpP p q cg W K h).1 : ℤ) % 2 ^ K = horner (2 ^ W : ℤ) (reJ p q cg h) % 2 ^ K
  | [] => by show ((0 : ℕ) : ℤ) % 2 ^ K = horner (2 ^ W : ℤ) [] % 2 ^ K; simp
  | x :: rest => by
    have ih : Int.ModEq (2 ^ K) ((reexpP p q cg W K rest).1 : ℤ) (horner (2 ^ W : ℤ) (reJ p q cg rest)) :=
      reexpP_fst p q cg W K rest
    rw [reexpP_cons_fst, signed_step, reexpP_snd]
    have hJ : horner (2 ^ W : ℤ) (reJ p q cg (x :: rest)) =
        x * 2 ^ (q * rest.length) + ((p : ℤ) + 2 ^ W * 2 ^ cg) * horner (2 ^ W : ℤ) (reJ p q cg rest) := by
      simp only [reJ, horner_addL, horner_scaleL, horner_cons, horner_nil]; ring
    have e : (((Nat.add (Nat.mul p (reexpP p q cg W K rest).1)
        (Nat.shiftLeft (reexpP p q cg W K rest).1 (Nat.add W cg)) : ℕ) : ℤ) +
          x * ((2 ^ (q * rest.length) : ℕ) : ℤ)) =
        x * 2 ^ (q * rest.length) + ((p : ℤ) + 2 ^ W * 2 ^ cg) * ((reexpP p q cg W K rest).1 : ℤ) := by
      simp only [Nat.add_eq, Nat.mul_eq, Nat.shiftLeft_eq', Nat.shiftLeft_eq]
      push_cast; ring
    rw [hJ, e]
    exact Int.ModEq.add_left _ (Int.ModEq.mul_left _ ih)

theorem reexpM_snd (p q cg : ℕ) : ∀ h : List ℤ, (reexpM p q cg h).2 = 2 ^ (q * h.length)
  | [] => by show (1 : ℕ) = 2 ^ (q * 0); rw [Nat.mul_zero, pow_zero]
  | x :: rest => by
    show Nat.shiftLeft (reexpM p q cg rest).2 q = _
    rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq, reexpM_snd p q cg rest, ← pow_add, List.length_cons,
      mul_add_one]

theorem reexpM_cons_fst (p q cg : ℕ) (x : ℤ) (rest : List ℤ) :
    (reexpM p q cg (x :: rest)).1 =
      x.natAbs * (reexpM p q cg rest).2 + (p + 2 ^ cg) * (reexpM p q cg rest).1 := rfl

/-- `Σ |J_k| ≤ reexpM.1` -/
theorem reJ_natAbs (p q cg : ℕ) : ∀ h : List ℤ, ((reJ p q cg h).map Int.natAbs).sum ≤ (reexpM p q cg h).1
  | [] => by simp only [reJ, List.map_nil, List.sum_nil]; exact Nat.zero_le _
  | x :: rest => by
    have ih := reJ_natAbs p q cg rest
    rw [reexpM_cons_fst, reexpM_snd]
    have e0 : reJ p q cg (x :: rest) = addL [x * 2 ^ (q * rest.length)]
        (addL (scaleL (p : ℤ) (reJ p q cg rest)) (0 :: scaleL ((2 : ℤ) ^ cg) (reJ p q cg rest))) := rfl
    rw [e0]
    have h1 := natAbs_addL_le [x * 2 ^ (q * rest.length)]
      (addL (scaleL (p : ℤ) (reJ p q cg rest)) (0 :: scaleL ((2 : ℤ) ^ cg) (reJ p q cg rest)))
    have h2 := natAbs_addL_le (scaleL (p : ℤ) (reJ p q cg rest)) (0 :: scaleL ((2 : ℤ) ^ cg) (reJ p q cg rest))
    have e1 : ([x * 2 ^ (q * rest.length)].map Int.natAbs).sum = x.natAbs * 2 ^ (q * rest.length) := by
      rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Int.natAbs_mul, Int.natAbs_pow]
      rfl
    have e2 : ((0 :: scaleL ((2 : ℤ) ^ cg) (reJ p q cg rest)).map Int.natAbs).sum =
        2 ^ cg * ((reJ p q cg rest).map Int.natAbs).sum := by
      rw [List.map_cons, List.sum_cons, Int.natAbs_zero, zero_add, natAbs_scaleL, Int.natAbs_pow]
      rfl
    have e3 : ((scaleL (p : ℤ) (reJ p q cg rest)).map Int.natAbs).sum =
        p * ((reJ p q cg rest).map Int.natAbs).sum := by
      rw [natAbs_scaleL, Int.natAbs_natCast]
    rw [e1] at h1
    rw [e2, e3] at h2
    have h3 : p * ((reJ p q cg rest).map Int.natAbs).sum + 2 ^ cg * ((reJ p q cg rest).map Int.natAbs).sum ≤
        (p + 2 ^ cg) * (reexpM p q cg rest).1 := by
      rw [← add_mul]; exact Nat.mul_le_mul_left _ ih
    exact h1.trans (Nat.add_le_add_left (h2.trans h3) _)

theorem natAbs_getD_le (J : List ℤ) (k : ℕ) : (J.getD k 0).natAbs ≤ (J.map Int.natAbs).sum := by
  rw [← getD_map_of_zero Int.natAbs 0 0 rfl J k]
  exact getD_le_sum _ k

/-- **decoding**: under the bound `reexpM.1 < 2^(W-1)` every slot of the packed `J` is the exact `J_k` -/
theorem reexp_decode (p q cg W L : ℕ) (hW : 1 ≤ W) (h : List ℤ) (hlen : h.length ≤ L)
    (hM : (reexpM p q cg h).1 < 2 ^ (W - 1)) (k : ℕ) (hk : k < L) :
    pvGet W L (reexpP p q cg W (Nat.mul W L) h).1 k =
      (decide ((reJ p q cg h).getD k 0 < 0), ((reJ p q cg h).getD k 0).natAbs) := by
  have hJl : (reJ p q cg h).length ≤ L := by rw [reJ_length]; exact hlen
  have hb : ∀ i, |(reJ p q cg h).getD i 0| < 2 ^ (W - 1) := by
    intro i
    have h1 := natAbs_getD_le (reJ p q cg h) i
    have h2 := reJ_natAbs p q cg h
    have h3 : ((reJ p q cg h).getD i 0).natAbs < 2 ^ (W - 1) := by omega
    rw [← Int.natCast_natAbs]; exact_mod_cast h3
  obtain ⟨z, hz⟩ : ∃ z : List ℤ, z = (List.range L).map fun i => (reJ p q cg h).getD i 0 := ⟨_, rfl⟩
  have hzl : z.length = L := by rw [hz, List.length_map, List.length_range]
  have hzb : ∀ x ∈ z, |x| < 2 ^ (W - 1) := by
    intro x hx
    rw [hz] at hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact hb i
  have hzg : ∀ i, z.getD i 0 = (reJ p q cg h).getD i 0 := by
    intro i
    by_cases hi : i < L
    · rw [hz, getD_of_lt _ _ (by rw [List.length_map, List.length_range]; exact hi), List.getElem_map,
        List.getElem_range]
    · rw [getD_of_ge z 0 (by omega), getD_of_ge (reJ p q cg h) 0 (by omega)]
  have hV : ((reexpP p q cg W (Nat.mul W L) h).1 : ℤ) % 2 ^ (W * L) = horner (2 ^ W : ℤ) z % 2 ^ (W * L) := by
    rw [horner_eq_of_getD (2 ^ W) z (reJ p q cg h) hzg]
    exact reexpP_fst p q cg W (Nat.mul W L) h
  have hpb := pb_digits hW z hzl hzb _ hV
  have e : pvGet W L (reexpP p q cg W (Nat.mul W L) h).1 k =
      pbGet W (Nat.land (Nat.add (reexpP p q cg W (Nat.mul W L) h).1 (pvBias W L)) (mask (Nat.mul W L))) k :=
    rfl
  rw [e, hpb, pbGet_ofDigits hW z hzb k (by omega)]
  have hzk : ∀ hk' : k < z.length, z[k] = (reJ p q cg h).getD k 0 := fun hk' => by
    rw [← hzg k, getD_of_lt z 0 hk']
  rw [hzk]

/-! ## Real evaluation of the re-expansion -/

theorem evalZ_cons (c : ℤ) (l : List ℤ) (t : ℝ) : evalZ (c :: l) t = c + t * evalZ l t := by
  simp only [evalZ, List.map_cons, horner_cons]

theorem evalZ_nil (t : ℝ) : evalZ [] t = 0 := by simp only [evalZ, List.map_nil, horner_nil]

theorem evalZ_reJ_cons (p q cg : ℕ) (x : ℤ) (rest : List ℤ) (u : ℝ) :
    evalZ (reJ p q cg (x :: rest)) u =
      (x : ℝ) * 2 ^ (q * rest.length) + ((p : ℝ) + 2 ^ cg * u) * evalZ (reJ p q cg rest) u := by
  simp only [reJ, evalZ_addL, evalZ_scaleL, evalZ_cons, evalZ_nil]
  push_cast; ring

/-- `2^q Σ_k J_k u^k = 2^(q |h|) h((p + 2^cg u)/2^q)` -/
theorem reJ_eval (p q cg : ℕ) : ∀ (h : List ℤ) (u : ℝ),
    (2 : ℝ) ^ q * evalZ (reJ p q cg h) u =
      (2 : ℝ) ^ (q * h.length) * evalZ h (((p : ℝ) + 2 ^ cg * u) / 2 ^ q)
  | [], u => by simp only [reJ, evalZ_nil, mul_zero]
  | x :: rest, u => by
    have ih := reJ_eval p q cg rest u
    have hq : (2 : ℝ) ^ q ≠ 0 := by positivity
    have hqa : (2 : ℝ) ^ q * (((p : ℝ) + 2 ^ cg * u) / 2 ^ q) = (p : ℝ) + 2 ^ cg * u := by
      rw [mul_div_assoc', mul_div_cancel_left₀ _ hq]
    rw [evalZ_reJ_cons, evalZ_cons, List.length_cons, mul_add_one, pow_add]
    linear_combination ((p : ℝ) + 2 ^ cg * u) * ih -
      (2 : ℝ) ^ (q * rest.length) * evalZ rest (((p : ℝ) + 2 ^ cg * u) / 2 ^ q) * hqa

theorem anchor_eq (p q g : ℕ) (hgq : g ≤ q) (u : ℝ) :
    (p : ℝ) / 2 ^ q + 1 / 2 ^ g * u = ((p : ℝ) + 2 ^ (q - g) * u) / 2 ^ q := by
  have h2 : (2 : ℝ) ^ q = 2 ^ (q - g) * 2 ^ g := by rw [← pow_add, Nat.sub_add_cancel hgq]
  have hA : (2 : ℝ) ^ (q - g) ≠ 0 := by positivity
  rw [h2, add_div, mul_div_mul_left _ _ hA]
  ring

theorem evalZ_eq_sum : ∀ (l : List ℤ) (n : ℕ), l.length ≤ n → ∀ u : ℝ,
    evalZ l u = ∑ k ∈ Finset.range n, (l.getD k 0 : ℝ) * u ^ k
  | [], n, _, u => by simp [evalZ]
  | x :: l, 0, h, u => by simp at h
  | x :: l, n + 1, h, u => by
    rw [evalZ_cons, evalZ_eq_sum l n (by simp at h; omega) u, Finset.sum_range_succ']
    have e : ∀ k ∈ Finset.range n, (((x :: l).getD (k + 1) 0 : ℤ) : ℝ) * u ^ (k + 1) =
        u * ((l.getD k 0 : ℝ) * u ^ k) := by
      intro k _; rw [List.getD_cons_succ, pow_succ]; ring
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum, List.getD_cons_zero, pow_zero, mul_one]
    ring

/-- `h(a0 + σ u) 2^(q (|h|-1)) = Σ_{k<L} J_k u^k` -/
theorem reexp_eval_sum (p q g : ℕ) (hgq : g ≤ q) (hh : List ℤ) (hpos : 0 < hh.length) (L : ℕ)
    (hlen : hh.length ≤ L) (u : ℝ) :
    evalZ hh ((p : ℝ) / 2 ^ q + 1 / 2 ^ g * u) * 2 ^ (q * (hh.length - 1)) =
      ∑ k ∈ Finset.range L, ((reJ p q (q - g) hh).getD k 0 : ℝ) * u ^ k := by
  rw [anchor_eq p q g hgq u, ← evalZ_eq_sum (reJ p q (q - g) hh) L (by rw [reJ_length]; exact hlen) u]
  have h1 := reJ_eval p q (q - g) hh u
  have hpos1 : 1 ≤ hh.length := hpos
  have hl : q * hh.length = q * (hh.length - 1) + q := by rw [← mul_add_one, Nat.sub_add_cancel hpos1]
  rw [hl, pow_add] at h1
  have hq : (2 : ℝ) ^ q ≠ 0 := by positivity
  apply mul_left_cancel₀ hq
  linear_combination -h1

/-! ## Real-number helpers -/

theorem zpow_two_split (F : ℤ) : (2 : ℝ) ^ F = 2 ^ F.toNat / 2 ^ (-F).toNat := by
  conv_lhs => rw [← Int.toNat_sub_toNat_neg F]
  rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast, zpow_natCast]

theorem coef_real (F : ℤ) (x : ℝ) (n : ℕ) :
    (2 : ℝ) ^ F * x / 2 ^ n = x * 2 ^ F.toNat / 2 ^ (n + (-F).toNat) := by
  rw [zpow_two_split, pow_add]; ring

theorem half_bound {X Y D : ℝ} (hD : 0 < D) (h : 2 * |X - Y * D| ≤ D) : |X / D - Y| ≤ 1 / 2 := by
  have e : X / D - Y = (X - Y * D) / D := by rw [sub_div, mul_div_assoc, div_self hD.ne', mul_one]
  rw [e, abs_div, abs_of_pos hD, div_le_iff₀ hD]
  linarith

theorem br_div_mul_cancel (X E N : ℝ) (hN : N ≠ 0) : X / N * (E * N) = X * E := by
  rw [mul_comm E N, ← mul_assoc, div_mul_cancel₀ X hN]

/-- coefficientwise `1/2` closeness gives `L/2` closeness on `|u| ≤ 1` -/
theorem sum_dev (L : ℕ) (c e : ℕ → ℝ) (hce : ∀ k < L, |c k - e k| ≤ 1 / 2) (u : ℝ) (hu : |u| ≤ 1) :
    |∑ k ∈ Finset.range L, c k * u ^ k - ∑ k ∈ Finset.range L, e k * u ^ k| ≤ (L : ℝ) / 2 := by
  rw [← Finset.sum_sub_distrib]
  calc |∑ k ∈ Finset.range L, (c k * u ^ k - e k * u ^ k)|
      ≤ ∑ k ∈ Finset.range L, |c k * u ^ k - e k * u ^ k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range L, (1 / 2 : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [← sub_mul, abs_mul, abs_pow]
        have h1 := hce k (Finset.mem_range.mp hk)
        have h2 : |u| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg u) hu
        calc |c k - e k| * |u| ^ k ≤ 1 / 2 * 1 := mul_le_mul h1 h2 (by positivity) (by norm_num)
          _ = 1 / 2 := by norm_num
    _ = (L : ℝ) / 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-! ## One entry -/

theorem coefOk_sound (Fp E w : ℕ) (x : ℤ) (sl : ℕ) (h : coefOk Fp E w (decide (x < 0), x.natAbs) sl = true) :
    2 * |x * 2 ^ Fp - ((sl : ℤ) - 2 ^ (w - 1)) * 2 ^ E| ≤ 2 ^ E := by
  have h1 : 2 * cond (!(xor (decide (x < 0)) (Nat.blt sl (2 ^ (w - 1)))))
      (ndist (Nat.shiftLeft x.natAbs Fp) (Nat.shiftLeft (ndist sl (2 ^ (w - 1))) E))
      (Nat.add (Nat.shiftLeft x.natAbs Fp) (Nat.shiftLeft (ndist sl (2 ^ (w - 1))) E)) ≤ 2 ^ E :=
    Nat.le_of_ble_eq_true h
  have h2 := cond_dist_le _ _ _ _ _ h1
  simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, sv_mul, sv_int, sv_slot] at h2
  push_cast at h2
  exact h2

/-- the offset slot of `eslot` as a signed coefficient (`0` for the dropped coefficients) -/
theorem eslot_val (r : RowT) (k idx : ℕ) :
    ((eslot r k idx : ℕ) : ℤ) - 2 ^ (r.w - 1) = if k < r.L then r.ehat idx k else 0 := by
  unfold eslot RowT.ehat
  by_cases hk : k < r.L
  · rw [if_pos hk, show Nat.blt k r.L = true from Nat.blt_eq.mpr hk, cond_true]
  · rw [if_neg hk, show Nat.blt k r.L = false from Bool.eq_false_iff.mpr (fun h => hk (Nat.blt_eq.mp h)),
      cond_false]
    show (((2 ^ (r.w - 1) : ℕ) : ℤ)) - 2 ^ (r.w - 1) = 0
    push_cast; ring

theorem sum_range_ite_lt (L dE : ℕ) (h : L ≤ dE) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.range dE, (if k < L then f k else 0) = ∑ k ∈ Finset.range L, f k := by
  rw [← Finset.sum_range_add_sum_Ico _ h]
  have h1 : ∑ k ∈ Finset.range L, (if k < L then f k else 0) = ∑ k ∈ Finset.range L, f k :=
    Finset.sum_congr rfl (fun k hk => if_pos (Finset.mem_range.mp hk))
  have h2 : ∑ k ∈ Finset.Ico L dE, (if k < L then f k else 0) = 0 :=
    Finset.sum_eq_zero (fun k hk => if_neg (by have := (Finset.mem_Ico.mp hk).1; omega))
  rw [h1, h2, add_zero]

theorem shr_shr (x a b : ℕ) : Nat.shiftRight (Nat.shiftRight x a) b = Nat.shiftRight x (a + b) := by
  show x >>> a >>> b = x >>> (a + b)
  rw [Nat.shiftRight_add]

theorem pbGet_shift (W Jb k : ℕ) : pbGet W (Nat.shiftRight Jb W) k = pbGet W Jb (k + 1) := by
  unfold pbGet slot
  rw [shr_shr, show W + Nat.mul W k = Nat.mul W (k + 1) by show W + W * k = W * (k + 1); ring]

theorem coefsOk_spec (Fp E w W : ℕ) : ∀ (es : List ℕ) (Jb : ℕ), coefsOk Fp E w W es Jb = true →
    ∀ k < es.length, coefOk Fp E w (pbGet W Jb k) (es.getD k 0) = true
  | [], _, _, k, hk => absurd hk (by simp)
  | s :: es, Jb, h, k, hk => by
    have h' : and (coefOk Fp E w (pbGet W Jb 0) s) (coefsOk Fp E w W es (Nat.shiftRight Jb W)) = true := h
    obtain ⟨h1, h2⟩ := band_true h'
    cases k with
    | zero => exact h1
    | succ k =>
      rw [List.getD_cons_succ, ← pbGet_shift]
      exact coefsOk_spec Fp E w W es _ h2 k (by simp at hk; omega)

theorem eslots_length (r : RowT) (ht : r.t.length = r.L) (hLdE : r.L ≤ r.dE) (idx : ℕ) :
    (eslots r idx).length = r.dE := by
  unfold eslots
  show (List.map _ r.t ++ List.replicate _ _).length = _
  rw [List.length_append, List.length_map, List.length_replicate, ht]
  show r.L + (r.dE - r.L) = r.dE
  omega

theorem eslots_getD (r : RowT) (ht : r.t.length = r.L) (hLdE : r.L ≤ r.dE) (idx k : ℕ) (hk : k < r.dE) :
    (eslots r idx).getD k 0 = eslot r k idx := by
  unfold eslots eslot
  show (List.map _ r.t ++ List.replicate _ _).getD k 0 = _
  rw [List.getD_eq_getElem?_getD]
  by_cases hkL : k < r.L
  · have h1 : k < (List.map (fun tk => slot r.w tk idx) r.t).length := by rw [List.length_map, ht]; exact hkL
    rw [List.getElem?_append_left h1, show Nat.blt k r.L = true from Nat.blt_eq.mpr hkL, cond_true,
      List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem (by rw [ht]; exact hkL)]
    rfl
  · have h1 : (List.map (fun tk => slot r.w tk idx) r.t).length ≤ k := by rw [List.length_map, ht]; omega
    rw [List.getElem?_append_right h1, show Nat.blt k r.L = false from
      Bool.eq_false_iff.mpr (fun h => hkL (Nat.blt_eq.mp h)), cond_false, List.length_map, ht,
      List.getElem?_replicate, if_pos (by show k - r.L < Nat.sub r.dE r.L; show k - r.L < r.dE - r.L; omega)]
    rfl

/-- **an entry**: `|2^F h(a0 + σ u) - Σ_{k<L} ê_k u^k| ≤ dE/2` on `|u| ≤ 1` -/
theorem entryOk_sound (p q g W : ℕ) (r : RowT) (idx : ℕ) (hh : List ℤ) (hgq : g ≤ q) (hW : 1 ≤ W)
    (hLdE : r.L ≤ r.dE) (ht : r.t.length = r.L) (h : entryOk p q g W r idx hh = true) (u : ℝ) (hu : |u| ≤ 1) :
    |(2 : ℝ) ^ r.F * evalZ hh ((p : ℝ) / 2 ^ q + 1 / 2 ^ g * u) - evalZ (r.ecoef idx) u| ≤ (r.dE : ℝ) / 2 := by
  have h0 : and (and (and (Nat.ble hh.length r.dE) (Nat.blt 0 hh.length))
      (Nat.blt (reexpM p q (q - g) hh).1 (2 ^ (W - 1))))
    (coefsOk r.F.toNat (q * (hh.length - 1) + (-r.F).toNat) r.w W (eslots r idx)
      (Nat.land (Nat.add (reexpP p q (q - g) W (Nat.mul W r.dE) hh).1 (pvBias W r.dE)) (mask (Nat.mul W r.dE))))
      = true := h
  obtain ⟨hA, hC⟩ := band_true h0
  obtain ⟨hA, hM⟩ := band_true hA
  obtain ⟨hlen, hpos⟩ := band_true hA
  have hlen : hh.length ≤ r.dE := Nat.le_of_ble_eq_true hlen
  have hpos : 0 < hh.length := Nat.le_of_ble_eq_true hpos
  have hM : (reexpM p q (q - g) hh).1 < 2 ^ (W - 1) := Nat.le_of_ble_eq_true hM
  have hC' : ∀ k ∈ List.range r.dE, coefOk r.F.toNat (q * (hh.length - 1) + (-r.F).toNat) r.w
      (pvGet W r.dE (reexpP p q (q - g) W (Nat.mul W r.dE) hh).1 k) (eslot r k idx) = true := by
    intro k hk
    have hk' := List.mem_range.mp hk
    have := coefsOk_spec _ _ _ _ _ _ hC k (by rw [eslots_length r ht hLdE]; exact hk')
    rw [eslots_getD r ht hLdE idx k hk'] at this
    exact this
  set e' : ℕ → ℝ := fun k => (((if k < r.L then r.ehat idx k else 0 : ℤ)) : ℝ) with he'
  have hk : ∀ k < r.dE, |(2 : ℝ) ^ r.F * ((reJ p q (q - g) hh).getD k 0 : ℝ) / 2 ^ (q * (hh.length - 1)) -
      e' k| ≤ 1 / 2 := by
    intro k hkL
    have h1 := hC' k (List.mem_range.mpr hkL)
    rw [reexp_decode p q (q - g) W r.dE hW hh hlen hM k hkL] at h1
    have h2 := coefOk_sound _ _ _ _ _ h1
    rw [eslot_val] at h2
    have h3 : (2 : ℝ) * |((reJ p q (q - g) hh).getD k 0 : ℝ) * 2 ^ r.F.toNat -
        e' k * 2 ^ (q * (hh.length - 1) + (-r.F).toNat)| ≤
        2 ^ (q * (hh.length - 1) + (-r.F).toNat) := by
      simp only [he']; exact_mod_cast h2
    rw [coef_real]
    exact half_bound (by positivity) h3
  have hsum : (2 : ℝ) ^ r.F * evalZ hh ((p : ℝ) / 2 ^ q + 1 / 2 ^ g * u) =
      ∑ k ∈ Finset.range r.dE, ((2 : ℝ) ^ r.F * ((reJ p q (q - g) hh).getD k 0 : ℝ) /
        2 ^ (q * (hh.length - 1))) * u ^ k := by
    have hn : (2 : ℝ) ^ (q * (hh.length - 1)) ≠ 0 := by positivity
    have e1 : ∀ k ∈ Finset.range r.dE, ((2 : ℝ) ^ r.F * ((reJ p q (q - g) hh).getD k 0 : ℝ) /
        2 ^ (q * (hh.length - 1))) * u ^ k =
        (2 : ℝ) ^ r.F / 2 ^ (q * (hh.length - 1)) * (((reJ p q (q - g) hh).getD k 0 : ℝ) * u ^ k) := by
      intro k _; ring
    rw [Finset.sum_congr rfl e1, ← Finset.mul_sum, ← reexp_eval_sum p q g hgq hh hpos r.dE hlen u,
      br_div_mul_cancel _ _ _ hn]
  have hev : evalZ (r.ecoef idx) u = ∑ k ∈ Finset.range r.dE, e' k * u ^ k := by
    unfold RowT.ecoef
    rw [evalZ_range, ← sum_range_ite_lt r.L r.dE hLdE (fun k => (r.ehat idx k : ℝ) * u ^ k)]
    apply Finset.sum_congr rfl
    intro k _
    rw [he']
    by_cases hk : k < r.L
    · simp [hk]
    · simp [hk]
  rw [hsum, hev]
  exact sum_dev r.dE (fun k => (2 : ℝ) ^ r.F * ((reJ p q (q - g) hh).getD k 0 : ℝ) / 2 ^ (q * (hh.length - 1)))
    e' hk u hu

/-! ## Magnitude bounds -/

theorem ndist_ehat (r : RowT) (idx k : ℕ) :
    ((ndist (slot r.w (r.t.getD k 0) idx) (2 ^ (r.w - 1)) : ℕ) : ℝ) = |(r.ehat idx k : ℝ)| := by
  have h := ndist_cast (slot r.w (r.t.getD k 0) idx) (2 ^ (r.w - 1))
  push_cast at h
  unfold RowT.ehat
  rw [← Int.cast_natCast, h, Int.cast_abs]

/-- **magnitude**: from the entry bound, `|y| ≤ mag` on `|u| ≤ 2^-uDg` -/
theorem magOk_sound (uDg : ℕ) (r : RowT) (idx mag : ℕ) (h : magOk uDg r idx mag = true) (y u : ℝ)
    (hu : |u| ≤ 1 / 2 ^ uDg) (hy : |y - evalZ (r.ecoef idx) u| ≤ (r.dE : ℝ) / 2) : |y| ≤ mag := by
  have h1 : 2 * lsum ((List.range r.L).map fun k =>
      Nat.shiftLeft (ndist (slot r.w (r.t.getD k 0) idx) (2 ^ (r.w - 1))) (uDg * (r.L - 1 - k))) +
      Nat.shiftLeft r.dE (uDg * (r.L - 1)) ≤ Nat.shiftLeft (2 * mag) (uDg * (r.L - 1)) :=
    Nat.le_of_ble_eq_true h
  simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, lsum_eq_sum, list_sum_range'] at h1
  have h2 : (2 : ℝ) * ∑ k ∈ Finset.range r.L, ((ndist (slot r.w (r.t.getD k 0) idx) (2 ^ (r.w - 1)) : ℕ) : ℝ) *
      2 ^ (uDg * (r.L - 1 - k)) + (r.dE : ℝ) * 2 ^ (uDg * (r.L - 1)) ≤ 2 * (mag : ℝ) * 2 ^ (uDg * (r.L - 1)) := by
    exact_mod_cast h1
  have hD : (0 : ℝ) < 2 ^ (uDg * (r.L - 1)) := by positivity
  have hu' : |u| * 2 ^ uDg ≤ 1 := (le_div_iff₀ (by positivity)).mp hu
  have hterm : ∀ k ∈ Finset.range r.L, |(r.ehat idx k : ℝ) * u ^ k| * 2 ^ (uDg * (r.L - 1)) ≤
      ((ndist (slot r.w (r.t.getD k 0) idx) (2 ^ (r.w - 1)) : ℕ) : ℝ) * 2 ^ (uDg * (r.L - 1 - k)) := by
    intro k hk
    have hkL := Finset.mem_range.mp hk
    rw [ndist_ehat, abs_mul, abs_pow]
    have e : (2 : ℝ) ^ (uDg * (r.L - 1)) = 2 ^ (uDg * (r.L - 1 - k)) * (2 ^ uDg) ^ k := by
      rw [← pow_mul, ← pow_add, ← Nat.mul_add, Nat.sub_add_cancel (by omega : k ≤ r.L - 1)]
    rw [e]
    have h3 : (|u| * 2 ^ uDg) ^ k ≤ 1 := pow_le_one₀ (by positivity) hu'
    have h4 : 0 ≤ |(r.ehat idx k : ℝ)| * 2 ^ (uDg * (r.L - 1 - k)) := by positivity
    calc |(r.ehat idx k : ℝ)| * |u| ^ k * (2 ^ (uDg * (r.L - 1 - k)) * (2 ^ uDg) ^ k)
        = |(r.ehat idx k : ℝ)| * 2 ^ (uDg * (r.L - 1 - k)) * (|u| * 2 ^ uDg) ^ k := by
          rw [mul_pow]; ring
      _ ≤ |(r.ehat idx k : ℝ)| * 2 ^ (uDg * (r.L - 1 - k)) * 1 := mul_le_mul_of_nonneg_left h3 h4
      _ = _ := mul_one _
  have hE : |evalZ (r.ecoef idx) u| * 2 ^ (uDg * (r.L - 1)) ≤
      ∑ k ∈ Finset.range r.L, ((ndist (slot r.w (r.t.getD k 0) idx) (2 ^ (r.w - 1)) : ℕ) : ℝ) *
        2 ^ (uDg * (r.L - 1 - k)) := by
    unfold RowT.ecoef
    rw [evalZ_range]
    calc |∑ k ∈ Finset.range r.L, (r.ehat idx k : ℝ) * u ^ k| * 2 ^ (uDg * (r.L - 1))
        ≤ (∑ k ∈ Finset.range r.L, |(r.ehat idx k : ℝ) * u ^ k|) * 2 ^ (uDg * (r.L - 1)) :=
          mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hD.le
      _ = ∑ k ∈ Finset.range r.L, |(r.ehat idx k : ℝ) * u ^ k| * 2 ^ (uDg * (r.L - 1)) := Finset.sum_mul _ _ _
      _ ≤ _ := Finset.sum_le_sum hterm
  have hyy : |y| ≤ |y - evalZ (r.ecoef idx) u| + |evalZ (r.ecoef idx) u| := by
    have := abs_add_le (y - evalZ (r.ecoef idx) u) (evalZ (r.ecoef idx) u)
    rwa [sub_add_cancel] at this
  have k1 : |y| * 2 ^ (uDg * (r.L - 1)) ≤
      (|y - evalZ (r.ecoef idx) u| + |evalZ (r.ecoef idx) u|) * 2 ^ (uDg * (r.L - 1)) :=
    mul_le_mul_of_nonneg_right hyy hD.le
  have k2 : |y - evalZ (r.ecoef idx) u| * 2 ^ (uDg * (r.L - 1)) ≤ ((r.dE : ℝ) / 2) * 2 ^ (uDg * (r.L - 1)) :=
    mul_le_mul_of_nonneg_right hy hD.le
  have key : |y| * 2 ^ (uDg * (r.L - 1)) ≤ (mag : ℝ) * 2 ^ (uDg * (r.L - 1)) := by linarith
  exact le_of_mul_le_mul_right key hD

/-! ## The row walk -/

theorem rowEntriesOk_zero (p q g W uDg : ℕ) (r : RowT) (hrow : ℕ → List ℤ) (m idx : ℕ) (ms mags : List ℕ) :
    rowEntriesOk p q g W uDg r hrow 0 m idx ms mags = ms.isEmpty := rfl

theorem rowEntriesOk_nil (p q g W uDg : ℕ) (r : RowT) (hrow : ℕ → List ℤ) (n m idx : ℕ) (mags : List ℕ) :
    rowEntriesOk p q g W uDg r hrow (n + 1) m idx [] mags =
      and ((hrow m).all fun x => decide (x = 0)) (rowEntriesOk p q g W uDg r hrow n (m + 1) idx [] []) := rfl

theorem rowEntriesOk_cons (p q g W uDg : ℕ) (r : RowT) (hrow : ℕ → List ℤ) (n m idx m' : ℕ)
    (rest mags : List ℕ) :
    rowEntriesOk p q g W uDg r hrow (n + 1) m idx (m' :: rest) mags =
      cond (Nat.beq m m')
        (and (and (entryOk p q g W r idx (hrow m)) (magOk uDg r idx (mags.headD 0)))
          (rowEntriesOk p q g W uDg r hrow n (m + 1) (idx + 1) rest mags.tail))
        (and (and ((hrow m).all fun x => decide (x = 0)) (Nat.blt m m'))
          (rowEntriesOk p q g W uDg r hrow n (m + 1) idx (m' :: rest) mags)) := rfl

theorem getD_zero_headD (l : List ℕ) : l.getD 0 0 = l.headD 0 := by cases l <;> rfl

theorem getD_succ_tail (l : List ℕ) (j : ℕ) : l.getD (j + 1) 0 = l.tail.getD j 0 := by
  cases l <;> simp

theorem all_zero_of {l : List ℤ} (h : (l.all fun x => decide (x = 0)) = true) : ∀ x ∈ l, x = 0 :=
  fun x hx => of_decide_eq_true (List.all_eq_true.mp h x hx)

/-- invariant of the row walk from entry `m` (position `idx`, remaining sorted entries `ms`, bounds `mags`) -/
theorem rowEntries_spec (p q g W uDg : ℕ) (r : RowT) (hrow : ℕ → List ℤ) :
    ∀ (n m idx : ℕ) (ms mags : List ℕ), rowEntriesOk p q g W uDg r hrow n m idx ms mags = true →
      ms.Pairwise (· < ·) ∧ (∀ x ∈ ms, m ≤ x ∧ x < m + n) ∧
      (∀ j < ms.length, entryOk p q g W r (idx + j) (hrow (ms.getD j 0)) = true ∧
        magOk uDg r (idx + j) (mags.getD j 0) = true) ∧
      (∀ x, m ≤ x → x < m + n → x ∉ ms → ∀ y ∈ hrow x, y = 0)
  | 0, m, idx, ms, mags, h => by
    rw [rowEntriesOk_zero] at h
    cases ms with
    | nil => exact ⟨List.Pairwise.nil, by simp, by simp, fun x h1 h2 _ => absurd h2 (by omega)⟩
    | cons a l => simp at h
  | n + 1, m, idx, [], mags, h => by
    rw [rowEntriesOk_nil] at h
    obtain ⟨h1, h2⟩ := band_true h
    obtain ⟨-, -, -, ih⟩ := rowEntries_spec p q g W uDg r hrow n (m + 1) idx [] [] h2
    refine ⟨List.Pairwise.nil, by simp, by simp, fun x hx1 hx2 _ => ?_⟩
    rcases Nat.eq_or_lt_of_le hx1 with rfl | hlt
    · exact all_zero_of h1
    · exact ih x hlt (by omega) (by simp)
  | n + 1, m, idx, m' :: rest, mags, h => by
    rw [rowEntriesOk_cons] at h
    by_cases hm : m = m'
    · subst m'
      rw [Nat.beq_refl, cond_true] at h
      obtain ⟨h12, h3⟩ := band_true h
      obtain ⟨h1, h2⟩ := band_true h12
      obtain ⟨ihs, ihr, ihe, ihz⟩ :=
        rowEntries_spec p q g W uDg r hrow n (m + 1) (idx + 1) rest mags.tail h3
      refine ⟨List.Pairwise.cons (fun x hx => by have := ihr x hx; show m < x; omega) ihs, ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · omega
        · have := ihr x hx; omega
      · intro j hj
        cases j with
        | zero =>
          rw [Nat.add_zero, List.getD_cons_zero, getD_zero_headD]
          exact ⟨h1, h2⟩
        | succ j =>
          have := ihe j (by simp at hj; omega)
          rw [List.getD_cons_succ, getD_succ_tail, show idx + (j + 1) = idx + 1 + j by omega]
          exact this
      · intro x hx1 hx2 hxn
        have hne : x ≠ m := fun e => hxn (List.mem_cons.mpr (Or.inl e))
        exact ihz x (by omega) (by omega) (fun hx => hxn (List.mem_cons_of_mem _ hx))
    · have hne : Nat.beq m m' = false :=
        Bool.eq_false_iff.mpr (fun hb => hm (Nat.eq_of_beq_eq_true hb))
      rw [hne, cond_false] at h
      obtain ⟨h12, h3⟩ := band_true h
      obtain ⟨h1, -⟩ := band_true h12
      obtain ⟨ihs, ihr, ihe, ihz⟩ := rowEntries_spec p q g W uDg r hrow n (m + 1) idx (m' :: rest) mags h3
      refine ⟨ihs, fun x hx => by have := ihr x hx; omega, ihe, ?_⟩
      intro x hx1 hx2 hxn
      rcases Nat.eq_or_lt_of_le hx1 with rfl | hlt'
      · exact all_zero_of h1
      · exact ihz x hlt' (by omega) hxn

/-! ## The denominator -/

/-- one denominator coefficient check (the body of the loop of `denOk`) -/
def denCoef (Fp E lam dq : ℕ) (Jk d : Bool × ℕ) : Bool :=
  let a := Nat.shiftLeft (Nat.mul Jk.2 lam) Fp
  let b := Nat.shiftLeft (Nat.mul d.2 dq) E
  Nat.ble (Nat.mul 2 (cond (Bool.not (xor Jk.1 d.1)) (ndist a b) (Nat.add a b))) (Nat.mul dq (Nat.pow 2 E))

theorem denCoef_sound (Fp E lam dq : ℕ) (x : ℤ) (d : Bool × ℕ)
    (h : denCoef Fp E lam dq (decide (x < 0), x.natAbs) d = true) :
    2 * |x * lam * 2 ^ Fp - sv d * dq * 2 ^ E| ≤ (dq : ℤ) * 2 ^ E := by
  obtain ⟨s, A⟩ := d
  have h1 : 2 * cond (!(xor (decide (x < 0)) s))
      (ndist (Nat.shiftLeft (x.natAbs * lam) Fp) (Nat.shiftLeft (A * dq) E))
      (Nat.add (Nat.shiftLeft (x.natAbs * lam) Fp) (Nat.shiftLeft (A * dq) E)) ≤ dq * 2 ^ E :=
    Nat.le_of_ble_eq_true h
  have h2 := cond_dist_le _ _ _ _ _ h1
  simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, sv_mul, sv_int] at h2
  push_cast at h2
  exact h2

theorem evalZ_dcoef (r : RowT) (u : ℝ) :
    evalZ r.dcoef u = ∑ k ∈ Finset.range r.Ld, (sv (smDec (slot r.wd r.dh k)) : ℝ) * u ^ k := by
  unfold RowT.dcoef RowT.dhL
  rw [List.map_map]
  exact evalZ_range _ _ _

end Bridge

open Bridge in
/-- **Bridge soundness of a row**: `rowBridgeOk` gives the entry, magnitude and shape fields of `RowSem` for the
table entries `hrow` (`m < n`) at `a = p/2^q + 2^-g u`. -/
theorem rowBridge_sound (n p q g W uDg : ℕ) (r : RowT) (hrow : ℕ → List ℤ) (hgq : g ≤ q) (hW : 2 ≤ W)
    (h : rowBridgeOk n p q g W uDg r hrow = true) :
    (∀ idx < r.nms, ∀ u : ℝ, |u| ≤ 1 →
      |(2 : ℝ) ^ r.F * evalZ (hrow (r.mAt idx)) ((p : ℝ) / 2 ^ q + 1 / 2 ^ g * u) - evalZ (r.ecoef idx) u|
        ≤ (r.dE : ℝ) / 2) ∧
    (∀ idx < r.nms, ∀ u : ℝ, |u| ≤ 1 / 2 ^ uDg →
      |(2 : ℝ) ^ r.F * evalZ (hrow (r.mAt idx)) ((p : ℝ) / 2 ^ q + 1 / 2 ^ g * u)| ≤ (r.magL.getD idx 0 : ℝ)) ∧
    r.msL.length = r.nms ∧ 1 ≤ r.w ∧ r.t.length = r.L ∧ 1 ≤ r.L ∧ r.L ≤ r.dE ∧ r.msL.Pairwise (· < ·) ∧
    (∀ m ∈ r.msL, m < n) ∧ (∀ m < n, m ∉ r.msL → ∀ x ∈ hrow m, x = 0) := by
  have hW1 : 1 ≤ W := by omega
  obtain ⟨h1, h2⟩ := band_true h
  obtain ⟨hl, h1⟩ := band_true h1
  obtain ⟨ht, h1⟩ := band_true h1
  obtain ⟨hL, h1⟩ := band_true h1
  obtain ⟨hw, hLd⟩ := band_true h1
  have hl : r.msL.length = r.nms := Nat.eq_of_beq_eq_true hl
  have ht : r.t.length = r.L := Nat.eq_of_beq_eq_true ht
  have hL : 1 ≤ r.L := Nat.le_of_ble_eq_true hL
  have hw : 1 ≤ r.w := Nat.le_of_ble_eq_true hw
  have hLd : r.L ≤ r.dE := Nat.le_of_ble_eq_true hLd
  obtain ⟨hs, hr, he, hz⟩ := rowEntries_spec p q g W uDg r hrow n 0 0 r.msL r.magL h2
  have hent : ∀ idx < r.nms, ∀ u : ℝ, |u| ≤ 1 →
      |(2 : ℝ) ^ r.F * evalZ (hrow (r.mAt idx)) ((p : ℝ) / 2 ^ q + 1 / 2 ^ g * u) - evalZ (r.ecoef idx) u|
        ≤ (r.dE : ℝ) / 2 := by
    intro idx hidx u hu
    have h3 := (he idx (by omega)).1
    rw [Nat.zero_add] at h3
    exact entryOk_sound p q g W r idx _ hgq hW1 hLd ht h3 u hu
  refine ⟨hent, ?_, hl, hw, ht, hL, hLd, hs, fun m hm => by have := hr m hm; omega,
    fun m hm hn => hz m (Nat.zero_le _) (by omega) hn⟩
  intro idx hidx u hu
  have hmag := (he idx (by omega)).2
  rw [Nat.zero_add] at hmag
  have hu1 : |u| ≤ 1 := hu.trans (by
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num))
  exact magOk_sound uDg r idx _ hmag _ u hu (hent idx hidx u hu1)

open Bridge in
/-- **Denominator bridge soundness**: `denOk` gives the denominator field of `RowSem` for `λ d = λ/dq · dz`. -/
theorem denOk_sound (p q g W : ℕ) (r : RowT) (lam dq : ℕ) (dz : List ℤ) (hgq : g ≤ q) (hW : 2 ≤ W)
    (h : denOk p q g W r lam dq dz = true) :
    ∀ u : ℝ, |u| ≤ 1 →
      |(2 : ℝ) ^ r.Fd * ((lam : ℝ) / dq * evalZ dz ((p : ℝ) / 2 ^ q + 1 / 2 ^ g * u)) - evalZ r.dcoef u|
        ≤ (r.Ld : ℝ) / 2 := by
  intro u hu
  have hW1 : 1 ≤ W := by omega
  have h0 : and (and (and (Nat.ble dz.length r.Ld) (Nat.blt 0 dz.length))
      (and (Nat.blt (reexpM p q (q - g) dz).1 (2 ^ (W - 1))) (Nat.blt 0 dq)))
    ((List.range r.Ld).all fun k => denCoef r.Fd.toNat (q * (dz.length - 1) + (-r.Fd).toNat) lam dq
      (pvGet W r.Ld (reexpP p q (q - g) W (Nat.mul W r.Ld) dz).1 k) (r.dhL.getD k (false, 0))) = true := h
  obtain ⟨hA, hC⟩ := band_true h0
  obtain ⟨hA, hB⟩ := band_true hA
  obtain ⟨hlen, hpos⟩ := band_true hA
  obtain ⟨hM, hdq⟩ := band_true hB
  have hlen : dz.length ≤ r.Ld := Nat.le_of_ble_eq_true hlen
  have hpos : 0 < dz.length := Nat.le_of_ble_eq_true hpos
  have hM : (reexpM p q (q - g) dz).1 < 2 ^ (W - 1) := Nat.le_of_ble_eq_true hM
  have hdq : 0 < dq := Nat.le_of_ble_eq_true hdq
  have hC' := List.all_eq_true.mp hC
  have hdqR : (0 : ℝ) < dq := by exact_mod_cast hdq
  have hd : ∀ k < r.Ld, r.dhL.getD k (false, 0) = smDec (slot r.wd r.dh k) := by
    intro k hk
    unfold RowT.dhL
    rw [getD_of_lt _ _ (by rw [List.length_map, List.length_range]; exact hk), List.getElem_map,
      List.getElem_range]
  have hk : ∀ k < r.Ld, |(2 : ℝ) ^ r.Fd * lam / dq * ((reJ p q (q - g) dz).getD k 0 : ℝ) /
      2 ^ (q * (dz.length - 1)) - (sv (smDec (slot r.wd r.dh k)) : ℝ)| ≤ 1 / 2 := by
    intro k hkL
    have h1 := hC' k (List.mem_range.mpr hkL)
    rw [reexp_decode p q (q - g) W r.Ld hW1 dz hlen hM k hkL, hd k hkL] at h1
    have h2 := denCoef_sound _ _ _ _ _ _ h1
    have h3 : (2 : ℝ) * |((reJ p q (q - g) dz).getD k 0 : ℝ) * lam * 2 ^ r.Fd.toNat -
        (sv (smDec (slot r.wd r.dh k)) : ℝ) * dq * 2 ^ (q * (dz.length - 1) + (-r.Fd).toNat)| ≤
        dq * 2 ^ (q * (dz.length - 1) + (-r.Fd).toNat) := by
      exact_mod_cast h2
    have e3 : (sv (smDec (slot r.wd r.dh k)) : ℝ) * dq * 2 ^ (q * (dz.length - 1) + (-r.Fd).toNat) =
        (sv (smDec (slot r.wd r.dh k)) : ℝ) * (dq * 2 ^ (q * (dz.length - 1) + (-r.Fd).toNat)) :=
      mul_assoc _ _ _
    rw [e3] at h3
    have e2 : (2 : ℝ) ^ r.Fd * lam / dq * ((reJ p q (q - g) dz).getD k 0 : ℝ) / 2 ^ (q * (dz.length - 1)) =
        ((reJ p q (q - g) dz).getD k 0 : ℝ) * lam * 2 ^ r.Fd.toNat /
          (dq * 2 ^ (q * (dz.length - 1) + (-r.Fd).toNat)) := by
      rw [zpow_two_split, pow_add]; ring
    rw [e2]
    exact half_bound (mul_pos hdqR (by positivity)) h3
  have hsum : (2 : ℝ) ^ r.Fd * ((lam : ℝ) / dq * evalZ dz ((p : ℝ) / 2 ^ q + 1 / 2 ^ g * u)) =
      ∑ k ∈ Finset.range r.Ld, ((2 : ℝ) ^ r.Fd * lam / dq * ((reJ p q (q - g) dz).getD k 0 : ℝ) /
        2 ^ (q * (dz.length - 1))) * u ^ k := by
    have hn : (2 : ℝ) ^ (q * (dz.length - 1)) ≠ 0 := by positivity
    have e1 : ∀ k ∈ Finset.range r.Ld, ((2 : ℝ) ^ r.Fd * lam / dq * ((reJ p q (q - g) dz).getD k 0 : ℝ) /
        2 ^ (q * (dz.length - 1))) * u ^ k =
        (2 : ℝ) ^ r.Fd * lam / dq / 2 ^ (q * (dz.length - 1)) *
          (((reJ p q (q - g) dz).getD k 0 : ℝ) * u ^ k) := by
      intro k _; ring
    rw [Finset.sum_congr rfl e1, ← Finset.mul_sum, ← reexp_eval_sum p q g hgq dz hpos r.Ld hlen u,
      br_div_mul_cancel _ _ _ hn]
    ring
  rw [hsum, evalZ_dcoef]
  exact sum_dev r.Ld (fun k => (2 : ℝ) ^ r.Fd * lam / dq * ((reJ p q (q - g) dz).getD k 0 : ℝ) /
    2 ^ (q * (dz.length - 1))) (fun k => (sv (smDec (slot r.wd r.dh k)) : ℝ)) hk u hu

end ThomsonCompact.Floor.B
