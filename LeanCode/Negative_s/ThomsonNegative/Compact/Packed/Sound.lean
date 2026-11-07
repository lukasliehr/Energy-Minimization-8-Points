import ThomsonNegative.Compact.Packed.Round

/-!
# Soundness of the packed Taylor-model operations

For `c = mkCtx N S B W` with `Good N S B W`:
`neg_sound`, `add_sound`, `addC_sound`, `smul_sound`, `mul_sound`, `range_sound`, `recip_sound`, `ofPQ_sound`.
Each takes enclosures of the inputs and the computed `ok` flag of the result.
-/

namespace ThomsonNegative.Compact.Packed
open Nat

/-! ## Helpers -/

theorem neg_emod_emod (a n : ℤ) : (-(a % n)) % n = (-a) % n := by
  have : -(a % n) = -a + n * (a / n) := by rw [Int.emod_def]; ring
  rw [this, Int.add_mul_emod_self_left]

theorem horner_neg {R : Type*} [CommRing R] (t : R) : ∀ L : List R, horner t (L.map (fun x => -x)) = -horner t L
  | [] => by simp
  | c :: L => by simp only [List.map_cons, horner_cons, horner_neg t L]; ring

theorem evalZ_neg (L : List ℤ) (t : ℝ) : evalZ (L.map (fun x => -x)) t = -evalZ L t := by
  have : (L.map (fun x => -x)).map (Int.cast : ℤ → ℝ) = (L.map (Int.cast : ℤ → ℝ)).map (fun x => -x) := by
    simp [List.map_map, Function.comp_def]
  rw [evalZ, this, horner_neg]; rfl

theorem evalZ_addL (a b : List ℤ) (t : ℝ) : evalZ (addL a b) t = evalZ a t + evalZ b t := by
  have h := map_addL (Int.castRingHom ℝ) a b
  simp only [evalZ]
  rw [show (Int.cast : ℤ → ℝ) = (Int.castRingHom ℝ : ℤ → ℝ) from rfl, h, horner_addL]

theorem evalZ_scaleL (q : ℤ) (a : List ℤ) (t : ℝ) : evalZ (scaleL q a) t = q * evalZ a t := by
  have h := map_scaleL (Int.castRingHom ℝ) q a
  simp only [evalZ]
  rw [show (Int.cast : ℤ → ℝ) = (Int.castRingHom ℝ : ℤ → ℝ) from rfl, h, horner_scaleL]

theorem evalZ_single (z : ℤ) (t : ℝ) : evalZ [z] t = z := by simp [evalZ]

theorem Dom.neg {a : List ℤ} {α : List ℕ} (h : Dom a α) : Dom (a.map (fun x => -x)) α := by
  intro k
  rw [getD_map_of_zero (fun x : ℤ => -x) 0 0 (by simp), abs_neg]
  exact h k

theorem ceil_le_self (S g : ℕ) : (g + (2 ^ S - 1)) / 2 ^ S ≤ g := by
  have hpos := Nat.two_pow_pos S
  have : (g + (2 ^ S - 1)) / 2 ^ S < g + 1 := by
    rw [Nat.div_lt_iff_lt_mul hpos]
    have : g ≤ g * 2 ^ S := Nat.le_mul_of_pos_right g hpos
    rw [Nat.add_mul, one_mul]
    omega
  omega

theorem sum_map_ceil_le (S : ℕ) : ∀ L : List ℕ, (L.map (fun g => (g + (2 ^ S - 1)) / 2 ^ S)).sum ≤ L.sum
  | [] => by simp
  | g :: L => by
    simp only [List.map_cons, List.sum_cons]
    have := ceil_le_self S g
    have := sum_map_ceil_le S L
    omega

theorem sum_take_le (L : List ℕ) (n : ℕ) : (L.take n).sum ≤ L.sum := by
  conv_rhs => rw [← List.take_append_drop n L]
  rw [List.sum_append]
  omega

theorem sum_scaleL_nat (q : ℕ) (L : List ℕ) : (scaleL q L).sum = q * L.sum := by
  rw [← horner_one, horner_scaleL, horner_one]

theorem ofDigits_scaleL (b q : ℕ) (L : List ℕ) : Nat.ofDigits b (scaleL q L) = q * Nat.ofDigits b L := by
  rw [ofDigits_eq_horner, ofDigits_eq_horner, horner_scaleL]

theorem two_pow_W {W : ℕ} (hW : 1 ≤ W) : (2 : ℕ) ^ W = 2 * 2 ^ (W - 1) := by
  conv_lhs => rw [show W = (W - 1) + 1 by omega]
  exact pow_succ' 2 (W - 1)

/-- `2^(2B) < 2^W - 1` and friends -/
theorem Good.pow_lt {N S B W : ℕ} (hg : Good N S B W) : 2 ^ (2 * B) + 2 ^ B < 2 ^ W - 1 := by
  have h1 : 2 ^ (2 * B) ≤ 2 ^ (W - 2) := Nat.pow_le_pow_right (by norm_num) (by have := hg.BW; omega)
  have h2 : 2 ^ B < 2 ^ (2 * B) := Nat.pow_lt_pow_right (by norm_num) (by have := hg.B1; omega)
  have h3 : 2 ^ W = 4 * 2 ^ (W - 2) := by
    conv_lhs => rw [show W = (W - 2) + 2 by have := hg.BW; omega]
    rw [pow_add]; ring
  omega

theorem Good.K_ge {N S B W : ℕ} (hg : Good N S B W) : B ≤ W * (2 * N + 1) := by
  have := hg.BW; nlinarith

theorem Good.m_le_K {N S B W : ℕ} (_hg : Good N S B W) : W * (N + 1) ≤ W * (2 * N + 1) :=
  Nat.mul_le_mul_left _ (by omega)

theorem toZ_mod_mask {K x : ℕ} : (((x &&& (2 ^ K - 1)) : ℕ) : ℤ) = (x : ℤ) % 2 ^ K := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Int.natCast_emod]; push_cast; rfl

/-! ## Basic enclosures -/

/-- A TM encloses its own polynomial. -/
theorem Encl.self {c : Ctx} {T : TM} {cs : List ℤ} {al : List ℕ} (h : Rep c T cs al) :
    Encl c T (fun t => evalZ cs t / 2 ^ c.S) :=
  ⟨cs, al, h, fun t _ => by simp only [sub_self, abs_zero]; positivity⟩

theorem range_sound {c : Ctx} {T : TM} {f : ℝ → ℝ} (h : Encl c T f) :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1, |f t| ≤ (range T : ℝ) / 2 ^ c.S := by
  obtain ⟨cs, al, hR, hf⟩ := h
  intro t ht
  have hta : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
  have h1 := hf t ht
  have h2 := abs_evalZ_le_s hR t hta
  have hD : (0 : ℝ) < 2 ^ c.S := by positivity
  have h3 : |evalZ cs t / 2 ^ c.S| ≤ (T.s : ℝ) / 2 ^ c.S := by
    rw [abs_div, abs_of_pos hD]; exact div_le_div_of_nonneg_right h2 hD.le
  have : (range T : ℝ) = T.s + T.e := by simp [range]
  rw [this, add_div]
  calc |f t| ≤ |f t - evalZ cs t / 2 ^ c.S| + |evalZ cs t / 2 ^ c.S| := by
        have := abs_sub_abs_le_abs_sub (f t) (evalZ cs t / 2 ^ c.S); linarith
    _ ≤ (T.e : ℝ) / 2 ^ c.S + (T.s : ℝ) / 2 ^ c.S := add_le_add h1 h3
    _ = _ := by ring

/-! ## neg, add, addC -/

variable {N S B W : ℕ}

theorem neg_sound {A : TM} {f : ℝ → ℝ} (hA : Encl (mkCtx N S B W) A f) :
    Encl (mkCtx N S B W) (neg (mkCtx N S B W) A) (fun t => -f t) := by
  obtain ⟨cs, al, hR, hf⟩ := hA
  have hvle : A.v ≤ 2 ^ (W * (2 * N + 1)) := hR.v_lt.le
  refine ⟨cs.map (fun x => -x), al, ⟨by simp [hR.lcs], hR.lal, ?_, hR.ha, hR.dom.neg, hR.hs, hR.sB⟩, ?_⟩
  · show ((((2 ^ (W * (2 * N + 1)) - A.v) &&& (2 ^ (W * (2 * N + 1)) - 1) : ℕ)) : ℤ) = _
    rw [toZ_mod_mask, Nat.cast_sub hvle, mk_W, mk_K, horner_neg]
    have hv := hR.hv
    simp only [mk_W, mk_K] at hv
    rw [show ((2 ^ (W * (2 * N + 1)) : ℕ) : ℤ) - (A.v : ℤ) = -(A.v : ℤ) + 2 ^ (W * (2 * N + 1)) * 1 by
      push_cast; ring, Int.add_mul_emod_self_left, hv, neg_emod_emod]
  · intro t ht
    have := hf t ht
    show |-f t - evalZ (cs.map (fun x => -x)) t / 2 ^ S| ≤ (A.e : ℝ) / 2 ^ S
    rw [evalZ_neg, show -f t - -evalZ cs t / 2 ^ S = -(f t - evalZ cs t / 2 ^ S) by ring, abs_neg]
    exact this

theorem add_sound {A B' : TM} {f g : ℝ → ℝ} (hA : Encl (mkCtx N S B W) A f) (hB : Encl (mkCtx N S B W) B' g)
    (hok : (add (mkCtx N S B W) A B').ok = true) :
    Encl (mkCtx N S B W) (add (mkCtx N S B W) A B') (fun t => f t + g t) := by
  obtain ⟨csA, alA, hRA, hfA⟩ := hA
  obtain ⟨csB, alB, hRB, hfB⟩ := hB
  have hs : A.s + B'.s < 2 ^ B := by
    have : (add (mkCtx N S B W) A B').ok = (A.ok && B'.ok && Nat.blt (A.s + B'.s) (2 ^ B)) := rfl
    rw [this] at hok
    simp only [Bool.and_eq_true, Nat.blt_eq] at hok
    exact hok.2
  refine ⟨addL csA csB, addL alA alB, ⟨?_, ?_, ?_, ?_, hRA.dom.addL hRB.dom, ?_, hs⟩, ?_⟩
  · rw [length_addL, hRA.lcs, hRB.lcs]; simp
  · rw [length_addL, hRA.lal, hRB.lal]; simp
  · show (((A.v + B'.v) &&& (2 ^ (W * (2 * N + 1)) - 1) : ℕ) : ℤ) = _
    have hA' := hRA.hv
    have hB' := hRB.hv
    simp only [mk_W, mk_K] at hA' hB' ⊢
    rw [toZ_mod_mask, horner_addL]
    push_cast
    rw [Int.add_emod, hA', hB', Int.emod_emod, Int.emod_emod, ← Int.add_emod]
  · show A.a + B'.a = _
    rw [hRA.ha, hRB.ha, ofDigits_addL]
  · show A.s + B'.s = _
    rw [hRA.hs, hRB.hs, sum_addL_nat]
  · intro t ht
    have h1 := hfA t ht
    have h2 := hfB t ht
    show |f t + g t - evalZ (addL csA csB) t / 2 ^ S| ≤ ((A.e + B'.e : ℕ) : ℝ) / 2 ^ S
    rw [evalZ_addL]
    push_cast
    calc |f t + g t - (evalZ csA t + evalZ csB t) / 2 ^ S|
        = |(f t - evalZ csA t / 2 ^ S) + (g t - evalZ csB t / 2 ^ S)| := by ring_nf
      _ ≤ |f t - evalZ csA t / 2 ^ S| + |g t - evalZ csB t / 2 ^ S| := abs_add_le _ _
      _ ≤ (A.e : ℝ) / 2 ^ S + (B'.e : ℝ) / 2 ^ S := add_le_add h1 h2
      _ = ((A.e : ℝ) + B'.e) / 2 ^ S := by ring

/-- Adding the constant `±mag·2^-S` encloses `f + κ` for every `κ` within `dq·2^-S` of it. -/
theorem addC_sound {A : TM} {f : ℝ → ℝ} (hA : Encl (mkCtx N S B W) A f) (ng : Bool) (mag dq : ℕ) (κ : ℝ)
    (hκ : |κ - (if ng then -(mag : ℝ) else mag) / 2 ^ S| ≤ (dq : ℝ) / 2 ^ S)
    (hok : (addC (mkCtx N S B W) ng mag dq A).ok = true) (hg : Good N S B W) :
    Encl (mkCtx N S B W) (addC (mkCtx N S B W) ng mag dq A) (fun t => f t + κ) := by
  obtain ⟨cs, al, hR, hf⟩ := hA
  have hs : A.s + mag < 2 ^ B := by
    have : (addC (mkCtx N S B W) ng mag dq A).ok = (A.ok && Nat.blt (A.s + mag) (2 ^ B)) := rfl
    rw [this] at hok
    simp only [Bool.and_eq_true, Nat.blt_eq] at hok
    exact hok.2
  have hm1 : 1 ≤ cs.length := by rw [hR.lcs]; simp
  have hmagK : mag ≤ 2 ^ (W * (2 * N + 1)) :=
    (by omega : mag ≤ 2 ^ B).trans (Nat.pow_le_pow_right (by norm_num) hg.K_ge)
  set z : ℤ := if ng then -(mag : ℤ) else (mag : ℤ) with hz
  refine ⟨addL cs [z], addL al [mag], ⟨?_, ?_, ?_, ?_, ?_, ?_, hs⟩, ?_⟩
  · rw [length_addL, hR.lcs]; simp
  · rw [length_addL, hR.lal]; simp
  · show (((A.v + cond ng (2 ^ (W * (2 * N + 1)) - mag) mag) &&& (2 ^ (W * (2 * N + 1)) - 1) : ℕ) : ℤ) = _
    have hv := hR.hv
    simp only [mk_W, mk_K] at hv ⊢
    rw [toZ_mod_mask, horner_addL]
    cases ng
    · simp only [cond_false, hz, if_false]
      push_cast
      rw [Int.add_emod, hv, Int.emod_emod, ← Int.add_emod]
      simp [horner]
    · simp only [cond_true, hz, if_true]
      rw [Nat.cast_add, Nat.cast_sub hmagK]
      push_cast
      rw [show (A.v : ℤ) + (2 ^ (W * (2 * N + 1)) - (mag : ℤ)) = ((A.v : ℤ) + -(mag : ℤ)) +
          2 ^ (W * (2 * N + 1)) * 1 by ring, Int.add_mul_emod_self_left, Int.add_emod, hv, Int.emod_emod,
        ← Int.add_emod]
      simp [horner]
  · show A.a + mag = _
    rw [hR.ha, ofDigits_addL]; simp
  · apply hR.dom.addL
    intro k
    cases k with
    | zero => cases ng <;> simp [hz]
    | succ k => simp
  · show A.s + mag = _
    rw [hR.hs, sum_addL_nat]; simp
  · intro t ht
    have h1 := hf t ht
    show |f t + κ - evalZ (addL cs [z]) t / 2 ^ S| ≤ ((A.e + dq : ℕ) : ℝ) / 2 ^ S
    rw [evalZ_addL, evalZ_single]
    have hzr : ((z : ℤ) : ℝ) = (if ng then -(mag : ℝ) else mag) := by
      rw [hz]; split_ifs <;> push_cast <;> rfl
    rw [hzr]
    push_cast
    calc |f t + κ - (evalZ cs t + (if ng then -(mag : ℝ) else mag)) / 2 ^ S|
        = |(f t - evalZ cs t / 2 ^ S) + (κ - (if ng then -(mag : ℝ) else mag) / 2 ^ S)| := by ring_nf
      _ ≤ |f t - evalZ cs t / 2 ^ S| + |κ - (if ng then -(mag : ℝ) else mag) / 2 ^ S| := abs_add_le _ _
      _ ≤ (A.e : ℝ) / 2 ^ S + (dq : ℝ) / 2 ^ S := add_le_add h1 hκ
      _ = ((A.e : ℝ) + dq) / 2 ^ S := by ring

end ThomsonNegative.Compact.Packed
