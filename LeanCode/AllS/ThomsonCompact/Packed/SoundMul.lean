import ThomsonCompact.Packed.Sound

/-!
# Soundness of the packed product (truncation and rounding into the error)
-/

namespace ThomsonCompact.Packed
open Nat

variable {N S B W : ℕ}

theorem drop_map' {α β : Type*} (f : α → β) :
    ∀ (L : List α) (n : ℕ), (L.map f).drop n = (L.drop n).map f
  | [], n => by simp
  | x :: L, 0 => by simp
  | x :: L, n + 1 => by rw [List.map_cons, List.drop_succ_cons, List.drop_succ_cons, drop_map' f L n]

theorem evalZ_take_drop (z : List ℤ) (n : ℕ) (t : ℝ) :
    evalZ z t = evalZ (z.take n) t + t ^ n * evalZ (z.drop n) t := by
  simp only [evalZ]
  rw [horner_take_drop t n (z.map (Int.cast : ℤ → ℝ)), take_map', drop_map']

/-- the real error bookkeeping of the truncated, rounded product -/
theorem mul_err_real {D f g PA PB sA sB eA eB X0 Zc Tl tl c1 c2 m : ℝ} (hD : 0 < D)
    (hprod : |f * g - PA * PB / (D * D)| ≤ (sA * eB + sB * eA + eA * eB) / (D * D))
    (hzt : PA * PB = X0 + Tl) (htl : |Tl| ≤ tl) (hround : |X0 - D * Zc| ≤ m * D)
    (hc1 : (sA * eB + sB * eA + eA * eB) / D ≤ c1) (hc2 : tl / D ≤ c2) :
    |f * g - Zc / D| ≤ (c1 + c2 + m) / D := by
  have hDD : 0 < D * D := by positivity
  have key : f * g - Zc / D = (f * g - PA * PB / (D * D)) + (X0 - D * Zc) / (D * D) + Tl / (D * D) := by
    rw [hzt]; field_simp; ring
  have b1 : |(X0 - D * Zc) / (D * D)| ≤ m / D := by
    rw [abs_div, abs_of_pos hDD, div_le_div_iff₀ hDD hD]
    nlinarith [abs_nonneg (X0 - D * Zc)]
  have b2 : |Tl / (D * D)| ≤ tl / (D * D) := by
    rw [abs_div, abs_of_pos hDD]; exact div_le_div_of_nonneg_right htl hDD.le
  have b3 : (sA * eB + sB * eA + eA * eB) / (D * D) ≤ c1 / D := by
    rw [← div_div]; exact div_le_div_of_nonneg_right hc1 hD.le
  have b4 : tl / (D * D) ≤ c2 / D := by
    rw [← div_div]; exact div_le_div_of_nonneg_right hc2 hD.le
  rw [key]
  calc |(f * g - PA * PB / (D * D)) + (X0 - D * Zc) / (D * D) + Tl / (D * D)|
      ≤ |f * g - PA * PB / (D * D)| + |(X0 - D * Zc) / (D * D)| + |Tl / (D * D)| := abs_add_three _ _ _
    _ ≤ c1 / D + m / D + c2 / D := by linarith
    _ = (c1 + c2 + m) / D := by ring

theorem mul_sound (hg : Good N S B W) {A B' : TM} {f g : ℝ → ℝ}
    (hA : Encl (mkCtx N S B W) A f) (hB : Encl (mkCtx N S B W) B' g)
    (hok : (mul (mkCtx N S B W) A B').ok = true) :
    Encl (mkCtx N S B W) (mul (mkCtx N S B W) A B') (fun t => f t * g t) := by
  obtain ⟨csA, alA, hRA, hfA⟩ := hA
  obtain ⟨csB, alB, hRB, hfB⟩ := hB
  have hW1 := hg.W1
  have hW0 : 0 < W := by omega
  have hlA : csA.length = N + 1 := hRA.lcs
  have hlB : csB.length = N + 1 := hRB.lcs
  have hlaA : alA.length = N + 1 := hRA.lal
  have hlaB : alB.length = N + 1 := hRB.lal
  set z := convL csA csB with hz
  set γ := convL alA alB with hγ
  have hzlen : z.length = 2 * N + 1 := by
    rw [hz, length_convL csB (List.ne_nil_of_length_pos (by omega)) csA
      (List.ne_nil_of_length_pos (by omega)), hlA, hlB]
    omega
  have hγlen : γ.length = 2 * N + 1 := by
    rw [hγ, length_convL alB (List.ne_nil_of_length_pos (by omega)) alA
      (List.ne_nil_of_length_pos (by omega)), hlaA, hlaB]
    omega
  have hdom : Dom z γ := Dom.convL hRB.dom csA alA (by rw [hlA, hlaA]) hRA.dom
  have hγsum : γ.sum = A.s * B'.s := by rw [hγ, sum_convL, ← hRA.hs, ← hRB.hs]
  have hsA := hRA.sB
  have hsB := hRB.sB
  simp only [mk_B] at hsA hsB
  have hsAB : A.s * B'.s < 2 ^ (2 * B) := by
    rw [two_mul, pow_add]; exact Nat.mul_lt_mul_of_lt_of_lt hsA hsB
  have hzb : ∀ x ∈ z, |x| < 2 ^ (2 * B) := by
    intro x hx
    have h1 := hdom.abs_le_sum hx
    have h2 : ((γ.sum : ℕ) : ℤ) < 2 ^ (2 * B) := by rw [hγsum]; exact_mod_cast hsAB
    linarith
  have hγb : ∀ d ∈ γ, d < 2 ^ (2 * B) := fun d hd => (mem_le_sum hd).trans_lt (hγsum ▸ hsAB)
  have hγW : ∀ d ∈ γ, d < 2 ^ W := fun d hd =>
    (hγb d hd).trans_le (Nat.pow_le_pow_right (by norm_num) (by have := hg.BW; omega))
  -- signed coefficients
  have hV : ((A.v * B'.v : ℕ) : ℤ) % 2 ^ (W * (2 * N + 1)) = horner (2 ^ W : ℤ) z % 2 ^ (W * (2 * N + 1)) := by
    have hA' := hRA.hv
    have hB' := hRB.hv
    simp only [mk_W, mk_K] at hA' hB'
    push_cast
    rw [Int.mul_emod, hA', hB', Int.emod_emod, Int.emod_emod, ← Int.mul_emod, hz, horner_convL]
  have hv := round_signed hg z hzlen hzb (A.v * B'.v) hV
  -- magnitude bounds
  have hG : A.a * B'.a = Nat.ofDigits (2 ^ W) γ := by
    rw [hRA.ha, hRB.ha, hγ, ofDigits_convL]; rfl
  have hsplit := ofDigits_take_drop hW0 γ hγW (N + 1)
  have hGm : (A.a * B'.a) &&& (mkCtx N S B W).maskWm = Nat.ofDigits (2 ^ W) (γ.take (N + 1)) := by
    rw [mk_maskWm, Nat.and_two_pow_sub_one_eq_mod, hG]; exact hsplit.1
  have hlt : (γ.take (N + 1)).length = N + 1 := by simp [hγlen]; omega
  have ha := round_abs hg (γ.take (N + 1)) hlt (fun d hd => hγb d (List.mem_of_mem_take hd))
  set alC := (γ.take (N + 1)).map (fun g => (g + (2 ^ S - 1)) / 2 ^ S) with halC
  have hsumC : alC.sum ≤ A.s * B'.s :=
    calc alC.sum ≤ (γ.take (N + 1)).sum := sum_map_ceil_le S _
      _ ≤ γ.sum := sum_take_le _ _
      _ = A.s * B'.s := hγsum
  have hmodC : Nat.ofDigits (2 ^ W) alC % (2 ^ W - 1) = alC.sum :=
    ofDigits_mod_pred (by have := hg.BW; omega) alC (by have := hg.pow_lt; omega)
  have haC : (mul (mkCtx N S B W) A B').a = Nat.ofDigits (2 ^ W) alC := by
    show ((((A.a * B'.a) &&& (mkCtx N S B W).maskWm) + (mkCtx N S B W).ceilAdd) &&&
      (mkCtx N S B W).rmask) >>> (mkCtx N S B W).S = _
    rw [hGm]; exact ha
  have hsC : (mul (mkCtx N S B W) A B').s = alC.sum := by
    show (mul (mkCtx N S B W) A B').a % (mkCtx N S B W).modW = _
    rw [haC, mk_modW, hmodC]
  have hs : (mul (mkCtx N S B W) A B').s < 2 ^ B := by
    have e : (mul (mkCtx N S B W) A B').ok =
        (A.ok && B'.ok && Nat.blt (mul (mkCtx N S B W) A B').s (mkCtx N S B W).twoB) := rfl
    rw [e] at hok
    simp only [Bool.and_eq_true, Nat.blt_eq] at hok
    exact hok.2
  -- tail mass
  have htail : ((A.a * B'.a) >>> (W * (N + 1))) % (2 ^ W - 1) = (γ.drop (N + 1)).sum := by
    rw [Nat.shiftRight_eq_div_pow, hG, hsplit.2]
    apply ofDigits_mod_pred (by have := hg.BW; omega)
    have : (γ.drop (N + 1)).sum ≤ γ.sum := by
      conv_rhs => rw [← List.take_append_drop (N + 1) γ]
      rw [List.sum_append]; omega
    have := hg.pow_lt
    omega
  refine ⟨(z.take (N + 1)).map (fun x => x / 2 ^ S), alC, ⟨?_, ?_, ?_, haC, dom_round S hdom (N + 1), hsC, hs⟩, ?_⟩
  · simp [hzlen]; omega
  · show alC.length = N + 1
    rw [halC, List.length_map, hlt]
  · exact hv
  · intro t ht
    have hta : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
    have hD : (0 : ℝ) < 2 ^ S := by positivity
    have h1 := hfA t ht
    have h2 := hfB t ht
    simp only [mk_S] at h1 h2
    have hpA := abs_evalZ_le_s hRA t hta
    have hpB := abs_evalZ_le_s hRB t hta
    have hprod := prod_err hD h1 h2 hpA hpB (by positivity) (by positivity)
    have hzt : evalZ csA t * evalZ csB t = evalZ (z.take (N + 1)) t + t ^ (N + 1) * evalZ (z.drop (N + 1)) t := by
      rw [← evalZ_convL, ← hz, ← evalZ_take_drop]
    have htl : |t ^ (N + 1) * evalZ (z.drop (N + 1)) t| ≤ ((γ.drop (N + 1)).sum : ℝ) := by
      rw [abs_mul, abs_pow]
      have h3 := abs_evalZ_le (hdom.drop (N + 1)) t hta
      have h4 : |t| ^ (N + 1) ≤ 1 := pow_le_one₀ (abs_nonneg t) hta
      calc |t| ^ (N + 1) * |evalZ (z.drop (N + 1)) t| ≤ 1 * ((γ.drop (N + 1)).sum : ℝ) :=
            mul_le_mul h4 h3 (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    have hround := eval_round S t hta (z.take (N + 1))
    rw [show (z.take (N + 1)).length = N + 1 by simp [hzlen]; omega] at hround
    have hcd1 := le_cdiv S (A.s * B'.e + B'.s * A.e + A.e * B'.e)
    have hcd2 := le_cdiv S ((γ.drop (N + 1)).sum)
    push_cast at hcd1 hcd2 hround
    show |f t * g t - evalZ ((z.take (N + 1)).map (fun x => x / 2 ^ S)) t / 2 ^ S| ≤
      ((cdiv S (A.s * B'.e + B'.s * A.e + A.e * B'.e) +
        cdiv S (((A.a * B'.a) >>> (W * (N + 1))) % (2 ^ W - 1)) + (N + 1) : ℕ) : ℝ) / 2 ^ S
    rw [htail]
    push_cast
    exact mul_err_real hD hprod hzt htl hround hcd1 hcd2

end ThomsonCompact.Packed
