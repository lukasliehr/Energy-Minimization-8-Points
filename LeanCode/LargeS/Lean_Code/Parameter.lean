import Lean_Code.Antiprism

open Real

noncomputable section

namespace SquareAntiprismVerification

lemma sqrt_two_pos : 0 < √(2 : ℝ) := Real.sqrt_pos.2 (by norm_num)

lemma sqrt_two_lt_two : √(2 : ℝ) < 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  nlinarith

lemma one_lt_sqrt_two : 1 < √(2 : ℝ) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp := sqrt_two_pos
  nlinarith

lemma aInf_mem_Ioo : aInf ∈ Set.Ioo (0 : ℝ) 1 := by
  unfold aInf
  constructor
  · nlinarith [one_lt_sqrt_two]
  · nlinarith [sqrt_two_lt_two]

lemma dA_aInf : dA aInf = tau := by rfl

lemma dB_aInf : dB aInf = 2 * tau := by
  unfold dB tau
  ring

lemma dC_aInf : dC aInf = tau := by
  have hs2 : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold dC tau aInf
  field_simp
  nlinarith [hs2]

lemma q_pos (s : ℝ) (hs : 0 ≤ s) : 0 < q s := by
  unfold q
  linarith

lemma dA_pos {a : ℝ} (ha : a < 1) : 0 < dA a := by
  unfold dA
  linarith

lemma dB_pos {a : ℝ} (ha : a < 1) : 0 < dB a := by
  unfold dB
  linarith

lemma dC_pos {a : ℝ} (ha : 0 ≤ a) : 0 < dC a := by
  unfold dC
  have hs₂ := sqrt_two_pos
  have hs₂' := sqrt_two_lt_two
  nlinarith

lemma dD_pos {a : ℝ} (ha : 0 ≤ a) : 0 < dD a := by
  unfold dD
  have hs₂ := sqrt_two_pos
  have hs₂' := sqrt_two_lt_two
  nlinarith

lemma rpow_neg_lt_rpow_neg {x y p : ℝ} (hx : 0 < x) (hxy : x < y) (hp : 0 < p) :
    y ^ (-p) < x ^ (-p) := by
  rw [Real.rpow_neg (le_of_lt hx), Real.rpow_neg (le_of_lt (hx.trans hxy))]
  simpa only [one_div] using one_div_lt_one_div_of_lt (Real.rpow_pos_of_pos hx p)
    (Real.rpow_lt_rpow (le_of_lt hx) hxy hp)

lemma F_strictMonoOn (s : ℝ) (hs : 0 ≤ s) : StrictMonoOn (F s) (Set.Ico 0 1) := by
  intro a ha b hb hab
  have hq := q_pos s hs
  have hAa : 0 < dA a := dA_pos ha.2
  have hAb : 0 < dA b := dA_pos hb.2
  have hBa : 0 < dB a := dB_pos ha.2
  have hBb : 0 < dB b := dB_pos hb.2
  have hCa : 0 < dC a := dC_pos ha.1
  have hCb : 0 < dC b := dC_pos hb.1
  have hDa : 0 < dD a := dD_pos ha.1
  have hDb : 0 < dD b := dD_pos hb.1
  have hdA : dA b < dA a := by unfold dA; linarith
  have hdB : dB b < dB a := by unfold dB; linarith
  have hdC : dC a < dC b := by
    unfold dC
    have : 0 < 2 + √(2 : ℝ) := by positivity
    nlinarith
  have hdD : dD a < dD b := by
    unfold dD
    have : 0 < 2 - √(2 : ℝ) := sub_pos.2 sqrt_two_lt_two
    nlinarith
  have hA := rpow_neg_lt_rpow_neg hAb hdA hq
  have hB := rpow_neg_lt_rpow_neg hBb hdB hq
  have hC := rpow_neg_lt_rpow_neg hCa hdC hq
  have hD := rpow_neg_lt_rpow_neg hDa hdD hq
  have hA' : 16 * dA a ^ (-q s) < 16 * dA b ^ (-q s) :=
    mul_lt_mul_of_pos_left hA (by norm_num)
  have hB' : 16 * dB a ^ (-q s) < 16 * dB b ^ (-q s) :=
    mul_lt_mul_of_pos_left hB (by norm_num)
  have hC' : 8 * (2 + √2) * dC b ^ (-q s) < 8 * (2 + √2) * dC a ^ (-q s) :=
    mul_lt_mul_of_pos_left hC (by positivity)
  have hD' : 8 * (2 - √2) * dD b ^ (-q s) < 8 * (2 - √2) * dD a ^ (-q s) :=
    mul_lt_mul_of_pos_left hD (mul_pos (by norm_num) (sub_pos.2 sqrt_two_lt_two))
  unfold F
  linarith

lemma continuousAt_F (s a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) : ContinuousAt (F s) a := by
  have hA : ContinuousAt (fun x => dA x ^ (-q s)) a :=
    (Real.continuousAt_rpow_const (dA a) (-q s) (Or.inl (ne_of_gt (dA_pos ha1)))).comp
      (by unfold dA; fun_prop)
  have hB : ContinuousAt (fun x => dB x ^ (-q s)) a :=
    (Real.continuousAt_rpow_const (dB a) (-q s) (Or.inl (ne_of_gt (dB_pos ha1)))).comp
      (by unfold dB; fun_prop)
  have hC : ContinuousAt (fun x => dC x ^ (-q s)) a :=
    (Real.continuousAt_rpow_const (dC a) (-q s) (Or.inl (ne_of_gt (dC_pos ha0)))).comp
      (by unfold dC; fun_prop)
  have hD : ContinuousAt (fun x => dD x ^ (-q s)) a :=
    (Real.continuousAt_rpow_const (dD a) (-q s) (Or.inl (ne_of_gt (dD_pos ha0)))).comp
      (by unfold dD; fun_prop)
  unfold F
  fun_prop

lemma continuousAt_G (s a : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) : ContinuousAt (G s) a := by
  have hA : ContinuousAt (fun x => dA x ^ (-s / 2)) a :=
    (Real.continuousAt_rpow_const (dA a) (-s / 2)
      (Or.inl (ne_of_gt (dA_pos ha1)))).comp
      (by unfold dA; fun_prop)
  have hB : ContinuousAt (fun x => dB x ^ (-s / 2)) a :=
    (Real.continuousAt_rpow_const (dB a) (-s / 2)
      (Or.inl (ne_of_gt (dB_pos ha1)))).comp
      (by unfold dB; fun_prop)
  have hC : ContinuousAt (fun x => dC x ^ (-s / 2)) a :=
    (Real.continuousAt_rpow_const (dC a) (-s / 2)
      (Or.inl (ne_of_gt (dC_pos ha0)))).comp
      (by unfold dC; fun_prop)
  have hD : ContinuousAt (fun x => dD x ^ (-s / 2)) a :=
    (Real.continuousAt_rpow_const (dD a) (-s / 2)
      (Or.inl (ne_of_gt (dD_pos ha0)))).comp
      (by unfold dD; fun_prop)
  unfold G
  fun_prop

/-- At the limiting packing parameter, the stationarity function is still
strictly negative.  Thus the energy-minimizing antiprism is slightly taller
than the limiting best-packing antiprism for every finite exponent. -/
lemma F_aInf_neg (s : ℝ) (hs : 0 ≤ s) : F s aInf < 0 := by
  have hq : 1 ≤ q s := by unfold q; linarith
  have hqpos : 0 < q s := q_pos s hs
  have htau : 0 < tau := by unfold tau; linarith [aInf_mem_Ioo.2]
  have h2q : (2 : ℝ) ^ (1 : ℝ) ≤ 2 ^ q s :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hq
  have h2inv : (2 : ℝ) ^ (-q s) ≤ 1 / 2 := by
    rw [Real.rpow_neg (by norm_num)]
    simpa only [Real.rpow_one, one_div] using
      (inv_le_inv₀ (Real.rpow_pos_of_pos (by norm_num) (q s)) (by norm_num)).2 h2q
  have htpow : 0 < tau ^ (-q s) := Real.rpow_pos_of_pos htau _
  have hmul := mul_le_mul_of_nonneg_right h2inv (le_of_lt htpow)
  have hBpow : dB aInf ^ (-q s) = 2 ^ (-q s) * tau ^ (-q s) := by
    rw [dB_aInf, Real.mul_rpow (by norm_num) (le_of_lt htau)]
  have hDcoef : 0 < 8 * (2 - √(2 : ℝ)) := by
    exact mul_pos (by norm_num) (sub_pos.2 sqrt_two_lt_two)
  have hDpow : 0 < dD aInf ^ (-q s) :=
    Real.rpow_pos_of_pos (dD_pos (le_of_lt aInf_mem_Ioo.1)) _
  have hCcoef : 24 < 8 * (2 + √(2 : ℝ)) := by
    nlinarith [one_lt_sqrt_two]
  unfold F
  rw [dA_aInf, hBpow, dC_aInf]
  nlinarith

/-- Paper Lemma 2.1: derivative of the antiprism-family energy. -/
theorem G_deriv (s a : ℝ) (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (G s) a = (s / 2) * F s a := by
  have hA_base : HasDerivAt dA (-2) a := by
    unfold dA
    simpa [id_eq] using ((hasDerivAt_id a).const_sub 1).const_mul 2
  have hB_base : HasDerivAt dB (-4) a := by
    unfold dB
    simpa [id_eq] using ((hasDerivAt_id a).const_sub 1).const_mul 4
  have hC_base : HasDerivAt dC (2 + √2) a := by
    unfold dC
    simpa [id_eq] using
      (((hasDerivAt_id a).const_mul (2 + √2)).const_add (2 - √2))
  have hD_base : HasDerivAt dD (2 - √2) a := by
    unfold dD
    simpa [id_eq] using
      (((hasDerivAt_id a).const_mul (2 - √2)).const_add (2 + √2))
  have hA_pow :=
    (Real.hasDerivAt_rpow_const (p := -s / 2)
      (Or.inl (ne_of_gt (dA_pos ha.2)))).comp a hA_base
  have hB_pow :=
    (Real.hasDerivAt_rpow_const (p := -s / 2)
      (Or.inl (ne_of_gt (dB_pos ha.2)))).comp a hB_base
  have hC_pow :=
    (Real.hasDerivAt_rpow_const (p := -s / 2)
      (Or.inl (ne_of_gt (dC_pos (le_of_lt ha.1))))).comp a hC_base
  have hD_pow :=
    (Real.hasDerivAt_rpow_const (p := -s / 2)
      (Or.inl (ne_of_gt (dD_pos (le_of_lt ha.1))))).comp a hD_base
  have hsum := (((hA_pow.const_mul 8).add (hB_pow.const_mul 4)).add
    (hC_pow.const_mul 8)).add (hD_pow.const_mul 8)
  have hexp : -s / 2 - 1 = -q s := by unfold q; ring
  rw [hexp] at hsum
  let gA : ℝ → ℝ := fun y => 8 * dA y ^ (-s / 2)
  let gB : ℝ → ℝ := fun y => 4 * dB y ^ (-s / 2)
  let gC : ℝ → ℝ := fun y => 8 * dC y ^ (-s / 2)
  let gD : ℝ → ℝ := fun y => 8 * dD y ^ (-s / 2)
  have hfun : ((gA + gB) + gC) + gD = G s := by
    funext x
    rfl
  have hderiv : deriv (G s) a =
      8 * (-s / 2 * dA a ^ (-q s) * (-2)) +
        4 * (-s / 2 * dB a ^ (-q s) * (-4)) +
        8 * (-s / 2 * dC a ^ (-q s) * (2 + √2)) +
        8 * (-s / 2 * dD a ^ (-q s) * (2 - √2)) := by
    rw [← hfun]
    simpa only [gA, gB, gC, gD, Function.comp_apply] using hsum.deriv
  rw [hderiv]
  unfold F
  ring

lemma F_zero_neg (s : ℝ) (hs : 0 ≤ s) : F s 0 < 0 := by
  have hq := q_pos s hs
  have hq1 : 1 ≤ q s := by unfold q; linarith
  have h2q : (2 : ℝ) ^ (1 : ℝ) ≤ 2 ^ q s :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hq1
  have h4q : (4 : ℝ) ^ (1 : ℝ) ≤ 4 ^ q s :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) hq1
  have h2inv : (2 : ℝ) ^ (-q s) ≤ 1 / 2 := by
    rw [Real.rpow_neg (by norm_num)]
    simpa only [Real.rpow_one, one_div] using
      (inv_le_inv₀ (Real.rpow_pos_of_pos (by norm_num) (q s)) (by norm_num)).2 h2q
  have h4inv : (4 : ℝ) ^ (-q s) ≤ 1 / 4 := by
    rw [Real.rpow_neg (by norm_num)]
    simpa only [Real.rpow_one, one_div] using
      (inv_le_inv₀ (Real.rpow_pos_of_pos (by norm_num) (q s)) (by norm_num)).2 h4q
  have hc0 : 0 < dC 0 := dC_pos (le_refl 0)
  have hc1 : dC 0 < 1 := by
    unfold dC
    nlinarith [one_lt_sqrt_two]
  have hcPow : 1 < dC 0 ^ (-q s) := by
    simpa only [Real.one_rpow] using rpow_neg_lt_rpow_neg hc0 hc1 hq
  have hdPow : 0 < dD 0 ^ (-q s) := Real.rpow_pos_of_pos (dD_pos (le_refl 0)) _
  have hA : 16 * dA 0 ^ (-q s) ≤ 8 := by
    norm_num [dA] at ⊢ h2inv
    linarith
  have hB : 16 * dB 0 ^ (-q s) ≤ 4 := by
    norm_num [dB] at ⊢ h4inv
    linarith
  have hC : 24 < 8 * (2 + √2) * dC 0 ^ (-q s) := by
    have hcCoef : 24 < 8 * (2 + √(2 : ℝ)) := by nlinarith [one_lt_sqrt_two]
    have hm := mul_lt_mul_of_pos_left hcPow (show 0 < 8 * (2 + √(2 : ℝ)) by positivity)
    nlinarith
  have hD : 0 < 8 * (2 - √2) * dD 0 ^ (-q s) := by
    have hc : 0 < 8 * (2 - √(2 : ℝ)) :=
      mul_pos (by norm_num) (sub_pos.2 sqrt_two_lt_two)
    exact mul_pos hc hdPow
  unfold F
  linarith

lemma F_three_fourths_pos (s : ℝ) (hs : 0 ≤ s) : F s (3 / 4) > 0 := by
  have hq := q_pos s hs
  have hA : 1 < dA (3 / 4) ^ (-q s) := by
    have h := rpow_neg_lt_rpow_neg (x := (1 / 2 : ℝ)) (y := 1) (by norm_num) (by norm_num) hq
    convert h using 1 <;> norm_num [dA, Real.one_rpow]
  have hB : dB (3 / 4) ^ (-q s) = 1 := by norm_num [dB, Real.one_rpow]
  have hcBase : 1 < dC (3 / 4) := by
    unfold dC
    nlinarith [sqrt_two_lt_two]
  have hdBase : 1 < dD (3 / 4) := by
    unfold dD
    nlinarith [sqrt_two_pos, sqrt_two_lt_two]
  have hC : dC (3 / 4) ^ (-q s) < 1 := by
    simpa only [Real.one_rpow] using
      rpow_neg_lt_rpow_neg (x := (1 : ℝ)) (y := dC (3 / 4)) (by norm_num) hcBase hq
  have hD : dD (3 / 4) ^ (-q s) < 1 := by
    simpa only [Real.one_rpow] using
      rpow_neg_lt_rpow_neg (x := (1 : ℝ)) (y := dD (3 / 4)) (by norm_num) hdBase hq
  have hA' : 16 < 16 * dA (3 / 4) ^ (-q s) :=
    by simpa only [mul_one] using
      mul_lt_mul_of_pos_left hA (by norm_num : (0 : ℝ) < 16)
  have hC' : 8 * (2 + √2) * dC (3 / 4) ^ (-q s) < 8 * (2 + √2) :=
    by
      have hc : 0 < 8 * (2 + √(2 : ℝ)) := by nlinarith [sqrt_two_pos]
      have ht := mul_lt_mul_of_pos_left hC hc
      simpa only [mul_one] using ht
  have hD' : 8 * (2 - √2) * dD (3 / 4) ^ (-q s) < 8 * (2 - √2) :=
    by
      have hd : 0 < 8 * (2 - √(2 : ℝ)) :=
        mul_pos (by norm_num) (sub_pos.2 sqrt_two_lt_two)
      have ht := mul_lt_mul_of_pos_left hD hd
      simpa only [mul_one] using ht
  unfold F
  rw [hB]
  nlinarith

/-- Paper Lemma 2.1, existence and uniqueness portion. -/
theorem F_root_exists_unique (s : ℝ) (hs : 0 ≤ s) :
    ∃! a : ℝ, a ∈ Set.Ioo 0 1 ∧ F s a = 0 := by
  have hcont : ContinuousOn (F s) (Set.Icc (0 : ℝ) (3 / 4)) := by
    intro a ha
    exact (continuousAt_F s a ha.1 (by linarith [ha.2])).continuousWithinAt
  have hz : (0 : ℝ) ∈ Set.Icc (F s 0) (F s (3 / 4)) :=
    ⟨le_of_lt (F_zero_neg s hs), le_of_lt (F_three_fourths_pos s hs)⟩
  have himage : (0 : ℝ) ∈ F s '' Set.Icc (0 : ℝ) (3 / 4) :=
    (intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 3 / 4) hcont) hz
  obtain ⟨a, ha, hFa⟩ := himage
  have ha0 : 0 < a := by
    rcases lt_or_eq_of_le ha.1 with h | h
    · exact h
    · subst a
      linarith [F_zero_neg s hs]
  have ha1 : a < 1 := by linarith [ha.2]
  refine ⟨a, ⟨⟨ha0, ha1⟩, hFa⟩, ?_⟩
  intro b hb
  by_contra hne
  rcases lt_or_gt_of_ne hne with hba | hab
  · have hlt := F_strictMonoOn s hs ⟨le_of_lt hb.1.1, hb.1.2⟩
        ⟨le_of_lt ha0, ha1⟩ hba
    rw [hb.2, hFa] at hlt
    exact (lt_irrefl 0 hlt)
  · have hlt := F_strictMonoOn s hs ⟨le_of_lt ha0, ha1⟩
        ⟨le_of_lt hb.1.1, hb.1.2⟩ hab
    rw [hFa, hb.2] at hlt
    exact (lt_irrefl 0 hlt)

/-- The uniquely selected stationarity parameter. -/
def aStar (s : ℝ) : ℝ :=
  if hs : 0 ≤ s then Classical.choose (F_root_exists_unique s hs) else 0

theorem aStar_spec (s : ℝ) (hs : 0 ≤ s) :
    aStar s ∈ Set.Ioo 0 1 ∧ F s (aStar s) = 0 := by
  simp only [aStar, dif_pos hs]
  exact (Classical.choose_spec (F_root_exists_unique s hs)).1

theorem aStar_unique (s : ℝ) (hs : 0 ≤ s) (b : ℝ)
    (hb : b ∈ Set.Ioo (0 : ℝ) 1) (hFb : F s b = 0) : b = aStar s := by
  simp only [aStar, dif_pos hs]
  exact (Classical.choose_spec (F_root_exists_unique s hs)).2 b ⟨hb, hFb⟩

theorem aStar_gt_aInf (s : ℝ) (hs : 0 ≤ s) : aInf < aStar s := by
  have ha := (aStar_spec s hs).1
  by_contra h
  have hle : aStar s ≤ aInf := le_of_not_gt h
  rcases hle.eq_or_lt with heq | hlt
  · have hroot := (aStar_spec s hs).2
    rw [heq] at hroot
    linarith [F_aInf_neg s hs]
  · have hf := F_strictMonoOn s hs
        ⟨le_of_lt ha.1, ha.2⟩
        ⟨le_of_lt aInf_mem_Ioo.1, aInf_mem_Ioo.2⟩ hlt
    rw [(aStar_spec s hs).2] at hf
    linarith [F_aInf_neg s hs]

/-- Exact zero-exponent calculation in Paper Lemma 2.1. -/
theorem aStar_zero : aStar 0 = (2 * √58 - 13) / 7 := by
  let a₀ : ℝ := (2 * √58 - 13) / 7
  have hs58 : √(58 : ℝ) ^ 2 = 58 := Real.sq_sqrt (by norm_num)
  have hs58nonneg : 0 ≤ √(58 : ℝ) := Real.sqrt_nonneg 58
  have hs58low : (15 / 2 : ℝ) < √58 := by nlinarith
  have hs58high : √(58 : ℝ) < 8 := by nlinarith
  have ha₀ : a₀ ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp [a₀]
    constructor <;> nlinarith
  have hA0 : dA a₀ ≠ 0 := ne_of_gt (dA_pos ha₀.2)
  have hB0 : dB a₀ ≠ 0 := ne_of_gt (dB_pos ha₀.2)
  have hC0 : dC a₀ ≠ 0 := ne_of_gt (dC_pos (le_of_lt ha₀.1))
  have hD0 : dD a₀ ≠ 0 := ne_of_gt (dD_pos (le_of_lt ha₀.1))
  have hs2 : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs58cube : √(58 : ℝ) ^ 3 = 58 * √58 := by
    calc
      √(58 : ℝ) ^ 3 = √58 ^ 2 * √58 := by ring
      _ = 58 * √58 := by rw [hs58]
  have hF : F 0 a₀ = 0 := by
    norm_num [F, q, Real.rpow_neg_one]
    field_simp [hA0, hB0, hC0, hD0]
    dsimp [dA, dB, dC, dD, a₀] at *
    ring_nf at *
    nlinarith [hs58cube]
  exact (aStar_unique 0 (by norm_num) a₀ ha₀ hF).symm

lemma G_aStar_lt (s b : ℝ) (hs : 0 < s)
    (hb : b ∈ Set.Ioo (0 : ℝ) 1) (hne : b ≠ aStar s) :
    G s (aStar s) < G s b := by
  have hs0 : 0 ≤ s := le_of_lt hs
  have ha := (aStar_spec s hs0).1
  have hFa := (aStar_spec s hs0).2
  rcases lt_or_gt_of_ne hne with hba | hab
  · have hcont : ContinuousOn (G s) (Set.Icc b (aStar s)) := by
      intro x hx
      rcases hx with ⟨hbx, hxa⟩
      exact (continuousAt_G s x (by linarith [hb.1])
        (by linarith [ha.2])).continuousWithinAt
    have hanti : StrictAntiOn (G s) (Set.Icc b (aStar s)) := by
      apply strictAntiOn_of_deriv_neg (D := Set.Icc b (aStar s))
        (convex_Icc b (aStar s)) hcont
      intro x hx
      have hxi : x ∈ Set.Ioo b (aStar s) := by
        simpa [interior_Icc, hba.ne] using hx
      have hFx : F s x < 0 := by
        have hmono := F_strictMonoOn s hs0
          ⟨by linarith [hb.1, hxi.1], by linarith [hxi.2, ha.2]⟩
          ⟨le_of_lt ha.1, ha.2⟩ hxi.2
        rw [hFa] at hmono
        exact hmono
      rw [G_deriv s x
        ⟨by linarith [hb.1, hxi.1], by linarith [hxi.2, ha.2]⟩]
      exact mul_neg_of_pos_of_neg (by positivity) hFx
    exact hanti (by exact ⟨le_rfl, le_of_lt hba⟩)
      (by exact ⟨le_of_lt hba, le_rfl⟩) hba
  · have hcont : ContinuousOn (G s) (Set.Icc (aStar s) b) := by
      intro x hx
      rcases hx with ⟨hax, hxb⟩
      exact (continuousAt_G s x (by linarith [ha.1])
        (by linarith [hb.2])).continuousWithinAt
    have hmono : StrictMonoOn (G s) (Set.Icc (aStar s) b) := by
      apply strictMonoOn_of_deriv_pos (D := Set.Icc (aStar s) b)
        (convex_Icc (aStar s) b) hcont
      intro x hx
      have hxi : x ∈ Set.Ioo (aStar s) b := by
        simpa [interior_Icc, hab.ne] using hx
      have hFx : 0 < F s x := by
        have hmono := F_strictMonoOn s hs0
          ⟨le_of_lt ha.1, ha.2⟩
          ⟨by linarith [ha.1, hxi.1], by linarith [hxi.2, hb.2]⟩ hxi.1
        rw [hFa] at hmono
        exact hmono
      rw [G_deriv s x
        ⟨by linarith [ha.1, hxi.1], by linarith [hxi.2, hb.2]⟩]
      exact mul_pos (by positivity) hFx
    exact hmono (by exact ⟨le_rfl, le_of_lt hab⟩)
      (by exact ⟨le_of_lt hab, le_rfl⟩) hab

/-- The selected parameter uniquely minimizes energy inside the
square-antiprism family for every positive exponent. -/
theorem aStar_family_minimizer (s : ℝ) (hs : 0 < s) (b : ℝ)
    (hb : b ∈ Set.Ioo (0 : ℝ) 1) :
    G s (aStar s) ≤ G s b ∧ (G s b = G s (aStar s) ↔ b = aStar s) := by
  by_cases hba : b = aStar s
  · subst b
    exact ⟨le_rfl, iff_of_true rfl rfl⟩
  · have hlt := G_aStar_lt s b hs hb hba
    exact ⟨le_of_lt hlt, ⟨fun heq => by linarith, fun h => (hba h).elim⟩⟩

theorem antiprism_sublevel (s : ℝ) (hs : 0 < s) :
    E s (X (aStar s)) ≤ E s P := by
  rw [energy_X_eq_G s (aStar s) (aStar_spec s (le_of_lt hs)).1]
  unfold P
  rw [energy_X_eq_G s aInf aInf_mem_Ioo]
  exact (aStar_family_minimizer s hs aInf aInf_mem_Ioo).1

end SquareAntiprismVerification
