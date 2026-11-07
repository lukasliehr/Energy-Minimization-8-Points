import ThomsonNegative.Definitions

/-!
Analytic root existence and uniqueness for the entire range `s > -2`.
Monotonicity and the upper-end argument adapt the read-only ThomsonV2
`Lean_Code/Parameter.lean`; the Jensen argument at zero is new.
-/

noncomputable section
open Real
namespace ThomsonNegative

def q (s : ℝ) : ℝ := 1 + s / 2

lemma sqrt_two_pos : 0 < √(2 : ℝ) := Real.sqrt_pos.2 (by norm_num)

lemma sqrt_two_lt_two : √(2 : ℝ) < 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  nlinarith

lemma one_lt_sqrt_two : 1 < √(2 : ℝ) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp := sqrt_two_pos
  nlinarith


lemma q_pos (s : ℝ) (hs : -2 < s) : 0 < q s := by
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

lemma F_strictMonoOn (s : ℝ) (hs : -2 < s) : StrictMonoOn (F s) (Set.Ico 0 1) := by
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
  simp only [F]
  dsimp only [q] at *
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
  dsimp only [q] at *
  fun_prop


/-- A two-point Jensen inequality removes the numerical lower-end root test. -/
lemma F_zero_neg (s : ℝ) (hs : -2 < s) : F s 0 < 0 := by
  have hq := q_pos s hs
  have hr := sqrt_two_pos
  have hr2 := sqrt_two_lt_two
  have hs2 : (√(2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  let x : ℝ := (2 + √2) / 2
  let y : ℝ := (2 - √2) / 2
  have hx : 0 < x := by dsimp [x]; positivity
  have hy : 0 < y := by dsimp [y]; linarith
  have hmean : (1 / 2 : ℝ) * x + (1 / 2 : ℝ) * y = 1 := by dsimp [x,y]; ring
  have hj := (convexOn_rpow (show 1 ≤ q s + 1 by linarith)).2
    hx.le hy.le (show (0 : ℝ) ≤ 1/2 by norm_num)
    (show (0 : ℝ) ≤ 1/2 by norm_num) (show (1/2 : ℝ) + 1/2 = 1 by norm_num)
  simp only [smul_eq_mul, hmean, Real.one_rpow] at hj
  have hcx : dC 0 = x⁻¹ := by
    apply (mul_eq_one_iff_eq_inv₀ (ne_of_gt hx)).mp
    dsimp [dC,x]
    nlinarith
  have hdy : dD 0 = y⁻¹ := by
    apply (mul_eq_one_iff_eq_inv₀ (ne_of_gt hy)).mp
    dsimp [dD,y]
    nlinarith
  have hC : 8 * (2 + √2) * dC 0 ^ (-q s) = 16 * x ^ (q s + 1) := by
    rw [hcx, Real.inv_rpow hx.le, ← Real.rpow_neg hx.le, neg_neg,
      Real.rpow_add hx, Real.rpow_one]
    dsimp [x]
    ring
  have hD : 8 * (2 - √2) * dD 0 ^ (-q s) = 16 * y ^ (q s + 1) := by
    rw [hdy, Real.inv_rpow hy.le, ← Real.rpow_neg hy.le, neg_neg,
      Real.rpow_add hy, Real.rpow_one]
    dsimp [y]
    ring
  have hA : dA 0 ^ (-q s) < 1 := by
    simpa [dA] using rpow_neg_lt_rpow_neg (x := (1 : ℝ)) (y := 2)
      (by norm_num) (by norm_num) hq
  have hB : dB 0 ^ (-q s) < 1 := by
    simpa [dB] using rpow_neg_lt_rpow_neg (x := (1 : ℝ)) (y := 4)
      (by norm_num) (by norm_num) hq
  simp only [F]
  dsimp only [q] at *
  rw [hC,hD]
  linarith

lemma F_three_fourths_pos (s : ℝ) (hs : -2 < s) : F s (3 / 4) > 0 := by
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
  simp only [F]
  dsimp only [q] at *
  rw [hB]
  nlinarith

/-- Paper Lemma 2.1, existence and uniqueness portion. -/
theorem F_root_exists_unique (s : ℝ) (hs : -2 < s) :
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


/-- Analytic choice of the stationary height, with no CAP assumptions. -/
def aStar (s : ℝ) : ℝ :=
  if hs : -2 < s then Classical.choose (F_root_exists_unique s hs) else 0

theorem aStar_spec (s : ℝ) (hs : -2 < s) :
    aStar s ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ b ∈ Set.Ioo (0 : ℝ) 1, F s b = 0 ↔ b = aStar s := by
  have h := Classical.choose_spec (F_root_exists_unique s hs)
  have he : aStar s = Classical.choose (F_root_exists_unique s hs) := by
    simp only [aStar, dif_pos hs]
  rw [he]
  refine ⟨h.1.1, fun b hb => ⟨fun hf => h.2 b ⟨hb,hf⟩,?_⟩⟩
  intro heq
  rw [heq]
  exact h.1.2

#print axioms F_root_exists_unique
end ThomsonNegative
