import ThomsonNegative.Analytic.RootLower

/-! A uniform separation from the upper rational height, useful for the exact
right-inverse denominators. All constants come from analytic inequalities. -/

noncomputable section
open Real
open scoped BigOperators
namespace ThomsonNegative

lemma slopeCoeff_lower (q : ℝ) (hq : 0 ≤ q) (n : ℕ) :
    1/((n:ℝ)+1) ≤ slopeCoeff q n := by
  have h (n : ℕ) : 1 ≤ slopeCoeff q n*((n:ℝ)+1) := by
    induction n with
    | zero => norm_num [slopeCoeff,seriesCoeff]
    | succ n ih =>
      rw [slopeCoeff_succ]
      simp only [Nat.cast_add,Nat.cast_one]
      rw [show (n:ℝ)+1+1=n+2 by ring,div_mul_cancel₀ _ (by positivity : (n:ℝ)+2 ≠ 0)]
      calc
        1 ≤ slopeCoeff q n*(n+1) := ih
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (slopeCoeff_pos q hq n).le
  exact (div_le_iff₀ (by positivity : (0:ℝ)<n+1)).mpr (h n)

lemma upper_root_partial_eight :
    (∑ n ∈ Finset.range 8, rootMoment (1/3) n/((n:ℝ)+1))=7499/14580 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  norm_num [Finset.sum_range_succ,rootMoment]
  linear_combination (-29*(√(2:ℝ))^6/979776-7313*(√(2:ℝ))^4/2449440-
    142273*(√(2:ℝ))^2/1224720-1067371/204120)*hs

lemma seriesRoot_upper_half (q : ℝ) (hq : 0 < q) : 1/2 ≤ seriesRoot q (1/3) := by
  have hsum := seriesRoot_hasSum q (1/3) hq.ne' ⟨by norm_num,le_rfl⟩
  have hpart : (7499/14580:ℝ) ≤ ∑ n ∈ Finset.range 8, slopeCoeff q n*rootMoment (1/3) n := by
    rw [← upper_root_partial_eight]
    apply Finset.sum_le_sum
    intro n hn
    have hh := mul_le_mul_of_nonneg_right (slopeCoeff_lower q hq.le n) (rootMoment_upper_nonneg n)
    simpa only [div_eq_mul_inv,one_mul,mul_comm] using hh
  have htail := Summable.sum_le_tsum (Finset.range 8)
    (fun n _ => mul_nonneg (slopeCoeff_pos q hq.le n).le (rootMoment_upper_nonneg n)) hsum.summable
  rw [hsum.tsum_eq] at htail
  linarith

lemma aux_curvature_le_inv_sq (q x r : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1)
    (hx : 0 ≤ x) (hxr : x ≤ r) (hr : r < 1) :
    (1-x)^(-q-1) ≤ 1/(1-r)^2 := by
  have hb : 0 < 1-x := by linarith
  have hrb : 0 < 1-r := by linarith
  have h1 : (1-x)^(-q-1) ≤ (1-r)^(-q-1) :=
    Real.rpow_le_rpow_of_nonpos hrb (by linarith) (by linarith [hq.1])
  have h2 : (1-r)^(-q-1) ≤ (1-r)^(-2:ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hrb (by linarith) (by linarith [hq.2])
  have h3 : (1-r)^(-2:ℝ)=1/(1-r)^2 := by rw [Real.rpow_neg hrb.le,Real.rpow_two,one_div]
  exact h1.trans (h2.trans_eq h3)

lemma rootCurvature_le_256 (q a : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1)
    (ha : a ∈ Set.Icc (5/16:ℝ) (1/3)) : rootCurvature q a ≤ 256 := by
  have ha' : a ∈ Set.Icc (1/4:ℝ) (1/3) := ⟨by linarith [ha.1],ha.2⟩
  obtain ⟨hA,hB,hC,hD⟩ := contact_series_domain a ha'
  have hr := sqrt_two_pos
  have hr2 := sqrt_two_lt_two
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hr10 : √(2:ℝ) ≤ 10/7 := by nlinarith
  have hr4 : (4/3:ℝ) ≤ √2 := by nlinarith
  have hCmax : (1-a)*(2+√2)/4 ≤ 3/5 := by
    have hh := mul_le_mul (show 1-a ≤ (11/16:ℝ) by linarith [ha.1])
      (show 2+√(2:ℝ) ≤ 24/7 by linarith) (by positivity : 0 ≤ 2+√(2:ℝ)) (by norm_num)
    linarith
  have hDmax : (1-a)*(2-√2)/4 ≤ 1/8 := by
    have hh := mul_le_mul (show 1-a ≤ (3/4:ℝ) by linarith [ha.1])
      (show 2-√(2:ℝ) ≤ 2/3 by linarith) (by linarith : 0 ≤ 2-√(2:ℝ)) (by norm_num)
    linarith
  have hAu := (aux_curvature_bounds q _ hq hA).2
  have hBu := aux_curvature_le_inv_sq q a (1/3) hq hB.1 ha.2 (by norm_num)
  have hCu := aux_curvature_le_inv_sq q _ (3/5) hq hC.1 hCmax (by norm_num)
  have hDu := aux_curvature_le_inv_sq q _ (1/8) hq hD.1 hDmax (by norm_num)
  norm_num at hBu hCu hDu
  have hCw := mul_le_mul_of_nonneg_left hCu (by positivity : 0 ≤ 2*(2+√(2:ℝ))^2)
  have hDw := mul_le_mul_of_nonneg_left hDu (by positivity : 0 ≤ 2*(2-√(2:ℝ))^2)
  unfold rootCurvature
  nlinarith

/-- A fixed analytic margin keeps the right-inverse factor `3a−1` away from
zero throughout the closed-above negative-exponent parameter interval. -/
theorem aStar_upper_margin (q : ℝ) (hq : q ∈ Set.Ioc (0:ℝ) 1) :
    aStar (2*q-2) ≤ 1/3-1/512 := by
  have hs : -2 < 2*q-2 := by linarith [hq.1]
  have ha := aStar_negative_range q hq
  have hspec := aStar_spec (2*q-2) hs
  have hf : seriesRoot q (aStar (2*q-2))=0 :=
    (stationarity_series_iff q _ hq.1 hspec.1).mp ((hspec.2 _ hspec.1).mpr rfl)
  have hd (x : ℝ) (hx : x ∈ Set.Icc (5/16:ℝ) (1/3)) :
      HasDerivWithinAt (seriesRoot q) (rootCurvature q x) (Set.Icc (5/16:ℝ) (1/3)) x :=
    (seriesRoot_hasDerivAt q x hq.1.ne' ⟨by linarith [hx.1],hx.2⟩).hasDerivWithinAt
  have hb (x : ℝ) (hx : x ∈ Set.Icc (5/16:ℝ) (1/3)) : ‖rootCurvature q x‖ ≤ 256 := by
    have hl := (rootCurvature_bounds q x ⟨hq.1.le,hq.2⟩ ⟨by linarith [hx.1],hx.2⟩).1
    rw [Real.norm_eq_abs,abs_of_nonneg (by linarith)]
    exact rootCurvature_le_256 q x ⟨hq.1.le,hq.2⟩ hx
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (convex_Icc (5/16:ℝ) (1/3)) ⟨ha.1.le,ha.2.le⟩ (show (1/3:ℝ) ∈ Set.Icc (5/16:ℝ) (1/3) from ⟨by norm_num,le_rfl⟩)
  have hu := seriesRoot_upper_half q hq.1
  rw [hf,sub_zero,Real.norm_eq_abs,abs_of_nonneg (by linarith),
    Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr ha.2.le)] at h
  linarith

#print axioms seriesRoot_upper_half
#print axioms rootCurvature_le_256
#print axioms aStar_upper_margin
end ThomsonNegative
