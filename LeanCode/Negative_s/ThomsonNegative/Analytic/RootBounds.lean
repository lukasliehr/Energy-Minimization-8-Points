import ThomsonNegative.RootBridge

/-!
Analytic root bracket and the positive series for the regularized stationarity
function. These results use no numerical certificate and include the entire
negative-exponent interval.
-/

noncomputable section
open Real
open scoped BigOperators
namespace ThomsonNegative

/-- Positive coefficients of the derivative of the auxiliary potential. -/
def slopeCoeff (q : ℝ) (n : ℕ) : ℝ := (n+2)*seriesCoeff q n

lemma slopeCoeff_pos (q : ℝ) (hq : 0 ≤ q) (n : ℕ) : 0 < slopeCoeff q n := by
  have hc : 0 < seriesCoeff q n := by
    induction n with
    | zero => norm_num [seriesCoeff]
    | succ n ih =>
      rw [seriesCoeff]
      exact div_pos (mul_pos ih (by positivity)) (by positivity)
  exact mul_pos (by positivity) hc

lemma slope_choose_coeff (q : ℝ) (n : ℕ) :
    Ring.choose (-q) (n+1) * (-1 : ℝ)^(n+1) = q*slopeCoeff q n := by
  induction n with
  | zero => simp [slopeCoeff, seriesCoeff]
  | succ n ih =>
    rw [show n+1+1=n+1+1 by rfl, choose_step, pow_succ]
    have he :
        Ring.choose (-q) (n+1) * (-q-(n+1)) / (n+1+1) *
          ((-1:ℝ)^(n+1)*(-1)) =
        (Ring.choose (-q) (n+1)*(-1:ℝ)^(n+1))*(q+n+1)/(n+2) := by
      ring
    simp only [Nat.cast_add, Nat.cast_one]
    rw [he,ih]
    simp only [slopeCoeff, seriesCoeff, Nat.cast_add, Nat.cast_one]
    have h2 : (n:ℝ)+2 ≠ 0 := by positivity
    have h3 : (n:ℝ)+3 ≠ 0 := by positivity
    field_simp
    ring

/-- The slope series is valid without the removable endpoint at `q=1` causing
any division; only `q=0` is excluded from the closed-form representation. -/
theorem auxSlope_hasSum (q x : ℝ) (hq : q ≠ 0) (hx : |x| < 1) :
    HasSum (fun n => slopeCoeff q n * x^(n+1)) (auxSlope q x) := by
  have hball : -x ∈ Metric.eball (0 : ℝ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa [Real.dist_eq, abs_neg] using hx
  have hb := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := -q)).hasSum hball
  simp only [binomialSeries, FormalMultilinearSeries.ofScalars_apply_eq,
    smul_eq_mul, ← sub_eq_add_neg] at hb
  have ht : HasSum (fun n => Ring.choose (-q) (n+1)*(-x)^(n+1))
      ((1-x)^(-q)-1) := by
    apply (hasSum_nat_add_iff (f := fun n : ℕ => Ring.choose (-q) n * (-x)^n) 1).mpr
    convert! hb using 1
    simp [sub_eq_add_neg]
  convert! ht.div_const q using 1
  · funext n
    rw [neg_pow, ← mul_assoc, slope_choose_coeff]
    field_simp

/-- The power moment multiplying the positive `n`th slope coefficient. -/
def rootMoment (a : ℝ) (n : ℕ) : ℝ :=
  16*((1+a)/2)^(n+1)+16*a^(n+1)-
    8*(2+√2)*((1-a)*(2+√2)/4)^(n+1)-
    8*(2-√2)*((1-a)*(2-√2)/4)^(n+1)

theorem seriesRoot_hasSum (q a : ℝ) (hq : q ≠ 0)
    (ha : a ∈ Set.Icc (1/4:ℝ) (1/3)) :
    HasSum (fun n => slopeCoeff q n*rootMoment a n) (seriesRoot q a) := by
  obtain ⟨hA,hB,hC,hD⟩ := contact_series_domain a ha
  have hA' : |(1+a)/2| < 1 := by rw [abs_of_nonneg hA.1]; linarith [hA.2]
  have hB' : |a| < 1 := by rw [abs_of_nonneg hB.1]; linarith [hB.2]
  have hC' : |(1-a)*(2+√2)/4| < 1 := by rw [abs_of_nonneg hC.1]; linarith [hC.2]
  have hD' : |(1-a)*(2-√2)/4| < 1 := by rw [abs_of_nonneg hD.1]; linarith [hD.2]
  have h := (((auxSlope_hasSum q _ hq hA').mul_left 16).add
    ((auxSlope_hasSum q _ hq hB').mul_left 16)).sub
    ((auxSlope_hasSum q _ hq hC').mul_left (8*(2+√2)))
  have h' := h.sub ((auxSlope_hasSum q _ hq hD').mul_left (8*(2-√2)))
  convert! h' using 1
  funext n
  unfold rootMoment
  ring

/-- The universal limiting height where contacts A and C coincide. -/
def limitingHeight : ℝ := (2*√2-1)/7

lemma limitingHeight_range : limitingHeight ∈ Set.Ioo (1/4:ℝ) (1/3) := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hp := sqrt_two_pos
  dsimp [limitingHeight]
  constructor <;> nlinarith

lemma limitingHeight_contact :
    (1-limitingHeight)*(2+√2)/4=(1+limitingHeight)/2 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  dsimp [limitingHeight]
  nlinarith

lemma rootMoment_limitingHeight_neg (n : ℕ) : rootMoment limitingHeight n < 0 := by
  have ha := limitingHeight_range
  have hdom := contact_series_domain limitingHeight ⟨ha.1.le,ha.2.le⟩
  let x : ℝ := (1+limitingHeight)/2
  have hx : 0 < x := by dsimp [x]; linarith [ha.1]
  have ha0 : 0 ≤ limitingHeight := by linarith [ha.1]
  have hax : limitingHeight ≤ x := by dsimp [x]; linarith [ha.2]
  have ha2 : 2*limitingHeight < x := by dsimp [x]; linarith [ha.2]
  have hpow := pow_le_pow_left₀ ha0 hax n
  have hleft : 2*limitingHeight^(n+1) < x^(n+1) := by
    rw [pow_succ, pow_succ]
    have hh := mul_le_mul_of_nonneg_right hpow (show 0 ≤ 2*limitingHeight by positivity)
    have hh' := mul_lt_mul_of_pos_left ha2 (pow_pos hx n)
    nlinarith
  have hsqrt := one_lt_sqrt_two
  have hxp := pow_pos hx (n+1)
  have hd := pow_nonneg hdom.2.2.2.1 (n+1)
  have hdc : 0 ≤ 8*(2-√(2:ℝ)) := by nlinarith [sqrt_two_lt_two]
  have hdp := mul_nonneg hdc hd
  unfold rootMoment
  rw [limitingHeight_contact]
  change 16*x^(n+1)+16*limitingHeight^(n+1)-8*(2+√2)*x^(n+1)-
      8*(2-√2)*((1-limitingHeight)*(2-√2)/4)^(n+1) < 0
  nlinarith

/-- Integer-power obstruction at the rational upper height. -/
def upperMoment (n : ℕ) : ℝ :=
  2^n+1-(1+√2/2)^(n+1)-(1-√2/2)^(n+1)

lemma upperMoment_zero : upperMoment 0 = 0 := by norm_num [upperMoment]; ring
lemma upperMoment_one : upperMoment 1 = 0 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  norm_num [upperMoment]
  nlinarith

lemma upperMoment_recurrence (n : ℕ) :
    upperMoment (n+2) = 2*upperMoment (n+1)-upperMoment n/2+(2^n-1)/2 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  unfold upperMoment
  simp only [pow_succ]
  linear_combination -((1+√(2:ℝ)/2)^n*(1+√2/2)+(1-√(2:ℝ)/2)^n*(1-√2/2))/4 * hs

lemma upperMoment_nonneg_mono (n : ℕ) :
    0 ≤ upperMoment n ∧ upperMoment n ≤ upperMoment (n+1) := by
  induction n with
  | zero => rw [upperMoment_zero,upperMoment_one]; constructor <;> norm_num
  | succ n ih =>
    have hp : (1:ℝ) ≤ 2^n := one_le_pow₀ (by norm_num)
    have hr := upperMoment_recurrence n
    constructor <;> nlinarith

lemma upperMoment_three : upperMoment 3 = 1/2 := by
  have h0 := upperMoment_recurrence 0
  have h1 := upperMoment_recurrence 1
  rw [upperMoment_zero,upperMoment_one] at h0
  norm_num at h0
  rw [upperMoment_one,h0] at h1
  norm_num at h1
  exact h1

lemma rootMoment_upper_eq (n : ℕ) :
    rootMoment (1/3) n = 16*(1/3:ℝ)^(n+1)*upperMoment (n+1) := by
  unfold rootMoment upperMoment
  rw [show (1+(1/3:ℝ))/2=2*(1/3) by ring,
    show (1-(1/3:ℝ))*(2+√2)/4=(1+√2/2)*(1/3) by ring,
    show (1-(1/3:ℝ))*(2-√2)/4=(1-√2/2)*(1/3) by ring]
  rw [mul_pow,mul_pow,mul_pow,pow_succ (1+√(2:ℝ)/2),pow_succ (1-√(2:ℝ)/2)]
  ring

lemma rootMoment_upper_nonneg (n : ℕ) : 0 ≤ rootMoment (1/3) n := by
  rw [rootMoment_upper_eq]
  exact mul_nonneg (by positivity) (upperMoment_nonneg_mono (n+1)).1

lemma rootMoment_upper_two_pos : 0 < rootMoment (1/3) 2 := by
  rw [rootMoment_upper_eq]
  norm_num [upperMoment_three]

/-- The lower sign is analytic for all positive q, not just the negative-s range. -/
theorem seriesRoot_limitingHeight_neg (q : ℝ) (hq : 0 < q) :
    seriesRoot q limitingHeight < 0 := by
  have ha := limitingHeight_range
  have hs := seriesRoot_hasSum q limitingHeight hq.ne' ⟨ha.1.le,ha.2.le⟩
  have hn (n : ℕ) : slopeCoeff q n*rootMoment limitingHeight n < 0 :=
    mul_neg_of_pos_of_neg (slopeCoeff_pos q hq.le n) (rootMoment_limitingHeight_neg n)
  have h := hs.neg.summable.le_tsum 0 (fun n _ => (neg_pos.mpr (hn n)).le)
  rw [hs.neg.tsum_eq] at h
  have h0 := hn 0
  linarith

theorem seriesRoot_one_third_pos (q : ℝ) (hq : 0 < q) :
    0 < seriesRoot q (1/3) := by
  have hs := seriesRoot_hasSum q (1/3) hq.ne' ⟨by norm_num,le_rfl⟩
  have hn (n : ℕ) : 0 ≤ slopeCoeff q n*rootMoment (1/3) n :=
    mul_nonneg (slopeCoeff_pos q hq.le n).le (rootMoment_upper_nonneg n)
  have h := hs.summable.le_tsum 2 (fun n _ => hn n)
  rw [hs.tsum_eq] at h
  exact (mul_pos (slopeCoeff_pos q hq.le 2) rootMoment_upper_two_pos).trans_le h

theorem F_limitingHeight_neg (s : ℝ) (hs : -2 < s) : F s limitingHeight < 0 := by
  have ha := limitingHeight_range
  have hq := q_pos s hs
  have hb := stationarity_series_bridge (q s) limitingHeight hq.ne'
    ⟨by linarith [ha.1],by linarith [ha.2]⟩
  rw [show 2*q s-2=s by unfold q; ring] at hb
  rw [hb]
  exact mul_neg_of_pos_of_neg (mul_pos hq (Real.rpow_pos_of_pos (by norm_num) _))
    (seriesRoot_limitingHeight_neg _ hq)

theorem F_one_third_pos (s : ℝ) (hs : -2 < s) : 0 < F s (1/3) := by
  have hq := q_pos s hs
  have hb := stationarity_series_bridge (q s) (1/3) hq.ne' ⟨by norm_num,by norm_num⟩
  rw [show 2*q s-2=s by unfold q; ring] at hb
  rw [hb]
  exact mul_pos (mul_pos hq (Real.rpow_pos_of_pos (by norm_num) _))
    (seriesRoot_one_third_pos _ hq)

/-- Global analytic root bracket: no numerical root-range gate remains. -/
theorem aStar_analytic_range (s : ℝ) (hs : -2 < s) :
    aStar s ∈ Set.Ioo limitingHeight (1/3) := by
  have ha := aStar_spec s hs
  have hf : F s (aStar s)=0 := (ha.2 _ ha.1).mpr rfl
  have hl := limitingHeight_range
  have hm := (F_strictMonoOn s hs).monotoneOn
  constructor
  · by_contra hh
    have hle : aStar s ≤ limitingHeight := le_of_not_gt hh
    have hv := hm ⟨ha.1.1.le,ha.1.2⟩
      ⟨by linarith [hl.1],by linarith [hl.2]⟩ hle
    rw [hf] at hv
    linarith [F_limitingHeight_neg s hs]
  · by_contra hh
    have hle : (1/3:ℝ) ≤ aStar s := le_of_not_gt hh
    have hv := hm ⟨by norm_num,by norm_num⟩ ⟨ha.1.1.le,ha.1.2⟩ hle
    rw [hf] at hv
    linarith [F_one_third_pos s hs]

/-- The existing scalar contact domain now applies unconditionally to the exact root. -/
theorem aStar_series_domain (s : ℝ) (hs : -2 < s) :
    (1+aStar s)/2 ∈ Set.Icc (0:ℝ) (2/3) ∧
    aStar s ∈ Set.Icc (0:ℝ) (2/3) ∧
    (1-aStar s)*(2+√2)/4 ∈ Set.Icc (0:ℝ) (2/3) ∧
    (1-aStar s)*(2-√2)/4 ∈ Set.Icc (0:ℝ) (2/3) := by
  apply contact_series_domain
  have ha := aStar_analytic_range s hs
  have hl := limitingHeight_range
  exact ⟨by linarith [ha.1,hl.1],ha.2.le⟩

/-- Actual height derivative of the regularized stationarity function. -/
def rootCurvature (q a : ℝ) : ℝ :=
  8*(1-(1+a)/2)^(-q-1)+16*(1-a)^(-q-1)+
    2*(2+√2)^2*(1-(1-a)*(2+√2)/4)^(-q-1)+
    2*(2-√2)^2*(1-(1-a)*(2-√2)/4)^(-q-1)

theorem seriesRoot_hasDerivAt (q a : ℝ) (hq : q ≠ 0)
    (ha : a ∈ Set.Icc (1/4:ℝ) (1/3)) :
    HasDerivAt (seriesRoot q) (rootCurvature q a) a := by
  obtain ⟨hA,hB,hC,hD⟩ := contact_series_domain a ha
  have hAa : HasDerivAt (fun y : ℝ => (1+y)/2) (1/2) a := by
    convert! ((hasDerivAt_id a).const_add 1).div_const 2 using 1
  have hCa := (((hasDerivAt_id a).const_sub 1).mul_const (2+√2)).div_const 4
  have hDa := (((hasDerivAt_id a).const_sub 1).mul_const (2-√2)).div_const 4
  simp only [id_eq] at hCa hDa
  have dA := (auxSlope_hasDerivAt q _ hq (by linarith [hA.2])).comp a hAa
  have dB := auxSlope_hasDerivAt q a hq (by linarith [hB.2])
  have dC := (auxSlope_hasDerivAt q _ hq (by linarith [hC.2])).comp a hCa
  have dD := (auxSlope_hasDerivAt q _ hq (by linarith [hD.2])).comp a hDa
  have hh := (((dA.const_mul 16).add (dB.const_mul 16)).sub
    (dC.const_mul (8*(2+√2)))).sub (dD.const_mul (8*(2-√2)))
  convert! hh using 1
  unfold rootCurvature
  ring

lemma aux_curvature_ge_four_mul (q x : ℝ) (hq : 0 ≤ q)
    (hx : x ∈ Set.Ico (0:ℝ) 1) : 4*x ≤ (1-x)^(-q-1) := by
  have hb : 0 < 1-x := by linarith [hx.2]
  have h1 : (1-x)^(-1:ℝ) ≤ (1-x)^(-q-1) :=
    Real.rpow_le_rpow_of_exponent_ge hb (by linarith [hx.1]) (by linarith)
  have h2 : 4*x ≤ (1-x)^(-1:ℝ) := by
    rw [Real.rpow_neg_one,← one_div]
    apply (le_div_iff₀ hb).mpr
    nlinarith [sq_nonneg (2*x-1)]
  exact h2.trans h1

/-- The weighted contact mean is exactly one half. The tangent inequality
`1/(1-x) ≥ 4x` therefore doubles the earlier derivative lower bound. -/
theorem rootCurvature_bounds (q a : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1)
    (ha : a ∈ Set.Icc (1/4:ℝ) (1/3)) :
    96 ≤ rootCurvature q a ∧ rootCurvature q a ≤ 432 := by
  obtain ⟨hA,hB,hC,hD⟩ := contact_series_domain a ha
  have hA' := aux_curvature_ge_four_mul q _ hq.1 ⟨hA.1,by linarith [hA.2]⟩
  have hB' := aux_curvature_ge_four_mul q _ hq.1 ⟨hB.1,by linarith [hB.2]⟩
  have hC' := aux_curvature_ge_four_mul q _ hq.1 ⟨hC.1,by linarith [hC.2]⟩
  have hD' := aux_curvature_ge_four_mul q _ hq.1 ⟨hD.1,by linarith [hD.2]⟩
  have hCw := mul_le_mul_of_nonneg_left hC' (by positivity : 0 ≤ 2*(2+√(2:ℝ))^2)
  have hDw := mul_le_mul_of_nonneg_left hD' (by positivity : 0 ≤ 2*(2-√(2:ℝ))^2)
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have he : 8*(4*((1+a)/2))+16*(4*a)+
      2*(2+√2)^2*(4*((1-a)*(2+√2)/4))+
      2*(2-√2)^2*(4*((1-a)*(2-√2)/4))=96 := by
    linear_combination 24*(1-a)*hs
  constructor
  · unfold rootCurvature
    nlinarith
  · exact (root_curvature_bounds q _ _ _ _ hq hA hB hC hD).2

/-- A single residual controls the root displacement; no iterative root or
numerical derivative validation is required. -/
theorem seriesRoot_residual_error (q a b : ℝ) (hq : q ∈ Set.Ioc (0:ℝ) 1)
    (ha : a ∈ Set.Icc (1/4:ℝ) (1/3)) (hb : b ∈ Set.Icc (1/4:ℝ) (1/3))
    (hroot : seriesRoot q a=0) :
    |a-b| ≤ |seriesRoot q b|/96 := by
  have hd (x : ℝ) (hx : x ∈ Set.Icc (1/4:ℝ) (1/3)) :=
    seriesRoot_hasDerivAt q x hq.1.ne' hx
  have hc : ContinuousOn (seriesRoot q) (Set.Icc (1/4:ℝ) (1/3)) :=
    fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (seriesRoot q) (interior (Set.Icc (1/4:ℝ) (1/3))) :=
    fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  have hderiv (x : ℝ) (hx : x ∈ interior (Set.Icc (1/4:ℝ) (1/3))) :
      96 ≤ deriv (seriesRoot q) x := by
    rw [(hd x (interior_subset hx)).deriv]
    exact (rootCurvature_bounds q x ⟨hq.1.le,hq.2⟩ (interior_subset hx)).1
  have hinc := (convex_Icc (1/4:ℝ) (1/3)).mul_sub_le_image_sub_of_le_deriv hc hdiff hderiv
  rcases le_total a b with hab | hba
  · have h := hinc a ha b hb hab
    rw [hroot] at h
    rw [abs_of_nonpos (sub_nonpos.mpr hab)]
    nlinarith [le_abs_self (seriesRoot q b)]
  · have h := hinc b hb a ha hba
    rw [hroot] at h
    rw [abs_of_nonneg (sub_nonneg.mpr hba)]
    nlinarith [neg_le_abs (seriesRoot q b)]

/-- Direct checker interface: evaluate one residual at any proposed height in
the fixed rational interval to enclose the exact analytic root. -/
theorem aStar_residual_error (q b : ℝ) (hq : q ∈ Set.Ioc (0:ℝ) 1)
    (hb : b ∈ Set.Icc (1/4:ℝ) (1/3)) :
    |aStar (2*q-2)-b| ≤ |seriesRoot q b|/96 := by
  have hs : -2 < 2*q-2 := by linarith [hq.1]
  have ha := aStar_analytic_range (2*q-2) hs
  have hl := limitingHeight_range
  have ha' : aStar (2*q-2) ∈ Set.Icc (1/4:ℝ) (1/3) :=
    ⟨by linarith [ha.1,hl.1],ha.2.le⟩
  have hspec := aStar_spec (2*q-2) hs
  have hf := (hspec.2 _ hspec.1).mpr rfl
  have hr := (stationarity_series_iff q _ hq.1 hspec.1).mp hf
  exact seriesRoot_residual_error q _ b hq ha' hb hr

#print axioms aStar_analytic_range
#print axioms seriesRoot_hasDerivAt
#print axioms rootCurvature_bounds
#print axioms seriesRoot_residual_error
end ThomsonNegative
