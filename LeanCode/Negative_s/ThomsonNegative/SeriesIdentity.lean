import ThomsonNegative.Series

noncomputable section
open scoped BigOperators
namespace ThomsonNegative

lemma choose_step (a : ℝ) (n : ℕ) :
    Ring.choose a (n+1) = Ring.choose a n * (a-n) / (n+1) := by
  simp only [Ring.choose_eq_smul, descPochhammer_succ_right,
    Polynomial.smeval_mul, Polynomial.smeval_sub, Polynomial.smeval_X,
    Polynomial.smeval_natCast, pow_one, smul_eq_mul, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_inv_rev]
  ring

/-- The Taylor coefficients of the Riesz power beyond its affine part. -/
lemma riesz_choose_coeff (q : ℝ) (n : ℕ) :
    Ring.choose (1-q) (n+2) * (-1 : ℝ)^(n+2) =
      -q*(1-q)*seriesCoeff q n := by
  induction n with
  | zero =>
    rw [show (0+2 : ℕ)=1+1 by rfl,choose_step,Ring.choose_one_right]
    norm_num [seriesCoeff]
    ring
  | succ n ih =>
    rw [show n+1+2=n+2+1 by omega,choose_step,pow_succ]
    simp only [seriesCoeff, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    have he :
        Ring.choose (1-q) (n+2) * ((1-q)-(n+2)) / ((n+2)+1) *
          ((-1 : ℝ)^(n+2)*(-1)) =
        (Ring.choose (1-q) (n+2) * (-1 : ℝ)^(n+2)) * (q+n+1)/(n+3) := by ring
    rw [he,ih]
    ring

/-- Closed form on the open parameter interval. This is the potential with
its constant and centroid parts removed, after a positive rescaling. -/
def normalizedAux (q x : ℝ) : ℝ :=
  (1-(1-q)*x-(1-x)^(1-q))/(q*(1-q))

/-- The positive-coefficient series is exactly the rescaled Riesz potential. -/
theorem normalizedAux_hasSum (q x : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hx : |x| < 1) :
    HasSum (fun n => seriesCoeff q n * x^(n+2)) (normalizedAux q x) := by
  have hball : -x ∈ Metric.eball (0 : ℝ) 1 := by
    rw [← ENNReal.ofReal_one, Metric.eball_ofReal]
    simpa [Real.dist_eq, abs_neg] using hx
  have hb := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := 1-q)).hasSum hball
  simp only [zero_add, binomialSeries, FormalMultilinearSeries.ofScalars_apply_eq,
    smul_eq_mul, add_neg_cancel_right, ← sub_eq_add_neg] at hb
  have ht : HasSum (fun n => Ring.choose (1-q) (n+2) * (-x)^(n+2))
      ((1-x)^(1-q)-1+(1-q)*x) := by
    apply (hasSum_nat_add_iff (f := fun n : ℕ => Ring.choose (1-q) n * (-x)^n) 2).mpr
    convert! hb using 1
    simp [Finset.sum_range_succ, Ring.choose_zero_right, Ring.choose_one_right]
    ring
  have hc : -q*(1-q) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hq.1.ne') (by linarith [hq.2])
  have he (n : ℕ) :
      Ring.choose (1-q) (n+2) * (-x)^(n+2) / (-q*(1-q)) =
        seriesCoeff q n * x^(n+2) := by
    rw [neg_pow]
    rw [← mul_assoc,riesz_choose_coeff]
    field_simp [hq.1.ne', (sub_pos.mpr hq.2).ne']
  convert! ht.div_const (-q*(1-q)) using 1
  · funext n
    exact (he n).symm
  · unfold normalizedAux
    field_simp [hq.1.ne', (sub_pos.mpr hq.2).ne']
    ring

#print axioms normalizedAux_hasSum
end ThomsonNegative
