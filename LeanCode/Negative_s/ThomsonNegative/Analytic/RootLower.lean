import ThomsonNegative.Analytic.ScalarReduction

/-!
A narrow analytic lower root bound on the negative-exponent range. At 5/16
there is a single sign change in the root moments. The slope coefficients
are decreasing, so the worst sign is controlled by the rational q=1 case.
-/

noncomputable section
open Real
open scoped BigOperators
namespace ThomsonNegative

lemma slopeCoeff_succ (q : ℝ) (n : ℕ) :
    slopeCoeff q (n+1)=slopeCoeff q n*(q+n+1)/(n+2) := by
  unfold slopeCoeff
  simp only [seriesCoeff,Nat.cast_add,Nat.cast_one]
  have h2 : (n:ℝ)+2 ≠ 0 := by positivity
  have h3 : (n:ℝ)+3 ≠ 0 := by positivity
  field_simp
  ring

lemma slopeCoeff_one (n : ℕ) : slopeCoeff 1 n=1 := by
  induction n with
  | zero => norm_num [slopeCoeff,seriesCoeff]
  | succ n ih =>
    rw [slopeCoeff_succ,ih]
    have h2 : (n:ℝ)+2 ≠ 0 := by positivity
    field_simp
    ring

lemma slopeCoeff_antitone (q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) :
    Antitone (slopeCoeff q) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [slopeCoeff_succ]
  apply (div_le_iff₀ (by positivity : (0:ℝ)<n+2)).mpr
  apply mul_le_mul_of_nonneg_left _ (slopeCoeff_pos q hq.1 n).le
  linarith [hq.2]

lemma rootMoment_five_sixteenths_zero : rootMoment (5/16) 0 = -1 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  unfold rootMoment
  linear_combination (-11/4:ℝ)*hs

lemma rootMoment_five_sixteenths_one : rootMoment (5/16) 1 = -1 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  unfold rootMoment
  linear_combination (-363/128:ℝ)*hs

lemma rootMoment_five_sixteenths_two : rootMoment (5/16) 2 = -2105/4096 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  unfold rootMoment
  linear_combination (-1331*(√(2:ℝ))^2/16384-17303/8192)*hs

lemma rootMoment_five_sixteenths_three : rootMoment (5/16) 3 = -15627/131072 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  unfold rootMoment
  linear_combination (-73205*(√(2:ℝ))^2/524288-366025/262144)*hs

lemma rootMoment_five_sixteenths_initial (n : ℕ) (hn : n < 4) :
    rootMoment (5/16) n ≤ 0 := by
  interval_cases n
  · rw [rootMoment_five_sixteenths_zero]; norm_num
  · rw [rootMoment_five_sixteenths_one]; norm_num
  · rw [rootMoment_five_sixteenths_two]; norm_num
  · rw [rootMoment_five_sixteenths_three]; norm_num

lemma five_sixteenths_domination_start :
    16*((1+(5/16:ℝ))/2)^5-
      8*(2+√2)*((1-(5/16:ℝ))*(2+√2)/4)^5-
      8*(2-√2)*((1-(5/16:ℝ))*(2-√2)/4)^5=392355/8388608 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  linear_combination (-161051*(√(2:ℝ))^4/67108864-
    4992581*(√(2:ℝ))^2/33554432-14655641/16777216)*hs

lemma weighted_power_domination (A C D u v : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 0 ≤ D) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hCA : C ≤ A) (hDA : D ≤ A) (N : ℕ)
    (hN : u*C^N+v*D^N ≤ 16*A^N) (n : ℕ) :
    u*C^(N+n)+v*D^(N+n) ≤ 16*A^(N+n) := by
  induction n with
  | zero => simpa using hN
  | succ n ih =>
    have hmul := mul_le_mul_of_nonneg_right ih hA
    have hCmul := mul_le_mul_of_nonneg_left hCA (mul_nonneg hu (pow_nonneg hC (N+n)))
    have hDmul := mul_le_mul_of_nonneg_left hDA (mul_nonneg hv (pow_nonneg hD (N+n)))
    rw [show N+(n+1)=(N+n)+1 by omega,pow_succ,pow_succ,pow_succ]
    nlinarith

lemma rootMoment_five_sixteenths_tail (n : ℕ) (hn : 4 ≤ n) :
    0 ≤ rootMoment (5/16) n := by
  have hdom := contact_series_domain (5/16) (by constructor <;> norm_num)
  have hr := sqrt_two_pos
  have hr2 := sqrt_two_lt_two
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hr3 : √(2:ℝ) ≤ 3/2 := by nlinarith
  have hC : (1-(5/16:ℝ))*(2+√2)/4 ≤ (1+(5/16:ℝ))/2 := by nlinarith
  have hD : (1-(5/16:ℝ))*(2-√2)/4 ≤ (1+(5/16:ℝ))/2 := by nlinarith
  have hstart := five_sixteenths_domination_start
  have hmain := weighted_power_domination ((1+(5/16:ℝ))/2)
    ((1-(5/16:ℝ))*(2+√2)/4) ((1-(5/16:ℝ))*(2-√2)/4)
    (8*(2+√2)) (8*(2-√2)) hdom.1.1 hdom.2.2.1.1 hdom.2.2.2.1
    (by positivity) (by nlinarith) hC hD 5 (by linarith) (n-4)
  have he : n+1=5+(n-4) := by omega
  have hB : 0 ≤ 16*(5/16:ℝ)^(n+1) := by positivity
  unfold rootMoment
  rw [he] at hB ⊢
  linarith

lemma auxSlope_one (x : ℝ) (hx : x < 1) : auxSlope 1 x=x/(1-x) := by
  unfold auxSlope
  norm_num [Real.rpow_neg_one]
  have hne : 1-x ≠ 0 := by linarith
  field_simp [hne]
  ring

lemma seriesRoot_one_five_sixteenths : seriesRoot 1 (5/16) = -12544/8371 := by
  have hdom := contact_series_domain (5/16) (by constructor <;> norm_num)
  have hr := sqrt_two_pos
  have hr2 := sqrt_two_lt_two
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  unfold seriesRoot
  rw [auxSlope_one _ (by linarith [hdom.1.2]),auxSlope_one _ (by norm_num),
    auxSlope_one _ (by linarith [hdom.2.2.1.2]),auxSlope_one _ (by linarith [hdom.2.2.2.2])]
  have hC : 1-(1-(5/16:ℝ))*(2+√2)/4 ≠ 0 := by linarith [hdom.2.2.1.2]
  have hD : 1-(1-(5/16:ℝ))*(2-√2)/4 ≠ 0 := by linarith [hdom.2.2.2.2]
  have hC' : (16*4-(16-5)*(2+√(2:ℝ))) ≠ 0 := by nlinarith
  have hD' : (16*4-(16-5)*(2-√(2:ℝ))) ≠ 0 := by nlinarith
  field_simp [hC,hD,hC',hD']
  nlinarith

/-- Monotone coefficient reweighting turns one rational endpoint calculation
into a uniform analytic sign on the full negative-s parameter interval. -/
theorem seriesRoot_five_sixteenths_neg (q : ℝ) (hq : q ∈ Set.Ioc (0:ℝ) 1) :
    seriesRoot q (5/16) < 0 := by
  have hq' : q ∈ Set.Icc (0:ℝ) 1 := ⟨hq.1.le,hq.2⟩
  have hsum := seriesRoot_hasSum q (5/16) hq.1.ne' (by constructor <;> norm_num)
  have hsum1 := seriesRoot_hasSum 1 (5/16) (by norm_num) (by constructor <;> norm_num)
  simp only [slopeCoeff_one,one_mul] at hsum1
  have hg := hsum1.mul_left (slopeCoeff q 3)
  have hterm (n : ℕ) : slopeCoeff q n*rootMoment (5/16) n ≤
      slopeCoeff q 3*rootMoment (5/16) n := by
    by_cases hn : n < 4
    · exact mul_le_mul_of_nonpos_right
        (slopeCoeff_antitone q hq' (by omega : n ≤ 3))
        (rootMoment_five_sixteenths_initial n hn)
    · exact mul_le_mul_of_nonneg_right
        (slopeCoeff_antitone q hq' (by omega : 3 ≤ n))
        (rootMoment_five_sixteenths_tail n (by omega))
  have hle := Summable.tsum_le_tsum hterm hsum.summable hg.summable
  rw [hsum.tsum_eq,hg.tsum_eq,seriesRoot_one_five_sixteenths] at hle
  exact hle.trans_lt (mul_neg_of_pos_of_neg (slopeCoeff_pos q hq.1.le 3) (by norm_num))

/-- The exact negative-s root satisfies the narrow rational physical range
needed for the one-moment contact-count equality argument. -/
theorem aStar_negative_range (q : ℝ) (hq : q ∈ Set.Ioc (0:ℝ) 1) :
    aStar (2*q-2) ∈ Set.Ioo (5/16:ℝ) (1/3) := by
  have hs : -2 < 2*q-2 := by linarith [hq.1]
  have hspec := aStar_spec (2*q-2) hs
  have hf : F (2*q-2) (aStar (2*q-2))=0 := (hspec.2 _ hspec.1).mpr rfl
  have hF : F (2*q-2) (5/16)<0 := by
    rw [stationarity_series_bridge q (5/16) hq.1.ne' ⟨by norm_num,by norm_num⟩]
    exact mul_neg_of_pos_of_neg (mul_pos hq.1 (Real.rpow_pos_of_pos (by norm_num) _))
      (seriesRoot_five_sixteenths_neg q hq)
  refine ⟨?_,(aStar_analytic_range (2*q-2) hs).2⟩
  by_contra hh
  have hle : aStar (2*q-2) ≤ (5/16:ℝ) := le_of_not_gt hh
  have hm := (F_strictMonoOn (2*q-2) hs).monotoneOn
    ⟨hspec.1.1.le,hspec.1.2⟩ ⟨by norm_num,by norm_num⟩ hle
  rw [hf] at hm
  linarith

#print axioms seriesRoot_five_sixteenths_neg
#print axioms aStar_negative_range
end ThomsonNegative
