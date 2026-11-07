import ThomsonNegative.Analytic.RootBounds
import ThomsonNegative.SeriesTail

/-!
Scalar evaluation reductions. The slope has an endpoint-safe positive series
with a geometric tail. Exact half-argument identities let the A contact reuse
B and move C below one third, without logarithms or exponentials.
-/

noncomputable section
open Real
open scoped BigOperators
namespace ThomsonNegative

lemma slopeCoeff_le_one (q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) (n : ℕ) :
    slopeCoeff q n ≤ 1 := by
  simpa [slopeCoeff,mul_comm] using (seriesCoeff_bounds q hq n).2

def slopeSeries (q x : ℝ) : ℝ := ∑' n, slopeCoeff q n*x^(n+1)

def slopePartial (q x : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, slopeCoeff q n*x^(n+1)

lemma slope_shift_term_bound (q x : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1)
    (hx : 0 ≤ x) (N n : ℕ) :
    slopeCoeff q (n+N)*x^(n+N+1) ≤ x^(N+1)*x^n := by
  have hc := slopeCoeff_le_one q hq (n+N)
  have hp : x^(n+N+1)=x^(N+1)*x^n := by rw [← pow_add]; congr 1; omega
  calc
    _ ≤ 1*x^(n+N+1) := mul_le_mul_of_nonneg_right hc (pow_nonneg hx _)
    _ = _ := by rw [one_mul,hp]

lemma slopeSeries_summable (q x : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1)
    (hx : x ∈ Set.Ico (0:ℝ) 1) :
    Summable (fun n => slopeCoeff q n*x^(n+1)) := by
  have h := ((hasSum_geometric_of_lt_one hx.1 hx.2).mul_left x).summable
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (slopeCoeff_pos q hq.1 n).le (pow_nonneg hx.1 _)) _ h
  intro n
  simpa using slope_shift_term_bound q x hq hx.1 0 n

/-- A uniform slope tail including both q endpoints. -/
theorem slopeSeries_tail (q x : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1)
    (hx : x ∈ Set.Ico (0:ℝ) 1) (N : ℕ) :
    0 ≤ slopeSeries q x-slopePartial q x N ∧
    slopeSeries q x-slopePartial q x N ≤ x^(N+1)/(1-x) := by
  have hs := slopeSeries_summable q x hq hx
  have hshift : Summable (fun n => slopeCoeff q (n+N)*x^(n+N+1)) :=
    (summable_nat_add_iff N).mpr hs
  have hgeom := (hasSum_geometric_of_lt_one hx.1 hx.2).mul_left (x^(N+1))
  have he : slopeSeries q x-slopePartial q x N =
      ∑' n, slopeCoeff q (n+N)*x^(n+N+1) := by
    have h := hs.sum_add_tsum_nat_add N
    change slopePartial q x N+_=slopeSeries q x at h
    linarith
  rw [he]
  refine ⟨tsum_nonneg (fun n =>
    mul_nonneg (slopeCoeff_pos q hq.1 _).le (pow_nonneg hx.1 _)),?_⟩
  calc
    _ ≤ ∑' n, x^(N+1)*x^n :=
      Summable.tsum_le_tsum (slope_shift_term_bound q x hq hx.1 N) hshift hgeom.summable
    _ = _ := by rw [hgeom.tsum_eq]; ring

theorem auxSlope_eq_slopeSeries (q x : ℝ) (hq : q ≠ 0) (hx : |x| < 1) :
    auxSlope q x=slopeSeries q x := (auxSlope_hasSum q x hq hx).tsum_eq.symm

theorem auxSlope_tail (q x : ℝ) (hq : q ∈ Set.Ioc (0:ℝ) 1)
    (hx : x ∈ Set.Ico (0:ℝ) 1) (N : ℕ) :
    0 ≤ auxSlope q x-slopePartial q x N ∧
    auxSlope q x-slopePartial q x N ≤ x^(N+1)/(1-x) := by
  rw [auxSlope_eq_slopeSeries q x hq.1.ne' (by rw [abs_of_nonneg hx.1]; exact hx.2)]
  exact slopeSeries_tail q x ⟨hq.1.le,hq.2⟩ hx N

/-- Exact recentering of the slope. Only the usual positive series is needed
at the anchor and the reduced argument. -/
theorem auxSlope_recenter (q c y : ℝ) (hq : q ≠ 0) (hc : c < 1) (hy : y < 1) :
    auxSlope q (c+(1-c)*y)=
      auxSlope q c+(1+q*auxSlope q c)*auxSlope q y := by
  have hcb : 0 < 1-c := by linarith
  have hyb : 0 < 1-y := by linarith
  have he : 1-(c+(1-c)*y)=(1-c)*(1-y) := by ring
  unfold auxSlope
  rw [he,Real.mul_rpow hcb.le hyb.le]
  field_simp
  ring

/-- Exact recentering of the potential, preserving the endpoint-safe scalar
representation and all affine terms. -/
theorem normalizedAux_recenter (q c y : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1)
    (hc : c < 1) (hy : y < 1) :
    normalizedAux q (c+(1-c)*y)=normalizedAux q c+(1-c)*y*auxSlope q c+
      (1-c)*(1+q*auxSlope q c)*normalizedAux q y := by
  have hcb : 0 < 1-c := by linarith
  have hyb : 0 < 1-y := by linarith
  have he : 1-(c+(1-c)*y)=(1-c)*(1-y) := by ring
  have hpow : (1-c)^(1-q)=(1-c)*(1-c)^(-q) := by
    rw [show 1-q=(1:ℝ)+(-q) by ring,Real.rpow_add hcb,Real.rpow_one]
  unfold normalizedAux auxSlope
  rw [he,Real.mul_rpow hcb.le hyb.le,hpow]
  field_simp [hq.1.ne',(sub_pos.mpr hq.2).ne']
  ring

theorem auxSlope_half_recenter (q y : ℝ) (hq : q ≠ 0) (hy : y < 1) :
    auxSlope q ((1+y)/2)=auxSlope q (1/2)+
      (1+q*auxSlope q (1/2))*auxSlope q y := by
  simpa only [show (1/2:ℝ)+(1-1/2)*y=(1+y)/2 by ring] using
    auxSlope_recenter q (1/2) y hq (by norm_num) hy

theorem normalizedAux_half_recenter (q y : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1)
    (hy : y < 1) :
    normalizedAux q ((1+y)/2)=normalizedAux q (1/2)+(y/2)*auxSlope q (1/2)+
      ((1+q*auxSlope q (1/2))/2)*normalizedAux q y := by
  convert normalizedAux_recenter q (1/2) y hq (by norm_num) hy using 1 <;> congr 1 <;> ring

/-- C after recentering at one half. A after the same recentering is exactly B. -/
def recenteredC (a : ℝ) : ℝ := (1-a)*(2+√2)/2-1

/-- Three low-argument series plus a single shared half-argument anchor suffice
for all four contacts throughout the analytic root bracket. -/
theorem recentered_contact_domain (a : ℝ)
    (ha : a ∈ Set.Icc limitingHeight (1/3)) :
    a ∈ Set.Icc (0:ℝ) (1/3) ∧
    recenteredC a ∈ Set.Icc (0:ℝ) limitingHeight ∧
    (1-a)*(2-√2)/4 ∈ Set.Icc (0:ℝ) (1/8) := by
  have hl := limitingHeight_range
  have hr := sqrt_two_pos
  have hr1 := one_lt_sqrt_two
  have hr2 := sqrt_two_lt_two
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hcontact := limitingHeight_contact
  have hCmin : 0 ≤ recenteredC a := by
    unfold recenteredC
    nlinarith [mul_nonneg (show 0 ≤ (1/3:ℝ)-a by linarith [ha.2])
      (show 0 ≤ 2+√(2:ℝ) by positivity)]
  have hCmax : recenteredC a ≤ limitingHeight := by
    unfold recenteredC
    nlinarith [mul_nonneg (show 0 ≤ a-limitingHeight by linarith [ha.1])
      (show 0 ≤ 2+√(2:ℝ) by positivity)]
  have hDmin : 0 ≤ (1-a)*(2-√2)/4 := by
    exact div_nonneg (mul_nonneg (by linarith [ha.2]) (by linarith)) (by norm_num)
  have hDmax : (1-a)*(2-√2)/4 ≤ 1/8 := by
    have hprod := mul_le_mul (show 1-a ≤ (3/4:ℝ) by linarith [ha.1,hl.1])
      (show 2-√(2:ℝ) ≤ 2/3 by nlinarith) (by linarith : 0 ≤ 2-√(2:ℝ)) (by norm_num)
    linarith
  exact ⟨⟨by linarith [ha.1,hl.1],ha.2⟩,⟨hCmin,hCmax⟩,⟨hDmin,hDmax⟩⟩

/-- Root residual from the shared half anchor and three small arguments. -/
theorem seriesRoot_recenter (q a : ℝ) (hq : q ≠ 0)
    (ha : a ∈ Set.Icc limitingHeight (1/3)) :
    seriesRoot q a=
      -8*√2*auxSlope q (1/2)+16*(2+q*auxSlope q (1/2))*auxSlope q a-
      8*(2+√2)*(1+q*auxSlope q (1/2))*auxSlope q (recenteredC a)-
      8*(2-√2)*auxSlope q ((1-a)*(2-√2)/4) := by
  have hdom := recentered_contact_domain a ha
  have hl := limitingHeight_range
  have hya : a < 1 := by linarith [ha.2]
  have hyc : recenteredC a < 1 := by linarith [hdom.2.1.2,hl.2]
  have hC : (1-a)*(2+√2)/4=(1+recenteredC a)/2 := by unfold recenteredC; ring
  unfold seriesRoot
  rw [auxSlope_half_recenter q a hq hya,hC,auxSlope_half_recenter q _ hq hyc]
  ring

#print axioms slopeSeries_tail
#print axioms auxSlope_recenter
#print axioms normalizedAux_recenter
#print axioms recentered_contact_domain
#print axioms seriesRoot_recenter
end ThomsonNegative
