import ThomsonNegative.SeriesIdentity
import ThomsonNegative.Definitions

noncomputable section
open Real
namespace ThomsonNegative

/-- Derivative in `x=(1+t)/2` of the rescaled auxiliary potential. -/
def auxSlope (q x : ℝ) : ℝ := ((1-x)^(-q)-1)/q

theorem auxSlope_hasDerivAt (q x : ℝ) (hq : q ≠ 0) (hx : x < 1) :
    HasDerivAt (auxSlope q) ((1-x)^(-q-1)) x := by
  have hbase : HasDerivAt (fun y : ℝ => 1-y) (-1) x := (hasDerivAt_id x).const_sub 1
  have hp := (Real.hasDerivAt_rpow_const (p := -q)
    (Or.inl (show 1-x ≠ 0 by linarith))).comp x hbase
  have h := (hp.sub_const 1).div_const q
  convert! h using 1
  field_simp

theorem normalizedAux_hasDerivAt (q x : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hx : x < 1) : HasDerivAt (normalizedAux q) (auxSlope q x) x := by
  have hbase : HasDerivAt (fun y : ℝ => 1-y) (-1) x := (hasDerivAt_id x).const_sub 1
  have hp := (Real.hasDerivAt_rpow_const (p := 1-q)
    (Or.inl (show 1-x ≠ 0 by linarith))).comp x hbase
  have ha := (((hasDerivAt_id x).const_mul (1-q)).const_sub 1).sub hp
  have h := ha.div_const (q*(1-q))
  convert! h using 1
  unfold auxSlope
  rw [show 1-q-1 = -q by ring]
  field_simp [hq.1.ne', (sub_pos.mpr hq.2).ne']
  ring

/-- Uniform scalar curvature bounds on the entire contact interval. -/
theorem aux_curvature_bounds (q x : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hx : x ∈ Set.Icc (0 : ℝ) (2/3)) :
    1 ≤ (1-x)^(-q-1) ∧ (1-x)^(-q-1) ≤ 9 := by
  have hb : 0 < 1-x := by linarith [hx.2]
  have he : -q-1 ≤ 0 := by linarith [hq.1]
  constructor
  · exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hb (by linarith [hx.1]) he
  · have h1 : (1-x)^(-q-1) ≤ (1/3 : ℝ)^(-q-1) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith [hx.2]) he
    have h2 : (1/3 : ℝ)^(-q-1) ≤ (1/3 : ℝ)^(-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith [hq.2])
    have h3 : (1/3 : ℝ)^(-2 : ℝ) = 9 := by norm_num [Real.rpow_neg, Real.rpow_two]
    exact h1.trans (h2.trans_eq h3)

/-- The analytic lower bound replacing the interval derivative gate.
The four arguments are the antiprism contact values `(1+t)/2`. -/
theorem root_curvature_bounds (q xA xB xC xD : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hA : xA ∈ Set.Icc (0 : ℝ) (2/3)) (hB : xB ∈ Set.Icc (0 : ℝ) (2/3))
    (hC : xC ∈ Set.Icc (0 : ℝ) (2/3)) (hD : xD ∈ Set.Icc (0 : ℝ) (2/3)) :
    let L := 8*(1-xA)^(-q-1)+16*(1-xB)^(-q-1)+
      2*(2+√2)^2*(1-xC)^(-q-1)+2*(2-√2)^2*(1-xD)^(-q-1)
    48 ≤ L ∧ L ≤ 432 := by
  have a := aux_curvature_bounds q xA hq hA
  have b := aux_curvature_bounds q xB hq hB
  have c := aux_curvature_bounds q xC hq hC
  have d := aux_curvature_bounds q xD hq hD
  have hc : 0 ≤ 2*(2+√(2:ℝ))^2 := by positivity
  have hd : 0 ≤ 2*(2-√(2:ℝ))^2 := by positivity
  have c0 := mul_le_mul_of_nonneg_left c.1 hc
  have c1 := mul_le_mul_of_nonneg_left c.2 hc
  have d0 := mul_le_mul_of_nonneg_left d.1 hd
  have d1 := mul_le_mul_of_nonneg_left d.2 hd
  have hs : (√(2:ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  have he : 8+16+2*(2+√(2:ℝ))^2+2*(2-√(2:ℝ))^2 = 48 := by nlinarith
  dsimp only
  constructor <;> nlinarith

#print axioms normalizedAux_hasDerivAt
#print axioms aux_curvature_bounds
#print axioms root_curvature_bounds
end ThomsonNegative
