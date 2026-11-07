import AllS.Units.N_FI.N_root_contraction.N_coordinates

noncomputable section
open Real
namespace Blueprint.Thomson.Finite

def rootHeightDeriv (q v : ℝ) : ℝ :=
  8*exp (v/q)/(q*(2*exp (v/q)+2+sqrt 2)^2)

theorem rootHeight_hasDerivAt (q v : ℝ) (hq : 0 < q) :
    HasDerivAt (rootHeight q) (rootHeightDeriv q v) v := by
  have hu := ((hasDerivAt_id v).div_const q).exp
  have hn := ((hu.const_mul 2).sub_const 2).add_const (sqrt 2)
  have hd := ((hu.const_mul 2).add_const 2).add_const (sqrt 2)
  have hden : 2*exp (v/q)+2+sqrt 2 ≠ 0 := by positivity
  have h := hn.div hd hden
  convert! h using 1
  dsimp [rootHeightDeriv]
  field_simp
  ring

theorem root_contraction_derivative_height (q q₀ v : ℝ) (hq₀ : 1 ≤ q₀) (hq : q₀ ≤ q) :
    HasDerivAt (rootHeight q) (rootHeightDeriv q v) v ∧
    0 < rootHeightDeriv q v ∧ rootHeightDeriv q v ≤ 5/(17*q₀) := by
  have hqpos : 0 < q := by linarith
  have hq₀pos : 0 < q₀ := by linarith
  have hu := Real.exp_pos (v/q)
  have hr := root_sqrt_bounds.1
  have hden : 0 < 2*exp (v/q)+2+sqrt 2 := by positivity
  have hk : 0 < 2+sqrt (2:ℝ) := by positivity
  refine ⟨rootHeight_hasDerivAt q v hqpos,?_,?_⟩
  · unfold rootHeightDeriv
    positivity
  · have hone : rootHeightDeriv q v ≤ 1/(q*(2+sqrt 2)) := by
      unfold rootHeightDeriv
      apply (div_le_div_iff₀ (mul_pos hqpos (sq_pos_of_pos hden)) (mul_pos hqpos hk)).mpr
      have hs : 8*exp (v/q)*(2+sqrt 2) ≤ (2*exp (v/q)+2+sqrt 2)^2 := by
        nlinarith [sq_nonneg (2*exp (v/q)-(2+sqrt 2))]
      nlinarith [mul_le_mul_of_nonneg_left hs hqpos.le]
    apply hone.trans
    apply (div_le_div_iff₀ (mul_pos hqpos hk) (by positivity : 0 < 17*q₀)).mpr
    nlinarith

#check root_contraction_derivative_height
#print axioms root_contraction_derivative_height
end Blueprint.Thomson.Finite
