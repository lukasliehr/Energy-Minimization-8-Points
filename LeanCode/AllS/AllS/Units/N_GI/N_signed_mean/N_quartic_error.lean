import AllS.Units.N_GI.N_signed_mean.N_physical_bounds
import AllS.Units.N_GI.N_signed_mean.N_chart_error

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def stressCubic (q : TangentCoordinates) : ℝ := -stressB q (fun i=>‖tangentVector q i‖^2)

theorem stress_cubic_split (q : TangentCoordinates) (hq : ‖q‖ < 1) :
    2*stressB q (chartNormalDisplacement q)=stressCubic q+2*stressB q (chartQuarticError q) := by
  have hb : chartNormalDisplacement q=(fun i=> -‖tangentVector q i‖^2/2+chartQuarticError q i) :=
    funext (chartNormalDisplacement_split q hq)
  rw [hb]
  unfold stressCubic stressB
  simp only [Finset.mul_sum,← Finset.sum_neg_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem signed_mean_quartic_error (q : TangentCoordinates) (hq : ‖q‖ < 1) :
    |2*stressB q (chartQuarticError q)+stressD (chartNormalDisplacement q) (chartNormalDisplacement q)| ≤
      (4*‖q‖+231/100)*‖q‖^4/(1+√(1-‖q‖^2))^2 := by
  let bn := ‖(WithLp.toLp 2 (chartNormalDisplacement q) : EuclideanSpace ℝ (Fin 8))‖
  let cn := ‖(WithLp.toLp 2 (chartQuarticError q) : EuclideanSpace ℝ (Fin 8))‖
  have hb := chartNormalDisplacement_norm q hq
  have hc := chartQuarticError_norm q hq
  have hB : |stressB q (chartQuarticError q)| ≤ 4*‖q‖*cn := by
    have h := stressB_bound q (chartQuarticError q)
    dsimp [cn]
    exact h.trans (by gcongr; norm_num)
  have hD : stressD (chartNormalDisplacement q) (chartNormalDisplacement q) ≤ (231:ℝ)/100*bn^2 := by
    have h := stressD_upper (chartNormalDisplacement q)
    dsimp [bn]
    exact h.trans (mul_le_mul_of_nonneg_right (by norm_num : (2309:ℝ)/1000 ≤ 231/100) (sq_nonneg _))
  have hd := stressD_nonneg (chartNormalDisplacement q)
  have hden : 0 < 1+√(1-‖q‖^2) := by positivity
  calc
    _ ≤ |2*stressB q (chartQuarticError q)|+
        |stressD (chartNormalDisplacement q) (chartNormalDisplacement q)| := abs_add_le _ _
    _ = 2*|stressB q (chartQuarticError q)|+
        stressD (chartNormalDisplacement q) (chartNormalDisplacement q) := by
      rw [abs_mul,abs_of_nonneg hd]
      norm_num
    _ ≤ 2*(4*‖q‖*cn)+(231:ℝ)/100*bn^2 := by gcongr
    _ ≤ 2*(4*‖q‖*(‖q‖^4/(2*(1+√(1-‖q‖^2))^2)))+
        (231:ℝ)/100*(‖q‖^2/(1+√(1-‖q‖^2)))^2 := by
      gcongr
    _ = _ := by field_simp <;> ring

/-- The sole remaining tensor input to the signed mean argument. This is
stated as a hypothesis here, not asserted or registered as a completed proof. -/
def MeanCubicAbsorption : Prop := ∀q : TangentCoordinates,
  stressH q q+stressCubic q ≤ (829:ℝ)/200*‖q‖^2+(11:ℝ)/10*‖q‖^4

theorem signed_mean_after_cubic (hC : MeanCubicAbsorption) (q : TangentCoordinates) (hq : ‖q‖ ≤ 3/10) :
    contactWeightedDelta q ≤ ((829:ℝ)/200+(11:ℝ)/10*‖q‖^2+
      (4*‖q‖+231/100)*‖q‖^2/(1+√(1-‖q‖^2))^2)*‖q‖^2 := by
  rw [signed_mean_stress_identity q hq]
  have hs := stress_cubic_split q (by linarith : ‖q‖ < 1)
  have he := (le_abs_self _).trans (signed_mean_quartic_error q (by linarith))
  have hc := hC q
  calc
    _ = (stressH q q+stressCubic q)+
        (2*stressB q (chartQuarticError q)+stressD (chartNormalDisplacement q) (chartNormalDisplacement q)) := by linarith
    _ ≤ ((829:ℝ)/200*‖q‖^2+(11:ℝ)/10*‖q‖^4)+
        (4*‖q‖+231/100)*‖q‖^4/(1+√(1-‖q‖^2))^2 := add_le_add hc he
    _ = _ := by ring

#print axioms signed_mean_quartic_error
#print axioms signed_mean_after_cubic
end Blueprint.Thomson.Tail.Implementation
