import AllS.Units.N_GI.N_derivative_stability.N_chart_derivative

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def chartMinRoot (r : ℝ) : ℝ := √(1-r^2)
def chartStretch (r : ℝ) : ℝ := √(2/(1+chartMinRoot r))

theorem chartStretch_nonneg (r : ℝ) : 0≤chartStretch r := Real.sqrt_nonneg _
theorem chartStretch_sq (r : ℝ) : (chartStretch r)^2=2/(1+chartMinRoot r) := by
  apply Real.sq_sqrt
  have h : 0≤chartMinRoot r := Real.sqrt_nonneg _
  positivity

theorem chart_metric_bounds (q : TangentCoordinates) (hq : ‖q‖≤3/10) :
    9/10<chartMinRoot ‖q‖ ∧ chartStretch ‖q‖<20/19 ∧
    1/chartMinRoot ‖q‖<10/9 ∧ chartStretch ‖q‖+1/chartMinRoot ‖q‖<3 := by
  have hr : 0≤‖q‖ := norm_nonneg _
  have hb : 0≤1-‖q‖^2 := by nlinarith
  have hs : (chartMinRoot ‖q‖)^2=1-‖q‖^2 := Real.sq_sqrt hb
  have hsn : 0≤chartMinRoot ‖q‖ := Real.sqrt_nonneg _
  have hsl : 9/10<chartMinRoot ‖q‖ := by nlinarith
  have hsp : 0<chartMinRoot ‖q‖ := by linarith
  have hi : 1/chartMinRoot ‖q‖<10/9 := by apply (div_lt_iff₀ hsp).mpr;linarith
  have hc : chartStretch ‖q‖<20/19 := by
    have hd : 2/(1+chartMinRoot ‖q‖)<20/19 := by
      apply (div_lt_iff₀ (by linarith : 0<1+chartMinRoot ‖q‖)).mpr
      linarith
    have he := chartStretch_sq ‖q‖
    have hp := chartStretch_nonneg ‖q‖
    nlinarith
  exact ⟨hsl,hc,hi,by linarith⟩

theorem chart_deviation_stretch (q : TangentCoordinates) (hq : ‖q‖<1) (i : Fin 8) :
    ‖orthographicChart q i-packingReference i‖≤chartStretch ‖q‖*‖tangentVector q i‖ := by
  obtain ⟨hs,hi,_⟩ := chartRoot_bounds q hq i
  have hsi : 0<chartRoot q i := hs.trans_le hi
  have he : ‖orthographicChart q i-packingReference i‖^2=
      2*‖tangentVector q i‖^2/(1+chartRoot q i) := by
    rw [chart_deviation_sq q hq i,chartRoot_rationalize q hq i]
    ring
  have hu : 2*‖tangentVector q i‖^2/(1+chartRoot q i)≤
      2*‖tangentVector q i‖^2/(1+chartMinRoot ‖q‖) := by
    apply div_le_div_of_nonneg_left (by positivity) (by dsimp [chartMinRoot];linarith)
    exact add_le_add (le_refl _) hi
  have hc := chartStretch_sq ‖q‖
  have hn := chartStretch_nonneg ‖q‖
  have hsq : ‖orthographicChart q i-packingReference i‖^2≤
      (chartStretch ‖q‖*‖tangentVector q i‖)^2 := by
    rw [mul_pow,hc,he]
    convert hu using 1 <;> ring
  nlinarith [norm_nonneg (orthographicChart q i-packingReference i),norm_nonneg (tangentVector q i),
    mul_nonneg hn (norm_nonneg (tangentVector q i))]

#print axioms chart_deviation_stretch
end Blueprint.Thomson.Tail.Implementation
