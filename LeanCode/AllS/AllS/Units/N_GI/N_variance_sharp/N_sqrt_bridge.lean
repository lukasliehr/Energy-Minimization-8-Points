import AllS.Units.N_GI.N_variance_sharp.N_radicand

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem sharp_variance_of_quartic (q : TangentCoordinates) (hq : ‖q‖≤3/10)
    (hquartic : (17:ℝ)/5*‖q‖^2-(15/4)*‖q‖^4≤
      (contactNorm (fun e=>contactLinearArray q e+contactCenter (contactQuadraticArray q) e))^2) :
    ‖q‖*√((17:ℝ)/5-(15/4)*‖q‖^2)-varianceSigmaH*‖q‖^2≤
      contactNorm (contactCenter (contactDeltaArray q)) := by
  have hrad := (variance_sharp_radicand ‖q‖ (norm_nonneg q) hq).2
  have hs := Real.sq_sqrt hrad.le
  have hroot : ‖q‖*√((17:ℝ)/5-(15/4)*‖q‖^2)≤
      contactNorm (fun e=>contactLinearArray q e+contactCenter (contactQuadraticArray q) e) := by
    have he : (‖q‖*√((17:ℝ)/5-(15/4)*‖q‖^2))^2=(17:ℝ)/5*‖q‖^2-(15/4)*‖q‖^4 := by
      rw [mul_pow,hs]
      ring
    nlinarith [contactNorm_nonneg (fun e=>contactLinearArray q e+contactCenter (contactQuadraticArray q) e),
      show 0≤‖q‖*√((17:ℝ)/5-(15/4)*‖q‖^2) by positivity]
  have he : (fun e=>contactCenter (contactDeltaArray q) e+(-contactCenter (contactRemainderArray q) e))=
      (fun e=>contactLinearArray q e+contactCenter (contactQuadraticArray q) e) := by
    rw [centered_delta_expansion q hq]
    funext e
    ring
  have h := contactNorm_add_le (contactCenter (contactDeltaArray q)) (fun e=>-contactCenter (contactRemainderArray q) e)
  rw [he,contactNorm_neg] at h
  have hR := variance_basic_remainder_norm q hq
  linarith

#print axioms sharp_variance_of_quartic
end Blueprint.Thomson.Tail.Implementation
