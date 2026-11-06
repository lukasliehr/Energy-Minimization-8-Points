import AllS.Units.N_GI.N_full_hessian.N_positive_part
import AllS.Units.N_GI.N_full_hessian.N_negative_part

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def hessianMargin (p : ℝ) : ℝ := (329/500)*(p+1)-(248/15)*tau

theorem hessianMargin_pos (p : ℝ) (hp : (97:ℝ)/2≤p) : 0<hessianMargin p := by
  have ht : tau<3/2 := by linarith [tail_geometric_constants.2.2.2.1]
  dsimp [hessianMargin]
  linarith

theorem full_hessian_strict_margin (p : ℝ) (hp : (97:ℝ)/2≤p) (q ξ : TangentCoordinates)
    (hq : q∈convexTailDomain p) (hξ : ξ∈rotationSlice) (hξ0 : ξ≠0) :
    hessianMargin p*‖ξ‖^2≤tau^(p+2)/p*energySecond p q ξ ∧ 0<hessianMargin p*‖ξ‖^2 := by
  have hp0 : 0<p := by linarith
  have he := full_hessian_exact_hessian p hp0 q ξ (tail_small_radius p hp q hq.2.1)
  have hP := full_hessian_positive_part p hp q ξ hq hξ
  have hN := full_hessian_negative_part p hp q ξ hq
  refine ⟨?_,mul_pos (hessianMargin_pos p hp) (sq_pos_of_pos (norm_pos_iff.mpr hξ0))⟩
  dsimp [hessianMargin]
  nlinarith

theorem convexTailDomain_norm_lt (p : ℝ) (hp : (97:ℝ)/2≤p) (q : TangentCoordinates)
    (hq : q∈convexTailDomain p) : ‖q‖<3/10 := by
  have hr := hq.2.1
  change ‖q‖≤(77/100)/p at hr
  have h := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤77/100) (by norm_num : (0:ℝ)<97/2) hp
  norm_num at h
  linarith

theorem energySecond_pos (p : ℝ) (hp : (97:ℝ)/2≤p) (q ξ : TangentCoordinates)
    (hq : q∈convexTailDomain p) (hξ : ξ∈rotationSlice) (hξ0 : ξ≠0) : 0<energySecond p q ξ := by
  obtain ⟨h,hpM⟩ := full_hessian_strict_margin p hp q ξ hq hξ hξ0
  have hp0 : 0<p := by linarith
  have hfac : 0<tau^(p+2)/p := div_pos (Real.rpow_pos_of_pos tau_pos _) hp0
  nlinarith

#print axioms full_hessian_strict_margin
#print axioms energySecond_pos
end Blueprint.Thomson.Tail.Implementation
