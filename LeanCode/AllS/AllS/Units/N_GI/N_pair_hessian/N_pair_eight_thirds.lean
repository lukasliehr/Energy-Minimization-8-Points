import AllS.Units.N_GI.N_pair_hessian.N_pair_upper_formula
import AllS.Units.N_GI.N_convex_domain.N_sublevel_bridge

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem pair_hessian_small_constants (r : ℝ) (hr : 0≤r) (hu : r≤2/125) :
    999/1000<chartMinRoot r ∧ chartStretch r<101/100 := by
  have hsp : 0≤chartMinRoot r := Real.sqrt_nonneg _
  have hsq : (chartMinRoot r)^2=1-r^2 := Real.sq_sqrt (by nlinarith)
  have hs : 999/1000<chartMinRoot r := by nlinarith
  have hc := chartStretch_sq r
  have hcp := chartStretch_nonneg r
  have hd : 2/(1+chartMinRoot r)<2000/1999 := by
    apply (div_lt_iff₀ (by linarith : 0<1+chartMinRoot r)).mpr
    linarith
  exact ⟨hs,by nlinarith⟩

theorem pair_hessian_scalar_bound (r : ℝ) (hr : 0≤r) (hu : r≤2/125) :
    pairHessianBound r<8/3 := by
  obtain ⟨hs,hc⟩ := pair_hessian_small_constants r hr hu
  have hsp : 0<chartMinRoot r := by linarith
  have hcp := chartStretch_nonneg r
  have ha := tail_geometric_constants.2.1
  have htwo := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤2)
    (by norm_num : (0:ℝ)<(999/1000)^2) (pow_le_pow_left₀ (by norm_num) hs.le 2)
  have hn : 2*(packingHeight+chartStretch r*r)≤2*(262/1000+(101/100)*(2/125)) := by nlinarith
  have hthree := (div_le_div_of_nonneg_right hn (pow_pos hsp 3).le).trans
    (div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤2*(262/1000+(101/100)*(2/125)))
      (by norm_num : (0:ℝ)<(999/1000)^3) (pow_le_pow_left₀ (by norm_num) hs.le 3))
  have h := add_le_add htwo hthree
  norm_num at h
  dsimp [pairHessianBound]
  linarith

theorem pair_hessian_pair_eight_thirds (p : ℝ) (hp : (97:ℝ)/2≤p) (q : TangentCoordinates)
    (hq : ‖q‖≤contraction/p) : pairHessianBound ‖q‖<8/3 := by
  apply pair_hessian_scalar_bound _ (norm_nonneg _)
  have h := div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤77/100) (by norm_num : (0:ℝ)<97/2) hp
  change ‖q‖≤(77/100)/p at hq
  norm_num at h
  linarith

#print axioms pair_hessian_pair_eight_thirds
end Blueprint.Thomson.Tail.Implementation
