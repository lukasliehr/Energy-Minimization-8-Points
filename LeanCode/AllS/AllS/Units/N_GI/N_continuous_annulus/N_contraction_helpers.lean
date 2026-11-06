import AllS.Units.N_GI.N_continuous_annulus.N_rational_surrogate
import AllS.Units.N_GI.N_continuous_annulus.N_energy_bridge

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem annulusEnergyLower_strictMonoOn (p : ℝ) (hp : (97:ℝ)/2≤p) :
    StrictMonoOn (annulusEnergyLower p) (Set.Icc annulusK 6) := by
  have hder (x : ℝ) (hx : x∈Set.Icc annulusK 6) :
      HasDerivAt (fun t=>log (annulusEnergyLower p t)) (annulusLogDeriv p x) x ∧ 0<annulusLogDeriv p x := by
    obtain ⟨_,hd,hbound⟩ := continuous_annulus_rational_surrogate p x hp hx.1 hx.2
    obtain ⟨hP,hV,_⟩ := continuous_annulus_polynomial_positive x hx.1 hx.2
    have hden : 0<annulusW*(1+annulusBeta*annulusV x) := by
      have hw : 0<annulusW := by norm_num [annulusW]
      have hb : 0<annulusBeta := by norm_num [annulusBeta]
      have hv : 0<annulusV x := by linarith
      positivity
    exact ⟨hd,(div_pos hP hden).trans hbound⟩
  have hlog : StrictMonoOn (fun t=>log (annulusEnergyLower p t)) (Set.Icc annulusK 6) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc annulusK 6)
    · intro x hx
      exact (hder x hx).1.continuousAt.continuousWithinAt
    · intro x hx
      have hx' : x∈Set.Icc annulusK 6 := interior_subset hx
      rw [(hder x hx').1.deriv]
      exact (hder x hx').2
  intro x hx y hy hxy
  have h := Real.exp_lt_exp.mpr (hlog hx hy hxy)
  simpa only [Real.exp_log (annulusEnergyLower_pos p x),Real.exp_log (annulusEnergyLower_pos p y)] using h

theorem continuous_annulus_of_quadratic_mean (p : ℝ) (hp : (97:ℝ)/2≤p)
    (q : TangentCoordinates) (hq : q∈rotationSlice) (hr : ‖q‖≤3/10)
    (hr6 : ‖q‖<6/p)
    (hM : contactNorm (contactCenter (contactQuadraticArray q))≤2*‖q‖^2)
    (hmean : balancedMean p q≤p*‖q‖^2/(5*tau))
    (henergy : tau^p*squaredEnergy p (orthographicChart q)≤ceiling) :
    ‖q‖<contraction/p := by
  have hpP : 0<p := by linarith
  by_contra hnot
  have hx : annulusK≤p*‖q‖ := by
    have h := (div_le_iff₀ hpP).mp (le_of_not_gt hnot)
    dsimp [annulusK,contraction] at h ⊢
    nlinarith
  have hxhi : p*‖q‖≤6 := by
    have h := (lt_div_iff₀ hpP).mp hr6
    nlinarith
  obtain ⟨_,hv,_⟩ := continuous_annulus_polynomial_positive (p*‖q‖) hx hxhi
  have hxP : 0<p*‖q‖ := by dsimp [annulusK] at hx;linarith
  have hvar := (annulus_actual_surrogate p (p*‖q‖) hp hxP).1
  have hE := annulus_energy_lower_of_quadratic_mean p hp q hq hr hM hmean (by linarith)
  have hmono := (annulusEnergyLower_strictMonoOn p hp).monotoneOn
    (show annulusK∈Set.Icc annulusK 6 from ⟨le_refl _,by norm_num [annulusK]⟩) ⟨hx,hxhi⟩ hx
  have hend := continuous_annulus_inner_endpoint_exclusion p hp
  dsimp [ceiling] at henergy
  linarith

#print axioms annulusEnergyLower_strictMonoOn
#print axioms continuous_annulus_of_quadratic_mean
end Blueprint.Thomson.Tail.Implementation
