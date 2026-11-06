import AllS.Units.N_GI.N_trial_ceiling.N_contact_trial

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem trial_error_ratios (p : ℝ) (hp : (97:ℝ)/2≤p) :
    0≤trialA/(p-trialA) ∧ trialA/(p-trialA)≤(1/50)/((97:ℝ)/2-1/50) ∧
    0≤trialB/(p-trialB) ∧ trialB/(p-trialB)≤(57/1000)/((97:ℝ)/2-57/1000) := by
  obtain ⟨hA,hAu,hB,hBu⟩ := trial_AB_bounds
  have hpa : 0<p-trialA := by linarith
  have hpb : 0<p-trialB := by linarith
  refine ⟨by positivity,?_,by positivity,?_⟩
  · calc
      _ ≤ (1/50)/(p-trialA) := div_le_div_of_nonneg_right hAu.le hpa.le
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  · calc
      _ ≤ (57/1000)/(p-trialB) := div_le_div_of_nonneg_right hBu.le hpb.le
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)

theorem trial_square_normalized_lt_two (p : ℝ) (hp : (97:ℝ)/2≤p) :
    tau^p*(SquareAntiprismVerification.dA (trialHeight p))^(-p)<2 := by
  have h := (trial_contact_individual p hp).1
  obtain ⟨hAr,hArU,_,_⟩ := trial_error_ratios p hp
  obtain ⟨_,_,_,_,hkL,hkU,_,_⟩ := tail_geometric_constants
  obtain ⟨_,_,_,hlU⟩ := tail_lambda_constants
  have hlP : 0<balancedLambda := Real.exp_pos _
  have hkP : 0<contactKappa := by linarith
  have hkl : contactKappa*balancedLambda≤(427:ℝ)/250*(357/500) :=
    mul_le_mul (by linarith) hlU.le hlP.le (by norm_num)
  have hb := mul_le_mul hkl (add_le_add (le_refl 1) hArU) (by linarith) (by norm_num)
  norm_num at hb
  linarith

theorem trial_noncontact_distances (p : ℝ) (hp : (97:ℝ)/2≤p) :
    SquareAntiprismVerification.dB (trialHeight p)=2*SquareAntiprismVerification.dA (trialHeight p) ∧
    2*tau≤SquareAntiprismVerification.dD (trialHeight p) := by
  have hp0 : 0<p := by linarith
  have hh : packingHeight≤trialHeight p := by
    dsimp [trialHeight]
    have := div_nonneg (mul_nonneg tau_pos.le balancedD_pos.le) (by positivity : 0≤2*p)
    linarith
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hsP := Real.sqrt_nonneg (2:ℝ)
  have hsU : √(2:ℝ)<2 := by nlinarith
  have hd : 2*tau≤SquareAntiprismVerification.dD packingHeight := by
    dsimp [SquareAntiprismVerification.dD,tau,packingHeight]
    nlinarith
  refine ⟨by dsimp [SquareAntiprismVerification.dA,SquareAntiprismVerification.dB]; ring,?_⟩
  dsimp [SquareAntiprismVerification.dD] at hd ⊢
  nlinarith [mul_nonneg (by linarith : 0≤2-√(2:ℝ)) (sub_nonneg.mpr hh)]

theorem trial_noncontact_small (p : ℝ) (hp : (97:ℝ)/2≤p) :
    tau^p*(4*(SquareAntiprismVerification.dB (trialHeight p))^(-p)+
      8*(SquareAntiprismVerification.dD (trialHeight p))^(-p)) < 16*(2:ℝ)^(-p) := by
  have hp0 : 0<p := by linarith
  have htr := trial_ceiling_trial_in_range p hp
  have hA : 0<SquareAntiprismVerification.dA (trialHeight p) := by
    dsimp [SquareAntiprismVerification.dA]
    linarith [htr.2]
  have htp := Real.rpow_pos_of_pos tau_pos p
  have htwo := Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (-p)
  obtain ⟨hdB,hdD⟩ := trial_noncontact_distances p hp
  have hB : tau^p*(SquareAntiprismVerification.dB (trialHeight p))^(-p)<2*(2:ℝ)^(-p) := by
    rw [hdB,Real.mul_rpow (by norm_num : (0:ℝ)≤2) hA.le]
    have h := mul_lt_mul_of_pos_right (trial_square_normalized_lt_two p hp) htwo
    nlinarith
  have hD : tau^p*(SquareAntiprismVerification.dD (trialHeight p))^(-p)≤(2:ℝ)^(-p) := by
    have h := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (mul_pos (by norm_num) tau_pos) hdD (by linarith : -p≤0)) htp.le
    rw [mul_comm 2 tau,trial_normalized_rpow p 2 (by norm_num)] at h
    exact h
  nlinarith

theorem trial_two_power_small (p : ℝ) (hp : (97:ℝ)/2≤p) :
    16*(2:ℝ)^(-p)<1/10^6 := by
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) (by linarith : -p≤-(48:ℝ))
  norm_num [Real.rpow_neg,Real.rpow_natCast] at h
  rw [Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
  linarith

theorem trial_contact_uniform (p : ℝ) (hp : (97:ℝ)/2≤p) :
    tau^p*(8*(SquareAntiprismVerification.dA (trialHeight p))^(-p)+
      8*(SquareAntiprismVerification.dC (trialHeight p))^(-p)) + 1/10^6 < (1547:ℝ)/100 := by
  have hc := (trial_ceiling_contact_trial p hp).2
  obtain ⟨hAr,hArU,hBr,hBrU⟩ := trial_error_ratios p hp
  obtain ⟨_,_,_,_,hkL,hkU,_,_⟩ := tail_geometric_constants
  obtain ⟨_,_,_,hlU⟩ := tail_lambda_constants
  have hlP : 0<balancedLambda := Real.exp_pos _
  have hkP : 0<contactKappa := by linarith
  have hka := mul_le_mul (show contactKappa≤(427:ℝ)/250 by linarith) hArU hAr (by norm_num)
  have herr := add_le_add hka hBrU
  have hspos : 0≤contactKappa*(trialA/(p-trialA))+trialB/(p-trialB) := by positivity
  have hb := mul_le_mul (show 8*balancedLambda≤8*((357:ℝ)/500) by linarith) herr hspos (by norm_num)
  have hC := tail_Cmin_constants.2
  norm_num at hb
  simp only [div_eq_mul_inv] at hc hb
  linarith

theorem trial_energy_formula (p a : ℝ) (ha : a∈Set.Ioo (0:ℝ) 1) :
    squaredEnergy p (X a)=SquareAntiprismVerification.G (2*p) a := by
  rw [squaredEnergy_eq_upstream,←Blueprint.antiprism_coordinates,
    SquareAntiprismVerification.energy_X_eq_G (2*p) a ha]

theorem trial_ceiling_noncontact_trial (p : ℝ) (hp : (97:ℝ)/2≤p) :
    tau^p*(4*(SquareAntiprismVerification.dB (trialHeight p))^(-p)+
      8*(SquareAntiprismVerification.dD (trialHeight p))^(-p)) < 16*(2:ℝ)^(-p) ∧
    tau^p*squaredEnergy p (X (trialHeight p))<(1547:ℝ)/100 := by
  refine ⟨trial_noncontact_small p hp,?_⟩
  have htr := trial_ceiling_trial_in_range p hp
  rw [trial_energy_formula p _ ⟨htr.1,by linarith [htr.2]⟩]
  have hc := trial_contact_uniform p hp
  have hn := (trial_noncontact_small p hp).trans (trial_two_power_small p hp)
  dsimp [SquareAntiprismVerification.G]
  have he : -(2*p)/2 = -p := by ring
  rw [he]
  nlinarith

#print axioms trial_ceiling_noncontact_trial
end Blueprint.Thomson.Tail.Implementation
