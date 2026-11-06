import AllS.Units.N_GI.N_trial_ceiling.N_trial_in_range
import AllS.Units.N_GI.N_trial_ceiling.N_scalar_log
import AllS.Units.N_GI.N_constants.N_algebra

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem trial_contact_distances (p : ℝ) (hp : 0<p) :
    SquareAntiprismVerification.dA (trialHeight p)=tau*(1-balancedD/p) ∧
    SquareAntiprismVerification.dC (trialHeight p)=tau*(1+contactKappa*balancedD/p) := by
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  rw [contactKappa_formula]
  dsimp [SquareAntiprismVerification.dA,SquareAntiprismVerification.dC,trialHeight,tau,packingHeight]
  constructor
  · ring
  · ring_nf
    simp only [hs]
    ring

theorem trial_normalized_rpow (p x : ℝ) (hx : 0<x) :
    tau^p*(tau*x)^(-p)=x^(-p) := by
  rw [Real.mul_rpow tau_pos.le hx.le,←mul_assoc,←Real.rpow_add tau_pos]
  simp

theorem balanced_exp_d : exp balancedD=contactKappa*balancedLambda := by
  have hk : 0<contactKappa := by
    obtain ⟨_,_,_,_,h,_,_,_⟩ := tail_geometric_constants
    linarith
  have hd : (contactKappa+1)*balancedD=log contactKappa := by
    unfold balancedD
    field_simp
  have he : balancedD=log contactKappa+(-contactKappa*balancedD) := by nlinarith
  rw [he,Real.exp_add,Real.exp_log hk]
  rfl

theorem trial_contact_individual (p : ℝ) (hp : (97:ℝ)/2≤p) :
    tau^p*(SquareAntiprismVerification.dA (trialHeight p))^(-p) ≤
      contactKappa*balancedLambda*(1+trialA/(p-trialA)) ∧
    tau^p*(SquareAntiprismVerification.dC (trialHeight p))^(-p) ≤
      balancedLambda*(1+trialB/(p-trialB)) := by
  have hp0 : 0<p := by linarith
  obtain ⟨hA,hAu,hB,hBu⟩ := trial_AB_bounds
  obtain ⟨_,hdu,_,_,hkd,hkdu⟩ := tail_d_constants
  have hdpos := balancedD_pos
  have hdp : balancedD/p≤balancedD/((97:ℝ)/2) :=
    div_le_div_of_nonneg_left hdpos.le (by norm_num) hp
  have hdp1 : balancedD/p<1 := by linarith
  have hbase : 0<1-balancedD/p := by linarith
  have hplus : 0<1+contactKappa*balancedD/p := by positivity
  have hratio : balancedD^2/(2*(1-balancedD/p))≤trialA := by
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by linarith) (by linarith)
  have hl1 := trial_log_sub_upper (balancedD/p) (by positivity) hdp1
  have hl2 := trial_log_add_lower (contactKappa*balancedD/p) (by positivity)
  have he1 : -p*log (1-balancedD/p)≤balancedD+trialA/p := by
    calc
      _ ≤ p*(balancedD/p+(balancedD/p)^2/(2*(1-balancedD/p))) := by nlinarith [mul_le_mul_of_nonneg_left hl1 hp0.le]
      _ = balancedD+(balancedD^2/(2*(1-balancedD/p)))/p := by field_simp <;> ring
      _ ≤ _ := add_le_add (le_refl _) (div_le_div_of_nonneg_right hratio hp0.le)
  have he2 : -p*log (1+contactKappa*balancedD/p)≤-contactKappa*balancedD+trialB/p := by
    calc
      _ ≤ -p*(contactKappa*balancedD/p-(contactKappa*balancedD/p)^2/2) := by
        nlinarith [mul_le_mul_of_nonneg_left hl2 hp0.le]
      _ = _ := by dsimp [trialB]; field_simp <;> ring
  obtain ⟨hdA,hdC⟩ := trial_contact_distances p hp0
  have hAe : exp (trialA/p)≤1+trialA/(p-trialA) := by
    convert trial_exp_error (trialA/p) (by positivity) ((div_lt_one hp0).mpr (by linarith)) using 1
    field_simp
    <;> ring
  have hBe : exp (trialB/p)≤1+trialB/(p-trialB) := by
    convert trial_exp_error (trialB/p) (by positivity) ((div_lt_one hp0).mpr (by linarith)) using 1
    field_simp
    <;> ring
  have hkp : 0<contactKappa := by nlinarith [hkd]
  have hlp : 0<balancedLambda := Real.exp_pos _
  constructor
  · rw [hdA,trial_normalized_rpow _ _ hbase,Real.rpow_def_of_pos hbase]
    calc
      _ ≤ exp (balancedD+trialA/p) := Real.exp_le_exp.mpr (by nlinarith [he1])
      _ = contactKappa*balancedLambda*exp (trialA/p) := by rw [Real.exp_add,balanced_exp_d]
      _ ≤ _ := mul_le_mul_of_nonneg_left hAe (by positivity)
  · rw [hdC,trial_normalized_rpow _ _ hplus,Real.rpow_def_of_pos hplus]
    calc
      _ ≤ exp (-contactKappa*balancedD+trialB/p) := Real.exp_le_exp.mpr (by nlinarith [he2])
      _ = balancedLambda*exp (trialB/p) := by rw [Real.exp_add]; rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left hBe hlp.le

theorem trial_contact_energy_bound (p : ℝ) (hp : (97:ℝ)/2≤p) :
    tau^p*(8*(SquareAntiprismVerification.dA (trialHeight p))^(-p)+
      8*(SquareAntiprismVerification.dC (trialHeight p))^(-p)) ≤
      balancedLambda*contactTotalWeight+8*balancedLambda*
        (contactKappa*trialA/(p-trialA)+trialB/(p-trialB)) := by
  obtain ⟨h1,h2⟩ := trial_contact_individual p hp
  have hW : contactTotalWeight=8*(contactKappa+1) := by
    rw [contactKappa_formula]
    dsimp [contactTotalWeight]
    ring
  rw [hW]
  simp only [div_eq_mul_inv] at h1 h2 ⊢
  nlinarith

theorem trial_ceiling_contact_trial (p : ℝ) (hp : (97:ℝ)/2≤p) :
    (0<trialA ∧ trialA<1/50 ∧ 0<trialB ∧ trialB<57/1000) ∧
    tau^p*(8*(SquareAntiprismVerification.dA (trialHeight p))^(-p)+
      8*(SquareAntiprismVerification.dC (trialHeight p))^(-p)) ≤
      balancedLambda*contactTotalWeight+8*balancedLambda*
        (contactKappa*trialA/(p-trialA)+trialB/(p-trialB)) :=
  ⟨trial_AB_bounds,trial_contact_energy_bound p hp⟩

#print axioms trial_contact_individual
#print axioms trial_ceiling_contact_trial
end Blueprint.Thomson.Tail.Implementation
