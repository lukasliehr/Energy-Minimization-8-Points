import AllS.Units.N_GI.N_continuous_annulus.N_polynomial_positive
import AllS.Units.N_GI.N_variance_basic.N_shifted_helpers
import AllS.Units.N_GI.N_tail_rational.N_analytic_bounds
import AllS.Units.N_GI.N_continuous_annulus.N_log_derivative

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem annulus_mu_bounds : (19521:ℝ)/10000<√varianceMu ∧ √varianceMu<9761/5000 := by
  have h : (√varianceMu)^2=(59546:ℝ)/15625 := Real.sq_sqrt (show 0≤varianceMu by norm_num [varianceMu])
  constructor <;> nlinarith [Real.sqrt_nonneg varianceMu]

theorem annulus_reference_denominator : (6212:ℝ)/10000<√(2*packingHeight*(1-packingHeight)) := by
  obtain ⟨_,ha,_,ht,_,_,_,_⟩ := tail_geometric_constants
  have hl : (653:ℝ)/2500<packingHeight := by dsimp [tau] at ht; linarith
  have hm := mul_pos (sub_pos.mpr hl) (show 0<1-packingHeight-653/2500 by linarith)
  have hs := Real.sq_sqrt (show 0≤2*packingHeight*(1-packingHeight) from
    mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith))
  nlinarith [Real.sqrt_nonneg (2*packingHeight*(1-packingHeight))]

theorem annulus_sigma_bound : varianceSigma<314/125 := by
  obtain ⟨_,_,_,_,_,_,_,hW⟩ := tail_geometric_constants
  have hs := Real.sq_sqrt (div_nonneg contactTotalWeight_pos.le (by norm_num : (0:ℝ)≤4))
  have hr : √(contactTotalWeight/4)<2327/1000 := by nlinarith [Real.sqrt_nonneg (contactTotalWeight/4)]
  dsimp [varianceSigma,varianceSigmaH]
  linarith

theorem annulus_coefficient_bounds (p : ℝ) (hp : (97:ℝ)/2≤p) :
    annulusA<√varianceMu/tau ∧ √varianceMu*balancedRefNorm<annulusB ∧
    varianceSigma/(tau*p)<annulusD := by
  obtain ⟨hmL,hmU⟩ := annulus_mu_bounds
  obtain ⟨_,_,htL,htU,_,_,_,_⟩ := tail_geometric_constants
  have hden := annulus_reference_denominator
  have hs := annulus_sigma_bound
  have hpP : 0<p := by linarith
  refine ⟨?_,?_,?_⟩
  · apply (lt_div_iff₀ tau_pos).mpr
    dsimp [annulusA]
    linarith
  · obtain ⟨_,hdU,_,_,_,_⟩ := tail_d_constants
    have hdP := balancedD_pos
    have hmP : 0<√varianceMu := by linarith
    dsimp [balancedRefNorm,annulusB]
    rw [←mul_div_assoc]
    apply (div_lt_iff₀ (by linarith : 0<√(2*packingHeight*(1-packingHeight)))).mpr
    have hh := mul_pos (sub_pos.mpr hmU) (sub_pos.mpr hdU)
    nlinarith
  · apply (div_lt_iff₀ (mul_pos tau_pos hpP)).mpr
    have hh := mul_nonneg (sub_nonneg.mpr htL.le) (sub_nonneg.mpr hp)
    dsimp [annulusD]
    nlinarith

def annulusActualV (p x : ℝ) : ℝ := √varianceMu*(x/tau-balancedRefNorm)-varianceSigma*x^2/(tau*p)

theorem annulus_actual_surrogate (p x : ℝ) (hp : (97:ℝ)/2≤p) (hx : 0<x) :
    annulusV x<annulusActualV p x ∧
    annulusA-2*annulusD*x<√varianceMu/tau-2*(varianceSigma/(tau*p))*x := by
  obtain ⟨hA,hB,hD⟩ := annulus_coefficient_bounds p hp
  have hAx := mul_pos (sub_pos.mpr hA) hx
  have hDx := mul_pos (sub_pos.mpr hD) hx
  have hDxx := mul_pos (sub_pos.mpr hD) (sq_pos_of_pos hx)
  have he : annulusActualV p x=(√varianceMu/tau)*x-√varianceMu*balancedRefNorm-(varianceSigma/(tau*p))*x^2 := by
    dsimp [annulusActualV]
    ring
  rw [he]
  dsimp [annulusV]
  constructor <;> nlinarith

#print axioms annulus_coefficient_bounds
#print axioms annulus_actual_surrogate

theorem annulus_weight_beta_bounds :
    1<contactTotalWeight ∧ contactTotalWeight<annulusW ∧
    0 < massOneBeta contactTotalWeight ∧ massOneBeta contactTotalWeight<annulusBeta := by
  obtain ⟨_,_,_,_,_,_,hwL,hwU⟩ := tail_geometric_constants
  have hW : 1<contactTotalWeight := by linarith
  obtain ⟨hA,hb,hbal,hAb,hbW⟩ := massOne_parameters contactTotalWeight hW
  have hsq : (massOneBeta contactTotalWeight)^2*(contactTotalWeight-1)=contactTotalWeight := by
    calc
      _ = contactTotalWeight*((contactTotalWeight-1)*twoValueB contactTotalWeight 1*massOneBeta contactTotalWeight) := by rw [hbW];ring
      _ = _ := by rw [←hbal,hAb,mul_one]
  refine ⟨hW,by dsimp [annulusW];linarith,hb,?_⟩
  by_contra hh
  have hh2 : annulusBeta^2≤(massOneBeta contactTotalWeight)^2 := by
    have hh1 : annulusBeta≤ massOneBeta contactTotalWeight := le_of_not_gt hh
    nlinarith [show 0<annulusBeta by norm_num [annulusBeta]]
  have hmul := mul_nonneg (sub_nonneg.mpr hh2) (sub_nonneg.mpr hW.le)
  dsimp [annulusBeta] at hmul
  nlinarith

theorem annulus_mean_derivative_coefficient (p : ℝ) (hp : (97:ℝ)/2≤p) :
    2/(5*tau*p)<annulusE := by
  have hpP : 0<p := by linarith
  have ht := tail_geometric_constants.2.2.1
  have hm := mul_nonneg (sub_nonneg.mpr ht.le) (sub_nonneg.mpr hp)
  apply (div_lt_iff₀ (by positivity : 0<5*tau*p)).mpr
  dsimp [annulusE]
  nlinarith

#print axioms annulus_weight_beta_bounds
#print axioms annulus_mean_derivative_coefficient
end Blueprint.Thomson.Tail.Implementation
