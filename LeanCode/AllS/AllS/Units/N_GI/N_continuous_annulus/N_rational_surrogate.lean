import AllS.Units.N_GI.N_continuous_annulus.N_inner_endpoint_exclusion

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem massOne_contact_surrogate (u v : ℝ) (hu : 0<u) (huv : u≤v) :
    u/(annulusW*(1+annulusBeta*u))≤
      twoValueA contactTotalWeight 1*(exp (massOneBeta contactTotalWeight*v)-1)/
        (1+(contactTotalWeight-1)*exp (massOneBeta contactTotalWeight*v)) := by
  obtain ⟨hW,hWup,hb,hbup⟩ := annulus_weight_beta_bounds
  have hv : 0<v := hu.trans_le huv
  have hden1 : 0<contactTotalWeight*(1+massOneBeta contactTotalWeight*u) := by positivity
  have hden2 : 0<contactTotalWeight*(1+massOneBeta contactTotalWeight*v) := by positivity
  have hden : contactTotalWeight*(1+massOneBeta contactTotalWeight*u)≤annulusW*(1+annulusBeta*u) := by
    gcongr
    norm_num [annulusW]
  have h1 := div_le_div_of_nonneg_left hu.le hden1 hden
  have h2 : u/(contactTotalWeight*(1+massOneBeta contactTotalWeight*u))≤
      v/(contactTotalWeight*(1+massOneBeta contactTotalWeight*v)) := by
    apply (div_le_div_iff₀ hden1 hden2).mpr
    have h := mul_nonneg contactTotalWeight_pos.le (sub_nonneg.mpr huv)
    nlinarith
  exact h1.trans (h2.trans (massOne_log_derivative_lower contactTotalWeight v hW hv))

def annulusLogDeriv (p x : ℝ) : ℝ :=
  (√varianceMu/tau-2*(varianceSigma/(tau*p))*x)*
    (twoValueA contactTotalWeight 1*(exp (massOneBeta contactTotalWeight*annulusActualV p x)-1)/
      (1+(contactTotalWeight-1)*exp (massOneBeta contactTotalWeight*annulusActualV p x)))-2*x/(5*tau*p)

theorem annulusActualV_hasDerivAt (p x : ℝ) :
    HasDerivAt (annulusActualV p) (√varianceMu/tau-2*(varianceSigma/(tau*p))*x) x := by
  have h := (((hasDerivAt_id x).div_const tau).sub_const balancedRefNorm).const_mul (√varianceMu)
  convert! h.sub ((((hasDerivAt_id x).pow 2).const_mul varianceSigma).div_const (tau*p)) using 1
  dsimp only [id]
  ring

theorem annulusEnergyLower_pos (p x : ℝ) : 0<annulusEnergyLower p x := by
  have hW := annulus_weight_beta_bounds.1
  dsimp [annulusEnergyLower,twoValueExp,balancedLambda]
  positivity

theorem annulusLog_hasDerivAt (p x : ℝ) (hv : 0<annulusActualV p x) :
    HasDerivAt (fun t=>log (annulusEnergyLower p t)) (annulusLogDeriv p x) x := by
  have hF (t : ℝ) : 0<twoValueExp contactTotalWeight (annulusActualV p t) 1 := by
    have hW := annulus_weight_beta_bounds.1
    dsimp [twoValueExp]
    positivity
  have hLam : 0<balancedLambda := by dsimp [balancedLambda]; positivity
  have heq : (fun t=>log (annulusEnergyLower p t))=
      (fun t=>log balancedLambda+log (twoValueExp contactTotalWeight (annulusActualV p t) 1)-t^2/(5*tau*p)) := by
    funext t
    rw [annulusEnergyLower,Real.log_mul (mul_pos hLam (hF t)).ne' (Real.exp_pos _).ne',
      Real.log_mul hLam.ne' (hF t).ne',Real.log_exp]
    ring
  rw [heq]
  have h := (massOne_log_hasDerivAt contactTotalWeight (annulusActualV p x)
    annulus_weight_beta_bounds.1 hv).comp x (annulusActualV_hasDerivAt p x)
  convert! ((hasDerivAt_const x (log balancedLambda)).add h).sub
    (((hasDerivAt_id x).pow 2).div_const (5*tau*p)) using 1
  dsimp [annulusLogDeriv]
  ring

theorem continuous_annulus_rational_surrogate (p x : ℝ) (hp : (97:ℝ)/2≤p)
    (hlo : annulusK≤x) (hhi : x≤6) :
    annulusV x<annulusActualV p x ∧
    HasDerivAt (fun t=>log (annulusEnergyLower p t)) (annulusLogDeriv p x) x ∧
    annulusP x/(annulusW*(1+annulusBeta*annulusV x))<annulusLogDeriv p x := by
  have hx : 0<x := by dsimp [annulusK] at hlo;linarith
  obtain ⟨hpP,hvU,hds⟩ := continuous_annulus_polynomial_positive x hlo hhi
  obtain ⟨hv,hder⟩ := annulus_actual_surrogate p x hp hx
  have hu : 0<annulusV x := by linarith
  have hF := massOne_contact_surrogate (annulusV x) (annulusActualV p x) hu hv.le
  have hden : 0<annulusW*(1+annulusBeta*annulusV x) := by
    have hw : 0<annulusW := by norm_num [annulusW]
    have hb : 0<annulusBeta := by norm_num [annulusBeta]
    positivity
  have hr : 0<annulusV x/(annulusW*(1+annulusBeta*annulusV x)) := div_pos hu hden
  have hm1 := mul_lt_mul_of_pos_right hder hr
  have hm2 := mul_le_mul_of_nonneg_left hF (hds.trans hder).le
  have hmean := mul_lt_mul_of_pos_right (annulus_mean_derivative_coefficient p hp) hx
  have hmean2 : 2*x/(5*tau*p)<annulusE*x := by convert! hmean using 1 <;> ring
  have hwne : annulusW≠0 := by norm_num [annulusW]
  have hdne : 1+annulusBeta*annulusV x≠0 := by
    apply ne_of_gt
    have hb : 0<annulusBeta := by norm_num [annulusBeta]
    positivity
  have hpoly : annulusP x/(annulusW*(1+annulusBeta*annulusV x))=
      (annulusA-2*annulusD*x)*(annulusV x/(annulusW*(1+annulusBeta*annulusV x)))-annulusE*x := by
    dsimp [annulusP]
    rw [sub_div]
    have he : annulusE*x*annulusW*(1+annulusBeta*annulusV x)=
        (annulusE*x)*(annulusW*(1+annulusBeta*annulusV x)) := by ring
    rw [he,mul_div_cancel_right₀ _ hden.ne']
    ring
  refine ⟨hv,annulusLog_hasDerivAt p x (hu.trans hv),?_⟩
  rw [hpoly]
  dsimp [annulusLogDeriv]
  linarith

#print axioms continuous_annulus_rational_surrogate
end Blueprint.Thomson.Tail.Implementation
