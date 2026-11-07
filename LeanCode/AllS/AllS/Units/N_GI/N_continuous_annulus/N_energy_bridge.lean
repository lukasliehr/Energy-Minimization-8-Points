import AllS.Units.N_GI.N_continuous_annulus.N_inner_endpoint_exclusion
import AllS.Units.N_GI.N_weighted_monotonicity.N_mass_one

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem contact_massOne_lower (x : ContactIndex→ℝ) (v : ℝ) (hv : 0<v)
    (hn : v≤contactNorm (contactCenter x)) :
    twoValueExp contactTotalWeight v 1≤∑ e : ContactIndex, contactWeight e*exp (-contactCenter x e) := by
  let e : Fin 16≃ContactIndex := (finProdFinEquiv : (Fin 8×Fin 2)≃Fin (8*2)).symm
  let w : Fin 16→ℝ := fun i=>contactWeight (e i)
  let z : Fin 16→ℝ := fun i=>-contactCenter x (e i)
  have hre (f : ContactIndex→ℝ) : (∑ i : Fin 16, f (e i))=∑ j : ContactIndex,f j := e.sum_comp f
  have hw (i : Fin 16) : 1≤w i := contactWeight_ge_one (e i)
  have hs : (∑ i : Fin 16, w i)=contactTotalWeight := (hre contactWeight).trans contactWeight_sum
  have hm : weightedMean w z=0 := by
    have hc := contactMean_center x
    unfold contactMean at hc
    have hzero : (∑ e : ContactIndex,contactWeight e*contactCenter x e)=0 :=
      (div_eq_zero_iff.mp hc).resolve_right contactTotalWeight_pos.ne'
    change (∑ i : Fin 16,contactWeight (e i)*(-contactCenter x (e i)))=0
    rw [hre (fun j=>contactWeight j*(-contactCenter x j))]
    simp only [mul_neg,Finset.sum_neg_distrib,hzero,neg_zero]
  have hq : weightedSquare w z=(contactNorm (contactCenter x))^2 := by
    change (∑ i : Fin 16,contactWeight (e i)*(-contactCenter x (e i))^2)=_
    rw [hre (fun j=>contactWeight j*(-contactCenter x j)^2)]
    simp only [neg_sq]
    exact (contactNorm_sq (contactCenter x)).symm
  have hqs : v^2≤weightedSquare w z := by
    rw [hq]
    nlinarith [contactNorm_nonneg (contactCenter x)]
  have h := weighted_monotonicity_mass_one (by norm_num : 2≤16) w z hw v hv hm hqs
  rw [hs] at h
  change twoValueExp contactTotalWeight v 1≤∑ i : Fin 16,contactWeight (e i)*exp (-contactCenter x (e i)) at h
  rwa [hre (fun j=>contactWeight j*exp (-contactCenter x j))] at h

theorem annulus_energy_lower_of_quadratic_mean (p : ℝ) (hp : (97:ℝ)/2≤p)
    (q : TangentCoordinates) (hq : q∈rotationSlice) (hr : ‖q‖≤3/10)
    (hM : contactNorm (contactCenter (contactQuadraticArray q))≤2*‖q‖^2)
    (hmean : balancedMean p q≤p*‖q‖^2/(5*tau))
    (hv : 0<annulusActualV p (p*‖q‖)) :
    annulusEnergyLower p (p*‖q‖)≤tau^p*squaredEnergy p (orthographicChart q) := by
  have hpP : 0<p := by linarith
  have hvar := shifted_variance_of_quadratic p hpP.le q hq hr hM
  have hval : annulusActualV p (p*‖q‖)=
      √varianceMu*((p*‖q‖)/tau-balancedRefNorm)-varianceSigma*p*‖q‖^2/tau := by
    dsimp [annulusActualV]
    field_simp [hpP.ne',tau_pos.ne']
    <;> ring
  have hnorm : annulusActualV p (p*‖q‖)≤contactNorm (contactCenter (balancedX p q)) := by rwa [hval]
  have hF := contact_massOne_lower (balancedX p q) _ hv hnorm
  have hscale : (p*‖q‖)^2/(5*tau*p)=p*‖q‖^2/(5*tau) := by
    field_simp [hpP.ne',tau_pos.ne']
    <;> ring
  have he : exp (-(p*‖q‖)^2/(5*tau*p))≤exp (-balancedMean p q) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div,hscale]
    linarith
  have hS : 0≤∑ e : ContactIndex,contactWeight e*exp (-contactCenter (balancedX p q) e) :=
    Finset.sum_nonneg (fun e _=>mul_nonneg (contactWeight_pos e).le (Real.exp_pos _).le)
  have hh := mul_le_mul hF he (Real.exp_pos _).le hS
  have hLam : 0≤balancedLambda := by dsimp [balancedLambda];positivity
  have hb := mul_le_mul_of_nonneg_left hh hLam
  have henergy := balanced_energy_exponential_lower p hpP q hr
  change balancedLambda*exp (-balancedMean p q)*
    (∑ e : ContactIndex,contactWeight e*exp (-contactCenter (balancedX p q) e))≤_ at henergy
  dsimp [annulusEnergyLower]
  calc
    _ = balancedLambda*(twoValueExp contactTotalWeight (annulusActualV p (p*‖q‖)) 1*
        exp (-(p*‖q‖)^2/(5*tau*p))) := by ring
    _ ≤ balancedLambda*((∑ e : ContactIndex,contactWeight e*exp (-contactCenter (balancedX p q) e))*
        exp (-balancedMean p q)) := hb
    _ = balancedLambda*exp (-balancedMean p q)*
        (∑ e : ContactIndex,contactWeight e*exp (-contactCenter (balancedX p q) e)) := by ring
    _ ≤ _ := henergy

#print axioms contact_massOne_lower
#print axioms annulus_energy_lower_of_quadratic_mean
end Blueprint.Thomson.Tail.Implementation
