import AllS.Units.N_GI.N_outer_annulus.N_endpoint_exclusion
import AllS.Units.N_GI.N_continuous_annulus.N_energy_bridge

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem contactNorm_balancedZ : contactNorm balancedZ=balancedZNorm := by
  have hs := contactNorm_sq balancedZ
  rw [balancedZ_square] at hs
  have hz : 0≤balancedZNorm := by dsimp [balancedZNorm];positivity
  nlinarith [contactNorm_nonneg balancedZ]

theorem balanced_variance_of_sharp (p : ℝ) (hp : 0≤p) (q : TangentCoordinates)
    (hsharp : outerF ‖q‖≤contactNorm (contactCenter (contactDeltaArray q))) :
    (p/tau)*outerF ‖q‖-balancedZNorm≤contactNorm (contactCenter (balancedX p q)) := by
  have hc : 0≤p/tau := div_nonneg hp tau_pos.le
  have hz : contactCenter balancedZ=balancedZ := by
    apply contactCenter_of_mean_zero
    simp only [contactMean,balancedZ_mean,zero_div]
  have hx : balancedX p q=(fun e=>(p/tau)*contactDeltaArray q e+(-1)*balancedZ e) := by
    funext e
    simp [balancedX,contactDeltaArray,sub_eq_add_neg]
  have he : (fun e=>contactCenter (balancedX p q) e+balancedZ e)=
      (fun e=>(p/tau)*contactCenter (contactDeltaArray q) e) := by
    rw [hx,contactCenter_add,contactCenter_smul,contactCenter_smul,hz]
    funext e
    ring
  have ht := contactNorm_add_le (contactCenter (balancedX p q)) balancedZ
  rw [he,contactNorm_smul,abs_of_nonneg hc,contactNorm_balancedZ] at ht
  have h := mul_le_mul_of_nonneg_left hsharp hc
  linarith

theorem outer_energy_lower_of_sharp_mean (p : ℝ) (hp : (97:ℝ)/2≤p)
    (q : TangentCoordinates) (hr : ‖q‖≤3/10) (hrL : 6/p≤‖q‖)
    (hsharp : outerF ‖q‖≤contactNorm (contactCenter (contactDeltaArray q)))
    (hmean : balancedMean p q≤p*‖q‖^2/(5*tau)) :
    outerEnergyLower p ‖q‖≤tau^p*squaredEnergy p (orthographicChart q) := by
  have hpP : 0<p := by linarith
  let v : ℝ := (p/tau)*outerF ‖q‖-balancedZNorm
  have hv : 0<v := (Real.sqrt_nonneg contactTotalWeight).trans_lt (outer_variance_scalar p ‖q‖ hp hrL hr)
  have hF := contact_massOne_lower (balancedX p q) v hv (balanced_variance_of_sharp p hpP.le q hsharp)
  have hdrop : (contactTotalWeight-1)*exp (v*outerAlpha)≤twoValueExp contactTotalWeight v 1 := by
    dsimp [twoValueExp,outerAlpha,twoValueB]
    exact le_add_of_nonneg_left (by positivity)
  have he : exp (-(p*‖q‖^2/(5*tau)))≤exp (-balancedMean p q) := Real.exp_le_exp.mpr (by linarith)
  have hS : 0≤∑ e : ContactIndex,contactWeight e*exp (-contactCenter (balancedX p q) e) :=
    Finset.sum_nonneg (fun e _=>mul_nonneg (contactWeight_pos e).le (Real.exp_pos _).le)
  have hh := mul_le_mul (hdrop.trans hF) he (Real.exp_pos _).le hS
  have hLam : 0≤balancedLambda := by dsimp [balancedLambda];positivity
  have hb := mul_le_mul_of_nonneg_left hh hLam
  have henergy := balanced_energy_exponential_lower p hpP q hr
  change balancedLambda*exp (-balancedMean p q)*
    (∑ e : ContactIndex,contactWeight e*exp (-contactCenter (balancedX p q) e))≤_ at henergy
  have hid : outerEnergyLower p ‖q‖=balancedLambda*((contactTotalWeight-1)*exp (v*outerAlpha)*
      exp (-(p*‖q‖^2/(5*tau)))) := by
    dsimp [outerEnergyLower,outerH,v]
    rw [show balancedLambda*((contactTotalWeight-1)*exp (((p/tau)*outerF ‖q‖-balancedZNorm)*outerAlpha)*
        exp (-(p*‖q‖^2/(5*tau))))=
      balancedLambda*(contactTotalWeight-1)*(exp (((p/tau)*outerF ‖q‖-balancedZNorm)*outerAlpha)*
        exp (-(p*‖q‖^2/(5*tau)))) by ring,←Real.exp_add]
    congr 2
    ring
  rw [hid]
  calc
    _ ≤ balancedLambda*((∑ e : ContactIndex,contactWeight e*exp (-contactCenter (balancedX p q) e))*
        exp (-balancedMean p q)) := hb
    _ = balancedLambda*exp (-balancedMean p q)*
        (∑ e : ContactIndex,contactWeight e*exp (-contactCenter (balancedX p q) e)) := by ring
    _ ≤ _ := henergy

theorem outer_annulus_of_sharp_mean (p : ℝ) (hp : (97:ℝ)/2≤p)
    (q : TangentCoordinates) (hr : ‖q‖≤3/10)
    (hsharp : outerF ‖q‖≤contactNorm (contactCenter (contactDeltaArray q)))
    (hmean : balancedMean p q≤p*‖q‖^2/(5*tau))
    (henergy : tau^p*squaredEnergy p (orthographicChart q)≤ceiling) : ‖q‖<6/p := by
  by_contra hh
  have hrL := le_of_not_gt hh
  have hE := outer_energy_lower_of_sharp_mean p hp q hr hrL hsharp hmean
  have hx := outer_annulus_endpoint_exclusion p ‖q‖ hp hrL hr
  dsimp [ceiling] at henergy
  linarith

#print axioms balanced_variance_of_sharp
#print axioms outer_annulus_of_sharp_mean
end Blueprint.Thomson.Tail.Implementation
