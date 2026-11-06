import AllS.Units.N_GI.N_continuous_annulus.N_scalar_constants
import AllS.Units.N_GI.N_continuous_annulus.N_cubic_exponential

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def annulusEnergyLower (p x : ℝ) : ℝ := balancedLambda*
  twoValueExp contactTotalWeight (annulusActualV p x) 1*exp (-x^2/(5*tau*p))

theorem annulus_endpoint_exponential (p : ℝ) (hp : (97:ℝ)/2≤p) :
    1-annulusE*annulusK^2/2<exp (-annulusK^2/(5*tau*p)) := by
  have h := annulus_mean_derivative_coefficient p hp
  have hk : 0<annulusK^2 := by norm_num [annulusK]
  have hh := mul_lt_mul_of_pos_right h hk
  have he := Real.add_one_le_exp (-annulusK^2/(5*tau*p))
  dsimp [annulusK] at hh he ⊢
  simp only [div_eq_mul_inv] at hh he ⊢
  nlinarith

theorem annulus_endpoint_F (p : ℝ) (hp : (97:ℝ)/2≤p) :
    (15457:ℝ)/1000*(1+(63/1024)/annulusW)<
      balancedLambda*twoValueExp contactTotalWeight (annulusActualV p annulusK) 1 := by
  obtain ⟨hW,hWup,_,_⟩ := annulus_weight_beta_bounds
  have hv : (3:ℝ)/8<annulusActualV p annulusK :=
    annulus_endpoint_bounds.2.2.trans (annulus_actual_surrogate p annulusK hp (by norm_num [annulusK])).1
  have hF := (twoValueExp_strictMono_variance contactTotalWeight 1 (by norm_num) hW)
    (by norm_num : (0:ℝ)<3/8) (show 0<annulusActualV p annulusK by linarith) hv
  have hT := massOne_cubic_lower contactTotalWeight (3/8) hW (by norm_num)
  norm_num at hT
  have hLam : 0<balancedLambda := by dsimp [balancedLambda]; positivity
  have hFL : balancedLambda*(contactTotalWeight+63/1024)<
      balancedLambda*twoValueExp contactTotalWeight (annulusActualV p annulusK) 1 := by
    apply mul_lt_mul_of_pos_left _ hLam
    linarith
  have hC := tail_Cmin_constants.1
  have hLamLower : (15457:ℝ)/1000/annulusW<balancedLambda := by
    apply (div_lt_iff₀ (by norm_num [annulusW])).mpr
    have h := mul_lt_mul_of_pos_left hWup hLam
    linarith
  have hh := mul_lt_mul_of_pos_right hLamLower (by norm_num : (0:ℝ)<63/1024)
  dsimp [annulusW] at hh ⊢
  nlinarith

theorem continuous_annulus_inner_endpoint_exclusion (p : ℝ) (hp : (97:ℝ)/2≤p) :
    (619:ℝ)/40<annulusEnergyLower p annulusK := by
  have hF := annulus_endpoint_F p hp
  have hE := annulus_endpoint_exponential p hp
  have hFp : 0<(15457:ℝ)/1000*(1+(63/1024)/annulusW) := by norm_num [annulusW]
  have hEp : 0<1-annulusE*annulusK^2/2 := by norm_num [annulusE,annulusK]
  have hh := mul_lt_mul hF hE.le hEp (hFp.trans hF).le
  have hr : (619:ℝ)/40<((15457:ℝ)/1000*(1+(63/1024)/annulusW))*(1-annulusE*annulusK^2/2) := by
    norm_num [annulusW,annulusE,annulusK]
  exact hr.trans hh

#print axioms continuous_annulus_inner_endpoint_exclusion
end Blueprint.Thomson.Tail.Implementation
