import AllS.Units.N_GI.N_tail_rational.N_analytic_bounds
import AllS.Units.N_GI.N_upstream_bridge.N_energy

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def trialHeight (p : ℝ) : ℝ := packingHeight+tau*balancedD/(2*p)
def trialA : ℝ := balancedD^2/(2*(1-balancedD/((97:ℝ)/2)))
def trialB : ℝ := (contactKappa*balancedD)^2/2

theorem trial_ceiling_trial_in_range (p : ℝ) (hp : (97:ℝ)/2≤p) :
    trialHeight p∈Set.Ioo (0:ℝ) (1/3) := by
  obtain ⟨hal,hau,htl,htu,_,_,_,_⟩ := tail_geometric_constants
  obtain ⟨hdl,hdu,_,_,_,_⟩ := tail_d_constants
  have hp0 : 0<p := by linarith
  have htd : tau*balancedD<(1847:ℝ)/1250*(197556/10^6) :=
    mul_lt_mul htu hdu.le (by linarith) (by norm_num)
  have hquot : tau*balancedD/(2*p)<1/100 := by
    apply (div_lt_iff₀ (by positivity)).mpr
    linarith
  dsimp [trialHeight]
  constructor
  · positivity
  · linarith

theorem trial_AB_bounds : 0<trialA ∧ trialA<1/50 ∧ 0<trialB ∧ trialB<57/1000 := by
  obtain ⟨hdl,hdu,_,_,hkl,hku⟩ := tail_d_constants
  have hden : 0<2*(1-balancedD/((97:ℝ)/2)) := by linarith
  refine ⟨div_pos (sq_pos_of_pos balancedD_pos) hden,?_,?_,?_⟩
  · unfold trialA
    apply (div_lt_iff₀ hden).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hdu.le) (by linarith : 0≤balancedD)]
  · unfold trialB
    positivity
  · unfold trialB
    nlinarith

#print axioms trial_ceiling_trial_in_range
#print axioms trial_AB_bounds
end Blueprint.Thomson.Tail.Implementation
