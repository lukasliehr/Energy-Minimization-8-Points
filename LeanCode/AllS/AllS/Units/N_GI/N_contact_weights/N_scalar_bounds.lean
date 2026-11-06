import AllS.Units.N_GI.N_convex_domain.N_convexity
import AllS.Units.N_GI.N_trial_ceiling.N_contact_trial

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem tail_epsilon_bounds (p : ℝ) (hp : (97:ℝ)/2≤p) :
    0<tailEpsilon p ∧ tailEpsilon p<621/50000 := by
  have hp0 : 0<p := by linarith
  have hden : 0<tau*p := mul_pos tau_pos hp0
  obtain ⟨_,_,htl,_,_,_,_,_⟩ := tail_geometric_constants
  have hprod : ((147759:ℝ)/10^5)*(97/2)≤tau*p :=
    mul_le_mul htl.le hp (by norm_num) tau_pos.le
  constructor
  · dsimp [tailEpsilon,contraction]
    positivity
  · dsimp [tailEpsilon,contraction]
    apply (div_lt_iff₀ hden).mpr
    linarith

theorem tail_Cstar_upper (p : ℝ) (hp : (97:ℝ)/2≤p) :
    0<tailCstar p ∧ tailCstar p<(3917:ℝ)/250 := by
  obtain ⟨heP,heU⟩ := tail_epsilon_bounds p hp
  have he := Real.exp_bound_div_one_sub_of_interval heP.le (show tailEpsilon p<1 by linarith)
  have hquot : 1/(1-tailEpsilon p)≤1/(1-(621:ℝ)/50000) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  dsimp [tailCstar,ceiling]
  exact ⟨by positivity,by nlinarith [he.trans hquot]⟩

#print axioms tail_Cstar_upper
end Blueprint.Thomson.Tail.Implementation
