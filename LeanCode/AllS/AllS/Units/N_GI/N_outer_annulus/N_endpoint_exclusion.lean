import AllS.Units.N_GI.N_outer_annulus.N_scalar_bounds
import Mathlib.Analysis.Convex.Jensen

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem outer_left_endpoint (p : ℝ) (hp : (97:ℝ)/2≤p) : (21:ℝ)/100<p*outerH (6/p) := by
  have hpP : 0<p := by linarith
  have hr3 : (6:ℝ)/p≤3/10 := (div_le_iff₀ hpP).mpr (by linarith)
  have hF := outerF_linear_lower (6/p) (by positivity) hr3
  obtain ⟨hA,hAu⟩ := outer_alpha_bounds
  have hAp : 0<outerAlpha := by linarith
  have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hF hAp.le) hpP.le
  have he : p*(outerAlpha*((159:ℝ)/100*(6/p))-(6/p)^2/5)=
      (954:ℝ)/100*outerAlpha-36/(5*p) := by
    field_simp [hpP.ne']
    <;> ring
  have hfrac : (36:ℝ)/(5*p)≤72/485 := (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  have hH : (954:ℝ)/100*outerAlpha-36/(5*p)≤p*outerH (6/p) := by
    rw [←he]
    dsimp [outerH]
    nlinarith
  linarith

theorem outer_right_endpoint (p : ℝ) (hp : (97:ℝ)/2≤p) : (21:ℝ)/100<p*outerH (3/10) := by
  have hpP : 0<p := by linarith
  have hF := outerF_linear_lower (3/10) (by norm_num) (le_refl _)
  obtain ⟨hA,hAu⟩ := outer_alpha_bounds
  have hAp : 0<outerAlpha := by linarith
  have hh := mul_le_mul_of_nonneg_left hF hAp.le
  have hH : (4419:ℝ)/10^6<outerH (3/10) := by dsimp [outerH];nlinarith
  have hh2 := mul_lt_mul_of_pos_left hH hpP
  nlinarith

theorem outerH_interval_lower (p r : ℝ) (hp : (97:ℝ)/2≤p) (hrL : 6/p≤r) (hrU : r≤3/10) :
    (21:ℝ)/100<p*outerH r := by
  have hpP : 0<p := by linarith
  have h0 : 0≤(6:ℝ)/p := by positivity
  have h3 : (6:ℝ)/p≤3/10 := hrL.trans hrU
  have hm := outerH_strictConcave.concaveOn.min_le_of_mem_Icc
    (show (6/p)∈Set.Icc (0:ℝ) (3/10) from ⟨h0,h3⟩)
    (show (3/10:ℝ)∈Set.Icc (0:ℝ) (3/10) from ⟨by norm_num,le_refl _⟩) ⟨hrL,hrU⟩
  have hl : (21:ℝ)/100/p<outerH (6/p) := (div_lt_iff₀ hpP).mpr (by nlinarith [outer_left_endpoint p hp])
  have hu : (21:ℝ)/100/p<outerH (3/10) := (div_lt_iff₀ hpP).mpr (by nlinarith [outer_right_endpoint p hp])
  have h := (div_lt_iff₀ hpP).mp ((lt_min hl hu).trans_le hm)
  nlinarith

def outerEnergyLower (p r : ℝ) : ℝ := balancedLambda*(contactTotalWeight-1)*
  exp (-outerAlpha*balancedZNorm+(p/tau)*outerH r)

theorem outer_annulus_endpoint_exclusion (p r : ℝ) (hp : (97:ℝ)/2≤p)
    (hrL : 6/p≤r) (hrU : r≤3/10) : (619:ℝ)/40<outerEnergyLower p r := by
  have hH := outerH_interval_lower p r hp hrL hrU
  obtain ⟨hA,hAu⟩ := outer_alpha_bounds
  have hZ := outer_Z_bound
  have hZp : 0≤balancedZNorm := by dsimp [balancedZNorm];positivity
  have hAZ : outerAlpha*balancedZNorm<(121:ℝ)/2000 := by
    calc
      _ ≤ (1/20:ℝ)*balancedZNorm := mul_le_mul_of_nonneg_right hAu.le hZp
      _ < (1/20:ℝ)*(121/100) := mul_lt_mul_of_pos_left hZ (by norm_num)
      _ = _ := by norm_num
  have ht : tau<(148:ℝ)/100 := by have h := tail_geometric_constants.2.2.2.1;linarith
  have hquot : (281:ℝ)/2000<(p/tau)*outerH r := by
    rw [show (p/tau)*outerH r=(p*outerH r)/tau by ring]
    apply (lt_div_iff₀ tau_pos).mpr
    nlinarith
  have he : (2:ℝ)/25< -outerAlpha*balancedZNorm+(p/tau)*outerH r := by linarith
  have hexp : (27:ℝ)/25<exp (-outerAlpha*balancedZNorm+(p/tau)*outerH r) := by
    linarith [Real.add_one_le_exp (-outerAlpha*balancedZNorm+(p/tau)*outerH r)]
  have hpre := outer_prefactor_bound
  have hm := mul_pos (sub_pos.mpr hpre) (sub_pos.mpr hexp)
  dsimp [outerEnergyLower]
  nlinarith

#print axioms outer_annulus_endpoint_exclusion
end Blueprint.Thomson.Tail.Implementation
