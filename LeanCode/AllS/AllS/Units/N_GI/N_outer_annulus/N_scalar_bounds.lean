import AllS.Units.N_GI.N_outer_annulus.N_concave_scalar

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem outer_alpha_bounds : (47:ℝ)/1000<outerAlpha ∧ outerAlpha<1/20 := by
  obtain ⟨_,_,_,_,_,_,hWL,hWU⟩ := tail_geometric_constants
  have hW : 1<contactTotalWeight := by linarith
  have hA : 0<outerAlpha := (twoValue_coefficients contactTotalWeight 1 (by norm_num) hW).2.1
  have hs : outerAlpha^2=1/(contactTotalWeight*(contactTotalWeight-1)) := by
    exact Real.sq_sqrt (by positivity)
  have hp : 0<contactTotalWeight*(contactTotalWeight-1) := by positivity
  have hid : outerAlpha^2*(contactTotalWeight*(contactTotalWeight-1))=1 := (eq_div_iff hp.ne').mp hs
  have hprodL : (440:ℝ)<contactTotalWeight*(contactTotalWeight-1) := by nlinarith
  have hprodU : contactTotalWeight*(contactTotalWeight-1)<(450:ℝ) := by nlinarith
  have hl := mul_lt_mul_of_pos_left hprodU (sq_pos_of_pos hA)
  have hu := mul_lt_mul_of_pos_left hprodL (sq_pos_of_pos hA)
  rw [hid] at hl hu
  constructor <;> nlinarith

theorem outer_Z_bound : balancedZNorm<(121:ℝ)/100 := by
  obtain ⟨_,_,_,_,hkL,hkU,_,_⟩ := tail_geometric_constants
  obtain ⟨hdL,hdU,_,_,_,_⟩ := tail_d_constants
  have hkP : 0<contactKappa := by linarith
  have hdP := balancedD_pos
  have hs : balancedZNorm^2=8*contactKappa*(contactKappa+1)*balancedD^2 := Real.sq_sqrt (by positivity)
  have hb : 8*contactKappa*(contactKappa+1)*balancedD^2 <
      (8:ℝ)*(1708/1000)*(2708/1000)*(198/1000)^2 := by
    gcongr <;> linarith
  have hz : 0≤balancedZNorm := by dsimp [balancedZNorm];positivity
  norm_num at hb
  nlinarith

theorem outer_prefactor_bound : (147:ℝ)/10<balancedLambda*(contactTotalWeight-1) := by
  obtain ⟨_,hl,_,_⟩ := tail_lambda_constants
  obtain ⟨_,_,_,_,_,_,hw,_⟩ := tail_geometric_constants
  have hh := mul_pos (sub_pos.mpr hl) (sub_pos.mpr hw)
  nlinarith

theorem outerF_linear_lower (r : ℝ) (hr0 : 0≤r) (hr3 : r≤3/10) : (159:ℝ)/100*r≤outerF r := by
  have hrad := outer_radical_positive r hr0 hr3
  -- Keep the same square-root expression in the identity and comparison.
  have hs : (√(outerRadicand r))^2=(17:ℝ)/5-(15/4)*r^2 := Real.sq_sqrt hrad.le
  have hroot : (7:ℝ)/4≤√(outerRadicand r) := by
    nlinarith [Real.sqrt_nonneg (outerRadicand r)]
  have hsigma : varianceSigmaH<64/125 := by
    have hh := annulus_sigma_bound
    dsimp [varianceSigma] at hh
    linarith
  have h1 := mul_nonneg (sub_nonneg.mpr hroot) hr0
  have h2 := mul_nonneg (sub_nonneg.mpr hsigma.le) (sq_nonneg r)
  have h3 := mul_nonneg hr0 (sub_nonneg.mpr hr3)
  dsimp [outerF]
  nlinarith

theorem outer_variance_scalar (p r : ℝ) (hp : (97:ℝ)/2≤p) (hrL : 6/p≤r) (hrU : r≤3/10) :
    √contactTotalWeight<(p/tau)*outerF r-balancedZNorm := by
  have hpP : 0<p := by linarith
  have hr0 : 0≤r := (div_nonneg (by norm_num) hpP.le).trans hrL
  have hF := outerF_linear_lower r hr0 hrU
  have hpr : 6≤p*r := by have h := (div_le_iff₀ hpP).mp hrL; nlinarith
  have hh := mul_le_mul_of_nonneg_left hF hpP.le
  have hZ := outer_Z_bound
  obtain ⟨_,_,htL,htU,_,_,_,hW⟩ := tail_geometric_constants
  have hroot : √contactTotalWeight<5 := by
    have hs := Real.sq_sqrt contactTotalWeight_pos.le
    nlinarith [Real.sqrt_nonneg contactTotalWeight]
  have hFprod : (159:ℝ)/100*6≤p*outerF r := by nlinarith
  have ht : tau<(148:ℝ)/100 := by linarith
  have hquot : (621:ℝ)/100<(p/tau)*outerF r := by
    have he : (p/tau)*outerF r=(p*outerF r)/tau := by ring
    rw [he]
    apply (lt_div_iff₀ tau_pos).mpr
    nlinarith
  linarith

#print axioms outer_alpha_bounds
#print axioms outer_variance_scalar
end Blueprint.Thomson.Tail.Implementation
