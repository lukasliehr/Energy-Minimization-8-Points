import AllS.Units.N_GI.N_continuous_annulus.N_scalar_constants
import Mathlib.Analysis.Convex.Deriv

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def outerRadicand (r : ℝ) : ℝ := 17/5-(15/4)*r^2
def outerF (r : ℝ) : ℝ := r*√(outerRadicand r)-varianceSigmaH*r^2
def outerAlpha : ℝ := twoValueB contactTotalWeight 1
def outerH (r : ℝ) : ℝ := outerAlpha*outerF r-r^2/5
def outerFDeriv (r : ℝ) : ℝ := √(outerRadicand r)-(15/4)*r^2/√(outerRadicand r)-2*varianceSigmaH*r
def outerFSecond (r : ℝ) : ℝ := -(45/4)*r/√(outerRadicand r)-(225/16)*r^3/(√(outerRadicand r))^3-2*varianceSigmaH

theorem outer_radical_positive (r : ℝ) (hr0 : 0≤r) (hr3 : r≤3/10) : 0<outerRadicand r := by
  dsimp [outerRadicand]
  nlinarith

theorem outer_root_hasDerivAt (r : ℝ) (hr : 0<outerRadicand r) :
    HasDerivAt (fun t=>√(outerRadicand t)) (-(15/4)*r/√(outerRadicand r)) r := by
  have h := ((hasDerivAt_const r (17/5:ℝ)).sub (((hasDerivAt_id r).pow 2).const_mul (15/4))).sqrt hr.ne'
  convert! h using 1 <;> dsimp [outerRadicand,id] <;> ring

theorem outerF_hasDerivAt (r : ℝ) (hr : 0<outerRadicand r) :
    HasDerivAt outerF (outerFDeriv r) r := by
  have h := ((hasDerivAt_id r).mul (outer_root_hasDerivAt r hr)).sub
    (((hasDerivAt_id r).pow 2).const_mul varianceSigmaH)
  convert! h using 1 <;> dsimp [outerF,outerFDeriv,id] <;> ring

theorem outerFDeriv_hasDerivAt (r : ℝ) (hr : 0<outerRadicand r) :
    HasDerivAt outerFDeriv (outerFSecond r) r := by
  have hroot := outer_root_hasDerivAt r hr
  have hrootP : 0<√(outerRadicand r) := Real.sqrt_pos.mpr hr
  have h := (hroot.sub ((((hasDerivAt_id r).pow 2).const_mul (15/4)).div hroot hrootP.ne')).sub
    ((hasDerivAt_id r).const_mul (2*varianceSigmaH))
  convert! h using 1
  dsimp [outerFSecond,id]
  field_simp [hrootP.ne']
  <;> ring

theorem outerH_hasDerivAt (r : ℝ) (hr : 0<outerRadicand r) :
    HasDerivAt outerH (outerAlpha*outerFDeriv r-2*r/5) r := by
  convert! ((outerF_hasDerivAt r hr).const_mul outerAlpha).sub
    (((hasDerivAt_id r).pow 2).div_const 5) using 1
  dsimp only [id]
  ring

theorem outerH_second_derivative (r : ℝ) (hr : 0<outerRadicand r) :
    HasDerivAt (deriv outerH) (outerAlpha*outerFSecond r-2/5) r := by
  have hd : HasDerivAt (fun t=>outerAlpha*outerFDeriv t-2*t/5) (outerAlpha*outerFSecond r-2/5) r := by
    convert! ((outerFDeriv_hasDerivAt r hr).const_mul outerAlpha).sub
      (((hasDerivAt_id r).const_mul 2).div_const 5) using 1 <;> ring
  apply hd.congr_of_eventuallyEq
  have hc : ContinuousAt outerRadicand r := by unfold outerRadicand;fun_prop
  filter_upwards [hc.eventually (isOpen_Ioi.mem_nhds hr)] with t ht
  exact (outerH_hasDerivAt t ht).deriv

theorem outerH_second_neg (r : ℝ) (hr0 : 0≤r) (hr3 : r≤3/10) : outerAlpha*outerFSecond r-2/5<0 := by
  have hroot : 0<√(outerRadicand r) := Real.sqrt_pos.mpr (outer_radical_positive r hr0 hr3)
  have hA : 0<outerAlpha := (twoValue_coefficients contactTotalWeight 1 (by norm_num) annulus_weight_beta_bounds.1).2.1
  have hsig : 0≤varianceSigmaH := by dsimp [varianceSigmaH];positivity
  have hf : outerFSecond r≤0 := by
    have h1 : 0≤(45/4:ℝ)*r/√(outerRadicand r) := by positivity
    have h2 : 0≤(225/16:ℝ)*r^3/(√(outerRadicand r))^3 := by positivity
    dsimp [outerFSecond]
    simp only [neg_mul,neg_div]
    linarith
  have hh := mul_nonpos_of_nonneg_of_nonpos hA.le hf
  linarith

theorem outerH_strictConcave : StrictConcaveOn ℝ (Set.Icc 0 (3/10)) outerH := by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc 0 (3/10))
  · intro r hr
    exact (outerH_hasDerivAt r (outer_radical_positive r hr.1 hr.2)).continuousAt.continuousWithinAt
  · intro r hr
    have hr' : r∈Set.Icc (0:ℝ) (3/10) := interior_subset hr
    have hd := outerH_second_derivative r (outer_radical_positive r hr'.1 hr'.2)
    change deriv (deriv outerH) r<0
    rw [hd.deriv]
    exact outerH_second_neg r hr'.1 hr'.2

theorem outer_annulus_concave_scalar (p : ℝ) (hp : (97:ℝ)/2≤p) :
    StrictConcaveOn ℝ (Set.Icc (6/p) (3/10)) outerH := by
  have hpP : 0<p := by linarith
  apply outerH_strictConcave.subset
  · intro r hr
    exact ⟨le_trans (div_nonneg (by norm_num) hpP.le) hr.1,hr.2⟩
  · exact convex_Icc _ _

#print axioms outer_annulus_concave_scalar
end Blueprint.Thomson.Tail.Implementation
