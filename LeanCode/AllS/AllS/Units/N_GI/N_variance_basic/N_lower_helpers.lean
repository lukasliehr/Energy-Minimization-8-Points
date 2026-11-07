import AllS.Units.N_GI.N_variance_basic.N_remainder_norm
import AllS.Units.N_G.N_contact_spectrum
import AllS.Units.N_GI.N_balanced_energy.N_reference_direction
import AllS.Units.N_GI.N_derivative_stability.N_row_error

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def varianceMu : ℝ := 59546/15625

theorem contactLinearArray_mean (q : TangentCoordinates) : contactMean (contactLinearArray q)=0 := by
  unfold contactMean contactLinearArray
  rw [contact_spectrum_stress_zero,zero_div]

theorem contactLinearArray_norm_lower (q : TangentCoordinates) (hq : q∈rotationSlice) :
    √varianceMu*‖q‖≤contactNorm (contactLinearArray q) := by
  have h := contact_spectrum_physical_weighted q hq
  have he := contactNorm_sq (contactLinearArray q)
  have hm := Real.sq_sqrt (show 0≤varianceMu by norm_num [varianceMu])
  change varianceMu*‖q‖^2≤_ at h
  change (contactNorm (contactLinearArray q))^2=∑ e, contactWeight e*(contactLinear q e.1 (contactNext e))^2 at he
  have hp : 0≤√varianceMu*‖q‖ := by positivity
  nlinarith [contactNorm_nonneg (contactLinearArray q)]

theorem contactNorm_reverse_three (x y z : ContactIndex→ℝ) :
    contactNorm x≤contactNorm (fun e=>x e+y e+z e)+contactNorm y+contactNorm z := by
  have he : x=(fun e=>(x e+y e+z e)+(-y e)+(-z e)) := by funext e;ring
  calc
    _ = contactNorm (fun e=>(x e+y e+z e)+(-y e)+(-z e)) := congrArg contactNorm he
    _ ≤ contactNorm (fun e=>(x e+y e+z e)+(-y e))+contactNorm (fun e=>-z e) := contactNorm_add_le _ _
    _ ≤ (contactNorm (fun e=>x e+y e+z e)+contactNorm (fun e=>-y e))+contactNorm (fun e=>-z e) :=
      add_le_add (contactNorm_add_le _ _) (le_refl _)
    _ = _ := by rw [contactNorm_neg,contactNorm_neg]

theorem centered_delta_expansion (q : TangentCoordinates) (hq : ‖q‖≤3/10) :
    contactCenter (contactDeltaArray q)=fun e=>contactLinearArray q e+
      contactCenter (contactQuadraticArray q) e+contactCenter (contactRemainderArray q) e := by
  rw [contactArray_expansion q hq,contactCenter_add,contactCenter_add,
    contactCenter_of_mean_zero _ (contactLinearArray_mean q)]

theorem variance_lower_of_quadratic (q : TangentCoordinates) (hq : q∈rotationSlice) (hr : ‖q‖≤3/10)
    (hM : contactNorm (contactCenter (contactQuadraticArray q))≤2*‖q‖^2) :
    √varianceMu*‖q‖-varianceSigma*‖q‖^2≤contactNorm (contactCenter (contactDeltaArray q)) := by
  have hL := contactLinearArray_norm_lower q hq
  have hR := variance_basic_remainder_norm q hr
  have h := contactNorm_reverse_three (contactLinearArray q)
    (contactCenter (contactQuadraticArray q)) (contactCenter (contactRemainderArray q))
  rw [←centered_delta_expansion q hr] at h
  dsimp [varianceSigma]
  linarith

#print axioms variance_lower_of_quadratic
end Blueprint.Thomson.Tail.Implementation
