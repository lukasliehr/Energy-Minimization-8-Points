import AllS.Units.N_GI.N_variance_basic.N_lower_helpers
import AllS.Units.N_GI.N_balanced_energy.N_energy_inequality

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem centered_balanced_expansion (p : ℝ) (q : TangentCoordinates) (hq : ‖q‖≤3/10) :
    contactCenter (balancedX p q)=fun e=>contactLinearArray ((p/tau) • q-balancedReference) e+
      (p/tau)*contactCenter (contactQuadraticArray q) e+(p/tau)*contactCenter (contactRemainderArray q) e := by
  have hX : balancedX p q=(fun e=>(p/tau)*contactDeltaArray q e+(-1)*balancedZ e) := by
    funext e
    simp [balancedX,contactDeltaArray,sub_eq_add_neg]
  have hz : contactCenter balancedZ=balancedZ := by
    apply contactCenter_of_mean_zero
    simp only [contactMean,balancedZ_mean,zero_div]
  have hl (e : ContactIndex) : contactLinearArray ((p/tau) • q-balancedReference) e=
      (p/tau)*contactLinearArray q e-balancedZ e := by
    change referencePairDerivative e.1 (contactNext e) ((p/tau) • q-balancedReference)=_
    rw [map_sub,map_smul,referencePairDerivative_apply,referencePairDerivative_apply,balancedReference_contact]
    rfl
  rw [hX,contactCenter_add,contactCenter_smul,contactCenter_smul,hz,centered_delta_expansion q hq]
  funext e
  rw [hl]
  ring

theorem shifted_variance_of_quadratic (p : ℝ) (hp : 0≤p) (q : TangentCoordinates)
    (hq : q∈rotationSlice) (hr : ‖q‖≤3/10)
    (hM : contactNorm (contactCenter (contactQuadraticArray q))≤2*‖q‖^2) :
    √varianceMu*((p*‖q‖)/tau-balancedRefNorm)-varianceSigma*p*‖q‖^2/tau≤
      contactNorm (contactCenter (balancedX p q)) := by
  have hc : 0≤p/tau := div_nonneg hp tau_pos.le
  have hslice : (p/tau) • q-balancedReference∈rotationSlice :=
    rotationSlice.sub_mem (rotationSlice.smul_mem _ hq) balancedReference_mem_slice
  have hlinear := contactLinearArray_norm_lower _ hslice
  have hnorm := norm_sub_norm_le ((p/tau) • q) balancedReference
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hc,balancedReference_norm] at hnorm
  have hL := mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg varianceMu)
  have hR := variance_basic_remainder_norm q hr
  have h := contactNorm_reverse_three (contactLinearArray ((p/tau) • q-balancedReference))
    (fun e=>(p/tau)*contactCenter (contactQuadraticArray q) e)
    (fun e=>(p/tau)*contactCenter (contactRemainderArray q) e)
  rw [←centered_balanced_expansion p q hr,contactNorm_smul,contactNorm_smul,abs_of_nonneg hc] at h
  have hME := mul_le_mul_of_nonneg_left hM hc
  have hRE := mul_le_mul_of_nonneg_left hR hc
  dsimp [varianceSigma]
  simp only [div_eq_mul_inv] at hL hlinear h hME hRE ⊢
  nlinarith

#print axioms shifted_variance_of_quadratic
end Blueprint.Thomson.Tail.Implementation
