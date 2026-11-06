import AllS.Units.N_GI.N_signed_mean.N_stress_model
import AllS.Units.N_GI.N_constants.N_pair_table

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem stress_remainder_identity (q : TangentCoordinates) :
    (∑ e : ContactIndex, contactWeight e*contactRemainder q e.1 (contactNext e))=
      2*stressB q (chartNormalDisplacement q)+stressD (chartNormalDisplacement q) (chartNormalDisplacement q) := by
  unfold stressB stressD
  rw [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  dsimp [contactRemainder,chartNormalDisplacement]
  rw [real_inner_comm (tangentVector q e.1) (packingReference (contactNext e)),
    real_inner_comm (tangentVector q (contactNext e)) (packingReference e.1)]
  ring

theorem signed_mean_stress_identity (q : TangentCoordinates) (hq : ‖q‖ ≤ 3/10) :
    contactWeightedDelta q=stressH q q+2*stressB q (chartNormalDisplacement q)+
      stressD (chartNormalDisplacement q) (chartNormalDisplacement q) := by
  have he (e : ContactIndex) := contact_taylor_exact_expansion q hq e.1 (contactNext e)
    ((constants_pair_table.2.2.2.1 e).1)
  unfold contactWeightedDelta
  simp_rw [he,mul_add]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,contact_spectrum_stress_zero,
    zero_add,← stressH_quadratic,stress_remainder_identity]
  ring

#print axioms signed_mean_stress_identity
end Blueprint.Thomson.Tail.Implementation
