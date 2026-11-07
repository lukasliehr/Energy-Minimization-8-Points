import AllS.Units.N_GI.N_contact_spectrum.N_contact_rows

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem contact_spectrum_stress_zero (q : TangentCoordinates) :
    (∑ e : ContactIndex, contactWeight e*contactLinear q e.1 (contactNext e))=0 := by
  simp_rw [contactLinear_cyclic_formula]
  norm_num [Fintype.sum_prod_type,Fin.sum_univ_succ,contactWeight,contactNext,
    contactSine,contactMeridianFactor,Fin.add_def,Fin.succ]
  ring

#print axioms contact_spectrum_stress_zero
end Blueprint.Thomson.Tail.Implementation
