import AllS.Units.N_GI.N_contact_spectrum.N_stress_zero

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

/-- The manuscript's stress forms, represented as the sum over the 16 contacts.
This is also the assembly of their 2-by-2 contact blocks. -/
def stressH (q v : TangentCoordinates) : ℝ :=
  ∑ e : ContactIndex, contactWeight e*(
    packingHeight*(inner ℝ (tangentVector q e.1) (tangentVector v e.1)+
      inner ℝ (tangentVector q (contactNext e)) (tangentVector v (contactNext e)))-
    inner ℝ (tangentVector q e.1) (tangentVector v (contactNext e))-
    inner ℝ (tangentVector q (contactNext e)) (tangentVector v e.1))

def stressB (q : TangentCoordinates) (b : Fin 8 → ℝ) : ℝ :=
  ∑ e : ContactIndex, contactWeight e*(-b (contactNext e)*
      inner ℝ (tangentVector q e.1) (packingReference (contactNext e))-
    b e.1*inner ℝ (tangentVector q (contactNext e)) (packingReference e.1))

def stressD (b c : Fin 8 → ℝ) : ℝ :=
  ∑ e : ContactIndex, contactWeight e*packingHeight*(b e.1-b (contactNext e))*(c e.1-c (contactNext e))

def chartNormalDisplacement (q : TangentCoordinates) (i : Fin 8) : ℝ := chartRoot q i-1

def contactWeightedDelta (q : TangentCoordinates) : ℝ :=
  ∑ e : ContactIndex, contactWeight e*contactDelta q e.1 (contactNext e)

def contactMeanDelta (q : TangentCoordinates) : ℝ := contactWeightedDelta q/contactTotalWeight

theorem stressH_quadratic (q : TangentCoordinates) :
    stressH q q=∑ e : ContactIndex, contactWeight e*contactQuadratic q e.1 (contactNext e) := by
  apply Finset.sum_congr rfl
  intro e _
  simp only [stressH,contactQuadratic,real_inner_self_eq_norm_sq]
  rw [real_inner_comm (tangentVector q (contactNext e)) (tangentVector q e.1)]
  ring

end Blueprint.Thomson.Tail.Implementation
