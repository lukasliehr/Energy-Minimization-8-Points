import AllS.Units.N_GI.N_boundary_basis.N_definitions
import AllS.Units.N_GI.N_constants.N_algebra

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def boundaryZ : ℝ := 1+√2/4
def boundaryM : ℝ := 2+9*√2/4
def boundaryT : ℝ := 1+√2/2

theorem boundary_field_identities :
    boundaryZ*packingRadius^2=1 ∧
    boundaryM*(packingZHeight^2*packingRadius^2)=1 ∧
    boundaryT*packingRadius^2=1+packingZHeight^2 ∧
    (1+2*√2)*packingZHeight^2=1 := by
  obtain ⟨_,_,hH,hR⟩ := packing_parameters
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  rw [hH,hR]
  dsimp [boundaryZ,boundaryM,boundaryT,packingHeight]
  constructor
  · nlinarith [hs]
  constructor
  · ring_nf
    have h3 : (√(2:ℝ))^3=2*√2 := by
      calc
        _ = (√(2:ℝ))^2*√2 := by ring
        _ = _ := by rw [hs]
    rw [h3,hs]
    ring
  constructor <;> nlinarith [hs]

theorem boundary_field_inverses :
    packingHeight⁻¹=1+2*√2 ∧ (1-packingHeight)⁻¹=boundaryZ ∧
    (packingHeight*(1-packingHeight))⁻¹=boundaryM ∧
    (1+packingHeight)/(1-packingHeight)=boundaryT := by
  obtain ⟨hz,hm,ht,hh⟩ := boundary_field_identities
  obtain ⟨_,_,hH,hR⟩ := packing_parameters
  simp only [hH,hR] at hz hm ht hh
  have ha := packingHeight_mem_Ioo
  have hn : packingHeight≠0 := ne_of_gt ha.1
  have hr : 1-packingHeight≠0 := by linarith [ha.2]
  constructor
  · field_simp
    nlinarith [hh]
  constructor
  · field_simp
    nlinarith [hz]
  constructor
  · field_simp
    nlinarith [hm]
  · apply (div_eq_iff hr).mpr
    nlinarith [ht]

#print axioms boundary_field_identities
end Blueprint.Thomson.Tail.Implementation
