import AllS.Units.N_GI.N_signed_mean.N_stress_model

set_option maxHeartbeats 6000000
noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def contactCosine (k : Fin 2) : ℝ := if k=0 then 1/√2 else 0

def contactParity (k : Fin 2) : ℝ := if k=0 then -1 else 1

def contactFrameDot (q v : TangentCoordinates) (e : ContactIndex) : ℝ :=
  contactCosine e.2*q (e.1,0)*v (contactNext e,0)-
  packingZHeight*contactSine e.2*q (e.1,0)*v (contactNext e,1)+
  packingZHeight*contactSine e.2*q (e.1,1)*v (contactNext e,0)+
  (packingHeight*contactCosine e.2+(1-packingHeight)*contactParity e.2)*
    q (e.1,1)*v (contactNext e,1)

theorem tangentVector_self_inner (q v : TangentCoordinates) (i : Fin 8) :
    inner ℝ (tangentVector q i) (tangentVector v i)=q (i,0)*v (i,0)+q (i,1)*v (i,1) := by
  have hff : inner ℝ (azimuthFrame i) (azimuthFrame i)=1 := localFrame_inner i 1 1
  have hfg : inner ℝ (azimuthFrame i) (meridianFrame i)=0 := localFrame_inner i 1 2
  have hgf : inner ℝ (meridianFrame i) (azimuthFrame i)=0 := localFrame_inner i 2 1
  have hgg : inner ℝ (meridianFrame i) (meridianFrame i)=1 := localFrame_inner i 2 2
  simp only [tangentVector,inner_add_left,inner_add_right,real_inner_smul_left,
    real_inner_smul_right,hff,hfg,hgf,hgg]
  ring

theorem tangentVector_contact_inner (q v : TangentCoordinates) (e : ContactIndex) :
    inner ℝ (tangentVector q e.1) (tangentVector v (contactNext e))=contactFrameDot q v e := by
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hpos : 0<√(2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hinv : (√(2:ℝ))⁻¹=√2/2 := by field_simp; nlinarith
  have hH := packing_parameters.2.2.1
  have hR := packing_parameters.2.2.2
  rcases e with ⟨i,k⟩
  simp only [tangentVector,inner_add_left,inner_add_right,real_inner_smul_left,
    real_inner_smul_right,azimuthFrame,meridianFrame,PiLp.inner_apply]
  dsimp only [contactFrameDot]
  fin_cases i <;> fin_cases k <;>
    norm_num [contactNext,contactCosine,contactSine,contactParity,Fin.sum_univ_succ,
      angularCos,angularSin,layerSign,Fin.val_add,div_eq_mul_inv,hinv] <;>
    ring_nf <;> simp [hs,hH,hR] <;> ring_nf <;> simp [hs,hH,hR] <;> ring

theorem tangentVector_contact_reference (q : TangentCoordinates) (e : ContactIndex) :
    inner ℝ (tangentVector q e.1) (packingReference (contactNext e))=
      packingRadius*(contactSine e.2*q (e.1,0)+packingZHeight*contactMeridianFactor e.2*q (e.1,1)) ∧
    inner ℝ (tangentVector q (contactNext e)) (packingReference e.1)=
      packingRadius*(-contactSine e.2*q (contactNext e,0)+packingZHeight*contactMeridianFactor e.2*q (contactNext e,1)) := by
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hpos : 0<√(2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hinv : (√(2:ℝ))⁻¹=√2/2 := by field_simp; nlinarith
  rcases e with ⟨i,k⟩
  simp only [tangentVector,inner_add_left,real_inner_smul_left,
    packingReference_formula,azimuthFrame,meridianFrame,PiLp.inner_apply]
  fin_cases i <;> fin_cases k <;> constructor <;>
    norm_num [contactNext,contactSine,contactMeridianFactor,Fin.sum_univ_succ,
      angularCos,angularSin,layerSign,Fin.val_add,contactKappa_formula,div_eq_mul_inv,hinv] <;>
      ring_nf <;> simp [hs] <;> ring_nf <;> simp [hs] <;> ring

theorem stressH_coordinate_formula (q v : TangentCoordinates) :
    stressH q v=∑ e : ContactIndex,contactWeight e*(packingHeight*(
      q (e.1,0)*v (e.1,0)+q (e.1,1)*v (e.1,1)+
      (q (contactNext e,0)*v (contactNext e,0)+q (contactNext e,1)*v (contactNext e,1)))-
      contactFrameDot q v e-contactFrameDot v q e) := by
  unfold stressH
  apply Finset.sum_congr rfl
  intro e _
  have he : inner ℝ (tangentVector q (contactNext e)) (tangentVector v e.1)=contactFrameDot v q e := by
    rw [real_inner_comm]
    exact tangentVector_contact_inner v q e
  rw [tangentVector_self_inner,tangentVector_self_inner,tangentVector_contact_inner q v e,he]

theorem stressB_coordinate_formula (q : TangentCoordinates) (b : Fin 8 → ℝ) :
    stressB q b=∑ e : ContactIndex,contactWeight e*(-b (contactNext e)*
      (packingRadius*(contactSine e.2*q (e.1,0)+packingZHeight*contactMeridianFactor e.2*q (e.1,1)))-
      b e.1*(packingRadius*(-contactSine e.2*q (contactNext e,0)+packingZHeight*contactMeridianFactor e.2*q (contactNext e,1)))) := by
  unfold stressB
  apply Finset.sum_congr rfl
  intro e _
  rw [(tangentVector_contact_reference q e).1,(tangentVector_contact_reference q e).2]

#print axioms stressH_coordinate_formula
#print axioms stressB_coordinate_formula
end Blueprint.Thomson.Tail.Implementation
