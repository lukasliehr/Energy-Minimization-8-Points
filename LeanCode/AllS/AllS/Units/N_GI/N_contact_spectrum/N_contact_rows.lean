import AllS.Units.N_GI.N_constants.N_weights
import AllS.Units.N_GI.N_contact_taylor.N_exact_expansion

set_option maxHeartbeats 4000000
noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def contactSine (k : Fin 2) : ℝ := if k=0 then 1/√2 else 1
def contactMeridianFactor (k : Fin 2) : ℝ := if k=0 then -contactKappa else 1

theorem contactLinear_cyclic_formula (q : TangentCoordinates) (e : ContactIndex) :
    contactLinear q e.1 (contactNext e)=
      -2*packingRadius*(contactSine e.2*(q (e.1,0)-q (contactNext e,0))+
        packingZHeight*contactMeridianFactor e.2*(q (e.1,1)+q (contactNext e,1))) := by
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hpos : 0<√(2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hinv : (√(2:ℝ))⁻¹=√2/2 := by field_simp; nlinarith
  rcases e with ⟨i,k⟩
  simp only [contactLinear,tangentVector,inner_add_right,real_inner_smul_right,
    packingReference_formula,azimuthFrame,meridianFrame,PiLp.inner_apply]
  fin_cases i <;> fin_cases k <;>
    norm_num [contactNext,contactSine,contactMeridianFactor,Fin.sum_univ_succ,
      angularCos,angularSin,layerSign,Fin.val_add,contactKappa_formula,div_eq_mul_inv,hinv] <;>
      ring_nf <;> simp [hs] <;> ring_nf <;> simp [hs] <;> ring

theorem contactLinear_add (q v : TangentCoordinates) (i j : Fin 8) :
    contactLinear (q+v) i j=contactLinear q i j+contactLinear v i j := by
  simp only [contactLinear,tangentVector_add,inner_add_right]
  ring

theorem contactLinear_smul_spectrum (c : ℝ) (q : TangentCoordinates) (i j : Fin 8) :
    contactLinear (c • q) i j=c*contactLinear q i j := by
  simp only [contactLinear,tangentVector_smul,real_inner_smul_right]
  ring

def contactLinearMap (e : ContactIndex) : TangentCoordinates →ₗ[ℝ] ℝ where
  toFun q := contactLinear q e.1 (contactNext e)
  map_add' q v := contactLinear_add q v _ _
  map_smul' c q := contactLinear_smul_spectrum c q _ _

#print axioms contactLinear_cyclic_formula
end Blueprint.Thomson.Tail.Implementation
