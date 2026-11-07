import AllS.Units.N_GI.N_signed_mean.N_edge_forms
import AllS.Units.N_GI.N_slice_point_bound.N_projection_algebra

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

def contactMComponents (e : ContactIndex) (q : TangentCoordinates) : Fin 4 → ℝ :=
  let c := contactCosine e.2
  let s := contactSine e.2
  let d := packingHeight*c+(1-packingHeight)*contactParity e.2
  ![packingHeight*q (e.1,0)-c*q (contactNext e,0)+packingZHeight*s*q (contactNext e,1),
    packingHeight*q (e.1,1)-packingZHeight*s*q (contactNext e,0)-d*q (contactNext e,1),
    packingHeight*q (contactNext e,0)-c*q (e.1,0)-packingZHeight*s*q (e.1,1),
    packingHeight*q (contactNext e,1)+packingZHeight*s*q (e.1,0)-d*q (e.1,1)]

def contactM (e : ContactIndex) (q : TangentCoordinates) : TangentCoordinates :=
  localEvaluation e.1 (contactMComponents e q 0) (contactMComponents e q 1)+
    localEvaluation (contactNext e) (contactMComponents e q 2) (contactMComponents e q 3)

def contactMBilinear (e : ContactIndex) (q v : TangentCoordinates) : ℝ :=
  packingHeight*(q (e.1,0)*v (e.1,0)+q (e.1,1)*v (e.1,1)+
      (q (contactNext e,0)*v (contactNext e,0)+q (contactNext e,1)*v (contactNext e,1)))-
    contactFrameDot q v e-contactFrameDot v q e

theorem contactM_inner (e : ContactIndex) (q v : TangentCoordinates) :
    inner ℝ q (contactM e v)=contactMBilinear e q v := by
  simp only [contactM,inner_add_right,localEvaluation_inner]
  norm_num [contactMComponents,contactMBilinear,contactFrameDot,Fin.instOfNat,Fin.ofNat,Fin.succ]
  dsimp
  ring

theorem contactM_symmetric (e : ContactIndex) (q v : TangentCoordinates) :
    inner ℝ q (contactM e v)=inner ℝ v (contactM e q) := by
  rw [contactM_inner,contactM_inner]
  unfold contactMBilinear
  ring

theorem contactM_quadratic (e : ContactIndex) (q : TangentCoordinates) :
    inner ℝ q (contactM e q)=contactQuadratic q e.1 (contactNext e) := by
  rw [contactM_inner]
  unfold contactMBilinear contactQuadratic
  rw [tangentVector_norm_sq,tangentVector_norm_sq,tangentVector_contact_inner]
  ring

theorem localEvaluation_pair_inner (i j : Fin 8) (u v s t : ℝ) :
    inner ℝ (localEvaluation i u v) (localEvaluation j s t)=if i=j then u*s+v*t else 0 := by
  rw [localEvaluation_inner]
  by_cases h : i=j
  · subst j
    simp [localEvaluation]
  · simp [localEvaluation,h,Ne.symm h]

theorem contactM_pair_inner (e : ContactIndex) (q v : TangentCoordinates) :
    inner ℝ (contactM e q) (contactM e v)=∑k : Fin 4,contactMComponents e q k*contactMComponents e v k := by
  have hn : contactNext e≠e.1 := by
    rcases e with ⟨i,b⟩
    fin_cases i <;> fin_cases b <;> decide
  simp only [contactM,inner_add_left,inner_add_right,localEvaluation_pair_inner]
  norm_num [hn,hn.symm,Fin.sum_univ_succ,Fin.succ,Fin.instOfNat,Fin.ofNat]
  simp only [add_assoc]
  rfl

theorem contactM_add (e : ContactIndex) (q v : TangentCoordinates) : contactM e (q+v)=contactM e q+contactM e v := by
  ext i
  simp [contactM,contactMComponents,localEvaluation,PiLp.add_apply]
  split_ifs <;> ring

theorem contactM_smul (e : ContactIndex) (c : ℝ) (q : TangentCoordinates) : contactM e (c • q)=c • contactM e q := by
  ext i
  simp [contactM,contactMComponents,localEvaluation,PiLp.smul_apply,smul_eq_mul]
  split_ifs <;> ring

def contactMLinear (e : ContactIndex) : TangentCoordinates →ₗ[ℝ] TangentCoordinates where
  toFun := contactM e
  map_add' := contactM_add e
  map_smul' := contactM_smul e

def stressMap (q : TangentCoordinates) : TangentCoordinates := ∑e : ContactIndex,contactWeight e • contactM e q

theorem stressMap_inner (q v : TangentCoordinates) : inner ℝ q (stressMap v)=stressH q v := by
  simp only [stressMap,inner_sum,real_inner_smul_right,contactM_inner]
  exact (stressH_coordinate_formula q v).symm

#print axioms contactM_quadratic
#print axioms contactM_pair_inner
#print axioms stressMap_inner
end Blueprint.Thomson.Tail.Implementation
