import AllS.Units.N_GI.N_variance_sharp.N_coordinate_kernels

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

def varianceAngularCosData : Fin 8 → MeanRadical :=
  ![![1,0,0,0],![0,1/2,0,0],0,![0,-1/2,0,0],![-1,0,0,0],![0,-1/2,0,0],0,![0,1/2,0,0]]
def varianceAngularSinData : Fin 8 → MeanRadical :=
  ![0,![0,1/2,0,0],![1,0,0,0],![0,1/2,0,0],0,![0,-1/2,0,0],![-1,0,0,0],![0,-1/2,0,0]]
def varianceLayerData : Fin 8 → ℚ := ![1,-1,1,-1,1,-1,1,-1]
def varianceRotationRawData (j : Fin 3) (p : Fin 8) (b : Fin 2) : MeanRadical :=
  if j=0 then
    if b=0 then -(varianceLayerData p • meanRadicalMul varianceZData (varianceAngularCosData p))
    else varianceLayerData p • varianceAngularSinData p
  else if j=1 then
    if b=0 then -(varianceLayerData p • meanRadicalMul varianceZData (varianceAngularSinData p))
    else -(varianceLayerData p • varianceAngularCosData p)
  else if b=0 then ![1,0,0,0] else 0
def varianceRotationScale (j : Fin 3) : ℝ := if j=2 then packingRadius else 1
def varianceRotationInverseWeightData (j : Fin 3) : MeanRadical :=
  if j=2 then ![1/8,0,0,0] else ![3/8,-1/8,0,0]
def varianceRotationCoeffKernel (j : Fin 3) (i : Fin 16) : MeanRadical :=
  ∑p : Fin 8,∑b : Fin 2,meanRadicalMul (varianceRotationRawData j p b) (varianceBasisKernel p b i)
def varianceRotationKernel (i k : Fin 16) : MeanRadical :=
  ∑j : Fin 3,meanRadicalMul (varianceRotationInverseWeightData j)
    (meanRadicalMul (varianceRotationCoeffKernel j i) (varianceRotationCoeffKernel j k))

theorem varianceAngularData_eval (p : Fin 8) :
    meanRadicalEval (varianceAngularCosData p)=angularCos p ∧
    meanRadicalEval (varianceAngularSinData p)=angularSin p ∧
    (varianceLayerData p:ℝ)=layerSign p := by
  have hs : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hi : (Real.sqrt (2:ℝ))⁻¹=Real.sqrt 2/2 := by field_simp; nlinarith
  fin_cases p <;> norm_num [varianceAngularCosData,varianceAngularSinData,varianceLayerData,
    meanRadicalEval,angularCos,angularSin,layerSign,div_eq_mul_inv,hi,
    Fin.instOfNat,Fin.ofNat,Fin.succ,Fin.ext_iff,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] <;> (repeat' constructor) <;> ring

theorem varianceRotationRawData_eval (j : Fin 3) (p : Fin 8) (b : Fin 2) :
    boundaryRotation j (p,b)=varianceRotationScale j*meanRadicalEval (varianceRotationRawData j p b) := by
  obtain ⟨hc,hs,hl⟩ := varianceAngularData_eval p
  have hz := (varianceScalarData_eval 0).2.1
  fin_cases j <;> fin_cases b <;>
    norm_num [boundaryRotation,boundaryRaw,boundaryRawPair,boundaryRotationIndex,
      boundaryCos3,boundarySin3,varianceRotationScale,varianceRotationRawData,
      meanRadicalEval_neg,meanRadicalEval_smul,meanRadicalEval_mul,hc,hs,hl,hz,
      Fin.instOfNat,Fin.ofNat,Fin.succ,Fin.ext_iff] <;>
    norm_num [meanRadicalEval,Fin.instOfNat,Fin.ofNat,Fin.succ,Matrix.cons_val_two,
      Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] <;> ring

theorem varianceRotationInverseWeight_identity (j : Fin 3) :
    meanRadicalEval (varianceRotationInverseWeightData j)*boundaryWeight (boundaryRotationIndex j)=
      (varianceRotationScale j)^2 := by
  have hs : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hH := packing_parameters.2.2.1
  fin_cases j <;>
    norm_num [varianceRotationInverseWeightData,meanRadicalEval,boundaryWeight,
      boundaryRotationIndex,varianceRotationScale,Fin.instOfNat,Fin.ofNat,Fin.succ,Fin.ext_iff,
      Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons] <;>
    (try simp only [hH,packingHeight]) <;> nlinarith

theorem varianceRotationCoeffKernel_inner (j : Fin 3) (i : Fin 16) :
    inner ℝ (boundaryRotation j) (meanFlatBasis i)=
      varianceRotationScale j*meanRadicalEval (varianceRotationCoeffKernel j i) := by
  simp only [PiLp.inner_apply,Fintype.sum_prod_type,Real.inner_apply,
    varianceRotationRawData_eval,meanFlatBasis_coordinates,varianceRotationCoeffKernel,
    meanRadicalEval_sum,meanRadicalEval_mul,varianceBasisKernel,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem varianceRotationNormalized_product (j : Fin 3) (i k : Fin 16) :
    inner ℝ (normalizedRotation j) (meanFlatBasis i)*
      inner ℝ (normalizedRotation j) (meanFlatBasis k)=
    meanRadicalEval (varianceRotationInverseWeightData j)*
      meanRadicalEval (varianceRotationCoeffKernel j i)*meanRadicalEval (varianceRotationCoeffKernel j k) := by
  have hw := boundaryWeight_pos (boundaryRotationIndex j)
  have hs := Real.sq_sqrt hw.le
  have hn : Real.sqrt (boundaryWeight (boundaryRotationIndex j)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hw)
  have hi := varianceRotationInverseWeight_identity j
  change inner ℝ ((Real.sqrt (boundaryWeight (boundaryRotationIndex j)))⁻¹ • boundaryRotation j) (meanFlatBasis i)*
    inner ℝ ((Real.sqrt (boundaryWeight (boundaryRotationIndex j)))⁻¹ • boundaryRotation j) (meanFlatBasis k)=_
  rw [real_inner_smul_left,real_inner_smul_left,varianceRotationCoeffKernel_inner,
    varianceRotationCoeffKernel_inner]
  field_simp
  rw [hs,← hi]
  ring

theorem varianceRotationKernel_eval (i k : Fin 16) :
    inner ℝ (meanFlatBasis i) (rotationProjection (meanFlatBasis k))=
      meanRadicalEval (varianceRotationKernel i k) := by
  simp only [rotationProjection,inner_sum,real_inner_smul_right,
    varianceRotationKernel,meanRadicalEval_sum,meanRadicalEval_mul]
  apply Finset.sum_congr rfl
  intro j _
  have hc : inner ℝ (meanFlatBasis i) (normalizedRotation j)=
    inner ℝ (normalizedRotation j) (meanFlatBasis i) := real_inner_comm _ _
  rw [hc,mul_comm,varianceRotationNormalized_product]
  ring

#print axioms varianceRotationKernel_eval
end Blueprint.Thomson.Tail.Implementation
