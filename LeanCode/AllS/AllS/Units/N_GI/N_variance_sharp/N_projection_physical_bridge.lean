import AllS.Units.N_GI.N_variance_sharp.N_physical_data_exact
import AllS.Units.N_GI.N_variance_sharp.N_rotation_data_exact
import AllS.Units.N_GI.N_variance_sharp.N_tensor_slack_positive

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem varianceRotationProjectionData_inner (i k : Fin 16) :
    inner ℝ (meanFlatBasis i) (rotationProjection (meanFlatBasis k))=
      meanRadicalEval (varianceRotationProjectionData i k) := by
  rw [varianceRotationKernel_eval,← varianceRotationFromCoeff_exact]
  simp only [varianceRotationKernel,varianceRotationFromCoeff,varianceRotationCoeffData_exact]

theorem varianceSliceProjectionData_inner (i k : Fin 16) :
    inner ℝ (meanFlatBasis i) (sliceProjection (meanFlatBasis k))=
      meanRadicalEval (varianceSliceProjectionData i k) := by
  rw [sliceProjection,inner_sub_right,varianceRotationProjectionData_inner,
    varianceSliceProjectionData_exact,meanRadicalEval_sub]
  have hon := orthonormal_iff_ite.mp meanFlatBasis.orthonormal
  rw [hon]
  by_cases h : i=k <;> simp [h,meanRadicalEval,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.head_cons,Matrix.tail_cons]

theorem varianceSliceProjection_basis (i : Fin 16) :
    sliceProjection (meanFlatBasis i)=∑b : Fin 2,
      meanRadicalEval (varianceSliceProjectionData (varianceBlockEntry i b) i) •
        meanFlatBasis (varianceBlockEntry i b) := by
  have hfull : (∑k : Fin 16,meanRadicalEval (varianceSliceProjectionData k i) • meanFlatBasis k)=
      sliceProjection (meanFlatBasis i) := by
    simpa only [OrthonormalBasis.repr_apply_apply,varianceSliceProjectionData_inner] using
      meanFlatBasis.sum_repr' (sliceProjection (meanFlatBasis i))
  rw [← hfull,← (finProdFinEquiv (m:=8) (n:=2)).sum_comp,Fintype.sum_prod_type,
    Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_eq_single ((finProdFinEquiv (m:=8) (n:=2)).symm i).1]
  · rfl
  · intro g _ hg
    have hz := varianceSliceProjectionData_block (finProdFinEquiv (g,b)) i
      (by simpa only [Equiv.symm_apply_apply] using hg)
    rw [hz]
    simp [meanRadicalEval]
  · simp

theorem varianceProjectedLinearData_eval (e : ContactIndex) (i : Fin 16) :
    contactLinearArray (sliceProjection (meanFlatBasis i)) e=
      packingRadius*meanRadicalEval (varianceProjectedLinearData (finProdFinEquiv e) i) := by
  rw [varianceSliceProjection_basis,← varianceProjectedLinearData_exact]
  change contactLinearMap e (∑b : Fin 2,
      meanRadicalEval (varianceSliceProjectionData (varianceBlockEntry i b) i) •
        meanFlatBasis (varianceBlockEntry i b))=_
  simp only [map_sum,map_smul,smul_eq_mul,contactLinearMap,LinearMap.coe_mk,AddHom.coe_mk]
  change (∑b : Fin 2,meanRadicalEval (varianceSliceProjectionData (varianceBlockEntry i b) i)*
    contactLinearArray (meanFlatBasis (varianceBlockEntry i b)) e)=_
  simp only [varianceLinearKernel_eval,varianceLinearData_exact,varianceProjectedLinearFromData,
    meanRadicalEval_sum,meanRadicalEval_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem varianceProjectedMData_eval (e : ContactIndex) (i j : Fin 16) :
    inner ℝ (sliceProjection (meanFlatBasis i)) (contactM e (sliceProjection (meanFlatBasis j)))=
      meanRadicalEval (varianceProjectedMData (finProdFinEquiv e) i j) := by
  rw [varianceSliceProjection_basis,varianceSliceProjection_basis,← varianceProjectedMData_exact]
  change inner ℝ (∑b : Fin 2,
      meanRadicalEval (varianceSliceProjectionData (varianceBlockEntry i b) i) •
        meanFlatBasis (varianceBlockEntry i b))
    (contactMLinear e (∑c : Fin 2,
      meanRadicalEval (varianceSliceProjectionData (varianceBlockEntry j c) j) •
        meanFlatBasis (varianceBlockEntry j c)))=_
  simp only [map_sum,map_smul,sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,
    contactMLinear,LinearMap.coe_mk,AddHom.coe_mk,Finset.mul_sum,varianceMKernel_eval,
    varianceMData_exact,varianceProjectedMFromData,meanRadicalEval_sum,meanRadicalEval_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem varianceCubicKernelData_eval (i j k : Fin 16) :
    varianceTrilinear (sliceProjection (meanFlatBasis i)) (sliceProjection (meanFlatBasis j))
      (sliceProjection (meanFlatBasis k))=
      packingRadius*meanRadicalEval (varianceCubicKernelData i j k) := by
  simp only [varianceTrilinear,varianceProjectedLinearData_eval,varianceProjectedMData_eval,
    varianceCubicKernelData,meanRadicalEval_smul,meanRadicalEval_sum,meanRadicalEval_mul,
    meanRadicalEval_add,varianceWeightData_eval]
  norm_num only [Rat.cast_div,Rat.cast_ofNat]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

#print axioms varianceSliceProjection_basis
#print axioms varianceCubicKernelData_eval
end Blueprint.Thomson.Tail.Implementation
