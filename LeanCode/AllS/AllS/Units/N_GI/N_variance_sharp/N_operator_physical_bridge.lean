import AllS.Units.N_GI.N_variance_sharp.N_physical_data_exact
import AllS.Units.N_GI.N_variance_sharp.N_rotation_data_exact
import AllS.Units.N_GI.N_variance_sharp.N_operator_data_exact
import AllS.Units.N_GI.N_variance_sharp.N_tensor_slack_positive

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem varianceAbsorptionOperator_isSymmetric : varianceAbsorptionOperator.IsSymmetric := by
  intro q v
  calc
    inner ℝ (varianceAbsorptionOperator q) v=inner ℝ v (varianceAbsorptionOperator q) := real_inner_comm _ _
    _=inner ℝ q (varianceAbsorptionOperator v) := varianceAbsorptionOperator_symmetric v q

theorem varianceLinearData_eval (e : ContactIndex) (i : Fin 16) :
    contactLinearArray (meanFlatBasis i) e=
      packingRadius*meanRadicalEval (varianceLinearData (finProdFinEquiv e) i) := by
  rw [varianceLinearKernel_eval,varianceLinearData_exact]

theorem varianceMData_eval (e : ContactIndex) (i j : Fin 16) :
    inner ℝ (meanFlatBasis i) (contactM e (meanFlatBasis j))=
      meanRadicalEval (varianceMData (finProdFinEquiv e) i j) := by
  rw [varianceMKernel_eval,varianceMData_exact]

theorem varianceRotationProjectionData_eval (i k : Fin 16) :
    inner ℝ (meanFlatBasis i) (rotationProjection (meanFlatBasis k))=
      meanRadicalEval (varianceRotationProjectionData i k) := by
  rw [varianceRotationKernel_eval,← varianceRotationFromCoeff_exact]
  simp only [varianceRotationKernel,varianceRotationFromCoeff,varianceRotationCoeffData_exact]

theorem varianceAFromData_eval (i j : Fin 16) :
    inner ℝ (meanFlatBasis i) (varianceAbsorptionOperator (meanFlatBasis j))=
      meanRadicalEval (varianceAFromData i j) := by
  have hon := orthonormal_iff_ite.mp meanFlatBasis.orthonormal
  have hrot : (∑k : Fin 3,inner ℝ (normalizedRotation k) (meanFlatBasis i)*
      inner ℝ (normalizedRotation k) (meanFlatBasis j))=
      meanRadicalEval (varianceRotationProjectionData i j) := by
    rw [← varianceRotationProjectionData_eval]
    simp only [rotationProjection,inner_sum,real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro k _
    have hc : inner ℝ (normalizedRotation k) (meanFlatBasis i)=
      inner ℝ (meanFlatBasis i) (normalizedRotation k) := real_inner_comm _ _
    rw [hc]
    ring
  rw [varianceAbsorptionOperator_inner,hrot,hon]
  simp only [varianceAFromData,meanRadicalEval_add,meanRadicalEval_sub,meanRadicalEval_smul,
    meanRadicalEval_mul,meanRadicalEval_sum,varianceLinearData_eval,
    (varianceScalarData_eval 0).2.2.1,varianceWeightData_eval]
  have hd : meanRadicalEval (if i=j then (![17/5,0,0,0]:MeanRadical) else 0)=
      (17/5:ℝ)*(if i=j then 1 else 0) := by
    split_ifs <;> norm_num [meanRadicalEval,Matrix.cons_val_two,Matrix.cons_val_three,
      Matrix.head_cons,Matrix.tail_cons]
  rw [hd,Finset.mul_sum]
  norm_num only [Rat.cast_div,Rat.cast_ofNat]
  congr 2
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem varianceAbsorptionOperator_flat_entries (i j : Fin 16) :
    inner ℝ (meanFlatBasis i) (varianceAbsorptionOperator (meanFlatBasis j))=
      if ((finProdFinEquiv (m:=8) (n:=2)).symm i).1=((finProdFinEquiv (m:=8) (n:=2)).symm j).1 then
        meanRadicalEval (varianceBlockAData ((finProdFinEquiv (m:=8) (n:=2)).symm i).1
          ((finProdFinEquiv (m:=8) (n:=2)).symm i).2 ((finProdFinEquiv (m:=8) (n:=2)).symm j).2) else 0 := by
  rw [varianceAFromData_eval,varianceAFromData_exact]
  split_ifs <;> simp [meanRadicalEval]

theorem varianceAbsorptionOperator_block_entries (j k : Fin 8 × Fin 2) :
    inner ℝ (meanBlockBasis j) (varianceAbsorptionOperator (meanBlockBasis k))=
      if j.1=k.1 then meanRadicalEval (varianceBlockAData j.1 j.2 k.2) else 0 := by
  simpa only [meanFlatBasis,OrthonormalBasis.reindex_apply,Equiv.symm_apply_apply] using
    varianceAbsorptionOperator_flat_entries (finProdFinEquiv j) (finProdFinEquiv k)

#print axioms varianceAbsorptionOperator_block_entries
end Blueprint.Thomson.Tail.Implementation
