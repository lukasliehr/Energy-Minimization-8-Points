import AllS.Units.N_GI.N_variance_sharp.N_projected_tensor
import AllS.Units.N_GI.N_variance_sharp.N_projection_physical_bridge
import AllS.Units.N_GI.N_variance_sharp.N_column_dual_bound

set_option maxRecDepth 8192
noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

def varianceUniformU (q : TangentCoordinates) : TangentCoordinates :=
  ∑a : Fin 16 × Fin 16,(meanFlatBasis.repr q a.1*meanFlatBasis.repr q a.2) • varianceUniformColumn a

theorem varianceUniformU_norm_bound
    (hG : ∀i j,varianceUniformGramFromU i j=varianceUniformGramData i j) (q : TangentCoordinates) :
    inner ℝ (varianceUniformU q) (varianceAbsorptionOperator (varianceUniformU q)) ≤ (15:ℝ)*‖q‖^4 := by
  have h := varianceUniformColumn_norm_bound hG (fun a=>meanFlatBasis.repr q a.1*meanFlatBasis.repr q a.2)
  change inner ℝ (varianceUniformU q) (varianceAbsorptionOperator (varianceUniformU q)) ≤ _ at h
  have he : (∑a : Fin 16 × Fin 16,(meanFlatBasis.repr q a.1*meanFlatBasis.repr q a.2)^2)=‖q‖^4 := by
    rw [← meanFlatBasis.repr.norm_map q,← orderedSquare_norm_sq]
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  rwa [he] at h

theorem varianceUniformColumn_flat_A_inner (i j k : Fin 16) :
    inner ℝ (meanFlatBasis i) (varianceAbsorptionOperator (varianceUniformColumn (j,k)))=
      packingRadius*meanRadicalEval (varianceAUData i j k) := by
  simp only [meanFlatBasis,OrthonormalBasis.reindex_apply]
  rw [show (finProdFinEquiv (m:=8) (n:=2)).symm i=
    (((finProdFinEquiv (m:=8) (n:=2)).symm i).1,((finProdFinEquiv (m:=8) (n:=2)).symm i).2) from rfl]
  rw [varianceUniformColumn_A_inner]
  simp only [varianceAUData,varianceBlockEntry,meanRadicalEval_sum,meanRadicalEval_mul]

theorem varianceUniformU_contraction
    (hC : ∀i j k,varianceSymAUData i j k=varianceCubicKernelData i j k) (q : TangentCoordinates) :
    inner ℝ q (varianceAbsorptionOperator (varianceUniformU q))=varianceCubic (sliceProjection q) := by
  let x := meanFlatBasis.repr q
  have hq : (∑i : Fin 16,x i • meanFlatBasis i)=q := by
    simpa only [x,OrthonormalBasis.repr_apply_apply] using meanFlatBasis.sum_repr' q
  have he : inner ℝ q (varianceAbsorptionOperator (varianceUniformU q))=
      tensorCubic (fun i j k=>packingRadius*meanRadicalEval (varianceAUData k i j)) x := by
    conv_lhs => lhs; rw [← hq]
    simp only [varianceUniformU,map_sum,map_smul,sum_inner,inner_sum,real_inner_smul_left,
      real_inner_smul_right,Finset.mul_sum,Fintype.sum_prod_type,varianceUniformColumn_flat_A_inner,tensorCubic]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    dsimp [x]
    ring
  have hcycle : tensorCubic (fun i j k=>packingRadius*meanRadicalEval (varianceAUData k i j)) x=
      tensorCubic (fun i j k=>packingRadius*meanRadicalEval (varianceAUData i j k)) x :=
    (tensorCubic_swap23 (fun i j k=>packingRadius*meanRadicalEval (varianceAUData j i k)) x).trans
      (tensorCubic_swap12 (fun i j k=>packingRadius*meanRadicalEval (varianceAUData i j k)) x)
  rw [he,hcycle,← tensorCubic_symSix]
  have ht : tensorSymSix (fun i j k=>packingRadius*meanRadicalEval (varianceAUData i j k))=
      (fun i j k=>varianceTrilinear (sliceProjection (meanFlatBasis i))
        (sliceProjection (meanFlatBasis j)) (sliceProjection (meanFlatBasis k))) := by
    funext i j k
    rw [varianceCubicKernelData_eval,← hC]
    simp only [tensorSymSix,varianceSymAUData,meanRadicalEval_smul,meanRadicalEval_add]
    norm_num
    ring
  rw [ht]
  exact varianceProjectedTensor_contraction q

#print axioms varianceUniformU_norm_bound
#print axioms varianceUniformU_contraction
end Blueprint.Thomson.Tail.Implementation
