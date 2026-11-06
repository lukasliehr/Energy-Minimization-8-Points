import AllS.Units.N_GI.N_signed_mean.N_tensor_physical_bridge
import AllS.Units.N_GI.N_signed_mean.N_tensor_symmetrization
import AllS.Units.N_GI.N_signed_mean.N_column_dual_bound

set_option maxRecDepth 8192
noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

def meanUniformU (q : TangentCoordinates) : TangentCoordinates :=
  ∑a : Fin 16 × Fin 16,(meanFlatBasis.repr q a.1*meanFlatBasis.repr q a.2) • meanUniformColumn a

theorem meanUniformU_norm_bound
    (hG : ∀i j,meanUniformGramFromU i j=meanUniformGramData i j) (q : TangentCoordinates) :
    inner ℝ (meanUniformU q) (meanAbsorptionOperator (meanUniformU q)) ≤ (22/5:ℝ)*‖q‖^4 := by
  have h := meanUniformColumn_norm_bound hG (fun a=>meanFlatBasis.repr q a.1*meanFlatBasis.repr q a.2)
  change inner ℝ (meanUniformU q) (meanAbsorptionOperator (meanUniformU q)) ≤ _ at h
  have he : (∑a : Fin 16 × Fin 16,(meanFlatBasis.repr q a.1*meanFlatBasis.repr q a.2)^2)=‖q‖^4 := by
    rw [← meanFlatBasis.repr.norm_map q,← orderedSquare_norm_sq]
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  rwa [he] at h

theorem meanUniformColumn_flat_A_inner (i j k : Fin 16) :
    inner ℝ (meanFlatBasis i) (meanAbsorptionOperator (meanUniformColumn (j,k)))=
      packingRadius*meanRadicalEval (meanAUData i j k) := by
  simp only [meanFlatBasis,OrthonormalBasis.reindex_apply]
  rw [show (finProdFinEquiv (m:=8) (n:=2)).symm i=
    (((finProdFinEquiv (m:=8) (n:=2)).symm i).1,((finProdFinEquiv (m:=8) (n:=2)).symm i).2) from rfl]
  rw [meanUniformColumn_A_inner]
  simp only [meanAUData,meanRadicalEval_sum,meanRadicalEval_mul]

theorem meanUniformU_contraction
    (hC : ∀i j k,meanSymAUData i j k=meanCubicKernelData i j k) (q : TangentCoordinates) :
    inner ℝ q (meanAbsorptionOperator (meanUniformU q))=stressCubic q := by
  let x := meanFlatBasis.repr q
  have hq : (∑i : Fin 16,x i • meanFlatBasis i)=q := by
    simpa only [x,OrthonormalBasis.repr_apply_apply] using meanFlatBasis.sum_repr' q
  have he : inner ℝ q (meanAbsorptionOperator (meanUniformU q))=
      tensorCubic (fun i j k=>packingRadius*meanRadicalEval (meanAUData k i j)) x := by
    conv_lhs => lhs; rw [← hq]
    simp only [meanUniformU,map_sum,map_smul,sum_inner,inner_sum,real_inner_smul_left,
      real_inner_smul_right,Finset.mul_sum,Fintype.sum_prod_type,meanUniformColumn_flat_A_inner,tensorCubic]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    dsimp [x]
    ring
  have hcycle : tensorCubic (fun i j k=>packingRadius*meanRadicalEval (meanAUData k i j)) x=
      tensorCubic (fun i j k=>packingRadius*meanRadicalEval (meanAUData i j k)) x :=
    (tensorCubic_swap23 (fun i j k=>packingRadius*meanRadicalEval (meanAUData j i k)) x).trans
      (tensorCubic_swap12 (fun i j k=>packingRadius*meanRadicalEval (meanAUData i j k)) x)
  rw [he,hcycle,← tensorCubic_symSix]
  have ht : tensorSymSix (fun i j k=>packingRadius*meanRadicalEval (meanAUData i j k))=
      meanPhysicalTensor meanFlatBasis := by
    funext i j k
    rw [meanPhysicalTensor_kernel,← hC]
    simp only [tensorSymSix,meanSymAUData,meanRadicalEval_smul,meanRadicalEval_add]
    norm_num
    ring
  rw [ht]
  exact meanPhysicalTensor_contraction meanFlatBasis q

#print axioms meanUniformU_norm_bound
#print axioms meanUniformU_contraction
end Blueprint.Thomson.Tail.Implementation
