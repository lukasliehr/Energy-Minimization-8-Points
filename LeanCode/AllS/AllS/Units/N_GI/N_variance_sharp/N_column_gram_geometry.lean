import AllS.Units.N_GI.N_variance_sharp.N_operator_physical_bridge
import AllS.Units.N_GI.N_variance_sharp.N_tensor_kernel_data
import AllS.Units.N_GI.N_variance_sharp.N_tensor_slack_positive
import AllS.Units.N_GI.N_signed_mean.N_column_gram_geometry
noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

def varianceUniformColumn (a : Fin 16 × Fin 16) : TangentCoordinates :=
  packingRadius • ∑i : Fin 8 × Fin 2,
    meanRadicalEval (varianceUniformUData (finProdFinEquiv i) a.1 a.2) • meanBlockBasis i

theorem varianceUniformColumn_A_inner (j : Fin 8) (b : Fin 2) (a : Fin 16 × Fin 16) :
    inner ℝ (meanBlockBasis (j,b)) (varianceAbsorptionOperator (varianceUniformColumn a))=
      packingRadius*(∑c : Fin 2,meanRadicalEval (varianceBlockAData j b c)*
        meanRadicalEval (varianceUniformUData (finProdFinEquiv (j,c)) a.1 a.2)) := by
  simp only [varianceUniformColumn,map_smul,map_sum,inner_sum,real_inner_smul_right,
    varianceAbsorptionOperator_block_entries,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [mul_ite,mul_zero]
  simp only [Finset.sum_ite_eq',Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem varianceAbsorptionOperator_block_value (v : TangentCoordinates) :
    inner ℝ v (varianceAbsorptionOperator v)=
      ∑j : Fin 8,∑b : Fin 2,∑c : Fin 2,
        meanBlockBasis.repr v (j,b)*meanBlockBasis.repr v (j,c)*meanRadicalEval (varianceBlockAData j b c) := by
  conv_lhs => rw [← meanBlockBasis_repr_synthesis v]
  simp only [map_sum,map_smul,sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,
    varianceAbsorptionOperator_block_entries,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro b _
  simp only [Prod.fst,Prod.snd,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq',Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  apply Finset.sum_congr rfl
  intro c _
  rw [varianceBlockAData_symm j c b]
  ring

#print axioms varianceUniformColumn_A_inner
#print axioms varianceAbsorptionOperator_block_value
end Blueprint.Thomson.Tail.Implementation
