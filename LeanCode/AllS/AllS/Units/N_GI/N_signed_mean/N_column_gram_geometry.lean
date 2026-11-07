import AllS.Units.N_GI.N_signed_mean.N_tensor_kernel_data
import AllS.Units.N_GI.N_signed_mean.N_block_basis
import AllS.Units.N_GI.N_signed_mean.N_slack_positive

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem finiteGram_sum {ι α : Type*} [Fintype ι] [Fintype α]
    (x : ι → ℝ) (u : ι → α → ℝ) :
    (∑a,(∑i,x i*u i a)^2)=∑i,∑j,x i*x j*(∑a,u i a*u j a) := by
  simp only [pow_two,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro a _
  ring

def meanUniformColumn (a : Fin 16 × Fin 16) : TangentCoordinates :=
  packingRadius • ∑i : Fin 8 × Fin 2,
    meanRadicalEval (meanUniformUData (finProdFinEquiv i) a.1 a.2) • meanBlockBasis i

theorem meanUniformColumn_A_inner (j : Fin 8) (b : Fin 2) (a : Fin 16 × Fin 16) :
    inner ℝ (meanBlockBasis (j,b)) (meanAbsorptionOperator (meanUniformColumn a))=
      packingRadius*(∑c : Fin 2,meanRadicalEval (meanBlockAData j b c)*
        meanRadicalEval (meanUniformUData (finProdFinEquiv (j,c)) a.1 a.2)) := by
  simp only [meanUniformColumn,map_smul,map_sum,inner_sum,real_inner_smul_right,
    meanAbsorptionOperator_block_entries,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp only [mul_ite,mul_zero]
  simp only [Finset.sum_ite_eq',Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem meanBlockBasis_repr_synthesis (v : TangentCoordinates) :
    (∑i : Fin 8 × Fin 2,meanBlockBasis.repr v i • meanBlockBasis i)=v := by
  simpa only [OrthonormalBasis.repr_apply_apply] using meanBlockBasis.sum_repr' v

theorem meanAbsorptionOperator_block_value (v : TangentCoordinates) :
    inner ℝ v (meanAbsorptionOperator v)=
      ∑j : Fin 8,∑b : Fin 2,∑c : Fin 2,
        meanBlockBasis.repr v (j,b)*meanBlockBasis.repr v (j,c)*meanRadicalEval (meanBlockAData j b c) := by
  conv_lhs => rw [← meanBlockBasis_repr_synthesis v]
  simp only [map_sum,map_smul,sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,
    meanAbsorptionOperator_block_entries,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro b _
  simp only [Prod.fst,Prod.snd,mul_ite,mul_zero]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq',Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  apply Finset.sum_congr rfl
  intro c _
  rw [meanBlockAData_symm j c b]
  ring

#print axioms meanUniformColumn_A_inner
#print axioms meanAbsorptionOperator_block_value
end Blueprint.Thomson.Tail.Implementation
