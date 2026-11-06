import AllS.Units.N_GI.N_variance_sharp.N_column_gram_geometry
import AllS.Units.N_GI.N_signed_mean.N_column_gram_bound
noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem varianceRadiusSquared_eval : meanRadicalEval varianceRadiusSquaredData=packingRadius^2 := by
  rw [packing_parameters.2.2.2]
  norm_num [varianceRadiusSquaredData,meanRadicalEval,packingHeight,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.head_cons,Matrix.tail_cons]
  ring

theorem varianceUniformColumn_inner (i : Fin 8 × Fin 2) (a : Fin 16 × Fin 16) :
    inner ℝ (meanBlockBasis i) (varianceUniformColumn a)=
      packingRadius*meanRadicalEval (varianceUniformUData (finProdFinEquiv i) a.1 a.2) := by
  have hon := orthonormal_iff_ite.mp meanBlockBasis.orthonormal
  simp only [varianceUniformColumn,real_inner_smul_right,inner_sum,hon,mul_ite,mul_one,mul_zero]
  simp

section Certificate

theorem varianceUniformColumn_gram (hG : ∀i j,varianceUniformGramFromU i j=varianceUniformGramData i j) (i j : Fin 8 × Fin 2) :
    (∑a : Fin 16 × Fin 16,inner ℝ (meanBlockBasis i) (varianceUniformColumn a)*
      inner ℝ (meanBlockBasis j) (varianceUniformColumn a))=
        meanRadicalEval (varianceUniformGramData (finProdFinEquiv i) (finProdFinEquiv j)) := by
  rw [← hG]
  simp only [varianceUniformGramFromU,meanRadicalEval_mul,meanRadicalEval_sum,
    varianceRadiusSquared_eval,varianceUniformColumn_inner,Fintype.sum_prod_type,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem varianceUniformColumn_A_inner_sum (i : Fin 8 × Fin 2) (a : Fin 16 × Fin 16) :
    inner ℝ (meanBlockBasis i) (varianceAbsorptionOperator (varianceUniformColumn a))=
      ∑c : Fin 2,meanRadicalEval (varianceBlockAData i.1 i.2 c)*
        inner ℝ (meanBlockBasis (i.1,c)) (varianceUniformColumn a) := by
  rcases i with ⟨j,b⟩
  rw [varianceUniformColumn_A_inner]
  simp only [varianceUniformColumn_inner,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem varianceUniformColumn_metricGram (hG : ∀i j,varianceUniformGramFromU i j=varianceUniformGramData i j) (i j : Fin 8 × Fin 2) :
    (∑a : Fin 16 × Fin 16,
      inner ℝ (meanBlockBasis i) (varianceAbsorptionOperator (varianceUniformColumn a))*
      inner ℝ (meanBlockBasis j) (varianceAbsorptionOperator (varianceUniformColumn a)))=
    (15:ℝ)*inner ℝ (meanBlockBasis i) (varianceAbsorptionOperator (meanBlockBasis j))-
      (if i.1=j.1 then meanRadicalEval (varianceUniformSlackData i.1 i.2 j.2) else 0) := by
  simp only [varianceUniformColumn_A_inner_sum]
  rw [finite_cross_gram_sum]
  simp only [varianceUniformColumn_gram hG,varianceAbsorptionOperator_block_entries]
  rcases i with ⟨f,b⟩
  rcases j with ⟨g,c⟩
  dsimp only
  by_cases hfg : f=g
  · subst g
    simp only [ite_true]
    have hs := congrArg meanRadicalEval (varianceUniformSlack_data f b c)
    simp only [varianceUniformSlackFromGram,meanRadicalEval_sub,meanRadicalEval_smul,
      meanRadicalEval_sum,meanRadicalEval_mul] at hs
    norm_num only [Rat.cast_div,Rat.cast_ofNat] at hs
    rw [← hs]
    have he : (∑s : Fin 2,∑t : Fin 2,meanRadicalEval (varianceBlockAData f b s)*
        meanRadicalEval (varianceBlockAData f c t)*
        meanRadicalEval (varianceUniformGramData (finProdFinEquiv (f,s)) (finProdFinEquiv (f,t))))=
      ∑s : Fin 2,∑t : Fin 2,
        (meanRadicalEval (varianceBlockAData f b s)*
        meanRadicalEval (varianceUniformGramData (finProdFinEquiv (f,s)) (finProdFinEquiv (f,t))))*
        meanRadicalEval (varianceBlockAData f t c) := by
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      rw [varianceBlockAData_symm f c t]
      ring
    rw [he]
    ring
  · have hz (s t : Fin 2) : varianceUniformGramData (finProdFinEquiv (f,s)) (finProdFinEquiv (g,t))=0 := by
      rw [varianceUniformGramData_block]
      simp [hfg]
    simp [hfg,hz,meanRadicalEval]

end Certificate
#print axioms varianceUniformColumn_metricGram
end Blueprint.Thomson.Tail.Implementation
