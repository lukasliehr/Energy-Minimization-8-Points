import AllS.Units.N_GI.N_signed_mean.N_column_gram_geometry
import AllS.Units.N_GI.N_signed_mean.N_dual_gram_bound

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem finite_cross_gram_sum {ι κ α : Type*} [Fintype ι] [Fintype κ] [Fintype α]
    (x : ι → ℝ) (y : κ → ℝ) (u : ι → α → ℝ) (v : κ → α → ℝ) :
    (∑a,(∑i,x i*u i a)*(∑j,y j*v j a))=∑i,∑j,x i*y j*(∑a,u i a*v j a) := by
  have he (a : α) : (∑i,x i*u i a)*(∑j,y j*v j a)=
      ∑i,∑j,x i*y j*(u i a*v j a) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

theorem meanRadiusSquared_eval : meanRadicalEval meanRadiusSquaredData=packingRadius^2 := by
  rw [packing_parameters.2.2.2]
  norm_num [meanRadiusSquaredData,meanRadicalEval,packingHeight,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.head_cons,Matrix.tail_cons]
  ring

theorem meanUniformColumn_inner (i : Fin 8 × Fin 2) (a : Fin 16 × Fin 16) :
    inner ℝ (meanBlockBasis i) (meanUniformColumn a)=
      packingRadius*meanRadicalEval (meanUniformUData (finProdFinEquiv i) a.1 a.2) := by
  have hon := orthonormal_iff_ite.mp meanBlockBasis.orthonormal
  simp only [meanUniformColumn,real_inner_smul_right,inner_sum,hon,mul_ite,mul_one,mul_zero]
  simp

section Certificate

theorem meanUniformColumn_gram (hG : ∀i j,meanUniformGramFromU i j=meanUniformGramData i j) (i j : Fin 8 × Fin 2) :
    (∑a : Fin 16 × Fin 16,inner ℝ (meanBlockBasis i) (meanUniformColumn a)*
      inner ℝ (meanBlockBasis j) (meanUniformColumn a))=
        meanRadicalEval (meanUniformGramData (finProdFinEquiv i) (finProdFinEquiv j)) := by
  rw [← hG]
  simp only [meanUniformGramFromU,meanRadicalEval_mul,meanRadicalEval_sum,
    meanRadiusSquared_eval,meanUniformColumn_inner,Fintype.sum_prod_type,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem meanUniformColumn_A_inner_sum (i : Fin 8 × Fin 2) (a : Fin 16 × Fin 16) :
    inner ℝ (meanBlockBasis i) (meanAbsorptionOperator (meanUniformColumn a))=
      ∑c : Fin 2,meanRadicalEval (meanBlockAData i.1 i.2 c)*
        inner ℝ (meanBlockBasis (i.1,c)) (meanUniformColumn a) := by
  rcases i with ⟨j,b⟩
  rw [meanUniformColumn_A_inner]
  simp only [meanUniformColumn_inner,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem meanUniformColumn_metricGram (hG : ∀i j,meanUniformGramFromU i j=meanUniformGramData i j) (i j : Fin 8 × Fin 2) :
    (∑a : Fin 16 × Fin 16,
      inner ℝ (meanBlockBasis i) (meanAbsorptionOperator (meanUniformColumn a))*
      inner ℝ (meanBlockBasis j) (meanAbsorptionOperator (meanUniformColumn a)))=
    (22/5:ℝ)*inner ℝ (meanBlockBasis i) (meanAbsorptionOperator (meanBlockBasis j))-
      (if i.1=j.1 then meanRadicalEval (meanUniformSlackData i.1 i.2 j.2) else 0) := by
  simp only [meanUniformColumn_A_inner_sum]
  rw [finite_cross_gram_sum]
  simp only [meanUniformColumn_gram hG,meanAbsorptionOperator_block_entries]
  rcases i with ⟨f,b⟩
  rcases j with ⟨g,c⟩
  dsimp only
  by_cases hfg : f=g
  · subst g
    simp only [ite_true]
    have hs := congrArg meanRadicalEval (meanUniformSlack_data f b c)
    simp only [meanUniformSlackFromGram,meanRadicalEval_sub,meanRadicalEval_smul,
      meanRadicalEval_sum,meanRadicalEval_mul] at hs
    norm_num only [Rat.cast_div,Rat.cast_ofNat] at hs
    rw [← hs]
    have he : (∑s : Fin 2,∑t : Fin 2,meanRadicalEval (meanBlockAData f b s)*
        meanRadicalEval (meanBlockAData f c t)*
        meanRadicalEval (meanUniformGramData (finProdFinEquiv (f,s)) (finProdFinEquiv (f,t))))=
      ∑s : Fin 2,∑t : Fin 2,
        (meanRadicalEval (meanBlockAData f b s)*
        meanRadicalEval (meanUniformGramData (finProdFinEquiv (f,s)) (finProdFinEquiv (f,t))))*
        meanRadicalEval (meanBlockAData f t c) := by
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro t _
      rw [meanBlockAData_symm f c t]
      ring
    rw [he]
    ring
  · have hz (s t : Fin 2) : meanUniformGramData (finProdFinEquiv (f,s)) (finProdFinEquiv (g,t))=0 := by
      rw [meanUniformGramData_block]
      simp [hfg]
    simp [hfg,hz,meanRadicalEval]

end Certificate
#print axioms meanUniformColumn_metricGram
end Blueprint.Thomson.Tail.Implementation
