import AllS.Units.N_GI.N_signed_mean.N_column_gram_bound

set_option maxRecDepth 8192
noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem meanUniformSlack_form_nonnegative (x : Fin 8 × Fin 2 → ℝ) :
    0 ≤ ∑i : Fin 8 × Fin 2,∑j : Fin 8 × Fin 2,
      x i*x j*(if i.1=j.1 then meanRadicalEval (meanUniformSlackData i.1 i.2 j.2) else 0) := by
  have he : (∑i : Fin 8 × Fin 2,∑j : Fin 8 × Fin 2,
      x i*x j*(if i.1=j.1 then meanRadicalEval (meanUniformSlackData i.1 i.2 j.2) else 0))=
    ∑j : Fin 8,(meanRadicalEval (meanUniformSlackData j 0 0)*(x (j,0))^2+
      2*meanRadicalEval (meanUniformSlackData j 0 1)*x (j,0)*x (j,1)+
      meanRadicalEval (meanUniformSlackData j 1 1)*(x (j,1))^2) := by
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j _
    have hrow (b : Fin 2) : (∑g : Fin 8,∑c : Fin 2,x (j,b)*x (g,c)*
        (if j=g then meanRadicalEval (meanUniformSlackData j b c) else 0))=
        ∑c : Fin 2,x (j,b)*x (j,c)*meanRadicalEval (meanUniformSlackData j b c) := by
      rw [Finset.sum_comm]
      simp [mul_ite,Finset.sum_ite_eq]
    change (∑b : Fin 2,∑g : Fin 8,∑c : Fin 2,x (j,b)*x (g,c)*
      (if j=g then meanRadicalEval (meanUniformSlackData j b c) else 0))=_
    simp_rw [hrow]
    simp only [Fin.sum_univ_two]
    rw [meanUniformSlack_symm j 1 0]
    ring
  rw [he]
  exact Finset.sum_nonneg (fun j _=>meanUniformSlack_psd j _ _)

theorem meanUniformColumn_dual_bound
    (hG : ∀i j,meanUniformGramFromU i j=meanUniformGramData i j) (v : TangentCoordinates) :
    (∑a : Fin 16 × Fin 16,(inner ℝ (meanAbsorptionOperator v) (meanUniformColumn a))^2) ≤
      (22/5:ℝ)*inner ℝ v (meanAbsorptionOperator v) := by
  let x := meanBlockBasis.repr v
  have hc (a : Fin 16 × Fin 16) : inner ℝ (meanAbsorptionOperator v) (meanUniformColumn a)=
      ∑i : Fin 8 × Fin 2,x i*inner ℝ (meanBlockBasis i) (meanAbsorptionOperator (meanUniformColumn a)) := by
    rw [meanAbsorptionOperator_symmetric]
    conv_lhs => rw [← meanBlockBasis_repr_synthesis v]
    simp only [sum_inner,real_inner_smul_left]
    rfl
  have hv : (∑i : Fin 8 × Fin 2,∑j : Fin 8 × Fin 2,
      x i*x j*inner ℝ (meanBlockBasis i) (meanAbsorptionOperator (meanBlockBasis j)))=
        inner ℝ v (meanAbsorptionOperator v) := by
    conv_rhs => rw [← meanBlockBasis_repr_synthesis v]
    simp only [map_sum,map_smul,sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [x]
    rw [← meanAbsorptionOperator_symmetric (meanBlockBasis i) (meanBlockBasis j),real_inner_comm]
    ring
  simp_rw [hc]
  rw [finiteGram_sum]
  simp only [meanUniformColumn_metricGram hG]
  have he (i j : Fin 8 × Fin 2) :
      x i*x j*((22/5:ℝ)*inner ℝ (meanBlockBasis i) (meanAbsorptionOperator (meanBlockBasis j))-
        (if i.1=j.1 then meanRadicalEval (meanUniformSlackData i.1 i.2 j.2) else 0))=
      (22/5:ℝ)*(x i*x j*inner ℝ (meanBlockBasis i) (meanAbsorptionOperator (meanBlockBasis j)))-
        x i*x j*(if i.1=j.1 then meanRadicalEval (meanUniformSlackData i.1 i.2 j.2) else 0) := by ring
  simp_rw [he,Finset.sum_sub_distrib,← Finset.mul_sum]
  rw [hv]
  exact sub_le_self _ (meanUniformSlack_form_nonnegative x)

theorem meanUniformColumn_norm_bound
    (hG : ∀i j,meanUniformGramFromU i j=meanUniformGramData i j) (z : Fin 16 × Fin 16 → ℝ) :
    inner ℝ (∑a,z a • meanUniformColumn a) (meanAbsorptionOperator (∑a,z a • meanUniformColumn a)) ≤
      (22/5:ℝ)*(∑a,(z a)^2) :=
  tensorMap_bound_of_dual_gram meanAbsorptionOperator meanUniformColumn (22/5)
    meanAbsorptionOperator_nonnegative (by norm_num) (meanUniformColumn_dual_bound hG) z

#print axioms meanUniformColumn_norm_bound
end Blueprint.Thomson.Tail.Implementation
