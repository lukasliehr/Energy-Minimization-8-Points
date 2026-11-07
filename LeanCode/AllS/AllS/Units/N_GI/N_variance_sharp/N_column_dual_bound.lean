import AllS.Units.N_GI.N_variance_sharp.N_column_gram_bound
set_option maxRecDepth 8192
noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem varianceUniformSlack_form_nonnegative (x : Fin 8 × Fin 2 → ℝ) :
    0 ≤ ∑i : Fin 8 × Fin 2,∑j : Fin 8 × Fin 2,
      x i*x j*(if i.1=j.1 then meanRadicalEval (varianceUniformSlackData i.1 i.2 j.2) else 0) := by
  have he : (∑i : Fin 8 × Fin 2,∑j : Fin 8 × Fin 2,
      x i*x j*(if i.1=j.1 then meanRadicalEval (varianceUniformSlackData i.1 i.2 j.2) else 0))=
    ∑j : Fin 8,(meanRadicalEval (varianceUniformSlackData j 0 0)*(x (j,0))^2+
      2*meanRadicalEval (varianceUniformSlackData j 0 1)*x (j,0)*x (j,1)+
      meanRadicalEval (varianceUniformSlackData j 1 1)*(x (j,1))^2) := by
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j _
    have hrow (b : Fin 2) : (∑g : Fin 8,∑c : Fin 2,x (j,b)*x (g,c)*
        (if j=g then meanRadicalEval (varianceUniformSlackData j b c) else 0))=
        ∑c : Fin 2,x (j,b)*x (j,c)*meanRadicalEval (varianceUniformSlackData j b c) := by
      rw [Finset.sum_comm]
      simp [mul_ite,Finset.sum_ite_eq]
    change (∑b : Fin 2,∑g : Fin 8,∑c : Fin 2,x (j,b)*x (g,c)*
      (if j=g then meanRadicalEval (varianceUniformSlackData j b c) else 0))=_
    simp_rw [hrow]
    simp only [Fin.sum_univ_two]
    rw [varianceUniformSlack_symm j 1 0]
    ring
  rw [he]
  exact Finset.sum_nonneg (fun j _=>varianceUniformSlack_psd j _ _)

theorem varianceUniformColumn_dual_bound
    (hG : ∀i j,varianceUniformGramFromU i j=varianceUniformGramData i j) (v : TangentCoordinates) :
    (∑a : Fin 16 × Fin 16,(inner ℝ (varianceAbsorptionOperator v) (varianceUniformColumn a))^2) ≤
      (15:ℝ)*inner ℝ v (varianceAbsorptionOperator v) := by
  let x := meanBlockBasis.repr v
  have hc (a : Fin 16 × Fin 16) : inner ℝ (varianceAbsorptionOperator v) (varianceUniformColumn a)=
      ∑i : Fin 8 × Fin 2,x i*inner ℝ (meanBlockBasis i) (varianceAbsorptionOperator (varianceUniformColumn a)) := by
    rw [varianceAbsorptionOperator_isSymmetric]
    conv_lhs => rw [← meanBlockBasis_repr_synthesis v]
    simp only [sum_inner,real_inner_smul_left]
    rfl
  have hv : (∑i : Fin 8 × Fin 2,∑j : Fin 8 × Fin 2,
      x i*x j*inner ℝ (meanBlockBasis i) (varianceAbsorptionOperator (meanBlockBasis j)))=
        inner ℝ v (varianceAbsorptionOperator v) := by
    conv_rhs => rw [← meanBlockBasis_repr_synthesis v]
    simp only [map_sum,map_smul,sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [x]
    rw [← varianceAbsorptionOperator_isSymmetric (meanBlockBasis i) (meanBlockBasis j),real_inner_comm]
    ring
  simp_rw [hc]
  rw [finiteGram_sum]
  simp only [varianceUniformColumn_metricGram hG]
  have he (i j : Fin 8 × Fin 2) :
      x i*x j*((15:ℝ)*inner ℝ (meanBlockBasis i) (varianceAbsorptionOperator (meanBlockBasis j))-
        (if i.1=j.1 then meanRadicalEval (varianceUniformSlackData i.1 i.2 j.2) else 0))=
      (15:ℝ)*(x i*x j*inner ℝ (meanBlockBasis i) (varianceAbsorptionOperator (meanBlockBasis j)))-
        x i*x j*(if i.1=j.1 then meanRadicalEval (varianceUniformSlackData i.1 i.2 j.2) else 0) := by ring
  simp_rw [he,Finset.sum_sub_distrib,← Finset.mul_sum]
  rw [hv]
  exact sub_le_self _ (varianceUniformSlack_form_nonnegative x)

theorem varianceUniformColumn_norm_bound
    (hG : ∀i j,varianceUniformGramFromU i j=varianceUniformGramData i j) (z : Fin 16 × Fin 16 → ℝ) :
    inner ℝ (∑a,z a • varianceUniformColumn a) (varianceAbsorptionOperator (∑a,z a • varianceUniformColumn a)) ≤
      (15:ℝ)*(∑a,(z a)^2) :=
  tensorMap_bound_of_dual_gram varianceAbsorptionOperator varianceUniformColumn 15
    varianceAbsorptionOperator_nonnegative (by norm_num) (varianceUniformColumn_dual_bound hG) z

#print axioms varianceUniformColumn_norm_bound
end Blueprint.Thomson.Tail.Implementation
