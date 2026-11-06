import AllS.Units.N_GI.N_centered_quadratic.N_projected_form

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem contactM_sum {ι : Type*} (s : Finset ι) (q : ι → TangentCoordinates) (e : ContactIndex) :
    contactM e (∑i∈s,q i)=∑i∈s,contactM e (q i) := by
  change contactMLinear e (∑i∈s,q i)=_
  exact map_sum (contactMLinear e) q s

theorem centeredContactGram_symm (q v : TangentCoordinates) : centeredContactGram q v=centeredContactGram v q := by
  unfold centeredContactGram
  simp only [real_inner_comm (contactM _ q) (contactM _ v),mul_comm]

theorem centeredContactGram_sum_left {ι : Type*} (s : Finset ι)
    (q : ι → TangentCoordinates) (v : TangentCoordinates) :
    centeredContactGram (∑i∈s,q i) v=∑i∈s,centeredContactGram (q i) v := by
  unfold centeredContactGram
  simp_rw [contactM_sum,sum_inner,inner_sum,stressH_sum_left]
  simp only [Finset.sum_mul,Finset.mul_sum,Finset.sum_div]
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.sum_comm,← Finset.sum_sub_distrib,Finset.mul_sum]
  · rw [Finset.sum_comm]

theorem centeredContactGram_smul_left (c : ℝ) (q v : TangentCoordinates) :
    centeredContactGram (c • q) v=c*centeredContactGram q v := by
  simp only [centeredContactGram,contactM_smul,real_inner_smul_left,real_inner_smul_right,stressH_smul_left]
  simp [mul_assoc,mul_left_comm,mul_comm,Finset.mul_sum,mul_sub,mul_div_assoc]
  rw [← Finset.mul_sum]
  ring

theorem centeredContactGram_synthesis (x y : Fin 8 × Fin 2 → ℝ) :
    centeredContactGram (meanTangentSynthesis x) (meanTangentSynthesis y)=
      ∑j,∑k,x j*y k*centeredContactGram (meanTangentRaw j) (meanTangentRaw k) := by
  unfold meanTangentSynthesis
  rw [centeredContactGram_sum_left]
  apply Finset.sum_congr rfl
  intro j _
  rw [centeredContactGram_smul_left,centeredContactGram_symm,centeredContactGram_sum_left,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [centeredContactGram_smul_left,centeredContactGram_symm]
  ring

#print axioms centeredContactGram_synthesis
end Blueprint.Thomson.Tail.Implementation
