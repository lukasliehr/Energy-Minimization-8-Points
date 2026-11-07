import AllS.Units.N_GI.N_signed_mean.N_gram_exact
import AllS.Units.N_GI.N_signed_mean.N_spectral_inequalities

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem meanPartner_norm_sum (x : Fin 8 × Fin 2 → ℝ) (b : Fin 2) :
    (∑j,meanScalarWeight j*(x (meanPartner j,b))^2)=∑j,meanScalarWeight j*(x (j,b))^2 := by
  norm_num [Fin.sum_univ_succ,Fin.succ,Fin.instOfNat,Fin.ofNat,meanPartner,meanScalarWeight]
  simp [Fin.ext_iff]
  <;> ring

theorem meanTangentSynthesis_norm_split (x : Fin 8 × Fin 2 → ℝ) :
    ‖meanTangentSynthesis x‖^2=(∑j,meanScalarWeight j*(x (j,0))^2)+
      ∑j,meanScalarWeight j*(x (j,1))^2 := by
  rw [meanTangentSynthesis_norm_sq]
  simp [Fintype.sum_prod_type,Fin.sum_univ_two,Finset.sum_add_distrib]

theorem stressH_upper (q : TangentCoordinates) : stressH q q ≤ meanHCeiling*‖q‖^2 := by
  obtain ⟨x,rfl⟩ := meanTangentSynthesis_surjective q
  rw [meanH_synthesis_value]
  unfold meanHValue
  calc
    _ ≤ ∑j,meanScalarWeight j*(meanHCeiling*((x (j,0))^2+(x (meanPartner j,1))^2)) := by
      exact Finset.sum_le_sum (fun j _=>mul_le_mul_of_nonneg_left
        (meanH_block_bound j _ _) (meanScalarWeight_pos j).le)
    _ = _ := by
      simp only [mul_add,Finset.sum_add_distrib]
      simp_rw [mul_left_comm (meanScalarWeight _) meanHCeiling]
      rw [← Finset.mul_sum,← Finset.mul_sum,meanPartner_norm_sum,meanTangentSynthesis_norm_split]
      ring

theorem stressH_strict_upper (q : TangentCoordinates) (hq : q≠0) :
    stressH q q < (413:ℝ)/100*‖q‖^2 := by
  have hp : 0 < ‖q‖^2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hq)
  have h := stressH_upper q
  unfold meanHCeiling at h
  nlinarith

theorem meanBOutput_bound (x : Fin 8 × Fin 2 → ℝ) :
    (∑j,meanScalarWeight j*(meanBOutput x j)^2) ≤ ((399:ℝ)/100)^2*‖meanTangentSynthesis x‖^2 := by
  calc
    _ ≤ ∑j,meanScalarWeight j*(((399:ℝ)/100)^2*((x (meanPartner j,0))^2+(x (j,1))^2)) := by
      exact Finset.sum_le_sum (fun j _=>mul_le_mul_of_nonneg_left
        (meanB_block_bound j _ _) (meanScalarWeight_pos j).le)
    _ = _ := by
      simp only [mul_add,Finset.sum_add_distrib]
      simp_rw [mul_left_comm (meanScalarWeight _) (((399:ℝ)/100)^2)]
      rw [← Finset.mul_sum,← Finset.mul_sum,meanPartner_norm_sum,meanTangentSynthesis_norm_split]
      ring

theorem finite_weighted_cauchy {ι : Type*} [Fintype ι] (w f g : ι → ℝ) (hw : ∀i,0 ≤ w i) :
    (∑i,w i*f i*g i)^2 ≤ (∑i,w i*(f i)^2)*(∑i,w i*(g i)^2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul
  · intro i _
    exact mul_nonneg (hw i) (sq_nonneg _)
  · intro i _
    exact mul_nonneg (hw i) (sq_nonneg _)
  · intro i _
    ring

theorem stressB_bound (q : TangentCoordinates) (b : Fin 8 → ℝ) :
    |stressB q b| ≤ (399:ℝ)/100*‖q‖*‖(WithLp.toLp 2 b : EuclideanSpace ℝ (Fin 8))‖ := by
  obtain ⟨x,rfl⟩ := meanTangentSynthesis_surjective q
  obtain ⟨y,rfl⟩ := meanScalarSynthesis_surjective b
  rw [meanB_synthesis_value]
  have hc := finite_weighted_cauchy meanScalarWeight (meanBOutput x) y (fun j=>(meanScalarWeight_pos j).le)
  rw [← meanScalarSynthesis_norm_sq y] at hc
  have hm := mul_le_mul_of_nonneg_right (meanBOutput_bound x)
    (sq_nonneg ‖(WithLp.toLp 2 (meanScalarSynthesis y) : EuclideanSpace ℝ (Fin 8))‖)
  have ha := sq_abs (∑j,meanScalarWeight j*meanBOutput x j*y j)
  have hn := norm_nonneg (meanTangentSynthesis x)
  have hb := norm_nonneg (WithLp.toLp 2 (meanScalarSynthesis y) : EuclideanSpace ℝ (Fin 8))
  have ht : 0 ≤ (399:ℝ)/100*‖meanTangentSynthesis x‖*
      ‖(WithLp.toLp 2 (meanScalarSynthesis y) : EuclideanSpace ℝ (Fin 8))‖ := by positivity
  nlinarith

theorem stressD_nonneg (b : Fin 8 → ℝ) : 0 ≤ stressD b b := by
  obtain ⟨y,rfl⟩ := meanScalarSynthesis_surjective b
  rw [meanD_synthesis_value]
  exact Finset.sum_nonneg (fun j _=>mul_nonneg
    (mul_nonneg (meanScalarWeight_pos j).le (meanD_conditions j).1) (sq_nonneg _))

theorem stressD_upper (b : Fin 8 → ℝ) :
    stressD b b ≤ (2309:ℝ)/1000*‖(WithLp.toLp 2 b : EuclideanSpace ℝ (Fin 8))‖^2 := by
  obtain ⟨y,rfl⟩ := meanScalarSynthesis_surjective b
  rw [meanD_synthesis_value,meanScalarSynthesis_norm_sq,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have h := mul_le_mul_of_nonneg_right (meanD_conditions j).2
    (mul_nonneg (meanScalarWeight_pos j).le (sq_nonneg (y j)))
  nlinarith

#print axioms stressH_strict_upper
#print axioms stressB_bound
#print axioms stressD_upper
end Blueprint.Thomson.Tail.Implementation
