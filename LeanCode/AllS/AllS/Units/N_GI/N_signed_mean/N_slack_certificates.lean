import AllS.Units.N_GI.N_signed_mean.N_tensor_kernel_data

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

def meanUniformSlackFromGram (j : Fin 8) (b c : Fin 2) : MeanRadical :=
  (22/5:ℚ) • meanBlockAData j b c-
  ∑s : Fin 2,∑t : Fin 2,meanRadicalMul (meanRadicalMul (meanBlockAData j b s)
    (meanUniformGramData (finProdFinEquiv (j,s)) (finProdFinEquiv (j,t)))) (meanBlockAData j t c)

def meanUniformMinorFromSlack (j : Fin 8) : MeanRadical :=
  meanRadicalMul (meanUniformSlackData j 0 0) (meanUniformSlackData j 1 1)-
    meanRadicalMul (meanUniformSlackData j 0 1) (meanUniformSlackData j 0 1)

theorem meanUniformSlack_data : ∀j b c,meanUniformSlackFromGram j b c=meanUniformSlackData j b c := by
  decide +kernel

theorem meanUniformSlack_minor : ∀j,meanUniformMinorFromSlack j=meanUniformSlackMinorData j := by
  decide +kernel

def meanRadicalLinearPositive (x : MeanRadical) : Prop :=
  x 2=0 ∧ x 3=0 ∧ 0<x 0+x 1*(14142135623/10000000000:ℚ) ∧
    0<x 0+x 1*(14142135624/10000000000:ℚ)

instance (x : MeanRadical) : Decidable (meanRadicalLinearPositive x) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem meanUniformSlack_positive_data : ∀j,
    meanRadicalLinearPositive (meanUniformSlackData j 0 0) ∧
    meanRadicalLinearPositive (meanUniformSlackMinorData j) := by decide +kernel

theorem meanRadicalLinearPositive_eval {x : MeanRadical} (hx : meanRadicalLinearPositive x) :
    0 < meanRadicalEval x := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hp := Real.sqrt_nonneg (2:ℝ)
  have hl : (14142135623:ℝ)/10000000000 < Real.sqrt 2 := by nlinarith
  have hu : Real.sqrt 2 < (14142135624:ℝ)/10000000000 := by nlinarith
  rcases hx with ⟨h2,h3,hlo,hhi⟩
  have hrl : (0:ℝ) < (x 0:ℝ)+(x 1:ℝ)*((14142135623:ℝ)/10000000000) := by
    have h := (Rat.cast_pos (K:=ℝ)).mpr hlo
    push_cast at h
    exact h
  have hru : (0:ℝ) < (x 0:ℝ)+(x 1:ℝ)*((14142135624:ℝ)/10000000000) := by
    have h := (Rat.cast_pos (K:=ℝ)).mpr hhi
    push_cast at h
    exact h
  simp only [meanRadicalEval,h2,h3,Rat.cast_zero,zero_mul,add_zero]
  by_cases hx1 : 0 ≤ (x 1:ℝ)
  · have := mul_le_mul_of_nonneg_left hl.le hx1
    linarith
  · have := mul_le_mul_of_nonpos_left hu.le (le_of_not_ge hx1)
    linarith

#print axioms meanUniformSlack_data
#print axioms meanUniformSlack_positive_data
#print axioms meanRadicalLinearPositive_eval
end Blueprint.Thomson.Tail.Implementation
