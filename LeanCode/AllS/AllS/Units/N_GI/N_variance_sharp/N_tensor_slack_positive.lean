import AllS.Units.N_GI.N_variance_sharp.N_tensor_slack
import AllS.Units.N_GI.N_signed_mean.N_slack_positive
import AllS.Units.N_GI.N_contact_spectrum.N_block_positivity

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem varianceUniformSlack_symm : ∀j b c,varianceUniformSlackData j b c=varianceUniformSlackData j c b := by decide +kernel

theorem varianceBlockAData_symm : ∀j b c,varianceBlockAData j b c=varianceBlockAData j c b := by decide +kernel

theorem varianceUniformGramData_block : ∀i j : Fin 8,∀b c : Fin 2,
    varianceUniformGramData (finProdFinEquiv (i,b)) (finProdFinEquiv (j,c))=
      if i=j then varianceUniformGramData (finProdFinEquiv (i,b)) (finProdFinEquiv (i,c)) else 0 := by decide +kernel

theorem varianceUniformSlack_psd (j : Fin 8) (x y : ℝ) :
    0 ≤ meanRadicalEval (varianceUniformSlackData j 0 0)*x^2+
      2*meanRadicalEval (varianceUniformSlackData j 0 1)*x*y+
      meanRadicalEval (varianceUniformSlackData j 1 1)*y^2 := by
  have hd := meanRadicalLinearPositive_eval (varianceUniformSlack_positive_data j).1
  have hm := meanRadicalLinearPositive_eval (varianceUniformSlack_positive_data j).2
  rw [← varianceUniformSlack_minor j] at hm
  simp only [varianceUniformMinorFromSlack,meanRadicalEval_sub,meanRadicalEval_mul] at hm
  exact contactBlock_psd _ _ _ x y hd (by simpa only [pow_two] using hm.le)

#print axioms varianceUniformSlack_psd
end Blueprint.Thomson.Tail.Implementation
