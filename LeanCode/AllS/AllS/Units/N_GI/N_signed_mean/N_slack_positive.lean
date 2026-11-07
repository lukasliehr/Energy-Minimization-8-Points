import AllS.Units.N_GI.N_signed_mean.N_slack_certificates
import AllS.Units.N_GI.N_contact_spectrum.N_block_positivity

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem meanRadicalEval_sub (x y : MeanRadical) :
    meanRadicalEval (x-y)=meanRadicalEval x-meanRadicalEval y := map_sub meanRadicalEvalHom x y

theorem meanUniformSlack_symm : ∀j b c,meanUniformSlackData j b c=meanUniformSlackData j c b := by decide +kernel

theorem meanBlockAData_symm : ∀j b c,meanBlockAData j b c=meanBlockAData j c b := by decide +kernel

theorem meanUniformGramData_block : ∀i j : Fin 8,∀b c : Fin 2,
    meanUniformGramData (finProdFinEquiv (i,b)) (finProdFinEquiv (j,c))=
      if i=j then meanUniformGramData (finProdFinEquiv (i,b)) (finProdFinEquiv (i,c)) else 0 := by decide +kernel

theorem meanUniformSlack_psd (j : Fin 8) (x y : ℝ) :
    0 ≤ meanRadicalEval (meanUniformSlackData j 0 0)*x^2+
      2*meanRadicalEval (meanUniformSlackData j 0 1)*x*y+
      meanRadicalEval (meanUniformSlackData j 1 1)*y^2 := by
  have hd := meanRadicalLinearPositive_eval (meanUniformSlack_positive_data j).1
  have hm := meanRadicalLinearPositive_eval (meanUniformSlack_positive_data j).2
  rw [← meanUniformSlack_minor j] at hm
  simp only [meanUniformMinorFromSlack,meanRadicalEval_sub,meanRadicalEval_mul] at hm
  exact contactBlock_psd _ _ _ x y hd (by simpa only [pow_two] using hm.le)

#print axioms meanUniformSlack_psd
end Blueprint.Thomson.Tail.Implementation
