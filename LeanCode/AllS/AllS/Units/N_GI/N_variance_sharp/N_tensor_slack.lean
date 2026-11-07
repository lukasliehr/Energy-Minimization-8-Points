import AllS.Units.N_GI.N_variance_sharp.N_variance_radical_data
import AllS.Units.N_GI.N_signed_mean.N_slack_certificates
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

def varianceUniformSlackFromGram (j : Fin 8) (b c : Fin 2) : MeanRadical :=
  (15:ℚ) • varianceBlockAData j b c-
  ∑s : Fin 2,∑t : Fin 2,meanRadicalMul (meanRadicalMul (varianceBlockAData j b s)
    (varianceUniformGramData (finProdFinEquiv (j,s)) (finProdFinEquiv (j,t)))) (varianceBlockAData j t c)

def varianceUniformMinorFromSlack (j : Fin 8) : MeanRadical :=
  meanRadicalMul (varianceUniformSlackData j 0 0) (varianceUniformSlackData j 1 1)-
    meanRadicalMul (varianceUniformSlackData j 0 1) (varianceUniformSlackData j 0 1)

theorem varianceUniformSlack_data : ∀j b c,varianceUniformSlackFromGram j b c=varianceUniformSlackData j b c := by
  decide +kernel

theorem varianceUniformSlack_minor : ∀j,varianceUniformMinorFromSlack j=varianceUniformSlackMinorData j := by
  decide +kernel

theorem varianceUniformSlack_symmetric : ∀j,varianceUniformSlackData j 0 1=varianceUniformSlackData j 1 0 := by
  decide +kernel

theorem varianceUniformSlack_positive_data : ∀j,
    meanRadicalLinearPositive (varianceUniformSlackData j 0 0) ∧
    meanRadicalLinearPositive (varianceUniformSlackMinorData j) := by decide +kernel

theorem varianceUniformSlack_leading_positive (j : Fin 8) :
    0 < meanRadicalEval (varianceUniformSlackData j 0 0) :=
  meanRadicalLinearPositive_eval (varianceUniformSlack_positive_data j).1

theorem varianceUniformSlack_minor_positive (j : Fin 8) :
    0 < meanRadicalEval (varianceUniformSlackMinorData j) :=
  meanRadicalLinearPositive_eval (varianceUniformSlack_positive_data j).2

#print axioms varianceUniformSlack_data
#print axioms varianceUniformSlack_positive_data
#print axioms varianceUniformSlack_minor_positive
end Blueprint.Thomson.Tail.Implementation
