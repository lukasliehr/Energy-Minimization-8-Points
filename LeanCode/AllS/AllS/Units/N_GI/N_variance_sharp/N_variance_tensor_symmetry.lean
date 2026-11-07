import AllS.Units.N_GI.N_variance_sharp.N_variance_tensor_data
import AllS.Units.N_GI.N_signed_mean.N_radical_operations
set_option maxRecDepth 100000
noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem varianceUniformGramFromU_symm (i j : Fin 16) :
    varianceUniformGramFromU i j=varianceUniformGramFromU j i := by
  unfold varianceUniformGramFromU
  simp only [meanRadicalMul_comm (varianceUniformUData i _ _) (varianceUniformUData j _ _)]

theorem varianceUniformGramData_symm : ∀i j,varianceUniformGramData i j=varianceUniformGramData j i := by decide +kernel
end Blueprint.Thomson.Tail.Implementation
