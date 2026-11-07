import AllS.Units.N_GI.N_variance_sharp.N_column_contraction
import AllS.Units.N_GI.N_variance_sharp.N_gram_data_exact
import AllS.Units.N_GI.N_variance_sharp.N_contraction_data_exact

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem variance_cubic_absorption : VarianceCubicAbsorption := by
  apply variance_absorption_of_full_space_square varianceAbsorptionOperator
    varianceAbsorptionOperator_nonnegative varianceAbsorptionOperator_symmetric
    varianceAbsorptionOperator_quad varianceUniformU
  · intro q hq
    rw [varianceUniformU_contraction varianceContractionData_exact,sliceProjection_eq_self q hq,
      varianceTrilinear_diagonal]
  · intro q _
    exact varianceUniformU_norm_bound varianceUniformGram_exact q

#print axioms variance_cubic_absorption
end Blueprint.Thomson.Tail.Implementation
