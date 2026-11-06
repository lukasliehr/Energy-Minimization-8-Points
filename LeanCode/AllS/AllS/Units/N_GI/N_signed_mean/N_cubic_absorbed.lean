import AllS.Units.N_GI.N_signed_mean.N_column_contraction
import AllS.Units.N_GI.N_signed_mean.N_gram_data_exact
import AllS.Units.N_GI.N_signed_mean.N_contraction_data_exact

set_option maxRecDepth 8192
noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem signed_mean_cubic_absorbed : MeanCubicAbsorption := by
  intro q
  have hs (x y : TangentCoordinates) : inner ℝ x (meanAbsorptionOperator y)=
      inner ℝ y (meanAbsorptionOperator x) := by
    rw [← meanAbsorptionOperator_symmetric,real_inner_comm]
  have h := (cubic_square_completion meanAbsorptionOperator meanAbsorptionOperator_nonnegative hs
    q (meanUniformU q) (stressCubic q) ((22/5:ℝ)*‖q‖^4)
    (meanUniformU_contraction meanContractionData_exact q)
    (meanUniformU_norm_bound meanUniformGram_exact q)).1
  rw [meanAbsorptionOperator_inner,real_inner_self_eq_norm_sq] at h
  nlinarith

alias mean_cubic_absorption := signed_mean_cubic_absorbed
#print axioms signed_mean_cubic_absorbed
end Blueprint.Thomson.Tail.Implementation
