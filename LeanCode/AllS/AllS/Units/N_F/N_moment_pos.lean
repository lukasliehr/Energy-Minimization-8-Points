import AllS.Units.N_FI.N_moment_pos.N_scalar_weights
import AllS.Units.N_FI.N_moment_pos.N_weighted_outer_products
import AllS.Units.N_FI.N_moment_pos.N_nonnegative_pairing

namespace Blueprint.Thomson.Finite

theorem moment_sum_positive : ScalarWeightsContract ∧ WeightedOuterProductsContract ∧
    GramPairingNonnegativeContract :=
  ⟨moment_pos_scalar_weights,moment_pos_weighted_outer_products,moment_pos_nonnegative_pairing⟩

#check moment_sum_positive
#print axioms moment_sum_positive
end Blueprint.Thomson.Finite
