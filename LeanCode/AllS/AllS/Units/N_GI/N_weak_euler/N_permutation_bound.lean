import AllS.Units.N_G.N_setup
import Lean_Code.PermutationFixedSpace

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

variable {α : Type*} [Fintype α]

theorem weak_euler_permutation_bound (e f : Equiv.Perm α) (a : α)
    (hconnected : ∀ v : EuclideanSpace ℝ α,
      (∀ i, v (e i) = v i) → (∀ i, v (f i) = v i) → ∀ i j, v i = v j) :
    Fintype.card (PermutationOrbit e) + Fintype.card (PermutationOrbit f) +
      Fintype.card (PermutationOrbit (e.trans f)) ≤ Fintype.card α + 2 := by
  have h := permutation_cycle_dimension_bound e f
  have hk := permutation_common_fixed_finrank_le_one e f a hconnected
  omega

#print axioms weak_euler_permutation_bound

end Blueprint.Thomson.Tail.Implementation
