import AllS.Units.N_FI.N_generic_moments.N_S_R_bridge
import AllS.Units.N_FI.N_generic_moments.N_complex_power_gram
import AllS.Units.N_FI.N_generic_moments.N_frame_features
import AllS.Units.N_FI.N_generic_moments.N_index_symmetry
import AllS.Units.N_FI.N_generic_moments.N_inner_frame
import AllS.Units.N_FI.N_generic_moments.N_kernelQ_complex
import AllS.Units.N_FI.N_generic_moments.N_kernelQ_swap
import AllS.Units.N_FI.N_generic_moments.N_kernel_diagonal
import AllS.Units.N_FI.N_generic_moments.N_matrix_psd
import AllS.Units.N_FI.N_generic_moments.N_moment_entry
import AllS.Units.N_FI.N_generic_moments.N_onTriples_symmetry
import AllS.Units.N_FI.N_generic_moments.N_outer_product_identity
import AllS.Units.N_FI.N_generic_moments.N_pair_count
import AllS.Units.N_FI.N_generic_moments.N_real_power_recurrence
import AllS.Units.N_FI.N_generic_moments.N_spherical_kernel_nonneg
import AllS.Units.N_FI.N_generic_moments.N_spherical_kernel_psd
import AllS.Units.N_FI.N_generic_moments.N_sum_linearity
import AllS.Units.N_FI.N_generic_moments.N_sum_swaps
import AllS.Units.N_FI.N_generic_moments.N_symmetry_counting
import AllS.Units.N_FI.N_generic_moments.N_tangent_normSq
import AllS.Units.N_FI.N_generic_moments.N_tangent_re
import AllS.Units.N_FI.N_generic_moments.N_triple_decomposition
import AllS.Units.N_FI.N_generic_moments.N_two_feature_square
import AllS.Units.N_FI.N_generic_moments.N_unit_frame
import Blueprint.FiniteDefinitions
import Blueprint.Target

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.GenericMoments
open Blueprint.Thomson.Finite (Configuration)

/-- Complete generic moment contract, including equality-use outer products. -/
def GenericMomentContract : Prop :=
  ∀ (m k : ℕ) (y : Configuration), (∀ i, ‖y i‖ = 1) →
    (momentMatrix m k y).PosSemidef ∧
    (∃ v w : Fin 8 → Fin m → ℝ,
      momentMatrix m k y = ∑ i : Fin 8, (fun a c => v i a * v i c + w i a * w i c)) ∧
    (∀ a b : Fin m,
      momentMatrix m k y a b = tripleSum (onTriples y (Sfun k a.val b.val)) ∧
      distinctSum (onTriples y (Rfun k a.val b.val)) = 6 * momentMatrix m k y a b)

theorem generic_moment_soundness : GenericMomentContract := by
  intro m k y hy
  exact ⟨momentMatrix_posSemidef m k y hy,
    momentMatrix_exists_outer_products m k y hy,
    fun a b => ⟨momentMatrix_eq_sum_Sfun m k y a b,
      sum_Rfun_eq_moment m k y hy a b⟩⟩

#check generic_moment_soundness
#print axioms generic_moment_soundness
#check momentMatrix_posSemidef
end Blueprint.Thomson.GenericMoments
