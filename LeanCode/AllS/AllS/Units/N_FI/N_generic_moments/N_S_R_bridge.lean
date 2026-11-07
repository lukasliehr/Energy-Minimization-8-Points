import AllS.Units.N_FI.N_generic_moments.N_kernel_diagonal
import AllS.Units.N_FI.N_generic_moments.N_moment_entry
import AllS.Units.N_FI.N_generic_moments.N_onTriples_symmetry
import AllS.Units.N_FI.N_generic_moments.N_symmetry_counting
import Blueprint.FiniteDefinitions
import Blueprint.Target

/-! Generic all-parameter proof. S/R identities adapt upstream RCounting
(commit50d14bc06bd41f61573eb6a36eedb8d00759af8f); outer products expand
the explicit proved tangent features. No fixed-exponent certificate. -/
noncomputable section
open scoped BigOperators InnerProductSpace
open Blueprint.Thomson.Finite (Configuration)
namespace Blueprint.Thomson.GenericMoments
noncomputable def Rfun (k a b : ℕ) (u v t : ℝ) : ℝ :=
  6 * Sfun k a b u v t + Sfun k a b u u 1 + Sfun k a b v v 1 +
    Sfun k a b t t 1 + (if k=0 then 1 else 0)/7

theorem symEval_swap12 (f : ℝ → ℝ → ℝ → ℝ) (u v t : ℝ) :
    symEval f u v t = symEval f v u t := by unfold symEval; ring

theorem symEval_swap23 (f : ℝ → ℝ → ℝ → ℝ) (u v t : ℝ) :
    symEval f u v t = symEval f u t v := by unfold symEval; ring

theorem momentMatrix_eq_sum_Sfun (m k : ℕ) (y : Configuration) (a b : Fin m) :
    momentMatrix m k y a b = tripleSum (onTriples y (Sfun k a.val b.val)) := by
  rw [momentMatrix_entry]
  exact (tripleSum_sym y (fun u v t => u^a.val * v^b.val * kernelQ k u v t)).symm

theorem sum_Rfun_eq_moment (m k : ℕ) (y : Configuration) (hy : ∀ i, ‖y i‖=1)
    (a b : Fin m) :
    distinctSum (onTriples y (Rfun k a.val b.val)) = 6 * momentMatrix m k y a b := by
  rw [momentMatrix_eq_sum_Sfun]
  unfold Rfun
  apply repeated_triple_count
  · intro u v t
    exact symEval_swap12 _ u v t
  · intro u v t
    exact symEval_swap23 _ u v t
  · exact Sfun_diagonal k a.val b.val
  · exact hy

end Blueprint.Thomson.GenericMoments
namespace Blueprint.Thomson.Finite
open GenericMoments

theorem generic_moments_S_R_bridge (m k : ℕ) (y : Configuration)
    (hy : ∀ i, ‖y i‖=1) (a b : Fin m) :
    momentMatrix m k y a b = tripleSum (onTriples y (Sfun k a.val b.val)) ∧
    distinctSum (onTriples y (Rfun k a.val b.val)) = 6 * momentMatrix m k y a b := by
  exact ⟨momentMatrix_eq_sum_Sfun m k y a b, sum_Rfun_eq_moment m k y hy a b⟩
end Blueprint.Thomson.Finite

#check Blueprint.Thomson.Finite.generic_moments_S_R_bridge
#print axioms Blueprint.Thomson.Finite.generic_moments_S_R_bridge
