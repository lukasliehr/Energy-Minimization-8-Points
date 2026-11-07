import AllS.Units.N_FI.N_generic_moments.N_index_symmetry
import Blueprint.FiniteDefinitions
import Blueprint.Target

/-! Clean generic proof port from upstream commit
50d14bc06bd41f61573eb6a36eedb8d00759af8f, Logarithmic/Thomson8.
Source declarations: TripleSymmetry.onTriples_sym, TripleSymmetry.tripleSum_sym, TripleSymmetry.distinctSum_sym.
Only target type aliases and explicit real symEval replace legacy interfaces. -/
noncomputable section
open scoped BigOperators InnerProductSpace
open Blueprint.Thomson.Finite (Configuration)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Blueprint.Thomson.GenericMoments

noncomputable def symEval (f : ℝ → ℝ → ℝ → ℝ) (u v t : ℝ) : ℝ :=
  (f u v t + f u t v + f v u t + f t u v + f v t u + f t v u) / 6

theorem onTriples_sym (x : Configuration) (f : ℝ → ℝ → ℝ → ℝ) :
    onTriples x (symEval f) = indexSym (onTriples x f) := by
  funext i j k
  simp only [onTriples,symEval,indexSym,real_inner_comm (x k) (x i),
    real_inner_comm (x j) (x i),real_inner_comm (x k) (x j)]
  ring

theorem tripleSum_sym (x : Configuration) (f : ℝ → ℝ → ℝ → ℝ) :
    tripleSum (onTriples x (symEval f)) = tripleSum (onTriples x f) := by
  rw [onTriples_sym,tripleSum_indexSym]

theorem distinctSum_sym (x : Configuration) (f : ℝ → ℝ → ℝ → ℝ) :
    distinctSum (onTriples x (symEval f)) = distinctSum (onTriples x f) := by
  rw [onTriples_sym,distinctSum_indexSym]

end Blueprint.Thomson.GenericMoments
namespace Blueprint.Thomson.Finite
open GenericMoments
theorem generic_moments_onTriples_symmetry (y : Configuration) (f : ℝ → ℝ → ℝ → ℝ) :
    onTriples y (symEval f) = indexSym (onTriples y f) ∧
    tripleSum (onTriples y (symEval f)) = tripleSum (onTriples y f) ∧
    distinctSum (onTriples y (symEval f)) = distinctSum (onTriples y f) := by
  exact ⟨onTriples_sym y f, tripleSum_sym y f, distinctSum_sym y f⟩
#check generic_moments_onTriples_symmetry
#print axioms generic_moments_onTriples_symmetry
end Blueprint.Thomson.Finite
