import AllS.Units.N_FI.N_generic_moments.N_pair_count
import AllS.Units.N_FI.N_generic_moments.N_sum_linearity
import AllS.Units.N_FI.N_generic_moments.N_triple_decomposition
import Blueprint.FiniteDefinitions
import Blueprint.Target

/-! Clean generic proof port from upstream commit
50d14bc06bd41f61573eb6a36eedb8d00759af8f, Logarithmic/Thomson8.
Source declarations: RCounting.repeated_triple_count.
Only target type aliases and explicit real symEval replace legacy interfaces. -/
noncomputable section
open scoped BigOperators InnerProductSpace
open Blueprint.Thomson.Finite (Configuration)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Blueprint.Thomson.GenericMoments

theorem repeated_triple_count (s : ℝ → ℝ → ℝ → ℝ) (c : ℝ)
    (hs12 : ∀ u v t, s u v t=s v u t) (hs23 : ∀ u v t, s u v t=s u t v)
    (hdiag : s 1 1 1=c) (y : Configuration) (hy : ∀ i, ‖y i‖=1) :
    distinctSum (onTriples y (fun u v t => 6*s u v t+s u u 1+s v v 1+s t t 1+c/7)) =
      6*tripleSum (onTriples y s) := by
  let p : Index → Index → ℝ := fun i j => s ⟪y i,y j⟫_ℝ ⟪y i,y j⟫_ℝ 1
  have hrepeated : (fun i j : Index => onTriples y s i i j +
      onTriples y s i j i+onTriples y s j i i) = fun i j => 3*p i j := by
    funext i j
    simp only [onTriples,real_inner_self_eq_norm_sq,hy,one_pow,real_inner_comm (y j) (y i)]
    rw [hs12 1,hs23 _ 1]
    dsimp [p]
    simp only [real_inner_comm]
    ring
  have hdiagonal : (∑ i : Index, onTriples y s i i i)=8*c := by
    simp [onTriples,real_inner_self_eq_norm_sq,hy,hdiag]
  have hdecomp := tripleSum_decomposition (onTriples y s)
  rw [hrepeated,offSum_mul,hdiagonal] at hdecomp
  have hsplit : onTriples y (fun u v t => 6*s u v t+s u u 1+s v v 1+s t t 1+c/7) =
      fun i j k => 6*onTriples y s i j k+p i j+p i k+p j k+c/7 := rfl
  rw [hsplit,distinctSum_add,distinctSum_add,distinctSum_add,distinctSum_add,
    distinctSum_mul,distinctSum_pair,distinctSum_pair13,distinctSum_pair23,distinctSum_const]
  linarith

end Blueprint.Thomson.GenericMoments
namespace Blueprint.Thomson.Finite
open GenericMoments
theorem generic_moments_symmetry_counting (s : ℝ → ℝ → ℝ → ℝ) (c : ℝ)
    (hs12 : ∀ u v t, s u v t=s v u t) (hs23 : ∀ u v t, s u v t=s u t v)
    (hdiag : s 1 1 1=c) (y : Configuration) (hy : ∀ i, ‖y i‖=1) :
    distinctSum (onTriples y (fun u v t => 6*s u v t+s u u 1+s v v 1+s t t 1+c/7)) =
      6*tripleSum (onTriples y s) :=
  GenericMoments.repeated_triple_count s c hs12 hs23 hdiag y hy
#check generic_moments_symmetry_counting
#print axioms generic_moments_symmetry_counting
end Blueprint.Thomson.Finite
