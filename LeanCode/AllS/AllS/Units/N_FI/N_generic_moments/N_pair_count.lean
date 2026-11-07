import AllS.Units.N_FI.N_generic_moments.N_sum_linearity
import AllS.Units.N_FI.N_generic_moments.N_sum_swaps
import Blueprint.FiniteDefinitions
import Blueprint.Target

/-! Clean generic proof port from upstream commit
50d14bc06bd41f61573eb6a36eedb8d00759af8f, Logarithmic/Thomson8.
Source declarations: TripleSums.distinctSum_pair, TripleSums.distinctSum_const, SumLinearity.distinctSum_pair13, SumLinearity.distinctSum_pair23.
Only target type aliases and explicit real symEval replace legacy interfaces. -/
noncomputable section
open scoped BigOperators InnerProductSpace
open Blueprint.Thomson.Finite (Configuration)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Blueprint.Thomson.GenericMoments

theorem distinctSum_pair (f : Index → Index → ℝ) :
    distinctSum (fun i j _ => f i j) = 6*offSum f := by
  have h (i j : Index) :
      (∑ k : Index, if i≠j ∧ j≠k ∧ k≠i then f i j else 0) =
        6*(if i≠j then f i j else 0) := by
    fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_succ] <;> ring
  simp only [distinctSum, Finite.DistinctSum,h,offSum,Finset.mul_sum]

theorem distinctSum_const (c : ℝ) : distinctSum (fun _ _ _ => c) = 336*c := by
  rw [distinctSum_pair]
  simp [offSum,Fin.sum_univ_succ]
  ring

theorem distinctSum_pair13 (f : Index → Index → ℝ) :
    distinctSum (fun i _ k => f i k)=6*offSum f :=
  (distinctSum_swap23 (fun i j _ => f i j)).trans (distinctSum_pair f)

theorem distinctSum_pair23 (f : Index → Index → ℝ) :
    distinctSum (fun _ j k => f j k)=6*offSum f :=
  (distinctSum_swap12 (fun i _ k => f i k)).trans (distinctSum_pair13 f)

end Blueprint.Thomson.GenericMoments
namespace Blueprint.Thomson.Finite
open GenericMoments
theorem generic_moments_pair_count (f : Fin 8 → Fin 8 → ℝ) (c : ℝ) :
    distinctSum (fun i j _ => f i j) = 6 * offSum f ∧
    distinctSum (fun i _ k => f i k) = 6 * offSum f ∧
    distinctSum (fun _ j k => f j k) = 6 * offSum f ∧
    distinctSum (fun _ _ _ => c) = 336 * c := by
  exact ⟨distinctSum_pair f, distinctSum_pair13 f, distinctSum_pair23 f, distinctSum_const c⟩
#check generic_moments_pair_count
#print axioms generic_moments_pair_count
end Blueprint.Thomson.Finite
