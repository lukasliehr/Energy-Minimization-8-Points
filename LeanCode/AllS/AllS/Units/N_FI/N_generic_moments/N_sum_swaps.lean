import Blueprint.FiniteDefinitions
import Blueprint.Target

/-! Clean generic proof port from upstream commit
50d14bc06bd41f61573eb6a36eedb8d00759af8f, Logarithmic/Thomson8.
Source declarations: TripleSums.Index, TripleSums.tripleSum, TripleSums.offSum, TripleSymmetry.onTriples, TripleSums.tripleSum_swap12, TripleSums.tripleSum_swap23, TripleSums.distinctSum_swap12, TripleSums.distinctSum_swap23.
Only target type aliases and explicit real symEval replace legacy interfaces. -/
noncomputable section
open scoped BigOperators InnerProductSpace
open Blueprint.Thomson.Finite (Configuration)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Blueprint.Thomson.GenericMoments

abbrev Index := Fin 8

noncomputable abbrev distinctSum (f : Fin 8 → Fin 8 → Fin 8 → ℝ) : ℝ := Finite.DistinctSum f

noncomputable def tripleSum (f : Index → Index → Index → ℝ) : ℝ := ∑ i, ∑ j, ∑ k, f i j k

noncomputable def offSum (f : Index → Index → ℝ) : ℝ := ∑ i, ∑ j, if i≠j then f i j else 0

noncomputable def onTriples (x : Configuration) (f : ℝ → ℝ → ℝ → ℝ)
    (i j k : Index) : ℝ := f ⟪x i,x j⟫_ℝ ⟪x i,x k⟫_ℝ ⟪x j,x k⟫_ℝ

theorem tripleSum_swap12 (f : Index → Index → Index → ℝ) :
    tripleSum (fun i j k => f j i k) = tripleSum f := by
  unfold tripleSum
  rw [Finset.sum_comm]

theorem tripleSum_swap23 (f : Index → Index → Index → ℝ) :
    tripleSum (fun i j k => f i k j) = tripleSum f := by
  unfold tripleSum
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

theorem distinctSum_swap12 (f : Index → Index → Index → ℝ) :
    distinctSum (fun i j k => f j i k) = distinctSum f := by
  unfold distinctSum Finite.DistinctSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  simp only [ne_comm,and_comm,and_left_comm,and_assoc]

theorem distinctSum_swap23 (f : Index → Index → Index → ℝ) :
    distinctSum (fun i j k => f i k j) = distinctSum f := by
  unfold distinctSum Finite.DistinctSum
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  simp only [ne_comm,and_comm,and_left_comm,and_assoc]

end Blueprint.Thomson.GenericMoments
namespace Blueprint.Thomson.Finite
open GenericMoments
theorem generic_moments_sum_swaps (f : Fin 8 → Fin 8 → Fin 8 → ℝ) :
    tripleSum (fun i j k => f j i k) = tripleSum f ∧
    tripleSum (fun i j k => f i k j) = tripleSum f ∧
    distinctSum (fun i j k => f j i k) = distinctSum f ∧
    distinctSum (fun i j k => f i k j) = distinctSum f := by
  exact ⟨tripleSum_swap12 f, tripleSum_swap23 f, distinctSum_swap12 f, distinctSum_swap23 f⟩
#check generic_moments_sum_swaps
#print axioms generic_moments_sum_swaps
end Blueprint.Thomson.Finite
