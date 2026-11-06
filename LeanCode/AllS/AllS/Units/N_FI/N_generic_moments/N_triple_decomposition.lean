import AllS.Units.N_FI.N_generic_moments.N_sum_swaps
import Blueprint.FiniteDefinitions
import Blueprint.Target

/-! Clean generic proof port from upstream commit
50d14bc06bd41f61573eb6a36eedb8d00759af8f, Logarithmic/Thomson8.
Source declarations: TripleSums.tripleSum_decomposition.
Only target type aliases and explicit real symEval replace legacy interfaces. -/
noncomputable section
open scoped BigOperators InnerProductSpace
open Blueprint.Thomson.Finite (Configuration)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Blueprint.Thomson.GenericMoments

theorem tripleSum_decomposition (f : Index → Index → Index → ℝ) :
    tripleSum f = distinctSum f +
      offSum (fun i j => f i i j+f i j i+f j i i) + ∑ i, f i i i := by
  simp only [tripleSum,distinctSum,Finite.DistinctSum,offSum,Fin.sum_univ_succ]
  norm_num [Fin.succ]
  ring

end Blueprint.Thomson.GenericMoments
namespace Blueprint.Thomson.Finite
open GenericMoments
theorem generic_moments_triple_decomposition (f : Index → Index → Index → ℝ) :
    tripleSum f = distinctSum f +
      offSum (fun i j => f i i j+f i j i+f j i i) + ∑ i, f i i i :=
  GenericMoments.tripleSum_decomposition f
#check generic_moments_triple_decomposition
#print axioms generic_moments_triple_decomposition
end Blueprint.Thomson.Finite
