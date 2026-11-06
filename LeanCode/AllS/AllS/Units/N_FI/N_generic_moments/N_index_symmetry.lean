import AllS.Units.N_FI.N_generic_moments.N_sum_linearity
import AllS.Units.N_FI.N_generic_moments.N_sum_swaps
import Blueprint.FiniteDefinitions
import Blueprint.Target

/-! Clean generic proof port from upstream commit
50d14bc06bd41f61573eb6a36eedb8d00759af8f, Logarithmic/Thomson8.
Source declarations: TripleSymmetry.indexSym, TripleSymmetry.tripleSum_indexSym, TripleSymmetry.distinctSum_indexSym.
Only target type aliases and explicit real symEval replace legacy interfaces. -/
noncomputable section
open scoped BigOperators InnerProductSpace
open Blueprint.Thomson.Finite (Configuration)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Blueprint.Thomson.GenericMoments

noncomputable def indexSym (f : Index → Index → Index → ℝ) (i j k : Index) : ℝ :=
  (f i j k+f i k j+f j i k+f k i j+f j k i+f k j i)/6

theorem tripleSum_indexSym (f : Index → Index → Index → ℝ) :
    tripleSum (indexSym f)=tripleSum f := by
  have h312 : tripleSum (fun i j k => f k i j)=tripleSum f :=
    (tripleSum_swap23 (fun i j k => f j i k)).trans (tripleSum_swap12 f)
  have h231 : tripleSum (fun i j k => f j k i)=tripleSum f :=
    (tripleSum_swap12 (fun i j k => f i k j)).trans (tripleSum_swap23 f)
  have h321 : tripleSum (fun i j k => f k j i)=tripleSum f :=
    (tripleSum_swap12 (fun i j k => f k i j)).trans h312
  have hsplit : tripleSum (indexSym f) =
      (tripleSum f+tripleSum (fun i j k => f i k j)+tripleSum (fun i j k => f j i k)+
        tripleSum (fun i j k => f k i j)+tripleSum (fun i j k => f j k i)+
        tripleSum (fun i j k => f k j i))/6 := by
    simp only [tripleSum,indexSym]
    simp_rw [← Finset.sum_div,Finset.sum_add_distrib]
  rw [hsplit,tripleSum_swap12 f,tripleSum_swap23 f,h312,h231,h321]
  ring

theorem distinctSum_indexSym (f : Index → Index → Index → ℝ) :
    distinctSum (indexSym f)=distinctSum f := by
  have h312 : distinctSum (fun i j k => f k i j)=distinctSum f :=
    (distinctSum_swap23 (fun i j k => f j i k)).trans (distinctSum_swap12 f)
  have h231 : distinctSum (fun i j k => f j k i)=distinctSum f :=
    (distinctSum_swap12 (fun i j k => f i k j)).trans (distinctSum_swap23 f)
  have h321 : distinctSum (fun i j k => f k j i)=distinctSum f :=
    (distinctSum_swap12 (fun i j k => f k i j)).trans h312
  have hsplit : distinctSum (indexSym f) =
      (distinctSum f+distinctSum (fun i j k => f i k j)+distinctSum (fun i j k => f j i k)+
        distinctSum (fun i j k => f k i j)+distinctSum (fun i j k => f j k i)+
        distinctSum (fun i j k => f k j i))/6 := by
    have he (p : Prop) [Decidable p] (a b c d e g : ℝ) :
        (if p then (a+b+c+d+e+g)/6 else 0) =
          ((if p then a else 0)+(if p then b else 0)+(if p then c else 0)+
            (if p then d else 0)+(if p then e else 0)+(if p then g else 0))/6 := by
      split_ifs <;> ring
    simp only [distinctSum, Finite.DistinctSum,indexSym,he]
    simp_rw [← Finset.sum_div,Finset.sum_add_distrib]
  rw [hsplit,distinctSum_swap12 f,distinctSum_swap23 f,h312,h231,h321]
  ring

end Blueprint.Thomson.GenericMoments
namespace Blueprint.Thomson.Finite
open GenericMoments
theorem generic_moments_index_symmetry (f : Fin 8 → Fin 8 → Fin 8 → ℝ) :
    tripleSum (indexSym f) = tripleSum f ∧ distinctSum (indexSym f) = distinctSum f := by
  exact ⟨tripleSum_indexSym f, distinctSum_indexSym f⟩
#check generic_moments_index_symmetry
#print axioms generic_moments_index_symmetry
end Blueprint.Thomson.Finite
