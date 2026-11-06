import AllS.Units.N_FI.N_generic_moments.N_triple_decomposition
import AllS.Units.N_FI.N_generic_moments.N_pair_count

noncomputable section
open scoped BigOperators
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite

def TriplePartitionContract : Prop :=
  (∀ f : Fin 8 → Fin 8 → Fin 8 → ℝ,
    GenericMoments.tripleSum f = DistinctSum f+
      GenericMoments.offSum (fun i j => f i i j+f i j i+f j i i)+∑ i, f i i i) ∧
  ((Finset.univ : Finset (Fin 8 × Fin 8 × Fin 8)).filter
    (fun p => p.1 ≠ p.2.1 ∧ p.2.1 ≠ p.2.2 ∧ p.2.2 ≠ p.1)).card = 336 ∧
  Fintype.card (Fin 8) = 8
theorem counting_finite_partitions : TriplePartitionContract :=
  ⟨GenericMoments.tripleSum_decomposition, by decide, by decide⟩

#check counting_finite_partitions
#print axioms counting_finite_partitions
#check TriplePartitionContract
#print axioms TriplePartitionContract
end Blueprint.Thomson.Finite
