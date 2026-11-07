import AllS.Units.N_FI.N_counting.N_finite_partitions
import AllS.Units.N_FI.N_counting.N_moment_identity
import AllS.Units.N_FI.N_counting.N_pair_identity

noncomputable section
namespace Blueprint.Thomson.Finite

def TripleCountingContract : Prop :=
  TriplePartitionContract ∧ MomentCountingContract ∧ PairCountingContract ∧
  DistinctSum (fun _ _ _ => 1) = 336

theorem triple_counting_identity : TripleCountingContract := by
  refine ⟨counting_finite_partitions,counting_moment_identity,counting_pair_identity,?_⟩
  simpa using GenericMoments.distinctSum_const 1

#check triple_counting_identity
#print axioms triple_counting_identity
#check TripleCountingContract
#print axioms TripleCountingContract
end Blueprint.Thomson.Finite
