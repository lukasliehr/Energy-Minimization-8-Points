import Blueprint.Tail

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Tail.Implementation

/-- The 28 unordered labelled pairs are represented by increasing indices. -/
def unorderedPairs : Finset (Fin 8 × Fin 8) :=
  Finset.univ.filter (fun ij => ij.1 < ij.2)

theorem setup_pairs : unorderedPairs.card = 28 := by decide

@[simp] theorem mem_unorderedPairs (i j : Fin 8) :
    (i, j) ∈ unorderedPairs ↔ i < j := by simp [unorderedPairs]

theorem squaredDistance_symm (Y : Fin 8 → Point) (i j : Fin 8) :
    squaredDistance Y i j = squaredDistance Y j i := by
  simp only [squaredDistance, norm_sub_rev (Y i) (Y j)]

#print axioms setup_pairs
#print axioms squaredDistance_symm
end Blueprint.Thomson.Tail.Implementation
