import AllS.Units.N_G.N_force_bound
import AllS.Units.N_GI.N_tail_rational.N_analytic_bounds

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def entryDistance : ℝ := tau-33/1000

theorem entryDistance_bounds : 0<entryDistance ∧ entryDistance<29/20 := by
  obtain ⟨_,_,hl,hu,_,_,_,_⟩ := tail_geometric_constants
  dsimp [entryDistance]
  constructor <;> linarith

theorem packing_entry_minimum_attained (Y : Fin 8→Point) (hY : IsConfiguration Y) :
    ∃ m : ℝ, 0< m ∧ (∀ i j : Fin 8, i≠j → m≤ squaredDistance Y i j) ∧
      (∃ i j : Fin 8, i≠j ∧ squaredDistance Y i j=m) ∧ 0<entryDistance ∧ entryDistance<29/20 := by
  obtain ⟨ij,hij,hm⟩ := Finset.exists_min_image unorderedPairs
    (fun ij=>squaredDistance Y ij.1 ij.2) (show unorderedPairs.Nonempty from ⟨(0,1),by decide⟩)
  have hne : ij.1≠ij.2 := ne_of_lt ((mem_unorderedPairs _ _).mp hij)
  refine ⟨squaredDistance Y ij.1 ij.2,setup_positive_distance Y hY _ _ hne,?_,⟨ij.1,ij.2,hne,rfl⟩,entryDistance_bounds⟩
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij | hij
  · exact hm (i,j) ((mem_unorderedPairs _ _).mpr hij)
  · rw [squaredDistance_symm Y i j]
    exact hm (j,i) ((mem_unorderedPairs _ _).mpr hij)

#print axioms packing_entry_minimum_attained
end Blueprint.Thomson.Tail.Implementation
