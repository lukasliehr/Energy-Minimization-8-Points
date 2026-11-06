import AllS.Units.N_GI.N_setup.N_positive_distance
import AllS.Units.N_GI.N_setup.N_aliases

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem setup_assemble (Y : Fin 8 → Point) (hY : IsConfiguration Y) :
    unorderedPairs.card = 28 ∧
    ∀ i j, i ≠ j → 0 < squaredDistance Y i j :=
  ⟨setup_pairs, setup_positive_distance Y hY⟩

end Blueprint.Thomson.Tail.Implementation
