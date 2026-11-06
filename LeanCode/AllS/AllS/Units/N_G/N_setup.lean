import AllS.Units.N_GI.N_setup.N_assemble

noncomputable section
namespace Blueprint.Thomson.Tail

/-- The definitions in this import closure use the target configuration,
the actual upstream contact types, and 28 unordered positive-distance pairs. -/
theorem setup (Y : Fin 8 → Point) (hY : IsConfiguration Y) :
    Implementation.unorderedPairs.card = 28 ∧
    ∀ i j, i ≠ j → 0 < squaredDistance Y i j :=
  Implementation.setup_assemble Y hY

end Blueprint.Thomson.Tail
