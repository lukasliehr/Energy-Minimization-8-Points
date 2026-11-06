import AllS.Units.N_GI.N_cycle_decomposition.N_decompose

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem cycle_decomposition_assemble (f : Fin 8 → Fin 8 → ℝ)
    (hf : NonnegativeCirculation f) :
    ∃ L : List (ℝ × FlowCycle),
      (∀ b ∈ L, 0 < b.1 ∧ b.2.Positive f) ∧
      (∀ i j, f i j=(L.map (fun b => b.1*b.2.unitFlow i j)).sum) :=
  cycle_decomposition_decompose f hf

#check cycle_decomposition_assemble
#print axioms cycle_decomposition_assemble
end Blueprint.Thomson.Tail.Implementation
