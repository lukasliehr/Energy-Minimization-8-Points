import AllS.Units.N_GI.N_cycle_decomposition.N_assemble

noncomputable section
namespace Blueprint.Thomson.Tail
open Implementation

theorem cycle_decomposition (f : Fin 8 → Fin 8 → ℝ)
    (hf : NonnegativeCirculation f) :
    ∃ L : List (ℝ × FlowCycle),
      (∀ b ∈ L, 0 < b.1 ∧ b.2.Positive f) ∧
      (∀ i j, f i j=(L.map (fun b => b.1*b.2.unitFlow i j)).sum) :=
  cycle_decomposition_assemble f hf

#check cycle_decomposition
#print axioms cycle_decomposition
end Blueprint.Thomson.Tail
