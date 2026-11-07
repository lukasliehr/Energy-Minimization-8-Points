import Blueprint.RootBridge

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem target_congruent_symm {Y Z : Fin 8 → Point} (h : Thomson.Congruent Y Z) :
    Thomson.Congruent Z Y := by
  obtain ⟨U, σ, h⟩ := h
  refine ⟨U.symm, σ.symm, ?_⟩
  intro i
  have hi : Y (σ.symm i) = U (Z i) := by simpa using h (σ.symm i)
  simpa using (congrArg U.symm hi).symm

theorem upstream_bridge_congruence (Y Z : Fin 8 → Point) :
    (Thomson.Congruent Y Z ↔ SquareAntiprismVerification.Congruent Z Y) ∧
    (Thomson.Congruent Y Z ↔ SquareAntiprismVerification.Congruent Y Z) := by
  refine ⟨Iff.rfl, ?_⟩
  change Thomson.Congruent Y Z ↔ Thomson.Congruent Z Y
  exact ⟨target_congruent_symm, target_congruent_symm⟩

#print axioms target_congruent_symm
#print axioms upstream_bridge_congruence
end Blueprint.Thomson.Tail.Implementation
