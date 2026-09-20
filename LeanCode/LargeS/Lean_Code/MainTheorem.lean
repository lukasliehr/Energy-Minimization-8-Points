import Lean_Code.Localization

open Real

noncomputable section

namespace SquareAntiprismVerification

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The verification-side theorem whose unfolded type matches the frozen
Showcase theorem. -/
theorem eventual_global_optimality :
    ∃ a : ℝ → ℝ,
      (∀ s ≥ (0 : ℝ), a s ∈ Set.Ioo 0 1 ∧ F s (a s) = 0 ∧
        ∀ b ∈ Set.Ioo (0 : ℝ) 1, F s b = 0 → b = a s) ∧
      a 0 = (2 * √58 - 13) / 7 ∧
      ∃ S > (83 / 5 : ℝ), ∀ s ≥ S,
        (∀ Y : Fin 8 → ℝ³, IsConfiguration Y →
          E s Y ≥ E s (X (a s)) ∧
          (E s Y = E s (X (a s)) ↔ Congruent Y (X (a s)))) ∧
        ℰ s = E s (X (a s)) := by
  refine ⟨aStar, ?_, aStar_zero, ?_⟩
  · intro s hs
    exact ⟨(aStar_spec s hs).1, (aStar_spec s hs).2, aStar_unique s hs⟩
  · obtain ⟨S₀, hS₀⟩ := large_exponent_conclusion
    let S : ℝ := max S₀ (83 / 5) + 1
    refine ⟨S, ?_, ?_⟩
    · dsimp [S]
      have h : (83 / 5 : ℝ) ≤ max S₀ (83 / 5) := le_max_right _ _
      linarith
    · intro s hs
      apply hS₀ s
      dsimp [S] at hs
      have h : S₀ ≤ max S₀ (83 / 5) := le_max_left _ _
      linarith

end SquareAntiprismVerification

