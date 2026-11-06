import AllS.Units.N_FI.N_congruence.N_lower_diagonals

noncomputable section
namespace Blueprint.Thomson.Finite

theorem congruence_relabel (a : ℝ) (Y : Fin 8 → Point) (hY : IsConfiguration Y)
    (U : Point ≃ₗᵢ[ℝ] Point) (hc : ∀ i, ∃ j, Y i=U (X a j)) : Congruent Y (X a) := by
  choose f hf using hc
  have hi : Function.Injective f := by
    intro i j hij
    apply hY.2
    rw [hf i,hf j,hij]
  exact ⟨U,Equiv.ofBijective f ⟨hi,Finite.surjective_of_injective hi⟩,hf⟩

#check congruence_relabel
#print axioms congruence_relabel
end Blueprint.Thomson.Finite
