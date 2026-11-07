import AllS.Units.N_GI.N_exterior_irreducible.N_compact_minimum

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

def ExteriorCountMinimum (H : (Fin 8 → Point) → ℝ) (η : ℝ) (Y : Fin 8 → Point) : Prop :=
  ExteriorMinimizer H η Y ∧ ∀Z,ExteriorMinimizer H η Z →
    (packingContacts (packingMaxInner Y) Y).card≤(packingContacts (packingMaxInner Z) Z).card

theorem ExteriorMinimizer.value_eq {H : (Fin 8 → Point) → ℝ} {η : ℝ} {Y Z : Fin 8 → Point}
    (hY : ExteriorMinimizer H η Y) (hZ : ExteriorMinimizer H η Z) : packingMaxInner Y=packingMaxInner Z :=
  le_antisymm (hY.2 hZ.1) (hZ.2 hY.1)

theorem exterior_irreducible_contact_count_minimum (H : (Fin 8 → Point) → ℝ) (η cstar : ℝ)
    (hH : ContinuousOn H packingUnitSet)
    (hstart : ∃Y,Y∈packingExterior H η ∧ packingMaxInner Y≤cstar) :
    ∃Y,ExteriorCountMinimum H η Y ∧ 0<packingMaxInner Y ∧ packingMaxInner Y≤cstar := by
  classical
  obtain ⟨Z,hZ,hZp,hZb⟩ := exterior_irreducible_compact_minimum H η cstar hH hstart
  let Q : ℕ → Prop := fun n=>∃Y,ExteriorMinimizer H η Y ∧ (packingContacts (packingMaxInner Y) Y).card=n
  have hex : ∃n,Q n := ⟨_,Z,hZ,rfl⟩
  obtain ⟨Y,hY,hYcard⟩ := Nat.find_spec hex
  have he : packingMaxInner Y=packingMaxInner Z := hY.value_eq hZ
  refine ⟨Y,⟨hY,?_⟩,by rw [he]; exact hZp,by rw [he]; exact hZb⟩
  intro W hW
  rw [hYcard]
  exact Nat.find_min' hex ⟨W,hW,rfl⟩

#print axioms exterior_irreducible_contact_count_minimum
end Blueprint.Thomson.Tail.Implementation
