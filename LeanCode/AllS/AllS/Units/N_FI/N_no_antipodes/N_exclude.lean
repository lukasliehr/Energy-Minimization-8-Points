import AllS.Units.N_FI.N_no_antipodes.N_third_vertex
import AllS.Units.N_F.N_contact_order

noncomputable section
namespace Blueprint.Thomson.Finite

def AllowedContacts (a : ℝ) (Y : Fin 8 → Point) : Prop :=
  ∀ i j, i ≠ j → inner ℝ (Y i) (Y j) = -1 ∨
    inner ℝ (Y i) (Y j) ∈ Set.range (contacts a)

theorem no_antipodes_exclude (a : ℝ) (Y : Fin 8 → Point) (ha : physical a)
    (hY : IsConfiguration Y) (hallowed : AllowedContacts a Y) :
    ∀ i j, i ≠ j → inner ℝ (Y i) (Y j) ∈ Set.range (contacts a) := by
  intro i j hij
  rcases hallowed i j hij with h | h
  · have hant := no_antipodes_antipodal_identity (Y i) (Y j) (hY.1 i) (hY.1 j) h
    obtain ⟨k,hki,hkj,hk⟩ := no_antipodes_third_vertex Y hY i j hij
    obtain ⟨_,hki1,_,hkj1⟩ := hk hant
    have hi := (hallowed i k hki.symm).resolve_left hki1
    have hj := (hallowed j k hkj.symm).resolve_left hkj1
    have hn := (contact_order_no_opposites a _ _ ha hi hj).2
    apply False.elim
    apply hn
    rw [hant,inner_neg_left]
    ring
  · exact h

#check no_antipodes_exclude
#print axioms no_antipodes_exclude
end Blueprint.Thomson.Finite
