import AllS.Units.N_GI.N_components.N_component_size

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem components_component_unique (Y : Fin 8 → Point) (c : ℝ)
    (hY : ∀i, ‖Y i‖=1) (hc : 0<c) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (i j : Fin 8)
    (hi : ∃k, ContactAdj Y c i k) (hj : ∃k, ContactAdj Y c j k) :
    contactComponent Y c i = contactComponent Y c j := by
  have hci := components_component_size Y c hY hc hcupper hirr i hi
  have hcj := components_component_size Y c hY hc hcupper hirr j hj
  have hinter : ((contactComponent Y c i) ∩ (contactComponent Y c j)).Nonempty := by
    by_contra h
    have hdis : Disjoint (contactComponent Y c i) (contactComponent Y c j) :=
      Finset.disjoint_iff_inter_eq_empty.mpr (Finset.not_nonempty_iff_eq_empty.mp h)
    have hcard := Finset.card_le_univ ((contactComponent Y c i) ∪ (contactComponent Y c j))
    rw [Finset.card_union_of_disjoint hdis] at hcard
    norm_num at hcard
    omega
  obtain ⟨k, hk⟩ := hinter
  obtain ⟨hik, hjk⟩ := Finset.mem_inter.mp hk
  apply contactComponent_eq_of_reachable
  exact ((mem_contactComponent Y c i k).mp hik).trans
    (contactReachable_symm ((mem_contactComponent Y c j k).mp hjk))

#print axioms components_component_unique
end Blueprint.Thomson.Tail.Implementation
