import AllS.Units.N_GI.N_components.N_closed_degree

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem components_component_size (Y : Fin 8 → Point) (c : ℝ)
    (hY : ∀i, ‖Y i‖=1) (hc : 0<c) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (root : Fin 8)
    (hroot : ∃j, ContactAdj Y c root j) :
    5 ≤ (contactComponent Y c root).card := by
  apply three_neighbor_component_size Y c hY hc.le (by linarith)
    (contactComponent Y c root) ⟨root, contactComponent_root Y c root⟩
  intro i hi
  exact components_closed_degree Y c hY hc hcupper hirr root i hroot hi

#print axioms components_component_size
end Blueprint.Thomson.Tail.Implementation
