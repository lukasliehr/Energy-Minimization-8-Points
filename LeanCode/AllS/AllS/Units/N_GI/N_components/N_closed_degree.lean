import AllS.Units.N_GI.N_setup.N_aliases

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem components_closed_degree (Y : Fin 8 → Point) (c : ℝ)
    (hY : ∀i, ‖Y i‖=1) (hc : 0<c) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (root i : Fin 8)
    (hroot : ∃j, ContactAdj Y c root j)
    (hi : i ∈ contactComponent Y c root) :
    3 ≤ (contactNeighborsWithin Y c (contactComponent Y c root) i).card := by
  apply irreducible_degree_in_closed_set Y c hY ⟨hc, by linarith⟩ hirr _ i
    (reachable_nonisolated ((mem_contactComponent Y c root i).mp hi) hroot)
  intro j hij
  exact contactComponent_closed Y c root i j hi hij

end Blueprint.Thomson.Tail.Implementation
