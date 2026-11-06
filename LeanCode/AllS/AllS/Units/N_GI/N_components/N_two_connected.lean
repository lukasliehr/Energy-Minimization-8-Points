import AllS.Units.N_GI.N_components.N_cut_partition

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem components_two_connected (Y : Fin 8 → Point) (c : ℝ)
    (hY : ∀i, ‖Y i‖=1) (hc : 0<c) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (root : Fin 8)
    (hroot : ∃k, ContactAdj Y c root k) (v i j : Fin 8)
    (hi : i ∈ contactComponent Y c root) (hj : j ∈ contactComponent Y c root)
    (hiv : i≠v) (hjv : j≠v) : ContactReachableWithout Y c v i j := by
  by_contra hnot
  obtain ⟨A,B,hA,hB,hdis,hvA,hvB,hdegA,hdegB⟩ :=
    components_cut_partition Y c hY hc hcupper hirr root hroot v i j hi hj hiv hjv hnot
  exact contact_cut_partition_impossible Y c hY hc.le (by linarith)
    A B v hA hB hdis hvA hvB hdegA hdegB

#print axioms components_two_connected
end Blueprint.Thomson.Tail.Implementation
