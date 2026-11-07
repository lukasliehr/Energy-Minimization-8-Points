import AllS.Units.N_GI.N_simple_cycles.N_close_cycle
import Lean_Code.ContactCycleEmbedding

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem sector_separation_edge_sides (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c∈Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hbound : PackingInnerBound c Y) (hirr : PackingIrreducible c Y)
    (v a : Fin 8) (ha : ContactAdj Y c v a) (p : Point) (hp : ‖p‖=1)
    (hpedge : p∈OpenContactArc (Y v) (Y a)) :
    ∃U : Set Point, IsOpen U ∧ p∈U ∧ ∀x∈U,∀y∈U,
      0 < inner ℝ (crossVec (Y v) (Y a)) x →
      inner ℝ (crossVec (Y v) (Y a)) y<0 →
      ¬JoinedIn (openSphericalRegion (contactGraphTrace Y c)ᶜ) x y := by
  obtain ⟨j,k,l,hjv,hkv,hlv,hjk,hjl,hkl,hvj,hvk,hvl⟩ :=
    irreducible_three_neighbors Y c hY.1 hc hirr v ⟨a,ha.1.symm,ha.2⟩
  have hneighbor : ∃b,ContactAdj Y c v b ∧ a≠b := by
    by_cases hja : j=a
    · exact ⟨k,⟨hkv.symm,hvk⟩,hja ▸ hjk⟩
    · exact ⟨j,⟨hjv.symm,hvj⟩,Ne.symm hja⟩
  obtain ⟨b,hb,hab⟩ := hneighbor
  obtain ⟨C,hv,ha',hb'⟩ := simple_cycles_close_cycle Y c hY.1 hc.1 hcupper hirr v a b ha hb hab
  have hp' : p∈OpenContactArc (Y (C.vertex 0)) (Y (C.vertex (C.next 0))) := by
    simpa only [SimpleContactCycle.next_apply,zero_add,hv,ha'] using hpedge
  simpa only [SimpleContactCycle.next_apply,zero_add,hv,ha'] using
    C.edge_sides_not_joined hY hc hbound 0 p hp hp'

#print axioms sector_separation_edge_sides
end Blueprint.Thomson.Tail.Implementation
