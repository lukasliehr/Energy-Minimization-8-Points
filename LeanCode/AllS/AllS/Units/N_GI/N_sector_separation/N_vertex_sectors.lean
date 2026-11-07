import AllS.Units.N_GI.N_simple_cycles.N_close_cycle
import Lean_Code.CycleVertexSeparation

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem sector_separation_vertex_sectors (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c∈Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hbound : PackingInnerBound c Y) (hirr : PackingIrreducible c Y)
    (v a b : Fin 8) (ha : ContactAdj Y c v a) (hb : ContactAdj Y c v b)
    (hturn : 0 < inner ℝ (crossVec (Y v) (Y a)) (Y b)) :
    ∃δ∈Set.Ioo (0:ℝ) 1,
      ∀x∈sphericalOpenCap (Y v) δ,∀y∈sphericalOpenCap (Y v) δ,
        0 < inner ℝ (crossVec (Y v) (Y a)) x →
        0 < inner ℝ (crossVec (Y b) (Y v)) x →
        (inner ℝ (crossVec (Y v) (Y a)) y<0 ∨
          inner ℝ (crossVec (Y b) (Y v)) y<0) →
        ¬JoinedIn (openSphericalRegion (contactGraphTrace Y c)ᶜ) x y := by
  have hab : a≠b := by
    intro h
    rw [h,crossVec_inner_right] at hturn
    exact lt_irrefl _ hturn
  obtain ⟨C,hv,ha',hb'⟩ := simple_cycles_close_cycle Y c hY.1 hc.1 hcupper hirr v a b ha hb hab
  have hnext : C.vertex (C.next 0)=a := by simpa only [SimpleContactCycle.next_apply,zero_add] using ha'
  have hprev : C.vertex (C.next.symm 0)=b := by rw [C.next_symm_zero];exact hb'
  have ht : 0 < inner ℝ (crossVec (Y (C.vertex 0)) (Y (C.vertex (C.next 0))))
      (Y (C.vertex (C.next.symm 0))) := by simpa only [hv,hnext,hprev] using hturn
  obtain ⟨δ,hδ,hsep⟩ := C.vertex_sectors_not_joined hY hc hbound 0 ht
  simp only [hv,hnext,hprev] at hsep
  refine ⟨δ,hδ,?_⟩
  intro x hx y hy hx1 hx2 hyN hjoined
  apply hsep x hx y hy hx1 hx2 hyN
  obtain ⟨γ,hγ⟩ := hjoined
  refine ⟨γ,fun t => ⟨(hγ t).1,?_⟩⟩
  intro htrace
  exact (hγ t).2 (C.trace_subset_graph htrace)

#print axioms sector_separation_vertex_sectors
end Blueprint.Thomson.Tail.Implementation
