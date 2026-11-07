import AllS.Units.N_GI.N_simple_cycles.N_avoiding_path

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem simple_cycles_close_cycle (Y : Fin 8 → Point) (c : ℝ)
    (hY : ∀i,‖Y i‖=1) (hc : 0<c) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (v a b : Fin 8)
    (ha : ContactAdj Y c v a) (hb : ContactAdj Y c v b) (hab : a≠b) :
    ∃C : SimpleContactCycle Y c,
      C.vertex 0=v ∧ C.vertex 1=a ∧ C.vertex (Fin.last (C.size+1))=b := by
  obtain ⟨p,hpath,hlen⟩ := simple_cycles_avoiding_path Y c hY hc hcupper hirr v a b ha hb hab
  let C : SimpleContactCycle Y c :=
    ⟨p.length,hlen,cycleVertexOfPath p,
      cycleVertexOfPath_injective p hpath ha.1.symm,
      cycleVertexOfPath_adjacent p ha hb⟩
  refine ⟨C,?_,?_,?_⟩
  · simp [C,cycleVertexOfPath]
  · simp [C,cycleVertexOfPath]
  · simp [C,cycleVertexOfPath]

#print axioms simple_cycles_close_cycle
end Blueprint.Thomson.Tail.Implementation
