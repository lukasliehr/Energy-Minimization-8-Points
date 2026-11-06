import AllS.Units.N_GI.N_components.N_two_connected
import Lean_Code.ContactSimpleCycles

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem simple_cycles_avoiding_path (Y : Fin 8 → Point) (c : ℝ)
    (hY : ∀i,‖Y i‖=1) (hc : 0<c) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (v a b : Fin 8)
    (ha : ContactAdj Y c v a) (hb : ContactAdj Y c v b) (hab : a≠b) :
    ∃p : (contactGraphWithout Y c v).Walk a b, p.IsPath ∧ 0<p.length := by
  have haC := contactComponent_closed Y c v v a (contactComponent_root Y c v) ha
  have hbC := contactComponent_closed Y c v v b (contactComponent_root Y c v) hb
  have hreach := components_two_connected Y c hY hc hcupper hirr v ⟨a,ha⟩
    v a b haC hbC ha.1.symm hb.1.symm
  obtain ⟨p⟩ := contact_walk_without_exists hreach
  let q := p.toPath
  refine ⟨q.val,q.property,?_⟩
  by_contra hn
  have hz : q.val.length=0 := by omega
  have hh := q.val.getVert_length
  rw [hz,q.val.getVert_zero] at hh
  exact hab hh

end Blueprint.Thomson.Tail.Implementation
