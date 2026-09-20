import Lean_Code.ContactSimpleCycles
import Lean_Code.ArcEmbedding

set_option maxHeartbeats 1500000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma closedShortSphereArc_cases (a b x : ℝ³) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hx : x ∈ closedShortSphereArc a b) : x = a ∨ x = b ∨ x ∈ OpenContactArc a b := by
  obtain ⟨r, hr, rfl⟩ := hx
  by_cases hr0 : r = 0
  · exact Or.inl (hr0 ▸ shortSphereArc_zero a b ha)
  by_cases hr1 : r = 1
  · exact Or.inr (Or.inl (hr1 ▸ shortSphereArc_one a b hb))
  · exact Or.inr (Or.inr ⟨r, lt_of_le_of_ne hr.1 (Ne.symm hr0),
      lt_of_le_of_ne hr.2 hr1, rfl⟩)

namespace SimpleContactCycle

def next {Y : Fin 8 → ℝ³} {c : ℝ} (C : SimpleContactCycle Y c) :
    Equiv.Perm (Fin (C.size + 2)) := Equiv.addRight 1

@[simp] lemma next_apply {Y : Fin 8 → ℝ³} {c : ℝ} (C : SimpleContactCycle Y c)
    (i : Fin (C.size + 2)) : C.next i = i + 1 := rfl

lemma next_next_ne {Y : Fin 8 → ℝ³} {c : ℝ} (C : SimpleContactCycle Y c)
    (i : Fin (C.size + 2)) : C.next (C.next i) ≠ i := by
  intro heq
  have hh : i + (1 + 1 : Fin (C.size + 2)) = i + 0 := by
    simpa only [next_apply, add_assoc, add_zero] using heq
  have hc := congrArg Fin.val (add_left_cancel hh)
  have hsize := C.size_pos
  norm_num [Fin.val_add, Nat.mod_eq_of_lt (show 2 < C.size + 2 by omega)] at hc

lemma edges_distinct {Y : Fin 8 → ℝ³} {c : ℝ} (C : SimpleContactCycle Y c)
    (i j : Fin (C.size + 2)) (hij : j ≠ i) :
    ¬((C.vertex i = C.vertex j ∧ C.vertex (C.next i) = C.vertex (C.next j)) ∨
      (C.vertex i = C.vertex (C.next j) ∧ C.vertex (C.next i) = C.vertex j)) := by
  rintro (h | h)
  · exact hij (C.injective h.1).symm
  · have h1 := C.injective h.1
    have h2 := C.injective h.2
    exact C.next_next_ne i ((congrArg C.next h2).trans h1.symm)

lemma edge_avoids_other_edges {Y : Fin 8 → ℝ³} {c : ℝ} (C : SimpleContactCycle Y c)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hbound : PackingInnerBound c Y)
    (i : Fin (C.size + 2)) (p : ℝ³)
    (hp : p ∈ OpenContactArc (Y (C.vertex i)) (Y (C.vertex (C.next i)))) :
    ∀ j, j ≠ i → p ∉ closedShortSphereArc (Y (C.vertex j)) (Y (C.vertex (C.next j))) := by
  intro j hji hj
  have hiAdj := C.adjacent i
  have hjAdj := C.adjacent j
  rcases closedShortSphereArc_cases _ _ _ (hY.1 _) (hY.1 _) hj with rfl | rfl | hjopen
  · exact contact_arc_avoids_vertices Y c hY hc hbound _ _ hiAdj.1 hiAdj.2 _ hp
  · exact contact_arc_avoids_vertices Y c hY hc hbound _ _ hiAdj.1 hiAdj.2 _ hp
  · exact Set.disjoint_left.mp
      (contact_graph_arcs_disjoint Y c hY hc hbound _ _ _ _ hiAdj.1 hjAdj.1 hiAdj.2 hjAdj.2
        (C.edges_distinct i j hji)) hp hjopen

lemma trace_subset_graph {Y : Fin 8 → ℝ³} {c : ℝ} (C : SimpleContactCycle Y c) :
    cycleArcTrace C.next (Y ∘ C.vertex) ⊆ contactGraphTrace Y c := by
  intro x hx
  obtain ⟨i, r, hr, rfl⟩ := Set.mem_iUnion.mp hx
  let d : ContactDart Y c := ⟨C.vertex i, C.vertex (C.next i),
    (C.adjacent i).1.symm, (C.adjacent i).2⟩
  exact contactGraphTrace_arc Y c d r hr

/-- Every simple contact cycle separates the local sides of each of its
edges even in the complement of the entire contact graph. -/
theorem edge_sides_not_joined {Y : Fin 8 → ℝ³} {c : ℝ} (C : SimpleContactCycle Y c)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hbound : PackingInnerBound c Y)
    (i : Fin (C.size + 2)) (p : ℝ³) (hp : ‖p‖ = 1)
    (hpedge : p ∈ OpenContactArc (Y (C.vertex i)) (Y (C.vertex (C.next i)))) :
    ∃ U : Set ℝ³, IsOpen U ∧ p ∈ U ∧ ∀ x ∈ U, ∀ y ∈ U,
      0 < inner ℝ (crossVec (Y (C.vertex i)) (Y (C.vertex (C.next i)))) x →
      inner ℝ (crossVec (Y (C.vertex i)) (Y (C.vertex (C.next i)))) y < 0 →
      ¬JoinedIn (openSphericalRegion (contactGraphTrace Y c)ᶜ) x y := by
  obtain ⟨U, hU, hpU, hsep⟩ := cycle_edge_sides_not_joined C.next (Y ∘ C.vertex) c
    (fun j => hY.1 _) hc (fun j => (C.adjacent j).2) i p hp hpedge
    (C.edge_avoids_other_edges hY hc hbound i p hpedge)
  refine ⟨U, hU, hpU, ?_⟩
  intro x hx y hy hxs hys hjoined
  apply hsep x hx y hy hxs hys
  obtain ⟨γ, hγ⟩ := hjoined
  refine ⟨γ, fun t => ⟨(hγ t).1, ?_⟩⟩
  intro htrace
  exact (hγ t).2 (C.trace_subset_graph htrace)

end SimpleContactCycle

/-- The sides of every actual contact edge are separated in the graph
complement; no face decomposition is assumed. -/
theorem contact_edge_sides_not_joined (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c ≤ aInf)
    (hbound : PackingInnerBound c Y) (hirr : PackingIrreducible c Y)
    (v a : Fin 8) (ha : ContactAdj Y c v a) (p : ℝ³) (hp : ‖p‖ = 1)
    (hpedge : p ∈ OpenContactArc (Y v) (Y a)) :
    ∃ U : Set ℝ³, IsOpen U ∧ p ∈ U ∧ ∀ x ∈ U, ∀ y ∈ U,
      0 < inner ℝ (crossVec (Y v) (Y a)) x →
      inner ℝ (crossVec (Y v) (Y a)) y < 0 →
      ¬JoinedIn (openSphericalRegion (contactGraphTrace Y c)ᶜ) x y := by
  obtain ⟨j, k, l, hjv, hkv, hlv, hjk, hjl, hkl, hvj, hvk, hvl⟩ :=
    irreducible_three_neighbors Y c hY.1 hc hirr v ⟨a, ha.1.symm, ha.2⟩
  have hneighbor : ∃ b, ContactAdj Y c v b ∧ a ≠ b := by
    by_cases hja : j = a
    · exact ⟨k, ⟨hkv.symm, hvk⟩, hja ▸ hjk⟩
    · exact ⟨j, ⟨hjv.symm, hvj⟩, Ne.symm hja⟩
  obtain ⟨b, hb, hab⟩ := hneighbor
  obtain ⟨C, hv, ha', hb'⟩ := simple_contact_cycle_through_neighbors Y c hY.1 hc.1 hcupper
    hirr v a b ha hb hab
  have hp' : p ∈ OpenContactArc (Y (C.vertex 0)) (Y (C.vertex (C.next 0))) := by
    simpa only [SimpleContactCycle.next_apply, zero_add, hv, ha'] using hpedge
  simpa only [SimpleContactCycle.next_apply, zero_add, hv, ha'] using
    C.edge_sides_not_joined hY hc hbound 0 p hp hp'

end SquareAntiprismVerification
