import Lean_Code.SupportedTiling

noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace ContactBoundaryCycle

variable {Y : Fin 8 → ℝ³} {c : ℝ} {hY : IsConfiguration Y} {hc : c ∈ Set.Ioo (0 : ℝ) 1}

lemma edge_vertex_nonneg (C : ContactBoundaryCycle Y c hY hc) (hsupport : C.StrictSupport)
    (i k : Fin (C.size + 1)) :
    0 ≤ inner ℝ (crossVec (Y (C.vertex i)) (Y (C.vertex (i + 1)))) (Y (C.vertex k)) := by
  by_cases hk : k = i
  · subst k; simp [crossVec_inner_left]
  by_cases hk' : k = i + 1
  · subst k; simp [crossVec_inner_right]
  exact (hsupport i k hk hk').le

theorem reverse_not_in_cycle (C : ContactBoundaryCycle Y c hY hc)
    (hirr : PackingIrreducible c Y) (hsupport : C.StrictSupport)
    (i j : Fin (C.size + 1)) : C.point j ≠ contactReverse Y c (C.point i) := by
  intro heq
  have hvertex : C.vertex j = C.vertex (i + 1) := by
    rw [C.vertex_next]
    exact congrArg Sigma.fst heq
  have hji : j = i + 1 := C.vertex_injective_of_support hsupport hvertex
  have hback : C.vertex (i + 1 + 1) = C.vertex i := by
    rw [← hji, C.vertex_next]
    exact congrArg (fun d : ContactDart Y c => d.2.val) heq
  have h := C.strict_turn hirr i
  rw [hback, crossVec_inner_left] at h
  exact lt_irrefl 0 h

theorem triangle_contacts (C : ContactBoundaryCycle Y c hY hc) (hlen : C.size + 1 = 3)
    (i j : Fin (C.size + 1)) (hij : i ≠ j) : inner ℝ (Y (C.vertex i)) (Y (C.vertex j)) = c := by
  have hcast : Fin.cast hlen i ≠ Fin.cast hlen j := by
    intro heq
    exact hij (Fin.ext (congrArg (fun k : Fin 3 => k.val) heq))
  exact C.reindex_triangle_contacts hlen (Fin.cast hlen i) (Fin.cast hlen j) hcast

end ContactBoundaryCycle

theorem opposite_boundary_orbit (Y : Fin 8 → ℝ³) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hirr : PackingIrreducible c Y)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport)
    (f : ContactBoundaryOrbit Y c hY hc) (i : Fin ((boundaryOrbitCycle Y c hY hc f).size + 1)) :
    ∃ (g : ContactBoundaryOrbit Y c hY hc) (j : Fin ((boundaryOrbitCycle Y c hY hc g).size + 1)),
      g ≠ f ∧ (boundaryOrbitCycle Y c hY hc g).point j =
        contactReverse Y c ((boundaryOrbitCycle Y c hY hc f).point i) := by
  obtain ⟨⟨g, j⟩, heq⟩ := (cyclePartitionMap_bijective (contactFaceNext Y c hY hc)).2
    (contactReverse Y c ((boundaryOrbitCycle Y c hY hc f).point i))
  refine ⟨g, j, ?_, heq⟩
  intro h
  subst g
  exact (boundaryOrbitCycle Y c hY hc f).reverse_not_in_cycle hirr (hsupport _) i j heq

lemma boundaryArray_ofLength (Y : Fin 8 → ℝ³) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (n : ℕ) (f : BoundaryOfLength Y c hY hc n) (j : Fin n) :
    boundaryArray Y c hY hc n ((Fintype.equivFin (BoundaryOfLength Y c hY hc n)) f) j =
      (boundaryOrbitCycle Y c hY hc f.val).reindex f.property j := by
  unfold boundaryArray
  simp only [Equiv.symm_apply_apply]

theorem supported_tiling_boundary_adjacency (Y : Fin 8 → ℝ³) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c ≤ aInf) (hirr : PackingIrreducible c Y)
    (hbound : PackingInnerBound c Y) (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport) :
    (supportedContactTilingData Y c hY hc hcupper hirr hbound hne hsupport).BoundaryAdjacency := by
  classical
  intro f k
  let b : BoundaryOfLength Y c hY hc 4 := (Fintype.equivFin (BoundaryOfLength Y c hY hc 4)).symm f
  let C := boundaryOrbitCycle Y c hY hc b.val
  let i : Fin (C.size + 1) := Fin.cast b.property.symm k
  have hk : boundaryArray Y c hY hc 4 f k = C.vertex i := rfl
  have hknext : boundaryArray Y c hY hc 4 f (k + 1) = C.vertex (i + 1) := by
    change C.vertex (Fin.cast b.property.symm (k + 1)) = _
    rw [fin_cast_add_one]
  obtain ⟨g, j, hgf, hreverse⟩ := opposite_boundary_orbit Y c hY hc hirr hsupport b.val i
  let D := boundaryOrbitCycle Y c hY hc g
  have hbase : D.vertex j = C.vertex (i + 1) := by
    rw [C.vertex_next]
    exact congrArg Sigma.fst hreverse
  have htip : D.vertex (j + 1) = C.vertex i := by
    rw [D.vertex_next]
    exact congrArg (fun d : ContactDart Y c => d.2.val) hreverse
  have hlength := D.three_or_four_of_support hirr hcupper (hsupport D)
  change (∃ t : Fin 8, (∀ l : Fin 4, t ≠ boundaryArray Y c hY hc 4 f l) ∧
      inner ℝ (Y (boundaryArray Y c hY hc 4 f k)) (Y t) = c ∧
      inner ℝ (Y (boundaryArray Y c hY hc 4 f (k + 1))) (Y t) = c) ∨
    (∃ g' : Fin (Fintype.card (BoundaryOfLength Y c hY hc 4)), g' ≠ f ∧
      ∃ l : Fin 4, boundaryArray Y c hY hc 4 g' l = boundaryArray Y c hY hc 4 f k)
  rcases hlength with h3 | h4
  · left
    let t := D.vertex (j + 1 + 1)
    have hturn := D.strict_turn hirr j
    have houtside : inner ℝ (crossVec (Y (C.vertex i)) (Y (C.vertex (i + 1)))) (Y t) < 0 := by
      rw [hbase, htip, crossVec_swap, inner_neg_left] at hturn
      change 0 < -inner ℝ (crossVec (Y (C.vertex i)) (Y (C.vertex (i + 1)))) (Y t) at hturn
      linarith
    refine ⟨t, ?_, ?_, ?_⟩
    · intro l heq
      have hl := C.edge_vertex_nonneg (hsupport C) i (Fin.cast b.property.symm l)
      change 0 ≤ inner ℝ (crossVec (Y (C.vertex i)) (Y (C.vertex (i + 1))))
        (Y (boundaryArray Y c hY hc 4 f l)) at hl
      rw [← heq] at hl
      linarith
    · rw [hk, ← htip]
      exact D.contact (j + 1)
    · rw [hknext, ← hbase]
      apply D.triangle_contacts h3
      intro h
      have ht := D.strict_turn hirr j
      rw [← h, crossVec_inner_left] at ht
      exact lt_irrefl 0 ht
  · right
    let b' : BoundaryOfLength Y c hY hc 4 := ⟨g, h4⟩
    let f' := (Fintype.equivFin (BoundaryOfLength Y c hY hc 4)) b'
    refine ⟨f', ?_, Fin.cast h4 (j + 1), ?_⟩
    · intro heq
      have hb : b' = b := by
        have h := congrArg (Fintype.equivFin (BoundaryOfLength Y c hY hc 4)).symm heq
        simpa only [f', Equiv.symm_apply_apply] using h
      exact hgf (congrArg Subtype.val hb)
    · rw [hk]
      change boundaryArray Y c hY hc 4 ((Fintype.equivFin (BoundaryOfLength Y c hY hc 4)) b')
        (Fin.cast h4 (j + 1)) = _
      rw [boundaryArray_ofLength]
      exact htip

end SquareAntiprismVerification
