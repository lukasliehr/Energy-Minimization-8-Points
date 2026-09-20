import Lean_Code.CycleVertexSeparation
import Lean_Code.ContactSector

set_option maxHeartbeats 1500000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Near a graph vertex only its own incident contact arcs occur. Other
vertices and nonincident arcs are excluded by a finite compact set. -/
theorem contactGraphTrace_local_star (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hbound : PackingInnerBound c Y)
    (v : Fin 8) :
    ∃ U : Set ℝ³, IsOpen U ∧ Y v ∈ U ∧ ∀ x ∈ U,
      x ∈ contactGraphTrace Y c ↔ x = Y v ∨
        ∃ j : ContactNeighbor Y c v, x ∈ closedShortSphereArc (Y v) (Y j) := by
  classical
  let A : Set ℝ³ := Set.range (fun j : {j : Fin 8 // j ≠ v} => Y j.val)
  let B : Set ℝ³ := ⋃ d : {d : ContactDart Y c // d.1 ≠ v ∧ d.2.val ≠ v},
    closedShortSphereArc (Y d.val.1) (Y d.val.2.val)
  have hA : IsCompact A := (Set.finite_range _).isCompact
  have hB : IsCompact B := by
    apply isCompact_iUnion
    intro d
    exact closedShortSphereArc_compact _ _ (hY.1 _) (hY.1 _)
      (contact_endpoints_nonantipodal _ _ (hY.1 _) c hc.1 d.val.2.property.2)
  have hvA : Y v ∉ A := by
    rintro ⟨j, hj⟩
    exact j.property (hY.2 hj)
  have hvB : Y v ∉ B := by
    intro hh
    obtain ⟨d, hd⟩ := Set.mem_iUnion.mp hh
    rcases closedShortSphereArc_cases _ _ _ (hY.1 _) (hY.1 _) hd with h | h | h
    · exact d.property.1 (hY.2 h).symm
    · exact d.property.2 (hY.2 h).symm
    · exact contact_arc_avoids_vertices Y c hY hc hbound _ _ d.val.2.property.1.symm
        d.val.2.property.2 v h
  refine ⟨(A ∪ B)ᶜ, (hA.union hB).isClosed.isOpen_compl, ?_, ?_⟩
  · exact fun h => h.elim hvA hvB
  · intro x hx
    constructor
    · rintro (h | h)
      · obtain ⟨j, rfl⟩ := h
        by_cases hj : j = v
        · exact Or.inl (congrArg Y hj)
        · exact False.elim (hx (Or.inl ⟨⟨j, hj⟩, rfl⟩))
      · obtain ⟨d, hd⟩ := Set.mem_iUnion.mp h
        obtain ⟨i, j, hji, hij⟩ := d
        by_cases hi : i = v
        · subst i
          exact Or.inr ⟨⟨j, hji, hij⟩, hd⟩
        by_cases hj : j = v
        · subst j
          exact Or.inr ⟨⟨i, hji.symm, (real_inner_comm (Y i) (Y v)).trans hij⟩,
            by rwa [closedShortSphereArc_comm]⟩
        · exact False.elim (hx (Or.inr (Set.mem_iUnion.mpr
            ⟨⟨⟨i, j, hji, hij⟩, hi, hj⟩, hd⟩)))
    · rintro (rfl | ⟨j, r, hr, rfl⟩)
      · exact contactGraphTrace_vertex Y c v
      · exact contactGraphTrace_arc Y c ⟨v, j⟩ r hr

lemma closed_arc_strict_normal_right (a b x n : ℝ³)
    (hna : inner ℝ n a = 0) (hx : x ∈ closedShortSphereArc a b)
    (hpos : 0 < inner ℝ n x) : 0 < inner ℝ n b := by
  obtain ⟨r, hr, rfl⟩ := hx
  by_contra h
  have hnb : inner ℝ n b ≤ 0 := le_of_not_gt h
  have hnonpos : inner ℝ n (shortSphereArc a b r) ≤ 0 := by
    simp only [shortSphereArc, sphereNormalize_inner, inner_add_right, inner_smul_right,
      hna, mul_zero, zero_add]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg _))
      (mul_nonpos_of_nonneg_of_nonpos hr.1 hnb)
  exact (not_lt_of_ge hnonpos) hpos

lemma contactRotateAt_sector_empty (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hbound : PackingInnerBound c Y) (hirr : PackingIrreducible c Y)
    (v : Fin 8) (a : ContactNeighbor Y c v) (k : ContactNeighbor Y c v) :
    ¬(0 < inner ℝ (crossVec (Y v) (Y a)) (Y k) ∧
      0 < inner ℝ (crossVec (Y (contactRotateAt Y c hY hc v a)) (Y v)) (Y k)) := by
  let b := contactRotateAt Y c hY hc v a
  let d : ContactDart Y c := ⟨b.val, ⟨v, b.property.1.symm,
    (real_inner_comm (Y v) (Y b)).trans b.property.2⟩⟩
  have hnext : (contactFaceNext Y c hY hc d).2.val = a.val := by
    change ((contactRotateAt Y c hY hc v).symm ((contactRotateAt Y c hY hc v) a)).val = a.val
    rw [Equiv.symm_apply_apply]
  rintro ⟨hleft, hright⟩
  have hl : 0 < inner ℝ (crossVec (Y d.2.val) (Y (contactFaceNext Y c hY hc d).2.val)) (Y k) := by
    simpa only [hnext] using hleft
  have hr : 0 < inner ℝ (crossVec (Y d.2.val) (Y k)) (Y d.1) := by
    change 0 < inner ℝ (crossVec (Y v) (Y k)) (Y b)
    rw [← triple_cyclic (Y b) (Y v) (Y k)]
    exact hright
  have hh := contact_corner_interior_strict Y c hY hc hirr hbound d k.val hl hr
  change inner ℝ (Y v) (Y k) < c at hh
  rw [k.property.2] at hh
  exact lt_irrefl _ hh

/-- Every consecutive sector is genuinely empty of the whole graph in a
fixed neighborhood of its vertex, not just empty of contact directions. -/
theorem contactGraphTrace_local_sectors_empty (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hbound : PackingInnerBound c Y) (hirr : PackingIrreducible c Y) (v : Fin 8) :
    ∃ U : Set ℝ³, IsOpen U ∧ Y v ∈ U ∧
      ∀ a : ContactNeighbor Y c v, ∀ x ∈ U,
        0 < inner ℝ (crossVec (Y v) (Y a)) x →
        0 < inner ℝ (crossVec (Y (contactRotateAt Y c hY hc v a)) (Y v)) x →
        x ∉ contactGraphTrace Y c := by
  obtain ⟨U, hU, hvU, hstar⟩ := contactGraphTrace_local_star Y c hY hc hbound v
  refine ⟨U, hU, hvU, ?_⟩
  intro a x hx hleft hright hgraph
  rcases (hstar x hx).mp hgraph with rfl | ⟨k, hk⟩
  · rw [crossVec_inner_left] at hleft
    exact lt_irrefl _ hleft
  · apply contactRotateAt_sector_empty Y c hY hc hbound hirr v a k
    exact ⟨closed_arc_strict_normal_right _ _ _ _ (crossVec_inner_left _ _) hk hleft,
      closed_arc_strict_normal_right _ _ _ _ (crossVec_inner_right _ _) hk hright⟩

end SquareAntiprismVerification
