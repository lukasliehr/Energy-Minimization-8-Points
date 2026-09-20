import Lean_Code.ContactLocalStars
import Lean_Code.ContactSectorCover

set_option maxHeartbeats 1500000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

theorem contact_sector_boundary_local (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (v a b : Fin 8) (ha : ContactAdj Y c v a) (hb : ContactAdj Y c v b)
    (hturn : 0 < inner ℝ (crossVec (Y v) (Y a)) (Y b)) :
    ∃ U : Set ℝ³, IsOpen U ∧ Y v ∈ U ∧ ∀ x ∈ U, ‖x‖ = 1 →
      x ∈ sphericalWedgeTrace (crossVec (Y v) (Y a)) (crossVec (Y b) (Y v)) →
      x ∈ contactGraphTrace Y c := by
  have ht' : 0 < inner ℝ (crossVec (Y b) (Y v)) (Y a) := by
    rw [triple_cyclic]
    exact hturn
  obtain ⟨U₁, hU₁, hv₁, hmodel₁⟩ := contact_arc_endpoint_halfplane (Y v) (Y a)
    (crossVec (Y b) (Y v)) c (hY.1 v) (hY.1 a) hc ha.2 (crossVec_inner_right _ _) ht'
  obtain ⟨U₂, hU₂, hv₂, hmodel₂⟩ := contact_arc_endpoint_halfplane (Y v) (Y b)
    (crossVec (Y v) (Y a)) c (hY.1 v) (hY.1 b) hc hb.2 (crossVec_inner_left _ _) hturn
  refine ⟨U₁ ∩ U₂, hU₁.inter hU₂, ⟨hv₁, hv₂⟩, ?_⟩
  intro x hx hxu htrace
  rcases htrace with h | h
  · obtain ⟨r, hr, rfl⟩ := (hmodel₁ x hx.1).mpr ⟨hxu, h.1, h.2⟩
    exact contactGraphTrace_arc Y c ⟨v, a, ha.1.symm, ha.2⟩ r hr
  · have hplane : inner ℝ (crossVec (Y v) (Y b)) x = 0 := by
      have hh := h.1
      rw [crossVec_swap, inner_neg_left] at hh
      exact neg_eq_zero.mp hh
    obtain ⟨r, hr, rfl⟩ := (hmodel₂ x hx.2).mpr ⟨hxu, hplane, h.2⟩
    exact contactGraphTrace_arc Y c ⟨v, b, hb.1.symm, hb.2⟩ r hr

/-- Off-graph unit points near a nonisolated vertex lie strictly inside
one of its consecutive contact sectors. Sector coverage was previously
non-strict; the endpoint arc models now exclude its boundary cases. -/
theorem contact_strict_sectors_cover_locally (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hirr : PackingIrreducible c Y) (v : Fin 8)
    (hne : ∃ j, j ≠ v ∧ inner ℝ (Y v) (Y j) = c) :
    ∃ U : Set ℝ³, IsOpen U ∧ Y v ∈ U ∧ ∀ x ∈ U, ‖x‖ = 1 →
      x ∉ contactGraphTrace Y c → ∃ a : ContactNeighbor Y c v,
        0 < inner ℝ (crossVec (Y v) (Y a)) x ∧
        0 < inner ℝ (crossVec (Y (contactRotateAt Y c hY hc v a)) (Y v)) x := by
  classical
  have hloc (a : ContactNeighbor Y c v) := contact_sector_boundary_local Y c hY hc v a
    (contactRotateAt Y c hY hc v a)
    ⟨a.property.1.symm, a.property.2⟩
    ⟨(contactRotateAt Y c hY hc v a).property.1.symm, (contactRotateAt Y c hY hc v a).property.2⟩
    (by rw [triple_cyclic]; exact contactRotateAt_triple_pos Y c hY hc hirr v a)
  choose U hU hvU hbd using hloc
  refine ⟨⋂ a, U a, isOpen_iInter_of_finite hU, Set.mem_iInter.mpr hvU, ?_⟩
  intro x hx hxu hxoff
  obtain ⟨a, ha₁, ha₂⟩ := contactRotateAt_sectors_cover Y c hY hc hirr v hne x
  have hxU := Set.mem_iInter.mp hx a
  have hne₁ : inner ℝ (crossVec (Y v) (Y a)) x ≠ 0 := by
    intro h
    exact hxoff (hbd a x hxU hxu (Or.inl ⟨h, ha₂⟩))
  have hne₂ : inner ℝ (crossVec (Y (contactRotateAt Y c hY hc v a)) (Y v)) x ≠ 0 := by
    intro h
    exact hxoff (hbd a x hxU hxu (Or.inr ⟨h, ha₁⟩))
  exact ⟨a, lt_of_le_of_ne ha₁ hne₁.symm, lt_of_le_of_ne ha₂ hne₂.symm⟩

end SquareAntiprismVerification
