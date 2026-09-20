import Lean_Code.EmptyContactSector

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- An induced contact quadrilateral occupies an actual contact sector.
Its opposite vertex excludes any additional contact direction in the sector. -/
theorem contact_quad_rotation (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (i k : Fin 8) (q r : ContactNeighbor Y c i)
    (hkq : inner ℝ (Y k) (Y q) = c) (hkr : inner ℝ (Y k) (Y r) = c)
    (hdiag : inner ℝ (Y i) (Y k) < c)
    (horient : 0 < inner ℝ (crossVec (Y i) (Y q)) (Y r)) :
    contactRotateAt Y c hY hc i q = r := by
  apply contactRotateAt_eq_of_empty_sector Y c hY hc hirr i q r horient
  intro z hzq hzr hsector
  have hzk : z.val ≠ k := by
    intro heq
    have hcontact := z.property.2
    rw [heq] at hcontact
    rw [hcontact] at hdiag
    exact (lt_irrefl c) hdiag
  have hzq' : z.val ≠ q.val := fun h => hzq (Subtype.ext h)
  have hzr' : z.val ≠ r.val := fun h => hzr (Subtype.ext h)
  apply contact_rhombus_corner_empty (Y i) (Y q) (Y k) (Y r) (Y z) c
    (hY.1 _) (hY.1 _) (hY.1 _) (hY.1 _) hc (hdiag.trans hc.2)
    q.property.2 hkq r.property.2 hkr horient z.property.2
    (hbound k z.val hzk.symm) (hbound z.val q.val hzq') (hbound z.val r.val hzr')
    hsector.1.le
  rw [triple_cyclic]
  exact hsector.2.le

/-- Following one side of a positively oriented induced quadrilateral
continues along its next side. -/
theorem contact_quad_next_tip (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (d : ContactDart Y c) (k l : Fin 8)
    (hjk : inner ℝ (Y d.2.val) (Y k) = c)
    (hkl : inner ℝ (Y k) (Y l) = c) (hli : inner ℝ (Y l) (Y d.1) = c)
    (hdiag : inner ℝ (Y d.2.val) (Y l) < c)
    (horient : 0 < inner ℝ (crossVec (Y d.1) (Y d.2.val)) (Y k)) :
    (contactFaceNext Y c hY hc d).2.val = k := by
  have hkj : k ≠ d.2.val := by
    intro h
    rw [h, crossVec_inner_right] at horient
    exact (lt_irrefl 0) horient
  let q : ContactNeighbor Y c d.2.val := ⟨k, hkj, hjk⟩
  let r : ContactNeighbor Y c d.2.val := (contactReverse Y c d).2
  have hlk : inner ℝ (Y l) (Y q) = c := (real_inner_comm (Y k) (Y l)).trans hkl
  have hrot : contactRotateAt Y c hY hc d.2.val q = r := by
    apply contact_quad_rotation Y c hY hc hirr hbound d.2.val l q r hlk hli hdiag
    change 0 < inner ℝ (crossVec (Y d.2.val) (Y k)) (Y d.1)
    rw [← triple_cyclic]
    exact horient
  have hinv := congrArg (contactRotateAt Y c hY hc d.2.val).symm hrot
  simp only [Equiv.symm_apply_apply] at hinv
  change ((contactRotateAt Y c hY hc d.2.val).symm r).val = k
  rw [← hinv]

end SquareAntiprismVerification
