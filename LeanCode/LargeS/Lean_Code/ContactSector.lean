import Lean_Code.CircleGapInterior
import Lean_Code.RotationSystem
import Lean_Code.TangentAngles
import Lean_Code.TangentWedge

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace ContactOrderData

variable {Y : Fin 8 → ℝ³} {c : ℝ} {i : Fin 8}

theorem gap_le_angle (D : ContactOrderData Y c i) (hY : ∀ j, ‖Y j‖ = 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (u v : Fin (D.size + 1))
    (htriple : 0 < inner ℝ (crossVec (Y (D.label u)) (Y (D.label v))) (Y i)) :
    D.gap u ≤ contactAngle c (Y (D.label u)) (Y (D.label v)) := by
  have ht := contactPhase_triple (Y i) (Y (D.label u)) (Y (D.label v)) c
    (hY i) (hY _) (hY _) hc (D.contact u).2 (D.contact v).2
  have hsin : 0 < Real.sin (D.phase v - D.phase u) := by
    rw [ht] at htriple
    by_contra h
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (norm_nonneg (crossVec (Y i) (Y (D.label u))))
        (norm_nonneg (crossVec (Y i) (Y (D.label v))))) (le_of_not_gt h)
    exact (not_lt_of_ge hnonpos) htriple
  have hvu : v ≠ u := by
    intro h
    subst v
    simp at hsin
  rw [contactPhase_angle (Y i) _ _ c (hY i) (hY _) (hY _) hc (D.contact u).2 (D.contact v).2]
  exact circleGap_le_angle_of_positive_sin D.phase D.increasing (D.phase_range hY hc) u v hvu hsin

theorem successor_minimal_angle (D : ContactOrderData Y c i) (hY : ∀ j, ‖Y j‖ = 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hirr : PackingIrreducible c Y)
    (q k : ContactNeighbor Y c i)
    (htriple : 0 < inner ℝ (crossVec (Y q) (Y k)) (Y i)) :
    contactAngle c (Y q) (Y (D.successor q)) ≤ contactAngle c (Y q) (Y k) := by
  obtain ⟨u, rfl⟩ := D.labelEquiv.surjective q
  obtain ⟨v, rfl⟩ := D.labelEquiv.surjective k
  simp only [D.successor_label, D.labelEquiv_val]
  rw [← D.gap_eq_contactAngle hY hc hirr u]
  exact D.gap_le_angle hY hc u v htriple

end ContactOrderData

theorem contactRotateAt_minimal_angle (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hirr : PackingIrreducible c Y) (i : Fin 8) (q k : ContactNeighbor Y c i)
    (htriple : 0 < inner ℝ (crossVec (Y q) (Y k)) (Y i)) :
    contactAngle c (Y q) (Y (contactRotateAt Y c hY hc i q)) ≤ contactAngle c (Y q) (Y k) := by
  classical
  have hne : ∃ j, j ≠ i ∧ inner ℝ (Y i) (Y j) = c := ⟨q, q.property⟩
  unfold contactRotateAt
  rw [dif_pos hne]
  exact (Classical.choice (contact_order_exists Y c i hY hc hne)).successor_minimal_angle
    hY.1 hc hirr q k htriple

/-- A boundary corner cannot skip an actual contact ray in its interior. -/
theorem contactFaceNext_no_interior_contact (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hirr : PackingIrreducible c Y) (d : ContactDart Y c) (k : ContactNeighbor Y c d.2.val)
    (htriple : 0 < inner ℝ (crossVec (Y (contactFaceNext Y c hY hc d).2.val) (Y k)) (Y d.2.val)) :
    ¬ contactAngle c (Y (contactFaceNext Y c hY hc d).2.val) (Y k) <
      contactAngle c (Y (contactFaceNext Y c hY hc d).2.val) (Y d.1) := by
  let e := contactFaceNext Y c hY hc d
  have he : contactRotateAt Y c hY hc d.2.val e.2 = (contactReverse Y c d).2 := by
    change contactRotateAt Y c hY hc d.2.val
      ((contactRotateAt Y c hY hc d.2.val).symm (contactReverse Y c d).2) = _
    exact (contactRotateAt Y c hY hc d.2.val).apply_symm_apply _
  have h := contactRotateAt_minimal_angle Y c hY hc hirr d.2.val e.2 k htriple
  rw [he] at h
  exact not_lt_of_ge h

theorem contact_corner_interior_strict (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (d : ContactDart Y c) (k : Fin 8)
    (hleft : 0 < inner ℝ (crossVec (Y d.2.val) (Y (contactFaceNext Y c hY hc d).2.val)) (Y k))
    (hright : 0 < inner ℝ (crossVec (Y d.2.val) (Y k)) (Y d.1)) :
    inner ℝ (Y d.2.val) (Y k) < c := by
  let e := contactFaceNext Y c hY hc d
  have hkp : k ≠ d.2.val := by
    intro heq
    rw [heq, crossVec_inner_left] at hleft
    exact (lt_irrefl 0) hleft
  have hle := hbound d.2.val k hkp.symm
  by_contra hnot
  have hpk : inner ℝ (Y d.2.val) (Y k) = c := le_antisymm hle (le_of_not_gt hnot)
  have hpq : inner ℝ (Y d.2.val) (Y e.2.val) = c := e.2.property.2
  have hpr : inner ℝ (Y d.2.val) (Y d.1) = c :=
    (real_inner_comm (Y d.1) (Y d.2.val)).trans d.2.property.2
  have hfull := contactFaceNext_triple_pos Y c hY hc hirr d
  rw [triple_cyclic] at hfull
  have hadd := sphereVertexAngle_add (Y d.2.val) (Y e.2.val) (Y k) (Y d.1)
    (hY.1 _) (hY.1 _) (hY.1 _) (hY.1 _) hleft hright hfull
  have hpositive := sphereVertexAngle_pos (Y d.2.val) (Y k) (Y d.1)
    (hY.1 _) (hY.1 _) (hY.1 _) hright
  rw [sphereVertexAngle_eq_contactAngle _ _ _ c (hY.1 _) (hY.1 _) (hY.1 _) hc hpq hpk,
    sphereVertexAngle_eq_contactAngle _ _ _ c (hY.1 _) (hY.1 _) (hY.1 _) hc hpk hpr,
    sphereVertexAngle_eq_contactAngle _ _ _ c (hY.1 _) (hY.1 _) (hY.1 _) hc hpq hpr] at hadd
  rw [sphereVertexAngle_eq_contactAngle _ _ _ c (hY.1 _) (hY.1 _) (hY.1 _) hc hpk hpr] at hpositive
  have hangle : contactAngle c (Y e.2.val) (Y k) < contactAngle c (Y e.2.val) (Y d.1) := by
    linarith
  have htriple : 0 < inner ℝ (crossVec (Y e.2.val) (Y k)) (Y d.2.val) := by
    rwa [← triple_cyclic]
  exact contactFaceNext_no_interior_contact Y c hY hc hirr d ⟨k, hkp, hpk⟩ htriple hangle

end SquareAntiprismVerification
