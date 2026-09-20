import Lean_Code.ContactSector
import Lean_Code.VoronoiRegions
import Lean_Code.RhombusOrientation

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace ContactOrderData

theorem successor_strict_minimal_angle {Y : Fin 8 → ℝ³} {c : ℝ} {i : Fin 8}
    (D : ContactOrderData Y c i) (hY : ∀ j, ‖Y j‖ = 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hirr : PackingIrreducible c Y)
    (q k : ContactNeighbor Y c i) (hne : k ≠ D.successor q)
    (htriple : 0 < inner ℝ (crossVec (Y q) (Y k)) (Y i)) :
    contactAngle c (Y q) (Y (D.successor q)) < contactAngle c (Y q) (Y k) := by
  obtain ⟨u, rfl⟩ := D.labelEquiv.surjective q
  obtain ⟨v, rfl⟩ := D.labelEquiv.surjective k
  simp only [D.successor_label, D.labelEquiv_val] at *
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
  have hvnext : v ≠ u + 1 := by
    intro h
    exact hne (congrArg D.labelEquiv h)
  rw [← D.gap_eq_contactAngle hY hc hirr u,
    contactPhase_angle (Y i) _ _ c (hY i) (hY _) (hY _) hc (D.contact u).2 (D.contact v).2]
  exact circleGap_lt_angle_of_positive_sin D.phase D.increasing (D.phase_range hY hc)
    u v hvu hvnext hsin

end ContactOrderData

theorem contactRotateAt_strict_minimal_angle (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hirr : PackingIrreducible c Y) (i : Fin 8) (q k : ContactNeighbor Y c i)
    (hne : k ≠ contactRotateAt Y c hY hc i q)
    (htriple : 0 < inner ℝ (crossVec (Y q) (Y k)) (Y i)) :
    contactAngle c (Y q) (Y (contactRotateAt Y c hY hc i q)) < contactAngle c (Y q) (Y k) := by
  classical
  have hneigh : ∃ j, j ≠ i ∧ inner ℝ (Y i) (Y j) = c := ⟨q, q.property⟩
  unfold contactRotateAt at *
  rw [dif_pos hneigh] at *
  exact (Classical.choice (contact_order_exists Y c i hY hc hneigh)).successor_strict_minimal_angle
    hY.1 hc hirr q k hne htriple

/-- An empty, positively oriented sector joins consecutive actual contact
directions. This is the converse of the earlier no-skipped-contact lemma. -/
theorem contactRotateAt_eq_of_empty_sector (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hirr : PackingIrreducible c Y) (i : Fin 8) (q r : ContactNeighbor Y c i)
    (hqr : 0 < inner ℝ (crossVec (Y i) (Y q)) (Y r))
    (hempty : ∀ k : ContactNeighbor Y c i, k ≠ q → k ≠ r →
      ¬ (0 < inner ℝ (crossVec (Y i) (Y q)) (Y k) ∧
         0 < inner ℝ (crossVec (Y i) (Y k)) (Y r))) :
    contactRotateAt Y c hY hc i q = r := by
  let k := contactRotateAt Y c hY hc i q
  have hqk : 0 < inner ℝ (crossVec (Y i) (Y q)) (Y k) := by
    rw [triple_cyclic]
    exact contactRotateAt_triple_pos Y c hY hc hirr i q
  have hkq : k ≠ q := by
    intro h
    rw [h, crossVec_inner_right] at hqk
    exact (lt_irrefl 0) hqk
  by_contra hkr
  have hlt := contactRotateAt_strict_minimal_angle Y c hY hc hirr i q r (Ne.symm hkr)
    (by rwa [← triple_cyclic])
  have hangle : sphereVertexAngle (Y i) (Y q) (Y k) < sphereVertexAngle (Y i) (Y q) (Y r) := by
    rw [sphereVertexAngle_eq_contactAngle _ _ _ c (hY.1 _) (hY.1 _) (hY.1 _) hc
      q.property.2 k.property.2,
      sphereVertexAngle_eq_contactAngle _ _ _ c (hY.1 _) (hY.1 _) (hY.1 _) hc
      q.property.2 r.property.2]
    exact hlt
  have hkr' := sphere_triple_pos_of_vertexAngle_lt (Y i) (Y q) (Y k) (Y r)
    (hY.1 _) (hY.1 _) (hY.1 _) (hY.1 _) hqk hqr hangle
  exact hempty k hkq hkr ⟨hqk, hkr'⟩

/-- No further contact direction fits inside a rhombus corner when its
opposite vertex has no larger inner product with that direction. -/
theorem contact_rhombus_corner_empty (a b d e z : ℝ³) (c : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (he : ‖e‖ = 1) (hz : ‖z‖ = 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (had : inner ℝ a d < 1)
    (hab : inner ℝ a b = c) (hdb : inner ℝ d b = c)
    (hae : inner ℝ a e = c) (hde : inner ℝ d e = c)
    (ht : 0 < inner ℝ (crossVec a b) e)
    (haz : inner ℝ a z = c) (hdz : inner ℝ d z ≤ c)
    (hzb : inner ℝ z b ≤ c) (hze : inner ℝ z e ≤ c)
    (hleft : 0 ≤ inner ℝ (crossVec a b) z)
    (hright : 0 ≤ inner ℝ (crossVec e a) z) : False := by
  obtain ⟨l, μ, ν, hl, hμ, hν, hrep⟩ := rhombus_maximal_corner_cone a b d e z c ha had
    hab hdb hae hde ht hleft hright (by rwa [haz])
  have hba : inner ℝ b a = c := (real_inner_comm a b).trans hab
  have hea : inner ℝ e a = c := (real_inner_comm a e).trans hae
  have ht' : inner ℝ (crossVec b a) e ≠ 0 := by
    rw [crossVec_swap, inner_neg_left]
    exact neg_ne_zero.mpr ht.ne'
  have hdiag := contact_diagonal_short b a e c hb ha he hba hae ht'
  have hrep' : z = μ • b + l • a + ν • e := by rw [hrep]; module
  have hza : z ≠ a := by
    intro h
    rw [h, real_inner_self_eq_norm_sq, ha] at haz
    norm_num at haz
    linarith [hc.2]
  rcases contact_rhombus_cone_covering b a e z c μ l ν hb ha he hz hc.1 hba hea hdiag
    hμ hl hν hrep' hza with h | h
  · exact (not_lt_of_ge hzb) h
  · exact (not_lt_of_ge hze) h

end SquareAntiprismVerification
