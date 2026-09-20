import Lean_Code.HemisphereCoordinates
import Lean_Code.ContactDirections

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma contact_arc_projection (p a : ℝ³) (c t : ℝ) (hp : ‖p‖ = 1) (hpa : inner ℝ p a = c) :
    let z := sphereNormalize ((1 - t) • p + t • a)
    z - inner ℝ p z • p =
      (‖(1 - t) • p + t • a‖⁻¹ * t) • (a - c • p) := by
  dsimp [sphereNormalize]
  simp only [inner_smul_right, inner_add_right, real_inner_self_eq_norm_sq, hp, hpa]
  module

lemma positive_smul_eq_of_equal_norm (u v : ℝ³) (a b : ℝ)
    (hu : 0 < ‖u‖) (hvn : ‖u‖ = ‖v‖) (ha : 0 < a) (hb : 0 < b)
    (heq : a • u = b • v) : u = v := by
  have hn := congrArg norm heq
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos ha, abs_of_pos hb, ← hvn] at hn
  have hab : a = b := by nlinarith
  rw [← hab] at heq
  have h := congrArg (fun w : ℝ³ => a⁻¹ • w) heq
  simpa only [smul_smul, inv_mul_cancel₀ ha.ne', one_smul] using h

theorem disjoint_contact_arcs_shared (p a b : ℝ³) (c : ℝ)
    (hp : ‖p‖ = 1) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hpa : inner ℝ p a = c) (hpb : inner ℝ p b = c)
    (hab : a ≠ b) : Disjoint (OpenContactArc p a) (OpenContactArc p b) := by
  apply Set.disjoint_left.mpr
  intro z hza hzb
  obtain ⟨t, ht, ht1, hzt⟩ := hza
  obtain ⟨s, hs, hs1, hzs⟩ := hzb
  have hnt := norm_convex_contact_combination_lower p a c t hp ha hpa hc.2.le
  have hns := norm_convex_contact_combination_lower p b c s hp hb hpb hc.2.le
  have htpos : 0 < ‖(1 - t) • p + t • a‖ := by
    nlinarith [norm_nonneg ((1 - t) • p + t • a), hc.1]
  have hspos : 0 < ‖(1 - s) • p + s • b‖ := by
    nlinarith [norm_nonneg ((1 - s) • p + s • b), hc.1]
  have hqa := contact_arc_projection p a c t hp hpa
  have hqb := contact_arc_projection p b c s hp hpb
  change sphereNormalize ((1 - t) • p + t • a) -
    inner ℝ p (sphereNormalize ((1 - t) • p + t • a)) • p = _ at hqa
  change sphereNormalize ((1 - s) • p + s • b) -
    inner ℝ p (sphereNormalize ((1 - s) • p + s • b)) • p = _ at hqb
  change z = sphereNormalize ((1 - t) • p + t • a) at hzt
  change z = sphereNormalize ((1 - s) • p + s • b) at hzs
  rw [← hzt] at hqa
  rw [← hzs] at hqb
  have hna := (contact_tangent_norm_sq p a c hp ha hpa).2
  have hnb := (contact_tangent_norm_sq p b c hp hb hpb).2
  have hnpos : 0 < ‖a - c • p‖ := by
    have hd : 0 < 1 - c ^ 2 := by nlinarith [mul_pos hc.1 (sub_pos.mpr hc.2)]
    nlinarith [norm_nonneg (a - c • p)]
  have hnorms : ‖a - c • p‖ = ‖b - c • p‖ := by
    nlinarith [norm_nonneg (a - c • p), norm_nonneg (b - c • p)]
  have heq := positive_smul_eq_of_equal_norm (a - c • p) (b - c • p) _ _ hnpos hnorms
    (mul_pos (inv_pos.mpr htpos) ht) (mul_pos (inv_pos.mpr hspos) hs) (hqa.symm.trans hqb)
  apply hab
  have h := congrArg (fun w : ℝ³ => w + c • p) heq
  simpa only [sub_add_cancel] using h

lemma OpenContactArc_comm (a b : ℝ³) : OpenContactArc a b = OpenContactArc b a := by
  have hswap : ∀ a b : ℝ³, OpenContactArc a b ⊆ OpenContactArc b a := by
    intro a b z hz
    obtain ⟨t, ht, ht1, heq⟩ := hz
    refine ⟨1 - t, by linarith, by linarith, ?_⟩
    have hv : (1 - (1 - t)) • b + (1 - t) • a = (1 - t) • a + t • b := by module
    rw [hv]
    exact heq
  exact Set.Subset.antisymm (hswap a b) (hswap b a)

theorem contact_graph_arcs_disjoint (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hbound : PackingInnerBound c Y)
    (i j k l : Fin 8) (hij : i ≠ j) (hkl : k ≠ l)
    (hijc : inner ℝ (Y i) (Y j) = c) (hklc : inner ℝ (Y k) (Y l) = c)
    (hdistinct : ¬ ((i = k ∧ j = l) ∨ (i = l ∧ j = k))) :
    Disjoint (OpenContactArc (Y i) (Y j)) (OpenContactArc (Y k) (Y l)) := by
  by_cases hik : i = k
  · subst k
    apply disjoint_contact_arcs_shared (Y i) (Y j) (Y l) c (hY.1 i) (hY.1 j) (hY.1 l) hc hijc hklc
    intro heq
    exact hdistinct (Or.inl ⟨rfl, hY.2 heq⟩)
  by_cases hil : i = l
  · subst l
    rw [OpenContactArc_comm (Y k) (Y i)]
    apply disjoint_contact_arcs_shared (Y i) (Y j) (Y k) c (hY.1 i) (hY.1 j) (hY.1 k) hc hijc
      ((real_inner_comm (Y k) (Y i)).trans hklc)
    intro heq
    exact hdistinct (Or.inr ⟨rfl, hY.2 heq⟩)
  by_cases hjk : j = k
  · subst k
    rw [OpenContactArc_comm (Y i) (Y j)]
    apply disjoint_contact_arcs_shared (Y j) (Y i) (Y l) c (hY.1 j) (hY.1 i) (hY.1 l) hc
      ((real_inner_comm (Y i) (Y j)).trans hijc) hklc
    intro heq
    exact hdistinct (Or.inr ⟨hY.2 heq, rfl⟩)
  by_cases hjl : j = l
  · subst l
    rw [OpenContactArc_comm (Y i) (Y j), OpenContactArc_comm (Y k) (Y j)]
    apply disjoint_contact_arcs_shared (Y j) (Y i) (Y k) c (hY.1 j) (hY.1 i) (hY.1 k) hc
      ((real_inner_comm (Y i) (Y j)).trans hijc) ((real_inner_comm (Y k) (Y j)).trans hklc)
    intro heq
    exact hdistinct (Or.inl ⟨hY.2 heq, rfl⟩)
  exact disjoint_contact_arcs (Y i) (Y j) (Y k) (Y l) c (hY.1 i) (hY.1 j) (hY.1 k) (hY.1 l)
    hc.1 hc.2 hijc hklc (hbound i k hik) (hbound i l hil) (hbound j k hjk) (hbound j l hjl)

lemma contact_arc_inner_left (a b z : ℝ³) (c : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hab : inner ℝ a b = c) (hz : z ∈ OpenContactArc a b) : c < inner ℝ a z := by
  obtain ⟨t, ht, ht1, heq⟩ := hz
  let v := (1 - t) • a + t • b
  have hvlow := norm_convex_contact_combination_lower a b c t ha hb hab hc.2.le
  have hvpos : 0 < ‖v‖ := by nlinarith [norm_nonneg v, hc.1]
  have hvupper : ‖v‖ ≤ 1 := by
    have h := norm_add_le ((1 - t) • a) (t • b)
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (by linarith : 0 < 1 - t), abs_of_pos ht, ha, hb] at h
    change ‖v‖ ≤ _ at h
    linarith
  have hinner : inner ℝ a z = ((1 - t) + t * c) / ‖v‖ := by
    rw [heq]
    simp only [inner_smul_right, inner_add_right, real_inner_self_eq_norm_sq, ha, hab]
    dsimp [v]
    ring
  rw [hinner]
  apply (lt_div_iff₀ hvpos).mpr
  have hstrict : c < (1 - t) + t * c := by nlinarith [mul_pos (by linarith : 0 < 1 - t) (sub_pos.mpr hc.2)]
  have hmul := mul_le_mul_of_nonneg_left hvupper hc.1.le
  linarith

theorem contact_arc_avoids_vertices (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hbound : PackingInnerBound c Y)
    (i j : Fin 8) (hij : i ≠ j) (hcontact : inner ℝ (Y i) (Y j) = c) :
    ∀ k : Fin 8, Y k ∉ OpenContactArc (Y i) (Y j) := by
  intro k hk
  have hleft := contact_arc_inner_left (Y i) (Y j) (Y k) c (hY.1 i) (hY.1 j) hc hcontact hk
  by_cases hki : k = i
  · subst k
    rw [OpenContactArc_comm] at hk
    have hright := contact_arc_inner_left (Y j) (Y i) (Y i) c (hY.1 j) (hY.1 i) hc
      ((real_inner_comm (Y i) (Y j)).trans hcontact) hk
    exact (not_lt_of_ge (hbound j i hij.symm)) hright
  · exact (not_lt_of_ge (hbound i k (Ne.symm hki))) hleft

end SquareAntiprismVerification
