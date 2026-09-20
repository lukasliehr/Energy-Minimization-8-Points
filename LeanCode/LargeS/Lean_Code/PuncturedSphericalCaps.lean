import Lean_Code.SphericalCapPaths

set_option maxHeartbeats 1500000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma unit_nearby_avoiding_two_planes (p n m : ℝ³) (hp : ‖p‖ = 1)
    (hn : n ≠ 0) (hm : m ≠ 0) (hnp : inner ℝ n p = 0) (hmp : inner ℝ m p = 0)
    (U : Set ℝ³) (hU : IsOpen U) (hpU : p ∈ U) :
    ∃ z ∈ U, ‖z‖ = 1 ∧ inner ℝ n z ≠ 0 ∧ inner ℝ m z ≠ 0 := by
  have hnn : 0 < inner ℝ n n := by rw [real_inner_self_eq_norm_sq]; exact sq_pos_of_pos (norm_pos_iff.mpr hn)
  have hmm : 0 < inner ℝ m m := by rw [real_inner_self_eq_norm_sq]; exact sq_pos_of_pos (norm_pos_iff.mpr hm)
  have hex : ∃ d m' : ℝ³, (m' = m ∨ m' = -m) ∧ 0 < inner ℝ n d ∧ 0 < inner ℝ m' d := by
    by_cases hmn : inner ℝ m n = 0
    · have hnm : inner ℝ n m = 0 := (real_inner_comm m n).trans hmn
      exact ⟨n + m, m, Or.inl rfl, by simpa [inner_add_right, hnm] using hnn,
        by simpa [inner_add_right, hmn] using hmm⟩
    · by_cases hpos : 0 < inner ℝ m n
      · exact ⟨n, m, Or.inl rfl, hnn, hpos⟩
      · refine ⟨n, -m, Or.inr rfl, hnn, ?_⟩
        rw [inner_neg_left]
        exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hpos) hmn)
  obtain ⟨d, m', hm', hd₁, hd₂⟩ := hex
  have hm'p : inner ℝ m' p = 0 := by rcases hm' with rfl | rfl <;> simp [hmp]
  let normal : Bool → ℝ³ := fun i => if i then n else m'
  obtain ⟨z, hzU, hzu, hzN⟩ := unit_nearby_strict_normals normal p d hp
    (fun i => by cases i <;> simp [normal, hnp, hm'p])
    (fun i => by cases i <;> simp [normal, hd₁, hd₂]) U hU hpU
  refine ⟨z, hzU, hzu, (hzN true).ne', ?_⟩
  have hh : 0 < inner ℝ m' z := hzN false
  rcases hm' with rfl | rfl
  · exact hh.ne'
  · rw [inner_neg_left] at hh
    exact (neg_pos.mp hh).ne

lemma cap_cross_ne_zero (p x : ℝ³) (hp : ‖p‖ = 1) (δ : ℝ) (hδ : 0 < δ)
    (hx : x ∈ sphericalOpenCap p δ) (hne : x ≠ p) : crossVec p x ≠ 0 := by
  intro hzero
  have hh := crossVec_norm_sq p x
  rw [hzero, norm_zero, hp, hx.1] at hh
  have hpos := hδ.trans hx.2
  have heq : inner ℝ p x = 1 := by nlinarith
  have hdist := norm_sub_sq_real x p
  rw [hx.1, hp, real_inner_comm p x, heq] at hdist
  have hz : ‖x - p‖ = 0 := by nlinarith [norm_nonneg (x - p)]
  exact hne (sub_eq_zero.mp (norm_eq_zero.mp hz))

lemma short_arc_avoids_point_of_plane (p x z n : ℝ³)
    (hx : ‖x‖ = 1) (hz : ‖z‖ = 1) (hanti : x ≠ -z)
    (hnp : inner ℝ n p = 0) (hnx : inner ℝ n x = 0) (hnz : inner ℝ n z ≠ 0)
    (hxp : x ≠ p) (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) : shortSphereArc x z r ≠ p := by
  by_cases hr0 : r = 0
  · simpa only [hr0, shortSphereArc_zero x z hx] using hxp
  · intro heq
    have hv : ‖(1 - r) • x + r • z‖ ≠ 0 := norm_ne_zero_iff.mpr
      (shortSphereArc_combination_ne_zero x z hx hz hanti r hr)
    have hh := congrArg (fun y : ℝ³ => inner ℝ n y) heq
    simp only [shortSphereArc, sphereNormalize_inner, inner_add_right, inner_smul_right,
      hnx, hnp, mul_zero, zero_add] at hh
    exact (mul_ne_zero (inv_ne_zero hv) (mul_ne_zero hr0 hnz)) hh

/-- Removing the center of a small spherical cap does not disconnect it.
A point off two great-circle planes supplies two short arcs avoiding the
center, including when the direct arc would pass through the puncture. -/
theorem punctured_spherical_cap_joined (p : ℝ³) (hp : ‖p‖ = 1) (δ : ℝ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (x y : ℝ³)
    (hx : x ∈ sphericalOpenCap p δ) (hy : y ∈ sphericalOpenCap p δ)
    (hxp : x ≠ p) (hyp : y ≠ p) :
    JoinedIn {z : ℝ³ | z ∈ sphericalOpenCap p δ ∧ z ≠ p} x y := by
  let n := crossVec p x
  let m := crossVec p y
  have hn := cap_cross_ne_zero p x hp δ hδ.1 hx hxp
  have hm := cap_cross_ne_zero p y hp δ hδ.1 hy hyp
  let U : Set ℝ³ := {z | δ < inner ℝ p z}
  have hU : IsOpen U := isOpen_lt continuous_const (by fun_prop)
  have hpU : p ∈ U := by simpa [U, real_inner_self_eq_norm_sq, hp] using hδ.2
  obtain ⟨z, hzU, hzu, hnz, hmz⟩ := unit_nearby_avoiding_two_planes p n m hp hn hm
    (crossVec_inner_left _ _) (crossVec_inner_left _ _) U hU hpU
  have hzcap : z ∈ sphericalOpenCap p δ := ⟨hzu, hzU⟩
  have hpath (a q : ℝ³) (ha : a ∈ sphericalOpenCap p δ) (hap : a ≠ p)
      (hqp : inner ℝ q p = 0) (hqa : inner ℝ q a = 0) (hqz : inner ℝ q z ≠ 0) :
      JoinedIn {z : ℝ³ | z ∈ sphericalOpenCap p δ ∧ z ≠ p} a z := by
    have hanti := sphericalOpenCap_nonantipodal p δ hδ.1 ha hzcap
    apply joinedIn_of_short_arc a z ha.1 hzu hanti
    intro r hr
    exact ⟨sphericalOpenCap_arcClosed p δ hδ.1 a ha z hzcap hanti r hr,
      short_arc_avoids_point_of_plane p a z q ha.1 hzu hanti hqp hqa hqz hap r hr⟩
  exact (hpath x n hx hxp (crossVec_inner_left _ _) (crossVec_inner_right _ _) hnz).trans
    (hpath y m hy hyp (crossVec_inner_left _ _) (crossVec_inner_right _ _) hmz).symm

end SquareAntiprismVerification
