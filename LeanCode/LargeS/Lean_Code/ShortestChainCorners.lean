import Lean_Code.GreatCircleCorners

set_option maxHeartbeats 1000000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma CompactArcPatchCover.local_cover_ambient {D : Set ℝ³} (P : CompactArcPatchCover D)
    (b : ℝ³) (hb : b ∈ D) :
    ∃ i, ∃ U ∈ nhds b, ∀ x ∈ D, x ∈ U → x ∈ P.patch i := by
  obtain ⟨i, hi⟩ := P.localCover ⟨b, hb⟩
  rw [nhds_subtype_eq_comap] at hi
  obtain ⟨U, hU, hsub⟩ := Filter.mem_comap.mp hi
  refine ⟨i, U, hU, ?_⟩
  intro x hx hxU
  exact @hsub ⟨x, hx⟩ hxU

lemma greatCirclePoint_endpoint_cut (m t : ℝ³) (hm : ‖m‖ = 1) (ht : ‖t‖ = 1)
    (horth : inner ℝ m t = 0) (θ δ : ℝ)
    (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) (hδ : δ ∈ Set.Icc (0 : ℝ) θ) :
    sphereAngle (greatCirclePoint m t θ) (greatCirclePoint m t δ) = θ - δ := by
  have habs : |θ - δ| = θ - δ := abs_of_nonneg (sub_nonneg.mpr hδ.2)
  rw [greatCirclePoint_angle m t hm ht horth θ δ (by rw [habs]; linarith [hθ.2, hδ.1]), habs]

/-- A shortest two-link chain must have opposite outgoing unit tangents at
its joining point. The competing three-link chain is explicitly constructed
from two endpoint cuts and a shortcut in one local convex patch. -/
theorem shortest_two_link_tangents_opposite {D : Set ℝ³} (P : CompactArcPatchCover D)
    (a b z t u : ℝ³) (hm : ‖b‖ = 1) (ht : ‖t‖ = 1) (hu : ‖u‖ = 1)
    (hmt : inner ℝ b t = 0) (hmu : inner ℝ b u = 0)
    (α β : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) Real.pi) (hβ : β ∈ Set.Ioo (0 : ℝ) Real.pi)
    (hframeA : greatCirclePoint b t α = a) (hframeZ : greatCirclePoint b u β = z)
    (i j : Fin P.count) (haI : a ∈ P.patch i) (hbI : b ∈ P.patch i)
    (hbJ : b ∈ P.patch j) (hzJ : z ∈ P.patch j)
    (hminimal : ∀ q : PatchArcChain P.patch a z, α + β ≤ q.length) : t = -u := by
  by_contra hne
  obtain ⟨k, U, hU, hUk⟩ := P.local_cover_ambient b (P.subset i hbI)
  obtain ⟨δ, hδ0, hδr, hxU, hyU, hshort⟩ := great_circle_corner_shortening_near b t u
    hm ht hu hmt hmu hne U hU (min α β) (lt_min hα.1 hβ.1)
  have hδα : δ < α := hδr.trans_le (min_le_left α β)
  have hδβ : δ < β := hδr.trans_le (min_le_right α β)
  let x := greatCirclePoint b t δ
  let y := greatCirclePoint b u δ
  have hxI : x ∈ P.patch i := greatCirclePoint_mem_shortArcClosed (P.arcClosed i) b t hm ht hmt
    α hα hbI (by simpa only [hframeA] using haI) δ ⟨hδ0.le, hδα.le⟩
  have hyJ : y ∈ P.patch j := greatCirclePoint_mem_shortArcClosed (P.arcClosed j) b u hm hu hmu
    β hβ hbJ (by simpa only [hframeZ] using hzJ) δ ⟨hδ0.le, hδβ.le⟩
  have hxK : x ∈ P.patch k := hUk x (P.subset i hxI) hxU
  have hyK : y ∈ P.patch k := hUk y (P.subset j hyJ) hyU
  have haunit : ‖a‖ = 1 := by rw [← hframeA]; exact greatCirclePoint_unit b t hm ht hmt α
  let q : PatchArcChain P.patch a z :=
    .tail (.tail (.tail (.point haunit) i x haI hxI) k y hxK hyK) j z hyJ hzJ
  have hax : sphereAngle a x = α - δ := by
    rw [← hframeA]
    exact greatCirclePoint_endpoint_cut b t hm ht hmt α δ ⟨hα.1.le, hα.2.le⟩ ⟨hδ0.le, hδα.le⟩
  have hyz : sphereAngle y z = β - δ := by
    rw [sphereAngle_comm, ← hframeZ]
    exact greatCirclePoint_endpoint_cut b u hm hu hmu β δ ⟨hβ.1.le, hβ.2.le⟩ ⟨hδ0.le, hδβ.le⟩
  have hq : q.length = (α - δ) + sphereAngle x y + (β - δ) := by
    change 0 + sphereAngle a x + sphereAngle x y + sphereAngle y z = _
    rw [hax, hyz, zero_add]
  have hmin := hminimal q
  rw [hq] at hmin
  change sphereAngle x y < 2 * δ at hshort
  linarith

/-- The preceding geometric statement applies to the actual minimizer of
the finite compact-patch construction, with its genuine endpoint angles. -/
theorem shortest_two_link_collinear {D : Set ℝ³} (P : CompactArcPatchCover D)
    (hunit : ∀ x ∈ D, ‖x‖ = 1)
    (a b z : ℝ³) (i j : Fin P.count)
    (haI : a ∈ P.patch i) (hbI : b ∈ P.patch i)
    (hbJ : b ∈ P.patch j) (hzJ : z ∈ P.patch j)
    (hab : a ≠ b) (hbz : b ≠ z)
    (hmin : (PatchArcChain.tail
      (PatchArcChain.tail (.point (P.patch_unit hunit i a haI)) i b haI hbI)
        j z hbJ hzJ).IsShortest) :
    inner ℝ (crossVec a b) z = 0 := by
  have ha := P.patch_unit hunit i a haI
  have hb := P.patch_unit hunit i b hbI
  have hz := P.patch_unit hunit j z hzJ
  have hantiA := P.nonantipodal i b hbI a haI
  have hantiZ := P.nonantipodal j b hbJ z hzJ
  obtain ⟨t, ht, hmt, hframeA⟩ := short_arc_frame_exists b a hb ha hab.symm hantiA
  obtain ⟨u, hu, hmu, hframeZ⟩ := short_arc_frame_exists b z hb hz hbz hantiZ
  have htu : t = -u := shortest_two_link_tangents_opposite P a b z t u hb ht hu hmt hmu
    (sphereAngle b a) (sphereAngle b z)
    ⟨sphereAngle_pos_of_ne b a hb ha hab.symm, sphereAngle_lt_pi_of_nonantipodal b a hb ha hantiA⟩
    ⟨sphereAngle_pos_of_ne b z hb hz hbz, sphereAngle_lt_pi_of_nonantipodal b z hb hz hantiZ⟩
    hframeA hframeZ i j haI hbI hbJ hzJ (by
      intro q
      have h := hmin q
      change 0 + sphereAngle a b + sphereAngle b z ≤ q.length at h
      simpa only [zero_add, sphereAngle_comm a b] using h)
  have hu' : u = -t := neg_eq_iff_eq_neg.mp htu.symm
  have hzrep : z = Real.cos (sphereAngle b z) • b - Real.sin (sphereAngle b z) • t := by
    calc
      z = greatCirclePoint b u (sphereAngle b z) := hframeZ.symm
      _ = _ := by rw [hu']; simp [greatCirclePoint, sub_eq_add_neg]
  have harep : a = Real.cos (sphereAngle b a) • b + Real.sin (sphereAngle b a) • t := hframeA.symm
  rw [harep, hzrep]
  simp [crossVec, inner_coordinate_sum, Fin.sum_univ_succ]
  <;> ring

end SquareAntiprismVerification
