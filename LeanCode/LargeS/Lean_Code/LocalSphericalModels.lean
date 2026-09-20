import Lean_Code.SphericalConvexPatches

set_option maxHeartbeats 1000000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- In a neighborhood of each point, the region is exactly the unit sphere
intersected with finitely many oriented closed great-circle halfspaces.
For an actual face these are zero, one, or two halfspaces. -/
def LocallySphericalPolyhedral (D : Set ℝ³) : Prop :=
  ∀ x ∈ D, ∃ U : Set ℝ³, IsOpen U ∧ x ∈ U ∧
    ∃ n : ℕ, ∃ normal : Fin n → ℝ³,
      ∀ y ∈ U, y ∈ D ↔ ‖y‖ = 1 ∧ ∀ i, 0 ≤ inner ℝ (normal i) y

lemma LocallySphericalPolyhedral.unit {D : Set ℝ³} (hD : LocallySphericalPolyhedral D)
    (x : ℝ³) (hx : x ∈ D) : ‖x‖ = 1 := by
  obtain ⟨U, hUo, hxU, n, normal, hmodel⟩ := hD x hx
  exact ((hmodel x hxU).mp hx).1

/-- The local models give compact shorter-arc-convex neighborhoods without
assuming global convexity or a hemisphere containing the whole region. -/
theorem compact_arc_neighborhoods_of_local_models {D : Set ℝ³}
    (hD : LocallySphericalPolyhedral D) : HasCompactArcNeighborhoods D := by
  intro x
  obtain ⟨U, hUo, hxU, n, normal, hmodel⟩ := hD x.val x.property
  have hxunit : ‖x.val‖ = 1 := hD.unit x.val x.property
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hUo.mem_nhds hxU)
  let ρ : ℝ := min ε 1 / 2
  have hρ : 0 < ρ := half_pos (lt_min hε zero_lt_one)
  have hρε : ρ < ε := by dsimp [ρ]; have := min_le_left ε 1; linarith
  have hρ1 : ρ < 1 := by dsimp [ρ]; have := min_le_right ε 1; linarith
  let δ : ℝ := 1 - ρ ^ 2 / 2
  have hδ0 : 0 < δ := by dsimp [δ]; nlinarith
  have hδ1 : δ < 1 := by dsimp [δ]; nlinarith [sq_pos_of_pos hρ]
  let K := sphericalHalfspacePatch normal x.val δ
  have hKU : K ⊆ U := by
    intro y hy
    have hynorm : ‖y‖ = 1 := hy.1
    have hycap : δ ≤ inner ℝ x.val y := hy.2.1
    have hsq : dist y x.val ^ 2 = 2 - 2 * inner ℝ x.val y := by
      rw [dist_eq_norm, norm_sub_sq_real, hynorm, hxunit, real_inner_comm x.val y]
      ring
    have hdist : dist y x.val < ε := by
      dsimp [δ] at hycap
      nlinarith [dist_nonneg (x := y) (y := x.val),
        mul_pos (sub_pos.mpr hρε) (show 0 < ε + ρ by linarith)]
    exact hball hdist
  refine ⟨K, sphericalHalfspacePatch_isCompact normal x.val δ, ?_,
    (fun a ha b hb => sphericalHalfspacePatch_nonantipodal normal x.val δ hδ0 a b ha hb),
    sphericalHalfspacePatch_arcClosed normal x.val δ hδ0, ?_⟩
  · intro y hy
    exact (hmodel y (hKU hy)).mpr ⟨hy.1, hy.2.2⟩
  · have hval : Filter.Tendsto (fun y : D => y.val) (nhds x) (nhds x.val) :=
      continuous_subtype_val.continuousAt
    have hUevent : ∀ᶠ y : D in nhds x, y.val ∈ U := hval (hUo.mem_nhds hxU)
    have hcapo : IsOpen {y : D | δ < inner ℝ x.val y.val} :=
      isOpen_lt continuous_const (by fun_prop)
    have hcapx : x ∈ {y : D | δ < inner ℝ x.val y.val} := by
      change δ < inner ℝ x.val x.val
      simpa [real_inner_self_eq_norm_sq, hxunit] using hδ1
    filter_upwards [hUevent, hcapo.mem_nhds hcapx] with y hyU hycap
    obtain ⟨hyunit, hynormal⟩ := (hmodel y.val hyU).mp y.property
    exact ⟨hyunit, hycap.le, hynormal⟩

theorem compact_arc_cover_of_local_models {D : Set ℝ³} (hcompact : IsCompact D)
    (hmodel : LocallySphericalPolyhedral D) : Nonempty (CompactArcPatchCover D) :=
  compact_arc_patch_cover_exists D hcompact (compact_arc_neighborhoods_of_local_models hmodel)

end SquareAntiprismVerification
