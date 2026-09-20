import Lean_Code.ShortestChainGreatCircle

set_option maxHeartbeats 1500000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace PatchArcChain

lemma endpoints_eq_of_labels_empty {ι : Type*} {patch : ι → Set ℝ³} {a b : ℝ³}
    (p : PatchArcChain patch a b) (h : p.labels = []) : a = b := by
  cases p with
  | point => rfl
  | tail => simp [labels] at h

lemma angle_le_length {ι : Type*} {patch : ι → Set ℝ³}
    (hunit : ∀ i x, x ∈ patch i → ‖x‖ = 1) {a b : ℝ³} (p : PatchArcChain patch a b) :
    sphereAngle a b ≤ p.length := by
  induction p with
  | point ha => simp [length, sphereAngle_self_unit a ha]
  | @tail b p i z hb hz ih =>
    have htri := sphereAngle_triangle a b z p.start_unit (hunit i b hb) (hunit i z hz)
    change sphereAngle a z ≤ p.length + sphereAngle b z
    linarith

/-- The cumulative-angle description represents the entire chain inside the
region, not just its vertices. Every portion is contained in its actual patch. -/
theorem followsCircle_trace {D : Set ℝ³} (P : CompactArcPatchCover D)
    (hunit : ∀ x ∈ D, ‖x‖ = 1) {a b : ℝ³} (p : PatchArcChain P.patch a b)
    (m t : ℝ³) (hm : ‖m‖ = 1) (ht : ‖t‖ = 1) (horth : inner ℝ m t = 0)
    (s : ℝ) (haD : a ∈ D) (hfollow : p.FollowsCircle m t s) :
    ∀ u ∈ Set.Icc (0 : ℝ) p.length, greatCirclePoint m t (s + u) ∈ D := by
  induction p with
  | point ha =>
    intro u hu
    have hu0 : u = 0 := by change 0 ≤ u ∧ u ≤ 0 at hu; linarith [hu.1, hu.2]
    change greatCirclePoint m t s = a at hfollow
    simpa only [hu0, add_zero, hfollow] using haD
  | @tail y p i z hy hz ih =>
    intro u hu
    have huend : u ≤ p.length + sphereAngle y z := hu.2
    by_cases hup : u ≤ p.length
    · exact ih hfollow.1 u ⟨hu.1, hup⟩
    have hpu : p.length < u := lt_of_not_ge hup
    let θ := sphereAngle y z
    have hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi :=
      ⟨by dsimp [θ]; linarith,
        sphereAngle_lt_pi_of_nonantipodal y z (P.patch_unit hunit i y hy)
          (P.patch_unit hunit i z hz) (P.nonantipodal i y hy z hz)⟩
    have hcenter := PatchArcChain.FollowsCircle.endpoint p m t s hfollow.1
    let v := greatCircleTangent m t (s + p.length)
    have hv : ‖v‖ = 1 := greatCircleTangent_unit m t hm ht horth _
    have hyv : inner ℝ y v = 0 := by
      simpa only [hcenter] using greatCircleTangent_orthogonal m t hm ht horth (s + p.length)
    have hlast : greatCirclePoint y v θ = z := by
      calc
        greatCirclePoint y v θ =
            greatCirclePoint (greatCirclePoint m t (s + p.length))
              (greatCircleTangent m t (s + p.length)) θ := by rw [hcenter]
        _ = greatCirclePoint m t (s + p.length + θ) := greatCirclePoint_add _ _ _ _
        _ = z := hfollow.2
    have hcut : u - p.length ∈ Set.Icc (0 : ℝ) θ := ⟨by linarith, by dsimp [θ]; linarith⟩
    have hin := greatCirclePoint_mem_shortArcClosed (P.arcClosed i) y v
      (P.patch_unit hunit i y hy) hv hyv θ hθ hy (by simpa only [hlast] using hz) (u - p.length) hcut
    have hparam : greatCirclePoint y v (u - p.length) = greatCirclePoint m t (s + u) := by
      calc
        greatCirclePoint y v (u - p.length) =
            greatCirclePoint (greatCirclePoint m t (s + p.length))
              (greatCircleTangent m t (s + p.length)) (u - p.length) := by rw [hcenter]
        _ = greatCirclePoint m t ((s + p.length) + (u - p.length)) := greatCirclePoint_add _ _ _ _
        _ = greatCirclePoint m t (s + u) := by congr 1; ring
    rw [hparam] at hin
    exact P.subset i hin

end PatchArcChain

/-- The compact local construction now yields an actual oriented great-circle
trace in the region whose length minimizes all patch chains between its ends.
The remaining global step is to show that this length cannot exceed pi. -/
theorem minimizing_great_circle_trace_exists {D : Set ℝ³} (P : CompactArcPatchCover D)
    [PreconnectedSpace D] (hunit : ∀ x ∈ D, ‖x‖ = 1) (a b : D) (hne : a ≠ b) :
    ∃ p : PatchArcChain P.patch a.val b.val, ∃ t : ℝ³,
      ‖t‖ = 1 ∧ inner ℝ a.val t = 0 ∧ p.IsShortest ∧ 0 < p.length ∧
      greatCirclePoint a.val t p.length = b.val ∧
      ∀ u ∈ Set.Icc (0 : ℝ) p.length, greatCirclePoint a.val t u ∈ D := by
  obtain ⟨p, hzero, hmin⟩ := reduced_shortest_patch_chain_exists P hunit a b
  rcases reduced_shortest_follows_great_circle P hunit p hzero hmin with hnil | ⟨t, ht, hat, hf⟩
  · exact (hne (Subtype.ext (p.endpoints_eq_of_labels_empty hnil))).elim
  · have hne' : a.val ≠ b.val := fun h => hne (Subtype.ext h)
    have hpos := (sphereAngle_pos_of_ne a.val b.val (hunit _ a.property) (hunit _ b.property) hne').trans_le
      (p.angle_le_length (P.patch_unit hunit))
    refine ⟨p, t, ht, hat, hmin, hpos, ?_, ?_⟩
    · simpa only [zero_add] using PatchArcChain.FollowsCircle.endpoint p a.val t 0 hf
    · simpa only [zero_add] using p.followsCircle_trace P hunit a.val t
        (hunit _ a.property) ht hat 0 a.property hf

end SquareAntiprismVerification
