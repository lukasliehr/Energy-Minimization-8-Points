import Lean_Code.GreatCircleFrames

set_option maxHeartbeats 2000000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Local straightness propagates through a reduced shortest chain: all its
vertices occur in order on one great circle at their cumulative arc lengths. -/
theorem reduced_shortest_follows_great_circle {D : Set ℝ³} (P : CompactArcPatchCover D)
    (hunit : ∀ x ∈ D, ‖x‖ = 1) {a b : ℝ³} (p : PatchArcChain P.patch a b)
    (hzero : p.NoZeroLinks) (hmin : p.IsShortest) :
    p.labels = [] ∨ ∃ t : ℝ³, ‖t‖ = 1 ∧ inner ℝ a t = 0 ∧ p.FollowsCircle a t 0 := by
  induction p with
  | point => exact Or.inl rfl
  | @tail b p i z hb hz ih =>
    have hpre := p.shortest_of_tail i z hb hz hmin
    have hprezero : p.NoZeroLinks := hzero.1
    have hbz : b ≠ z := hzero.2
    have hfirst : ∀ (ha : ‖a‖ = 1) (haI : a ∈ P.patch i) (haz : a ≠ z),
        ∃ t : ℝ³, ‖t‖ = 1 ∧ inner ℝ a t = 0 ∧
          (PatchArcChain.tail (.point ha) i z haI hz).FollowsCircle a t 0 := by
      intro ha haI haz
      obtain ⟨t, ht, hat, hframe⟩ := short_arc_frame_exists a z ha (P.patch_unit hunit i z hz)
        haz (P.nonantipodal i a haI z hz)
      refine ⟨t, ht, hat, ?_⟩
      change greatCirclePoint a t 0 = a ∧ greatCirclePoint a t (0 + 0 + sphereAngle a z) = z
      exact ⟨greatCirclePoint_zero a t, by simpa only [zero_add] using hframe⟩
    rcases ih hprezero hpre with hnil | ⟨t, ht, hat, hfollow⟩
    · cases p with
      | point ha => exact Or.inr (hfirst ha hb hbz)
      | tail => simp [PatchArcChain.labels] at hnil
    · cases p with
      | point ha => exact Or.inr (hfirst ha hb hbz)
      | @tail y q j b' hy hbJ =>
        let L : ℝ := q.length + sphereAngle y b
        have ha : ‖a‖ = 1 := q.start_unit
        have hbunit : ‖b‖ = 1 := P.patch_unit hunit i b hb
        have hyunit : ‖y‖ = 1 := P.patch_unit hunit j y hy
        have hzunit : ‖z‖ = 1 := P.patch_unit hunit i z hz
        have hyb : y ≠ b := hprezero.2
        have hFy : greatCirclePoint a t q.length = y := by
          simpa only [zero_add] using PatchArcChain.FollowsCircle.endpoint q a t 0 hfollow.1
        have hFb : greatCirclePoint a t L = b := by
          simpa only [zero_add] using hfollow.2
        let w := greatCircleTangent a t L
        have hw : ‖w‖ = 1 := greatCircleTangent_unit a t ha ht hat L
        have hbw : inner ℝ b w = 0 := by
          simpa only [hFb] using greatCircleTangent_orthogonal a t ha ht hat L
        have hα : sphereAngle b y ∈ Set.Ioo (0 : ℝ) Real.pi :=
          ⟨sphereAngle_pos_of_ne b y hbunit hyunit hyb.symm,
            sphereAngle_lt_pi_of_nonantipodal b y hbunit hyunit (P.nonantipodal j b hbJ y hy)⟩
        have hβ : sphereAngle b z ∈ Set.Ioo (0 : ℝ) Real.pi :=
          ⟨sphereAngle_pos_of_ne b z hbunit hzunit hbz,
            sphereAngle_lt_pi_of_nonantipodal b z hbunit hzunit (P.nonantipodal i b hb z hz)⟩
        have hback : greatCirclePoint b (-w) (sphereAngle b y) = y := by
          calc
            greatCirclePoint b (-w) (sphereAngle b y) =
                greatCirclePoint (greatCirclePoint a t L) (-greatCircleTangent a t L)
                  (sphereAngle b y) := by rw [hFb]
            _ = greatCirclePoint a t (L - sphereAngle b y) := greatCirclePoint_backwards _ _ _ _
            _ = y := by
              have hL : L - sphereAngle b y = q.length := by
                dsimp [L]
                rw [sphereAngle_comm y b]
                ring
              rw [hL]
              exact hFy
        obtain ⟨u, hu, hbu, hfront⟩ := short_arc_frame_exists b z hbunit hzunit hbz
          (P.nonantipodal i b hb z hz)
        have hopp : -w = -u := shortest_two_link_tangents_opposite P y b z (-w) u hbunit
          (by simpa using hw) hu (by simpa using hbw) hbu
          (sphereAngle b y) (sphereAngle b z) hα hβ hback hfront j i hy hbJ hb hz (by
            intro r
            have h := hmin (q.trans r)
            change q.length + sphereAngle y b + sphereAngle b z ≤ (q.trans r).length at h
            rw [PatchArcChain.trans_length, sphereAngle_comm y b] at h
            linarith)
        have hwu : w = u := neg_injective hopp
        have hnew : greatCirclePoint a t (L + sphereAngle b z) = z := by
          calc
            greatCirclePoint a t (L + sphereAngle b z) =
                greatCirclePoint (greatCirclePoint a t L) (greatCircleTangent a t L)
                  (sphereAngle b z) := (greatCirclePoint_add _ _ _ _).symm
            _ = greatCirclePoint b u (sphereAngle b z) := by rw [hFb]; change greatCirclePoint b w _ = _; rw [hwu]
            _ = z := hfront
        right
        refine ⟨t, ht, hat, hfollow, ?_⟩
        simpa only [zero_add, PatchArcChain.length] using hnew

end SquareAntiprismVerification
