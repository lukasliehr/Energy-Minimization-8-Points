import Lean_Code.TracePatchSubdivision

set_option maxHeartbeats 1000000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

def shortArcParameter (θ u : ℝ) : ℝ :=
  (Real.sin u / Real.sin θ) /
    (Real.sin (θ - u) / Real.sin θ + Real.sin u / Real.sin θ)

lemma shortArcParameter_den_pos (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi)
    (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) θ) :
    0 < Real.sin (θ - u) / Real.sin θ + Real.sin u / Real.sin θ := by
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  by_cases hu0 : u = 0
  · subst u
    simp [hsin.ne']
  have hupos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
  have hA : 0 ≤ Real.sin (θ - u) / Real.sin θ := div_nonneg (Real.sin_nonneg_of_mem_Icc
    ⟨by linarith [hu.2], by linarith [hu.1, hθ.2]⟩) hsin.le
  exact add_pos_of_nonneg_of_pos hA
    (div_pos (Real.sin_pos_of_pos_of_lt_pi hupos (hu.2.trans_lt hθ.2)) hsin)

lemma greatCirclePoint_shortArc_parameter (m t : ℝ³) (hm : ‖m‖ = 1) (ht : ‖t‖ = 1)
    (horth : inner ℝ m t = 0) (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi)
    (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) θ) :
    shortArcParameter θ u ∈ Set.Icc (0 : ℝ) 1 ∧
      shortSphereArc m (greatCirclePoint m t θ) (shortArcParameter θ u) = greatCirclePoint m t u := by
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  let A := Real.sin (θ - u) / Real.sin θ
  let B := Real.sin u / Real.sin θ
  have hA : 0 ≤ A := div_nonneg (Real.sin_nonneg_of_mem_Icc
    ⟨by linarith [hu.2], by linarith [hu.1, hθ.2]⟩) hsin.le
  have hB : 0 ≤ B := div_nonneg (Real.sin_nonneg_of_mem_Icc
    ⟨hu.1, hu.2.trans hθ.2.le⟩) hsin.le
  have hrep : greatCirclePoint m t u = A • m + B • greatCirclePoint m t θ :=
    greatCirclePoint_sine_combination m t θ u hsin.ne'
  have hsum : 0 < A + B := shortArcParameter_den_pos θ hθ u hu
  let r := B / (A + B)
  have hr : r ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hB hsum.le, (div_le_one hsum).mpr (by linarith)⟩
  have h1 : 1 - r = (A + B)⁻¹ * A := by dsimp [r]; field_simp; ring
  have h2 : r = (A + B)⁻¹ * B := by dsimp [r]; ring
  have hcomb : (1 - r) • m + r • greatCirclePoint m t θ =
      (A + B)⁻¹ • greatCirclePoint m t u := by
    rw [hrep, smul_add, smul_smul, smul_smul, h1, h2]
  change r ∈ Set.Icc (0 : ℝ) 1 ∧ shortSphereArc m (greatCirclePoint m t θ) r = _
  refine ⟨hr, ?_⟩
  unfold shortSphereArc
  rw [hcomb]
  exact sphereNormalize_pos_smul_unit _ (greatCirclePoint_unit m t hm ht horth u)
    _ (inv_pos.mpr hsum)

/-- A shorter arc contained in the region gives a finite admissible chain
with no more than its actual angular length. -/
theorem short_arc_patch_chain {D : Set ℝ³} (P : CompactArcPatchCover D)
    (a b : ℝ³) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hanti : a ≠ -b)
    (hinside : ∀ r ∈ Set.Icc (0 : ℝ) 1, shortSphereArc a b r ∈ D) :
    ∃ q : PatchArcChain P.patch a b, q.length ≤ sphereAngle a b := by
  by_cases heq : a = b
  · subst b
    exact ⟨.point ha, (sphereAngle_range a a).1⟩
  obtain ⟨t, ht, hat, hframe⟩ := short_arc_frame_exists a b ha hb heq hanti
  have hθ : sphereAngle a b ∈ Set.Ioo (0 : ℝ) Real.pi :=
    ⟨sphereAngle_pos_of_ne a b ha hb heq, sphereAngle_lt_pi_of_nonantipodal a b ha hb hanti⟩
  obtain ⟨q, hq⟩ := great_circle_patch_chain P a t ha ht hat 0 (sphereAngle a b) hθ.1.le (by
    intro u hu
    obtain ⟨hr, heq⟩ := greatCirclePoint_shortArc_parameter a t ha ht hat (sphereAngle a b) hθ u hu
    have hin := hinside _ hr
    rw [hframe] at heq
    rw [heq] at hin
    simpa only [zero_add] using hin)
  refine ⟨q.reendpoint (greatCirclePoint_zero a t) ?_, ?_⟩
  · simpa only [zero_add] using hframe
  · simpa only [PatchArcChain.reendpoint_length] using hq

lemma shortSphereArc_nonantipodal_of_ne_zero (a b : ℝ³)
    (h : shortSphereArc a b (1 / 2) ≠ 0) : a ≠ -b := by
  intro heq
  have hcomb : (1 - (1 / 2 : ℝ)) • a + (1 / 2 : ℝ) • b = 0 := by
    rw [heq]
    module
  apply h
  unfold shortSphereArc
  rw [hcomb]
  simp [sphereNormalize]

/-- The affine and angular descriptions cover exactly the same shorter arc. -/
theorem shortSphereArc_greatCircle_parameter (m t : ℝ³) (hm : ‖m‖ = 1) (ht : ‖t‖ = 1)
    (horth : inner ℝ m t = 0) (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) Real.pi)
    (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    ∃ u ∈ Set.Icc (0 : ℝ) θ,
      shortSphereArc m (greatCirclePoint m t θ) r = greatCirclePoint m t u := by
  have hsin : Real.sin θ ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2).ne'
  have hcont : ContinuousOn (shortArcParameter θ) (Set.Icc (0 : ℝ) θ) := by
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro u hu
      exact (shortArcParameter_den_pos θ hθ u hu).ne'
  have hzero : shortArcParameter θ 0 = 0 := by simp [shortArcParameter]
  have hone : shortArcParameter θ θ = 1 := by simp [shortArcParameter, hsin]
  have hr' : r ∈ Set.Icc (shortArcParameter θ 0) (shortArcParameter θ θ) := by
    simpa only [hzero, hone] using hr
  obtain ⟨u, hu, hur⟩ := intermediate_value_Icc hθ.1.le hcont hr'
  refine ⟨u, hu, ?_⟩
  have heq := (greatCirclePoint_shortArc_parameter m t hm ht horth θ hθ u hu).2
  simpa only [hur] using heq

end SquareAntiprismVerification
