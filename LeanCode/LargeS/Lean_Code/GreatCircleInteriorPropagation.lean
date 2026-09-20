import Lean_Code.SphericalRegionInterior

set_option maxHeartbeats 1000000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- If a great circle touches a supporting plane while lying locally on one
side, it lies in that plane everywhere. -/
lemma great_circle_plane_of_local_nonnegative (m t n : ℝ³) (r : ℝ)
    (hzero : inner ℝ n (greatCirclePoint m t r) = 0)
    (hlocal : ∀ᶠ s in nhds r, 0 ≤ inner ℝ n (greatCirclePoint m t s)) :
    ∀ s, inner ℝ n (greatCirclePoint m t s) = 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hlocal
  let δ := min ε Real.pi / 2
  have hδ : 0 < δ := half_pos (lt_min hε Real.pi_pos)
  have hδε : δ < ε := by dsimp [δ]; have := min_le_left ε Real.pi; linarith
  have hδpi : δ < Real.pi := by dsimp [δ]; have := min_le_right ε Real.pi; linarith [Real.pi_pos]
  have hp := hball (show r + δ ∈ Metric.ball r ε by
    simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hδ] using hδε)
  have hn := hball (show r - δ ∈ Metric.ball r ε by
    simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hδ] using hδε)
  change 0 ≤ inner ℝ n (greatCirclePoint m t (r + δ)) at hp
  change 0 ≤ inner ℝ n (greatCirclePoint m t (r - δ)) at hn
  have hp' : 0 ≤ Real.sin δ * inner ℝ n (greatCircleTangent m t r) := by
    rw [← greatCirclePoint_add] at hp
    rw [greatCirclePoint, inner_add_right, inner_smul_right, inner_smul_right, hzero] at hp
    simpa only [mul_zero, zero_add] using hp
  have hn' : Real.sin δ * inner ℝ n (greatCircleTangent m t r) ≤ 0 := by
    have heq : r - δ = r + (-δ) := sub_eq_add_neg r δ
    rw [heq, ← greatCirclePoint_add] at hn
    rw [greatCirclePoint, inner_add_right, inner_smul_right, inner_smul_right, hzero] at hn
    simp only [mul_zero, zero_add, Real.sin_neg, neg_mul] at hn
    linarith
  have hprod : Real.sin δ * inner ℝ n (greatCircleTangent m t r) = 0 := by linarith
  have htan : inner ℝ n (greatCircleTangent m t r) = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (Real.sin_pos_of_pos_of_lt_pi hδ hδpi).ne'
  intro s
  have hs : s = r + (s - r) := by ring
  rw [hs, ← greatCirclePoint_add]
  rw [greatCirclePoint, inner_add_right, inner_smul_right, inner_smul_right, hzero, htan]
  simp

/-- At any internal time of a trace in a locally polyhedral region,
noninteriority persists for all sufficiently nearby times. This is the
boundary-contact propagation needed by the shortening argument. -/
theorem great_circle_noninterior_local {D : Set ℝ³} (hmodel : LocallySphericalPolyhedral D)
    (m t : ℝ³) (hm : ‖m‖ = 1) (ht : ‖t‖ = 1) (horth : inner ℝ m t = 0)
    (L r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) L)
    (htrace : ∀ s ∈ Set.Icc (0 : ℝ) L, greatCirclePoint m t s ∈ D)
    (hrnot : greatCirclePoint m t r ∉ sphericalInteriorAmbient D) :
    ∀ᶠ s in nhds r, greatCirclePoint m t s ∉ sphericalInteriorAmbient D := by
  have hrD := htrace r ⟨hr.1.le, hr.2.le⟩
  obtain ⟨U, hU, hrU, k, normal, hUmodel⟩ := hmodel _ hrD
  obtain ⟨i, hi, hplane⟩ := active_normal_of_not_sphericalInterior normal hU hUmodel
    _ hrU hrD hrnot
  have heU : ∀ᶠ s in nhds r, greatCirclePoint m t s ∈ U :=
    (greatCirclePoint_continuous m t).continuousAt (hU.mem_nhds hrU)
  have heI : Set.Ioo (0 : ℝ) L ∈ nhds r := isOpen_Ioo.mem_nhds hr
  have hlocal : ∀ᶠ s in nhds r, 0 ≤ inner ℝ (normal i) (greatCirclePoint m t s) := by
    filter_upwards [heU, heI] with s hsU hsI
    exact ((hUmodel _ hsU).mp (htrace s ⟨hsI.1.le, hsI.2.le⟩)).2 i
  have hglobal := great_circle_plane_of_local_nonnegative m t (normal i) r hplane hlocal
  filter_upwards [heU] with s hsU
  exact not_sphericalInterior_of_local_support _ (normal i)
    (greatCirclePoint_unit m t hm ht horth s) hi (hglobal s) U (hU.mem_nhds hsU)
    (fun y hy hyU => ((hUmodel y hyU).mp hy).2 i)

/-- If one endpoint is a relative interior point, every internal point of
the great-circle trace is interior. Interior times and noninterior times
would otherwise disconnect the parameter interval. -/
theorem great_circle_interior_of_start {D : Set ℝ³} (hmodel : LocallySphericalPolyhedral D)
    (m t : ℝ³) (hm : ‖m‖ = 1) (ht : ‖t‖ = 1) (horth : inner ℝ m t = 0)
    (L : ℝ) (htrace : ∀ s ∈ Set.Icc (0 : ℝ) L, greatCirclePoint m t s ∈ D)
    (hstart : m ∈ sphericalInteriorAmbient D) :
    ∀ r ∈ Set.Ioo (0 : ℝ) L, greatCirclePoint m t r ∈ sphericalInteriorAmbient D := by
  let R := (greatCirclePoint m t) ⁻¹' sphericalInteriorAmbient D
  have hR : IsOpen R := (sphericalInteriorAmbient_isOpen D).preimage (greatCirclePoint_continuous m t)
  have hzero : 0 ∈ R := by
    change greatCirclePoint m t 0 ∈ sphericalInteriorAmbient D
    simpa only [greatCirclePoint_zero] using hstart
  intro r hr
  by_contra hn
  have hcover : Set.Ioo (0 : ℝ) L ⊆ R ∪ interior Rᶜ := by
    intro s hs
    by_cases hin : s ∈ R
    · exact Or.inl hin
    · apply Or.inr
      exact mem_interior_iff_mem_nhds.mpr
        (great_circle_noninterior_local hmodel m t hm ht horth L s hs htrace hin)
  have hrnot : r ∈ interior Rᶜ := mem_interior_iff_mem_nhds.mpr
    (great_circle_noninterior_local hmodel m t hm ht horth L r hr htrace hn)
  obtain ⟨s, hsR, hs0, hsL⟩ := exists_small_positive_in_neighborhood R
    (hR.mem_nhds hzero) L (hr.1.trans hr.2)
  obtain ⟨v, hvI, hvR, hvnot⟩ := isPreconnected_Ioo R (interior Rᶜ) hR isOpen_interior
    hcover ⟨s, ⟨hs0, hsL⟩, hsR⟩ ⟨r, hr, hrnot⟩
  exact (interior_subset hvnot) hvR

/-- The length bound now follows from an interior start point and the exact
local models, rather than an assumed interiority of the entire trace. -/
theorem shortest_great_circle_length_le_pi_of_interior_start {D : Set ℝ³}
    (P : CompactArcPatchCover D) (hmodel : LocallySphericalPolyhedral D)
    {m b : ℝ³} (p : PatchArcChain P.patch m b) (hmin : p.IsShortest)
    (t : ℝ³) (hm : ‖m‖ = 1) (ht : ‖t‖ = 1) (horth : inner ℝ m t = 0)
    (hend : greatCirclePoint m t p.length = b)
    (htrace : ∀ u ∈ Set.Icc (0 : ℝ) p.length, greatCirclePoint m t u ∈ D)
    (hstart : m ∈ sphericalInteriorAmbient D) : p.length ≤ Real.pi :=
  shortest_great_circle_length_le_pi_of_interior P p hmin t hm ht horth hend htrace
    (sphericalInteriorAmbient D) (sphericalInteriorAmbient_isOpen D)
    (fun x hx hu => sphericalInteriorAmbient_unit_mem hx hu)
    (great_circle_interior_of_start hmodel m t hm ht horth p.length htrace hstart)

end SquareAntiprismVerification
