import Lean_Code.RankinBound

open Real Filter
noncomputable section
namespace SquareAntiprismVerification

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- A normalized tangent-line version of the paper's great-circle push. -/
def packingPush (p v : ℝ³) (t : ℝ) : ℝ³ :=
  (Real.sqrt (1 + t ^ 2))⁻¹ • (p + t • v)

lemma packingPush_norm (p v : ℝ³) (hp : ‖p‖ = 1) (hv : ‖v‖ = 1)
    (horth : inner ℝ p v = 0) (t : ℝ) : ‖packingPush p v t‖ = 1 := by
  have hs : 0 < 1 + t ^ 2 := by positivity
  have horth' : inner ℝ v p = 0 := by rw [real_inner_comm]; exact horth
  have hnormsq : ‖p + t • v‖ ^ 2 = 1 + t ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
    simp [horth', horth, real_inner_self_eq_norm_sq, hp, hv]
    ring
  have hnorm : ‖p + t • v‖ = Real.sqrt (1 + t ^ 2) := by
    rw [← hnormsq, Real.sqrt_sq (norm_nonneg _)]
  rw [packingPush, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hs)),
    hnorm, inv_mul_cancel₀ (Real.sqrt_pos.mpr hs).ne']

@[simp] lemma packingPush_zero (p v : ℝ³) : packingPush p v 0 = p := by
  simp [packingPush]

lemma packingPush_continuous (p v : ℝ³) : Continuous (packingPush p v) := by
  unfold packingPush
  have hc : Continuous (fun t : ℝ => (Real.sqrt (1 + t ^ 2))⁻¹) := by
    apply Continuous.inv₀
    · fun_prop
    · intro t
      exact (Real.sqrt_pos.mpr (by positivity : 0 < 1 + t ^ 2)).ne'
  exact hc.smul (by fun_prop)

lemma packingPush_inner_lt (p v q : ℝ³) (c t : ℝ)
    (hc : 0 < c) (ht : 0 < t) (hpq : inner ℝ p q = c)
    (hvq : inner ℝ v q ≤ 0) : inner ℝ (packingPush p v t) q < c := by
  have hs : 1 < Real.sqrt (1 + t ^ 2) := by
    have hsq := Real.sq_sqrt (by positivity : 0 ≤ 1 + t ^ 2)
    have hn := Real.sqrt_nonneg (1 + t ^ 2)
    nlinarith [sq_pos_of_pos ht]
  rw [packingPush, inner_smul_left, inner_add_left, inner_smul_left, hpq]
  have hnum : c + t * inner ℝ v q ≤ c := by
    have := mul_nonpos_of_nonneg_of_nonpos ht.le hvq
    linarith
  calc
    _ ≤ (Real.sqrt (1 + t ^ 2))⁻¹ * c :=
      mul_le_mul_of_nonneg_left hnum (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ < c := by
      have hi : (Real.sqrt (1 + t ^ 2))⁻¹ < 1 := (inv_lt_one₀ (by linarith)).mpr hs
      nlinarith

/-- A vertex whose contact directions lie in a closed semicircle can be
moved arbitrarily little so that every one of its pair constraints is strict.
The hypothesis is written directly in tangent inner products. -/
theorem pushing_vertex (Y : Fin 8 → ℝ³) (i : Fin 8) (c : ℝ)
    (hY : ∀ j, ‖Y j‖ = 1) (hc : 0 < c)
    (hbound : ∀ j, j ≠ i → inner ℝ (Y i) (Y j) ≤ c)
    (v : ℝ³) (hv : ‖v‖ = 1) (horth : inner ℝ (Y i) v = 0)
    (hcontact : ∀ j, j ≠ i → inner ℝ (Y i) (Y j) = c → inner ℝ v (Y j) ≤ 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℝ³, ‖p‖ = 1 ∧ dist p (Y i) < ε ∧
      ∀ j, j ≠ i → inner ℝ p (Y j) < c := by
  have hnoncontact : ∀ j : Fin 8, ∀ᶠ t : ℝ in nhds 0,
      inner ℝ (Y i) (Y j) < c → inner ℝ (packingPush (Y i) v t) (Y j) < c := by
    intro j
    by_cases hj : inner ℝ (Y i) (Y j) < c
    · have hcont : ContinuousAt (fun t => inner ℝ (packingPush (Y i) v t) (Y j)) 0 :=
        (packingPush_continuous _ _).continuousAt.inner continuousAt_const
      have h := hcont.tendsto.eventually (eventually_lt_nhds (by simpa using hj))
      filter_upwards [h] with t ht
      exact fun _ => ht
    · exact Filter.Eventually.of_forall (fun _ h => (hj h).elim)
  have hclose : ∀ᶠ t : ℝ in nhds 0, dist (packingPush (Y i) v t) (Y i) < ε := by
    have hcont : ContinuousAt (fun t => dist (packingPush (Y i) v t) (Y i)) (0 : ℝ) :=
      (packingPush_continuous (Y i) v).continuousAt.dist continuousAt_const
    exact hcont.tendsto.eventually (eventually_lt_nhds (by simpa using hε))
  obtain ⟨δ, hδ, hδbound⟩ := Metric.eventually_nhds_iff.mp
    (hclose.and (Filter.eventually_all.mpr hnoncontact))
  let t := δ / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have htδ : dist t 0 < δ := by rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos ht]; dsimp [t]; linarith
  have hb := hδbound htδ
  refine ⟨packingPush (Y i) v t, packingPush_norm _ _ (hY i) hv horth t, hb.1, ?_⟩
  intro j hji
  rcases (hbound j hji).lt_or_eq with hj | hj
  · exact hb.2 j hj
  · exact packingPush_inner_lt _ _ _ c t hc ht hj (hcontact j hji hj)

end SquareAntiprismVerification
