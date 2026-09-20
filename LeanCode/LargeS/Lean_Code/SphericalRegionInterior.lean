import Lean_Code.InteriorChainShortening

set_option maxHeartbeats 1000000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- An ambient open set whose unit points are exactly the relative interior
points of the spherical region. Off-sphere points are harmless here. -/
def sphericalInteriorAmbient (D : Set ℝ³) : Set ℝ³ :=
  interior (D ∪ {x | ‖x‖ ≠ 1})

lemma sphericalInteriorAmbient_isOpen (D : Set ℝ³) : IsOpen (sphericalInteriorAmbient D) :=
  isOpen_interior

lemma sphericalInteriorAmbient_unit_mem {D : Set ℝ³} {x : ℝ³}
    (hx : x ∈ sphericalInteriorAmbient D) (hu : ‖x‖ = 1) : x ∈ D := by
  rcases interior_subset hx with h | h
  · exact h
  · exact (h hu).elim

lemma mem_sphericalInteriorAmbient_of_open {D U : Set ℝ³} (hU : IsOpen U)
    (hUD : ∀ x ∈ U, ‖x‖ = 1 → x ∈ D) {x : ℝ³} (hx : x ∈ U) :
    x ∈ sphericalInteriorAmbient D := by
  apply (interior_maximal ?_ hU) hx
  intro y hy
  by_cases hu : ‖y‖ = 1
  · exact Or.inl (hUD y hy hu)
  · exact Or.inr hu

/-- A genuine supporting plane through a unit point rules out relative
interiority. A small normalized tangent perturbation crosses that plane. -/
theorem not_sphericalInterior_of_local_support {D : Set ℝ³} (x n : ℝ³)
    (hx : ‖x‖ = 1) (hn : n ≠ 0) (hplane : inner ℝ n x = 0)
    (U : Set ℝ³) (hU : U ∈ nhds x)
    (hsupport : ∀ y ∈ D, y ∈ U → 0 ≤ inner ℝ n y) :
    x ∉ sphericalInteriorAmbient D := by
  intro hxin
  let t := -sphereNormalize n
  have ht : ‖t‖ = 1 := by simpa [t] using sphereNormalize_unit n hn
  have hxt : inner ℝ x t = 0 := by
    simp only [t, inner_neg_right, sphereNormalize_inner, real_inner_comm n x, hplane, mul_zero, neg_zero]
  have hnt : inner ℝ n t = -‖n‖ := by
    simp only [t, inner_neg_right, sphereNormalize_inner, real_inner_self_eq_norm_sq]
    field_simp
  let W := sphericalInteriorAmbient D ∩ U
  have hW : W ∈ nhds x := Filter.inter_mem
    ((sphericalInteriorAmbient_isOpen D).mem_nhds hxin) hU
  have hW0 : W ∈ nhds (greatCirclePoint x t 0) := by
    simpa only [greatCirclePoint_zero] using hW
  have hevent : {s | greatCirclePoint x t s ∈ W} ∈ nhds (0 : ℝ) :=
    (greatCirclePoint_continuous x t).continuousAt hW0
  obtain ⟨s, hsW, hs0, hspi⟩ := exists_small_positive_in_neighborhood _ hevent Real.pi Real.pi_pos
  have hunit := greatCirclePoint_unit x t hx ht hxt s
  have hD := sphericalInteriorAmbient_unit_mem hsW.1 hunit
  have hge := hsupport _ hD hsW.2
  have hneg : inner ℝ n (greatCirclePoint x t s) < 0 := by
    simp only [greatCirclePoint, inner_add_right, inner_smul_right, hplane, hnt, mul_zero, zero_add]
    exact mul_neg_of_pos_of_neg (Real.sin_pos_of_pos_of_lt_pi hs0 hspi)
      (neg_neg_of_pos (norm_pos_iff.mpr hn))
  exact (not_lt_of_ge hge) hneg

lemma sphericalInterior_of_strict_local_model {D U : Set ℝ³} {k : ℕ}
    (normal : Fin k → ℝ³) (hU : IsOpen U)
    (hmodel : ∀ y ∈ U, y ∈ D ↔ ‖y‖ = 1 ∧ ∀ i, 0 ≤ inner ℝ (normal i) y)
    (x : ℝ³) (hxU : x ∈ U) (hstrict : ∀ i, normal i = 0 ∨ 0 < inner ℝ (normal i) x) :
    x ∈ sphericalInteriorAmbient D := by
  let V : Set ℝ³ := ⋂ i, {y | normal i = 0 ∨ 0 < inner ℝ (normal i) y}
  have hV : IsOpen V := by
    apply isOpen_iInter_of_finite
    intro i
    by_cases hi : normal i = 0
    · simp [hi]
    · simp only [hi, false_or]
      exact isOpen_lt continuous_const (by fun_prop)
  apply mem_sphericalInteriorAmbient_of_open (hU.inter hV) ?_ ⟨hxU, ?_⟩
  · intro y hy hyunit
    apply (hmodel y hy.1).mpr
    refine ⟨hyunit, ?_⟩
    intro i
    have hi := Set.mem_iInter.mp hy.2 i
    rcases hi with hi | hi
    · simp [hi]
    · exact hi.le
  · exact Set.mem_iInter.mpr hstrict

/-- A noninterior point of an exact local halfspace model lies on at least
one of its nonzero supporting planes. -/
lemma active_normal_of_not_sphericalInterior {D U : Set ℝ³} {k : ℕ}
    (normal : Fin k → ℝ³) (hU : IsOpen U)
    (hmodel : ∀ y ∈ U, y ∈ D ↔ ‖y‖ = 1 ∧ ∀ i, 0 ≤ inner ℝ (normal i) y)
    (x : ℝ³) (hxU : x ∈ U) (hxD : x ∈ D) (hx : x ∉ sphericalInteriorAmbient D) :
    ∃ i, normal i ≠ 0 ∧ inner ℝ (normal i) x = 0 := by
  by_contra hn
  push_neg at hn
  apply hx
  apply sphericalInterior_of_strict_local_model normal hU hmodel x hxU
  intro i
  by_cases hi : normal i = 0
  · exact Or.inl hi
  · exact Or.inr (lt_of_le_of_ne (((hmodel x hxU).mp hxD).2 i) (Ne.symm (hn i hi)))

end SquareAntiprismVerification
