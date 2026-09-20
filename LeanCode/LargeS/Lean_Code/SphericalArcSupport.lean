import Lean_Code.HemisphereCoordinates
import Lean_Code.WeakBoundarySupport

set_option maxHeartbeats 1000000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The normalized affine parametrization of a shorter spherical arc.
The antipodal case is excluded in the theorems that use it. -/
def shortSphereArc (a b : ℝ³) (t : ℝ) : ℝ³ :=
  sphereNormalize ((1 - t) • a + t • b)

lemma shortSphereArc_zero (a b : ℝ³) (ha : ‖a‖ = 1) : shortSphereArc a b 0 = a := by
  simp [shortSphereArc, sphereNormalize, ha]

lemma shortSphereArc_one (a b : ℝ³) (hb : ‖b‖ = 1) : shortSphereArc a b 1 = b := by
  simp [shortSphereArc, sphereNormalize, hb]

lemma unit_pair_sum_support (a b : ℝ³) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hanti : a ≠ -b) : 0 < inner ℝ (a + b) a ∧ 0 < inner ℝ (a + b) b := by
  have hsum : a + b ≠ 0 := by
    intro h
    exact hanti (eq_neg_of_add_eq_zero_left h)
  have hn := norm_pos_iff.mpr hsum
  have hsq := real_inner_self_eq_norm_sq (a + b)
  simp only [inner_add_left, inner_add_right, real_inner_self_eq_norm_sq,
    ha, hb, real_inner_comm b a] at hsq
  constructor <;>
    simp only [inner_add_left, real_inner_self_eq_norm_sq, ha, hb, real_inner_comm b a] <;>
    nlinarith [sq_pos_of_pos hn]

lemma shortSphereArc_combination_ne_zero (a b : ℝ³) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hanti : a ≠ -b) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (1 - t) • a + t • b ≠ 0 := by
  obtain ⟨ha', hb'⟩ := unit_pair_sum_support a b ha hb hanti
  exact inner_pos_ne_zero (a + b) _ (positive_segment_inner (a + b) a b t ha' hb' ht)

lemma shortSphereArc_unit (a b : ℝ³) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hanti : a ≠ -b) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖shortSphereArc a b t‖ = 1 :=
  sphereNormalize_unit _ (shortSphereArc_combination_ne_zero a b ha hb hanti t ht)

lemma shortSphereArc_continuousAt (a b : ℝ³) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hanti : a ≠ -b) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ContinuousAt (shortSphereArc a b) t := by
  have hcomb : ContinuousAt (fun s : ℝ => (1 - s) • a + s • b) t := by fun_prop
  exact ContinuousAt.comp (f := fun s : ℝ => (1 - s) • a + s • b)
    (sphereNormalize_continuousAt _
      (shortSphereArc_combination_ne_zero a b ha hb hanti t ht)) hcomb

/-- Convexity with respect to every nonantipodal shorter arc. It deliberately
does not require hemisphere containment or assume that no antipodal pair exists. -/
def ShortArcClosed (D : Set ℝ³) : Prop :=
  ∀ a ∈ D, ∀ b ∈ D, a ≠ -b →
    ∀ t ∈ Set.Icc (0 : ℝ) 1, shortSphereArc a b t ∈ D

/-- The shortest-path argument supplies `ShortArcClosed`. Once that is known,
local support at a single boundary point is global support of the whole set.
The proof handles potential antipodal points explicitly. -/
theorem global_halfspace_of_local_support (D : Set ℝ³)
    (hunit : ∀ x ∈ D, ‖x‖ = 1) (hconv : ShortArcClosed D)
    (z n : ℝ³) (hz : z ∈ D) (hplane : inner ℝ n z = 0)
    (hlocal : ∃ ε > 0, ∀ x ∈ D, dist x z < ε → 0 ≤ inner ℝ n x) :
    ∀ x ∈ D, 0 ≤ inner ℝ n x := by
  intro x hx
  by_contra hnot
  have hneg : inner ℝ n x < 0 := lt_of_not_ge hnot
  have hanti : z ≠ -x := by
    intro h
    rw [h, inner_neg_right] at hplane
    linarith
  obtain ⟨ε, hε, hs⟩ := hlocal
  have hcont := shortSphereArc_continuousAt z x (hunit z hz) (hunit x hx) hanti 0
    (by norm_num)
  obtain ⟨δ, hδ, hnear⟩ := (Metric.continuousAt_iff.mp hcont) ε hε
  let t : ℝ := min δ 1 / 2
  have ht : 0 < t := half_pos (lt_min hδ zero_lt_one)
  have htδ : t < δ := by dsimp [t]; have := min_le_left δ 1; linarith
  have ht1 : t < 1 := by dsimp [t]; have := min_le_right δ 1; linarith
  have hdist : dist (shortSphereArc z x t) z < ε := by
    have hdt : dist t 0 < δ := by simpa [Real.dist_eq, abs_of_pos ht] using htδ
    simpa only [shortSphereArc_zero z x (hunit z hz)] using hnear hdt
  have hnonneg := hs _ (hconv z hz x hx hanti t ⟨ht.le, ht1.le⟩) hdist
  have hnpos : 0 < ‖(1 - t) • z + t • x‖ := norm_pos_iff.mpr
    (shortSphereArc_combination_ne_zero z x (hunit z hz) (hunit x hx) hanti t ⟨ht.le, ht1.le⟩)
  have hstrict : inner ℝ n (shortSphereArc z x t) < 0 := by
    unfold shortSphereArc
    rw [sphereNormalize_inner]
    simp only [inner_add_right, inner_smul_right, hplane, mul_zero, zero_add]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr hnpos) (mul_neg_of_pos_of_neg ht hneg)
  exact (not_lt_of_ge hnonneg) hstrict

namespace ContactBoundaryCycle

variable {Y : Fin 8 → ℝ³} {c : ℝ} {hY : IsConfiguration Y}
  {hc : c ∈ Set.Ioo (0 : ℝ) 1}

/-- A precise interface to the geometric face proof. Neither the set `D` nor
its shorter-arc closure is postulated globally; both are explicit hypotheses
which must be constructed for each actual boundary before this theorem applies. -/
theorem strict_support_of_short_arc_region (C : ContactBoundaryCycle Y c hY hc)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (D : Set ℝ³) (hunit : ∀ x ∈ D, ‖x‖ = 1) (hconv : ShortArcClosed D)
    (hvertices : ∀ i, Y (C.vertex i) ∈ D)
    (hedges : ∀ i, ∃ z ∈ D,
      inner ℝ (crossVec (Y (C.vertex i)) (Y (C.vertex (i + 1)))) z = 0 ∧
      ∃ ε > 0, ∀ x ∈ D, dist x z < ε →
        0 ≤ inner ℝ (crossVec (Y (C.vertex i)) (Y (C.vertex (i + 1)))) x) :
    C.StrictSupport := by
  apply C.strict_support_of_weak_support hirr hbound
  intro i j
  obtain ⟨z, hz, hplane, hlocal⟩ := hedges i
  exact global_halfspace_of_local_support D hunit hconv z _ hz hplane hlocal
    _ (hvertices j)

end ContactBoundaryCycle
end SquareAntiprismVerification
