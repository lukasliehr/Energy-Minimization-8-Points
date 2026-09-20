import Lean_Code.ContactFaceRegions
import Lean_Code.RhombusGram

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- At a nearest vertex of a contact triangle, the corner sector cannot
extend beyond the opposite side. -/
lemma triangle_maximal_corner_cone (a b d z : ℝ³) (c : ℝ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hc : c < 1)
    (hab : inner ℝ a b = c) (had : inner ℝ a d = c) (hbd : inner ℝ b d = c)
    (ht : 0 < inner ℝ (crossVec a b) d)
    (hleft : 0 ≤ inner ℝ (crossVec a b) z)
    (hright : 0 ≤ inner ℝ (crossVec d a) z)
    (hmax : inner ℝ b z ≤ inner ℝ a z) :
    ∃ l μ ν : ℝ, 0 ≤ l ∧ 0 ≤ μ ∧ 0 ≤ ν ∧ z = l • a + μ • b + ν • d := by
  have hba : inner ℝ b a = c := (real_inner_comm a b).trans hab
  have h := congrArg (fun w : ℝ³ => inner ℝ (a - b) w) (triple_cramer a b d z)
  simp only [inner_smul_right, inner_add_right, inner_sub_left,
    real_inner_self_eq_norm_sq, ha, hb, hab, hba, had, hbd, one_pow] at h
  have hbase : 0 ≤ inner ℝ (crossVec b d) z := by
    have hp := mul_nonneg ht.le (sub_nonneg.mpr hmax)
    have hq := mul_nonneg hright (sub_nonneg.mpr hc.le)
    nlinarith
  exact spherical_triangle_cone a b d z ht hleft hbase hright

/-- In a rhombus, the opposite vertex separates the nearest-vertex sector
from the other half of the rhombus. The two side vertices are equidistant
from the opposite vertices, so the Cramer coefficient has a fixed sign. -/
lemma rhombus_maximal_corner_cone (a b d e z : ℝ³) (c : ℝ)
    (ha : ‖a‖ = 1) (had : inner ℝ a d < 1)
    (hab : inner ℝ a b = c) (hdb : inner ℝ d b = c)
    (hae : inner ℝ a e = c) (hde : inner ℝ d e = c)
    (ht : 0 < inner ℝ (crossVec a b) e)
    (hleft : 0 ≤ inner ℝ (crossVec a b) z)
    (hright : 0 ≤ inner ℝ (crossVec e a) z)
    (hmax : inner ℝ d z ≤ inner ℝ a z) :
    ∃ l μ ν : ℝ, 0 ≤ l ∧ 0 ≤ μ ∧ 0 ≤ ν ∧ z = l • a + μ • b + ν • e := by
  have hda : inner ℝ d a = inner ℝ a d := real_inner_comm a d
  have h := congrArg (fun w : ℝ³ => inner ℝ (a - d) w) (triple_cramer a b e z)
  simp only [inner_smul_right, inner_add_right, inner_sub_left,
    real_inner_self_eq_norm_sq, ha, hda, hab, hdb, hae, hde, one_pow] at h
  have hbase : 0 ≤ inner ℝ (crossVec b e) z := by
    have hp := mul_nonneg ht.le (sub_nonneg.mpr hmax)
    nlinarith
  exact spherical_triangle_cone a b e z ht hleft hbase hright

namespace StrictSphericalPolygon

lemma cone_mem_closedRegion {n : ℕ} (Q : StrictSphericalPolygon n)
    (i j k : Fin (n + 3)) (z : ℝ³) (hz : ‖z‖ = 1) (l μ ν : ℝ)
    (hl : 0 ≤ l) (hμ : 0 ≤ μ) (hν : 0 ≤ ν)
    (hrep : z = l • Q.vertex i + μ • Q.vertex j + ν • Q.vertex k) : z ∈ Q.closedRegion := by
  refine ⟨hz, fun m => ?_⟩
  have hnonneg (r : Fin (n + 3)) :
      0 ≤ inner ℝ (crossVec (Q.vertex m) (Q.vertex (m + 1))) (Q.vertex r) := by
    by_cases hr : r = m
    · subst r; simp [crossVec_inner_left]
    by_cases hr' : r = m + 1
    · subst r; simp [crossVec_inner_right]
    exact (Q.support m r hr hr').le
  rw [hrep, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right, inner_smul_right]
  exact add_nonneg (add_nonneg (mul_nonneg hl (hnonneg i)) (mul_nonneg hμ (hnonneg j)))
    (mul_nonneg hν (hnonneg k))

theorem maximal_corner_mem_region {n : ℕ} (Q : StrictSphericalPolygon n) (c : ℝ)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c ≤ aInf)
    (hcontact : ∀ i, inner ℝ (Q.vertex i) (Q.vertex (i + 1)) = c)
    (z : ℝ³) (hz : ‖z‖ = 1)
    (hmax : ∀ j, inner ℝ (Q.vertex j) z ≤ inner ℝ (Q.vertex 0) z)
    (hleft : 0 ≤ inner ℝ (crossVec (Q.vertex 0) (Q.vertex 1)) z)
    (hright : 0 ≤ inner ℝ (crossVec (Q.vertex (0 - 1)) (Q.vertex 0)) z) :
    z ∈ Q.closedRegion := by
  have hn := contact_polygon_three_or_four Q c hc.1 hcupper hcontact
  have hn' : n = 0 ∨ n = 1 := by omega
  rcases hn' with rfl | rfl
  · have h02 : inner ℝ (Q.vertex 0) (Q.vertex 2) = c :=
      (real_inner_comm (Q.vertex 2) (Q.vertex 0)).trans (hcontact 2)
    obtain ⟨l, μ, ν, hl, hμ, hν, hrep⟩ := triangle_maximal_corner_cone
      (Q.vertex 0) (Q.vertex 1) (Q.vertex 2) z c (Q.unit 0) (Q.unit 1) hc.2
      (hcontact 0) h02 (hcontact 1) (Q.turn_pos 0) hleft hright (hmax 1)
    exact Q.cone_mem_closedRegion 0 1 2 z hz l μ ν hl hμ hν hrep
  · have h02 : Q.vertex 0 ≠ Q.vertex 2 := by
      intro heq
      have ht := Q.turn_pos 0
      change 0 < inner ℝ (crossVec (Q.vertex 0) (Q.vertex 1)) (Q.vertex 2) at ht
      rw [← heq, crossVec_inner_left] at ht
      exact lt_irrefl 0 ht
    have h03 : inner ℝ (Q.vertex 0) (Q.vertex 3) = c :=
      (real_inner_comm (Q.vertex 3) (Q.vertex 0)).trans (hcontact 3)
    have h21 : inner ℝ (Q.vertex 2) (Q.vertex 1) = c :=
      (real_inner_comm (Q.vertex 1) (Q.vertex 2)).trans (hcontact 1)
    obtain ⟨l, μ, ν, hl, hμ, hν, hrep⟩ := rhombus_maximal_corner_cone
      (Q.vertex 0) (Q.vertex 1) (Q.vertex 2) (Q.vertex 3) z c (Q.unit 0)
      (unit_inner_lt_one _ _ (Q.unit 0) (Q.unit 2) h02) (hcontact 0) h21 h03 (hcontact 2)
      (Q.support 0 3 (by decide) (by decide)) hleft hright (hmax 2)
    exact Q.cone_mem_closedRegion 0 1 3 z hz l μ ν hl hμ hν hrep

end StrictSphericalPolygon

end SquareAntiprismVerification
