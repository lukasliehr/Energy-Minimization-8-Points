import Lean_Code.PackingConstants
import Lean_Code.RankinBound

set_option maxHeartbeats 1500000
open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The two contact equations and one opposite-vertex packing inequality
select the lower root. No orientation premise is needed. -/
lemma exterior_triangle_coordinates (c r h x y z : ℝ)
    (hc : 0 < c) (hr : 0 < r) (hh : 0 < h)
    (hr2 : r ^ 2 = 1 - c) (hh2 : h ^ 2 = c)
    (hcquad : 7 * c ^ 2 + 2 * c - 1 = 0)
    (hnorm : x ^ 2 + y ^ 2 + z ^ 2 = 1)
    (hx : r * x + h * z = c) (hy : r * y + h * z = c)
    (hopp : -r * x + h * z ≤ c) : z = -h ∧ x = 2 * c / r ∧ y = 2 * c / r := by
  have hx' : x = (c - h * z) / r := (eq_div_iff hr.ne').mpr (by nlinarith)
  have hy' : y = (c - h * z) / r := (eq_div_iff hr.ne').mpr (by nlinarith)
  have hnorm' := hnorm
  rw [hx', hy'] at hnorm'
  field_simp [hr.ne'] at hnorm'
  have hpoly : (1 + c) * z ^ 2 - 4 * c * h * z + 2 * c ^ 2 + c - 1 = 0 := by
    rw [hr2] at hnorm'
    nlinarith [hh2]
  have hzupper : z ≤ h := by nlinarith [hx, hopp, hh2]
  have hfactor : (z + h) * ((1 + c) * z - h * (1 + 5 * c)) = 0 := by
    nlinarith [hpoly, hcquad, hh2]
  have hz : z = -h := by
    rcases mul_eq_zero.mp hfactor with hz | hz
    · linarith
    · have hmul := mul_le_mul_of_nonneg_left hzupper (by linarith : 0 ≤ 1 + c)
      nlinarith [mul_pos hc hh]
  refine ⟨hz, ?_, ?_⟩
  · apply (eq_div_iff hr.ne').mpr
    rw [hz] at hx
    nlinarith [hh2]
  · apply (eq_div_iff hr.ne').mpr
    rw [hz] at hy
    nlinarith [hh2]

lemma aInf_horizontal_identity : 2 * aInf / r aInf = r aInf * Real.sqrt 2 / 2 := by
  have hs : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrpos : 0 < r aInf := Real.sqrt_pos.mpr (by linarith [aInf_mem_Ioo.2])
  have hr2 : r aInf ^ 2 = 1 - aInf := Real.sq_sqrt (by linarith [aInf_mem_Ioo.2])
  have hrel : 1 - aInf = 2 * Real.sqrt 2 * aInf := by
    unfold aInf
    nlinarith
  apply (div_eq_iff hrpos.ne').mpr
  calc
    2 * aInf = (1 - aInf) * Real.sqrt 2 / 2 := by
      linear_combination -(Real.sqrt 2 / 2) * hrel - aInf * hs
    _ = r aInf * Real.sqrt 2 / 2 * r aInf := by rw [← hr2]; ring

theorem exterior_triangle_vertex (x : ℝ³) (hx : ‖x‖ = 1)
    (h0 : inner ℝ (Xc aInf 0) x = aInf)
    (h1 : inner ℝ (Xc aInf 1) x = aInf)
    (h2 : inner ℝ (Xc aInf 2) x ≤ aInf) : x = Xc aInf 4 := by
  have hnorm : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = 1 := by
    have hi : inner ℝ x x = 1 := by simp [hx]
    rw [inner_coordinate_sum] at hi
    simpa [Fin.sum_univ_succ, pow_two, add_assoc] using hi
  have h0' : r aInf * x 0 + h aInf * x 2 = aInf := by
    simpa [Xc, inner_coordinate_sum, Fin.sum_univ_succ] using h0
  have h1' : r aInf * x 1 + h aInf * x 2 = aInf := by
    simpa [Xc, inner_coordinate_sum, Fin.sum_univ_succ] using h1
  have h2' : -(r aInf) * x 0 + h aInf * x 2 ≤ aInf := by
    simpa [Xc, inner_coordinate_sum, Fin.sum_univ_succ] using h2
  obtain ⟨hz, hx0, hx1⟩ := exterior_triangle_coordinates aInf (r aInf) (h aInf)
    (x 0) (x 1) (x 2) aInf_mem_Ioo.1
    (Real.sqrt_pos.mpr (by linarith [aInf_mem_Ioo.2]))
    (Real.sqrt_pos.mpr aInf_mem_Ioo.1)
    (Real.sq_sqrt (by linarith [aInf_mem_Ioo.2]))
    (Real.sq_sqrt aInf_mem_Ioo.1.le) aInf_quadratic hnorm h0' h1' h2'
  rw [aInf_horizontal_identity] at hx0 hx1
  ext i
  fin_cases i
  · simpa [Xc, mul_div_assoc] using hx0
  · simpa [Xc, mul_div_assoc] using hx1
  · simpa [Xc] using hz

theorem exterior_triangle_vertex_cyclic (j : Fin 4) (x : ℝ³) (hx : ‖x‖ = 1)
    (h0 : inner ℝ (Xc aInf (Fin.castAdd 4 j)) x = aInf)
    (h1 : inner ℝ (Xc aInf (Fin.castAdd 4 (j + 1))) x = aInf)
    (h2 : inner ℝ (Xc aInf (Fin.castAdd 4 (j + 2))) x ≤ aInf) :
    x = Xc aInf (Fin.natAdd 4 j) := by
  have hnorm : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = 1 := by
    have hi : inner ℝ x x = 1 := by simp [hx]
    rw [inner_coordinate_sum] at hi
    simpa [Fin.sum_univ_succ, pow_two, add_assoc] using hi
  have hcalc := exterior_triangle_coordinates aInf (r aInf) (h aInf)
  have hcalc' : ∀ x y z : ℝ, x ^ 2 + y ^ 2 + z ^ 2 = 1 →
      r aInf * x + h aInf * z = aInf → r aInf * y + h aInf * z = aInf →
      -(r aInf) * x + h aInf * z ≤ aInf →
      z = -h aInf ∧ x = r aInf * Real.sqrt 2 / 2 ∧ y = r aInf * Real.sqrt 2 / 2 := by
    intro x y z hn h0 h1 h2
    simpa only [aInf_horizontal_identity] using hcalc x y z aInf_mem_Ioo.1
      (Real.sqrt_pos.mpr (by linarith [aInf_mem_Ioo.2]))
      (Real.sqrt_pos.mpr aInf_mem_Ioo.1)
      (Real.sq_sqrt (by linarith [aInf_mem_Ioo.2]))
      (Real.sq_sqrt aInf_mem_Ioo.1.le) aInf_quadratic hn h0 h1 h2
  fin_cases j
  · exact exterior_triangle_vertex x hx h0 h1 h2
  · have h0' : r aInf * x 1 + h aInf * x 2 = aInf := by
      simpa [Xc, inner_coordinate_sum, Fin.sum_univ_succ] using h0
    have h1' : r aInf * (-x 0) + h aInf * x 2 = aInf := by
      simpa [Xc, inner_coordinate_sum, Fin.sum_univ_succ] using h1
    have h2' : -(r aInf) * x 1 + h aInf * x 2 ≤ aInf := by
      simpa [Xc, inner_coordinate_sum, Fin.sum_univ_succ] using h2
    obtain ⟨hz, hy, hx0⟩ := hcalc' (x 1) (-x 0) (x 2) (by nlinarith) h0' h1' h2'
    ext i
    fin_cases i <;> simp [Xc] <;> nlinarith
  · have h0' : r aInf * (-x 0) + h aInf * x 2 = aInf := by
      simpa [Xc, inner_coordinate_sum, Fin.sum_univ_succ] using h0
    have h1' : r aInf * (-x 1) + h aInf * x 2 = aInf := by
      simpa [Xc, inner_coordinate_sum, Fin.sum_univ_succ] using h1
    have h2' : -(r aInf) * (-x 0) + h aInf * x 2 ≤ aInf := by
      simpa [Xc, inner_coordinate_sum, Fin.sum_univ_succ] using h2
    obtain ⟨hz, hx0, hy⟩ := hcalc' (-x 0) (-x 1) (x 2) (by nlinarith) h0' h1' h2'
    ext i
    fin_cases i <;> simp [Xc] <;> nlinarith
  · have h0' : r aInf * (-x 1) + h aInf * x 2 = aInf := by
      simpa [Xc, inner_coordinate_sum, Fin.sum_univ_succ] using h0
    have h1' : r aInf * x 0 + h aInf * x 2 = aInf := by
      simpa [Xc, inner_coordinate_sum, Fin.sum_univ_succ] using h1
    have h2' : -(r aInf) * (-x 1) + h aInf * x 2 ≤ aInf := by
      simpa [Xc, inner_coordinate_sum, Fin.sum_univ_succ] using h2
    obtain ⟨hz, hy, hx0⟩ := hcalc' (-x 1) (x 0) (x 2) (by nlinarith) h0' h1' h2'
    ext i
    fin_cases i <;> simp [Xc] <;> nlinarith

end SquareAntiprismVerification
