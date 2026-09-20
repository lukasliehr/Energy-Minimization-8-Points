import Lean_Code.PositiveStress

open Real
noncomputable section
namespace SquareAntiprismVerification

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

def polarP (i : Fin 8) : ℝ³ :=
  !₂[r aInf * cos (azimuth i), r aInf * sin (azimuth i),
    layerSign i * h aInf]

lemma inner_vec3 (x y z u v w : ℝ) :
    inner ℝ (!₂[x, y, z] : ℝ³) (!₂[u, v, w] : ℝ³) =
      x*u + y*v + z*w := by
  simp [PiLp.inner_apply, Fin.sum_univ_succ, RCLike.inner_apply]
  ring

def tangentVector (α β : Fin 8 → ℝ) (i : Fin 8) : ℝ³ :=
  !₂[-r aInf * sin (azimuth i) * α i -
        (aInf / r aInf) * cos (azimuth i) * β i,
      r aInf * cos (azimuth i) * α i -
        (aInf / r aInf) * sin (azimuth i) * β i,
      layerSign i * h aInf * β i]

lemma tangentVector_orthogonal (α β : Fin 8 → ℝ) (i : Fin 8) :
    inner ℝ (tangentVector α β i) (polarP i) = 0 := by
  simp only [tangentVector, polarP]
  rw [inner_vec3]
  have hra : r aInf ^ 2 = 1 - aInf := by
    unfold r
    exact Real.sq_sqrt (by linarith [aInf_mem_Ioo.2])
  have hha : h aInf ^ 2 = aInf := by
    unfold h
    exact Real.sq_sqrt (le_of_lt aInf_mem_Ioo.1)
  have hrne : r aInf ≠ 0 := ne_of_gt (by
    unfold r
    exact Real.sqrt_pos.2 (by linarith [aInf_mem_Ioo.2]))
  have htrig := Real.sin_sq_add_cos_sq (azimuth i)
  have hsign : layerSign i ^ 2 = 1 := by
    fin_cases i <;> simp
  field_simp [hrne]
  rw [hra, hha, hsign]
  linear_combination (-aInf * β i) * htrig

lemma inner_variation_eq_rigidityRow (α β : Fin 8 → ℝ) (i j : Fin 8) :
    inner ℝ (tangentVector α β i) (polarP j) +
      inner ℝ (polarP i) (tangentVector α β j) =
      rigidityRow i j α β := by
  simp only [tangentVector, polarP]
  rw [inner_vec3, inner_vec3]
  simp only [rigidityRow]
  have hra : r aInf ^ 2 = 1 - aInf := by
    unfold r
    exact Real.sq_sqrt (by linarith [aInf_mem_Ioo.2])
  have hha : h aInf ^ 2 = aInf := by
    unfold h
    exact Real.sq_sqrt (le_of_lt aInf_mem_Ioo.1)
  have hrne : r aInf ≠ 0 := ne_of_gt (by
    unfold r
    exact Real.sqrt_pos.2 (by linarith [aInf_mem_Ioo.2]))
  rw [Real.sin_sub, Real.cos_sub]
  field_simp [hrne]
  rw [hra, hha]
  ring

lemma P_eq_polarP : P = polarP := by
  unfold P
  rw [X_eq_Xc]
  funext i
  fin_cases i
  · simp [polarP, Xc]
  · simp [polarP, Xc]
  · simp [polarP, Xc]
  · have hs : sin (3 * π / 2) = -1 := by
      rw [show (3 : ℝ) * π / 2 = π + π / 2 by ring, Real.sin_add]
      simp
    have hc : cos (3 * π / 2) = 0 := by
      rw [show (3 : ℝ) * π / 2 = π + π / 2 by ring, Real.cos_add]
      simp
    simp [polarP, Xc, hs, hc]
  · simp [polarP, Xc, Real.sin_pi_div_four, Real.cos_pi_div_four]
  · have hs : sin (3 * π / 4) = √2 / 2 := by
      rw [show (3 : ℝ) * π / 4 = π / 2 + π / 4 by ring, Real.sin_add]
      simp [Real.sin_pi_div_four, Real.cos_pi_div_four]
    have hc : cos (3 * π / 4) = -√2 / 2 := by
      rw [show (3 : ℝ) * π / 4 = π / 2 + π / 4 by ring, Real.cos_add]
      simp [Real.sin_pi_div_four, Real.cos_pi_div_four]
      ring
    simp [polarP, Xc, hs, hc]
    ring
  · have hs : sin (5 * π / 4) = -√2 / 2 := by
      rw [show (5 : ℝ) * π / 4 = π + π / 4 by ring, Real.sin_add]
      simp [Real.sin_pi_div_four, Real.cos_pi_div_four]
      ring
    have hc : cos (5 * π / 4) = -√2 / 2 := by
      rw [show (5 : ℝ) * π / 4 = π + π / 4 by ring, Real.cos_add]
      simp [Real.sin_pi_div_four, Real.cos_pi_div_four]
      ring
    simp [polarP, Xc, hs, hc]
    ring
  · have hs : sin (7 * π / 4) = -√2 / 2 := by
      rw [show (7 : ℝ) * π / 4 = 2 * π - π / 4 by ring, Real.sin_sub]
      simp [Real.sin_pi_div_four, Real.cos_pi_div_four]
      ring
    have hc : cos (7 * π / 4) = √2 / 2 := by
      rw [show (7 : ℝ) * π / 4 = 2 * π - π / 4 by ring, Real.cos_sub]
      simp [Real.sin_pi_div_four, Real.cos_pi_div_four]
    simp [polarP, Xc, hs, hc]
    ring

/-- Differential at `P` of the squared distance for a coordinate tangent
vector. -/
def squaredDistanceDifferential (i j : Fin 8) (α β : Fin 8 → ℝ) : ℝ :=
  2 * inner ℝ (polarP i - polarP j)
    (tangentVector α β i - tangentVector α β j)

lemma squaredDistanceDifferential_eq (i j : Fin 8) (α β : Fin 8 → ℝ) :
    squaredDistanceDifferential i j α β = -2 * rigidityRow i j α β := by
  have hi := tangentVector_orthogonal α β i
  have hj := tangentVector_orthogonal α β j
  have hij := inner_variation_eq_rigidityRow α β i j
  have hii : inner ℝ (polarP i) (tangentVector α β i) = 0 := by
    rw [real_inner_comm]
    exact hi
  have hjj : inner ℝ (polarP j) (tangentVector α β j) = 0 := by
    rw [real_inner_comm]
    exact hj
  have hji : inner ℝ (polarP j) (tangentVector α β i) =
      inner ℝ (tangentVector α β i) (polarP j) := by
    rw [real_inner_comm]
  unfold squaredDistanceDifferential
  simp only [inner_sub_left, inner_sub_right]
  linarith

end SquareAntiprismVerification
