import Lean_Code.ChartInverse

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

def sliceTargetDen : ℝ := 1 - aInf + aInf ^ 2
def sliceTargetU (t : ℝ) : ℝ :=
  (r aInf * t - aInf * √(sliceTargetDen - t ^ 2)) / sliceTargetDen
def sliceTargetW (t : ℝ) : ℝ :=
  (aInf * t + r aInf * √(sliceTargetDen - t ^ 2)) / sliceTargetDen

/-- Canonical position of vertex one after vertex zero has been fixed.
It has prescribed inner product `t` with vertex zero and lies in the
plane required by the coordinate gauge. -/
def sliceTarget (t : ℝ) : ℝ³ :=
  !₂[sliceTargetU t, r aInf * sliceTargetW t, h aInf * sliceTargetW t]

lemma sliceTargetDen_pos : 0 < sliceTargetDen := by
  unfold sliceTargetDen
  nlinarith [aInf_mem_Ioo.2, sq_nonneg aInf]

lemma sliceTarget_coefficients (t : ℝ) (ht : t ^ 2 ≤ sliceTargetDen) :
    sliceTargetU t ^ 2 + sliceTargetW t ^ 2 = 1 := by
  have hr : r aInf ^ 2 = 1 - aInf := Real.sq_sqrt (by linarith [aInf_mem_Ioo.2])
  have hs : √(sliceTargetDen - t ^ 2) ^ 2 = sliceTargetDen - t ^ 2 :=
    Real.sq_sqrt (by linarith)
  unfold sliceTargetU sliceTargetW
  field_simp [ne_of_gt sliceTargetDen_pos]
  calc
    _ = (r aInf ^ 2 + aInf ^ 2) * (t ^ 2 + √(sliceTargetDen - t ^ 2) ^ 2) := by ring
    _ = sliceTargetDen ^ 2 := by
      rw [hr, hs]
      dsimp [sliceTargetDen]
      ring

lemma sliceTarget_norm (t : ℝ) (ht : t ^ 2 ≤ sliceTargetDen) :
    ‖sliceTarget t‖ = 1 := by
  have hr : r aInf ^ 2 = 1 - aInf := Real.sq_sqrt (by linarith [aInf_mem_Ioo.2])
  have hh : h aInf ^ 2 = aInf := Real.sq_sqrt aInf_mem_Ioo.1.le
  have hc := sliceTarget_coefficients t ht
  have hn : sliceTargetU t ^ 2 + (r aInf * sliceTargetW t) ^ 2 +
      (h aInf * sliceTargetW t) ^ 2 = 1 := by
    rw [mul_pow, mul_pow, hr, hh]
    nlinarith
  rw [sliceTarget, norm_vec3, hn]
  norm_num

lemma sliceTarget_inner (t : ℝ) : inner ℝ (sliceTarget t) (polarP 0) = t := by
  simp only [sliceTarget, polarP, azimuth_0, layerSign_0, cos_zero, sin_zero,
    mul_one, mul_zero]
  rw [inner_vec3]
  have hr : r aInf ^ 2 = 1 - aInf := Real.sq_sqrt (by linarith [aInf_mem_Ioo.2])
  have hh : h aInf ^ 2 = aInf := Real.sq_sqrt aInf_mem_Ioo.1.le
  unfold sliceTargetU sliceTargetW
  field_simp [ne_of_gt sliceTargetDen_pos]
  dsimp [sliceTargetDen]
  rw [hh]
  linear_combination t * hr

lemma sliceTarget_at_center : sliceTarget aInf = polarP 1 := by
  have hrad : sliceTargetDen - aInf ^ 2 = 1 - aInf := by
    unfold sliceTargetDen
    ring
  have hr : r aInf ^ 2 = 1 - aInf := Real.sq_sqrt (by linarith [aInf_mem_Ioo.2])
  have hu : sliceTargetU aInf = 0 := by
    simp [sliceTargetU, hrad, r, mul_comm]
  have hw : sliceTargetW aInf = 1 := by
    unfold sliceTargetW
    rw [hrad]
    change (aInf * aInf + r aInf * r aInf) / sliceTargetDen = 1
    apply (div_eq_one_iff_eq (ne_of_gt sliceTargetDen_pos)).mpr
    dsimp [sliceTargetDen]
    nlinarith
  simp [sliceTarget, hu, hw, polarP]

lemma sliceTarget_continuous : Continuous sliceTarget := by
  unfold sliceTarget sliceTargetU sliceTargetW
  fun_prop

lemma inverseSphereChart_sliceTarget (t : ℝ) :
    inverseSphereChart (polarP 1) (sliceTarget t) = !₂[sliceTargetU t, 0, 0] := by
  have hr : r aInf ^ 2 = 1 - aInf := Real.sq_sqrt (by linarith [aInf_mem_Ioo.2])
  have hh : h aInf ^ 2 = aInf := Real.sq_sqrt aInf_mem_Ioo.1.le
  have hin : inner ℝ (sliceTarget t) (polarP 1) = sliceTargetW t := by
    simp [sliceTarget, polarP, inner_vec3]
    linear_combination (sliceTargetW t) * hr + (sliceTargetW t) * hh
  unfold inverseSphereChart
  rw [hin]
  ext k
  fin_cases k <;> simp [sliceTarget, polarP] <;> ring

lemma coordinateInverse_in_gauge (Y : Fin 8 → ℝ³) (t : ℝ)
    (h₀ : Y 0 = polarP 0) (h₁ : Y 1 = sliceTarget t) :
    InContactGauge (coordinateInverse Y) := by
  have hzero : inverseSphereChart (polarP 0) (Y 0) = 0 := by
    rw [h₀]
    exact inverseSphereChart_at_center _ (polarP_norm 0)
  have hone : inverseSphereChart (polarP 1) (Y 1) = !₂[sliceTargetU t, 0, 0] := by
    rw [h₁]
    exact inverseSphereChart_sliceTarget t
  simp [InContactGauge, coordinateInverse, tangentCoordinateInverse, hzero, hone]

end SquareAntiprismVerification
