import Lean_Code.Infinitesimal
import Lean_Code.ContactRankBound

open Real
noncomputable section
namespace SquareAntiprismVerification

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The square-root chart from the paper, applied to one tangent vector. -/
def sphereChart (p v : ℝ³) : ℝ³ := √(1 - ‖v‖ ^ 2) • p + v

lemma sphereChart_norm (p v : ℝ³) (hp : ‖p‖ = 1)
    (hv : inner ℝ v p = 0) (hsmall : ‖v‖ ≤ 1) :
    ‖sphereChart p v‖ = 1 := by
  have hrad : 0 ≤ 1 - ‖v‖ ^ 2 := by nlinarith [norm_nonneg v]
  have hsqrt := Real.sq_sqrt hrad
  have hpv : inner ℝ p v = 0 := by rw [real_inner_comm]; exact hv
  have hsq : ‖sphereChart p v‖ ^ 2 = 1 := by
    simp [sphereChart, norm_add_sq_real, norm_smul, inner_smul_left, hp, hpv,
      Real.norm_eq_abs, sq_abs, hsqrt]
  nlinarith [norm_nonneg (sphereChart p v)]

@[simp] lemma sphereChart_zero (p : ℝ³) : sphereChart p 0 = p := by
  simp [sphereChart]

def coordinateChart (q : InfinitesimalCoordinates) (i : Fin 8) : ℝ³ :=
  sphereChart (polarP i) (tangentVector q.1 q.2 i)

lemma polarP_norm (i : Fin 8) : ‖polarP i‖ = 1 := by
  rw [← P_eq_polarP]
  exact X_mem_unitSphere aInf aInf_mem_Ioo i

lemma coordinateChart_mem_sphere (q : InfinitesimalCoordinates) (i : Fin 8)
    (hq : ‖tangentVector q.1 q.2 i‖ ≤ 1) :
    coordinateChart q i ∈ unitSphere := by
  exact sphereChart_norm _ _ (polarP_norm i)
    (tangentVector_orthogonal q.1 q.2 i) hq

lemma tangentVector_smul (c : ℝ) (q : InfinitesimalCoordinates) (i : Fin 8) :
    tangentVector (c • q).1 (c • q).2 i = c • tangentVector q.1 q.2 i := by
  simp only [tangentVector]
  ext k
  fin_cases k <;> simp <;> ring

@[simp] lemma tangentVector_zero (i : Fin 8) : tangentVector 0 0 i = 0 := by
  ext k
  fin_cases k <;> simp [tangentVector]

@[simp] lemma coordinateChart_zero (i : Fin 8) : coordinateChart 0 i = polarP i := by
  simp [coordinateChart]

def tangentVectorLinear (i : Fin 8) : InfinitesimalCoordinates →ₗ[ℝ] ℝ³ where
  toFun q := tangentVector q.1 q.2 i
  map_add' q q' := by
    ext k
    fin_cases k <;> simp [tangentVector] <;> ring
  map_smul' c q := tangentVector_smul c q i

lemma tangentVector_contDiff (i : Fin 8) :
    ContDiff ℝ 2 (fun q : InfinitesimalCoordinates => tangentVector q.1 q.2 i) := by
  exact (LinearMap.toContinuousLinearMap (tangentVectorLinear i)).contDiff

lemma coordinateChart_contDiffAt (i : Fin 8) :
    ContDiffAt ℝ 2 (fun q => coordinateChart q i) 0 := by
  have ht := (tangentVector_contDiff i).contDiffAt (x := (0 : InfinitesimalCoordinates))
  have hg : ContDiffAt ℝ 2 (fun q : InfinitesimalCoordinates =>
      1 - ‖tangentVector q.1 q.2 i‖ ^ 2) 0 := contDiffAt_const.sub (ht.norm_sq ℝ)
  have hs := hg.sqrt (by simp)
  exact (hs.smul contDiffAt_const).add ht

def chartRay (q : InfinitesimalCoordinates) (t : ℝ) (i : Fin 8) : ℝ³ :=
  let v := tangentVector q.1 q.2 i
  √(1 - t ^ 2 * ‖v‖ ^ 2) • polarP i + t • v

lemma coordinateChart_smul (q : InfinitesimalCoordinates) (t : ℝ) (i : Fin 8) :
    coordinateChart (t • q) i = chartRay q t i := by
  unfold coordinateChart sphereChart
  rw [tangentVector_smul]
  simp [chartRay, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

@[simp] lemma chartRay_zero (q : InfinitesimalCoordinates) (i : Fin 8) :
    chartRay q 0 i = polarP i := by
  simp [chartRay]

lemma chartRay_hasDerivAt (q : InfinitesimalCoordinates) (i : Fin 8) :
    HasDerivAt (fun t => chartRay q t i) (tangentVector q.1 q.2 i) 0 := by
  let v := tangentVector q.1 q.2 i
  have hg : HasDerivAt (fun t : ℝ => 1 - t ^ 2 * ‖v‖ ^ 2) 0 0 := by
    simpa using (((hasDerivAt_id (𝕜 := ℝ) 0).pow 2).mul_const
      (‖v‖ ^ 2)).const_sub 1
  have hsqrt : HasDerivAt (fun t : ℝ => √(1 - t ^ 2 * ‖v‖ ^ 2)) 0 0 := by
    simpa [Function.comp_def] using (Real.hasDerivAt_sqrt
      (x := 1 - (0 : ℝ) ^ 2 * ‖v‖ ^ 2) (by norm_num)).comp 0 hg
  have hfirst := hsqrt.smul_const (polarP i)
  have hsecond := (hasDerivAt_id (𝕜 := ℝ) 0).smul_const v
  convert! hfirst.add hsecond using 1 <;> simp [chartRay, v, Pi.add_apply]

def chartSquaredDistance (q : InfinitesimalCoordinates) (t : ℝ)
    (i j : Fin 8) : ℝ := ‖chartRay q t i - chartRay q t j‖ ^ 2

lemma chartSquaredDistance_hasDerivAt (q : InfinitesimalCoordinates)
    (i j : Fin 8) :
    HasDerivAt (fun t => chartSquaredDistance q t i j)
      (squaredDistanceDifferential i j q.1 q.2) 0 := by
  have hi := chartRay_hasDerivAt q i
  have hj := chartRay_hasDerivAt q j
  have h := (hi.sub hj).norm_sq
  simpa [chartSquaredDistance, Pi.sub_apply, chartRay_zero,
    squaredDistanceDifferential] using h

lemma chartSquaredDistance_deriv (q : InfinitesimalCoordinates)
    (i j : Fin 8) :
    deriv (fun t => chartSquaredDistance q t i j) 0 =
      -2 * rigidityRow i j q.1 q.2 := by
  rw [(chartSquaredDistance_hasDerivAt q i j).deriv,
    squaredDistanceDifferential_eq]

end SquareAntiprismVerification
