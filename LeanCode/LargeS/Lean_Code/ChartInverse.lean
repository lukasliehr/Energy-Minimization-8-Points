import Lean_Code.LocalChart

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Orthogonal projection onto the tangent plane used by the chart. -/
def inverseSphereChart (p y : ℝ³) : ℝ³ := y - (inner ℝ y p) • p

lemma inverseSphereChart_orthogonal (p y : ℝ³) (hp : ‖p‖ = 1) :
    inner ℝ (inverseSphereChart p y) p = 0 := by
  simp [inverseSphereChart, inner_sub_left, inner_smul_left,
    real_inner_self_eq_norm_sq, hp]

lemma inverseSphereChart_norm_sq (p y : ℝ³) (hp : ‖p‖ = 1) (hy : ‖y‖ = 1) :
    ‖inverseSphereChart p y‖ ^ 2 = 1 - (inner ℝ y p) ^ 2 := by
  simp [inverseSphereChart, norm_sub_sq_real, norm_smul, inner_smul_right,
    hp, hy, Real.norm_eq_abs, sq_abs]
  ring

lemma inverseSphereChart_norm_le (p y : ℝ³) (hp : ‖p‖ = 1) (hy : ‖y‖ = 1) :
    ‖inverseSphereChart p y‖ ≤ 1 := by
  have h := inverseSphereChart_norm_sq p y hp hy
  nlinarith [sq_nonneg (inner ℝ y p), norm_nonneg (inverseSphereChart p y)]

lemma sphereChart_inverse (p y : ℝ³) (hp : ‖p‖ = 1) (hy : ‖y‖ = 1)
    (hside : 0 ≤ inner ℝ y p) : sphereChart p (inverseSphereChart p y) = y := by
  have hsq : 1 - ‖inverseSphereChart p y‖ ^ 2 = (inner ℝ y p) ^ 2 := by
    rw [inverseSphereChart_norm_sq p y hp hy]
    ring
  unfold sphereChart
  rw [hsq, Real.sqrt_sq hside]
  simp [inverseSphereChart]

lemma inverseSphereChart_at_center (p : ℝ³) (hp : ‖p‖ = 1) :
    inverseSphereChart p p = 0 := by
  simp [inverseSphereChart, real_inner_self_eq_norm_sq, hp]

lemma inverseSphereChart_continuous (p : ℝ³) : Continuous (inverseSphereChart p) := by
  unfold inverseSphereChart
  fun_prop

/-- The two tangent coordinates obtained from the horizontal components.
On the tangent plane this is inverse to `tangentVector`. -/
def tangentCoordinateInverse (V : Fin 8 → ℝ³) : InfinitesimalCoordinates :=
  (fun i => (-sin (azimuth i) * V i 0 + cos (azimuth i) * V i 1) / r aInf,
   fun i => -(r aInf / aInf) * (cos (azimuth i) * V i 0 + sin (azimuth i) * V i 1))

lemma tangentCoordinateInverse_left (q : InfinitesimalCoordinates) :
    tangentCoordinateInverse (tangentVector q.1 q.2) = q := by
  have hrne : r aInf ≠ 0 := ne_of_gt (by
    unfold r
    exact Real.sqrt_pos.mpr (by linarith [aInf_mem_Ioo.2]))
  have hane : aInf ≠ 0 := ne_of_gt aInf_mem_Ioo.1
  apply Prod.ext <;> funext i
  · simp only [tangentCoordinateInverse, tangentVector, Matrix.cons_val_zero,
      Matrix.cons_val_one, WithLp.equiv_symm_apply, Prod.fst]
    field_simp [hrne]
    have htrig := Real.sin_sq_add_cos_sq (azimuth i)
    linear_combination (r aInf ^ 2 * q.1 i) * htrig
  · simp only [tangentCoordinateInverse, tangentVector, Matrix.cons_val_zero,
      Matrix.cons_val_one, WithLp.equiv_symm_apply, Prod.snd]
    field_simp [hrne, hane]
    have htrig := Real.sin_sq_add_cos_sq (azimuth i)
    linear_combination (aInf * q.2 i) * htrig

lemma tangentCoordinateInverse_right (V : Fin 8 → ℝ³)
    (hV : ∀ i, inner ℝ (V i) (polarP i) = 0) :
    tangentVector (tangentCoordinateInverse V).1 (tangentCoordinateInverse V).2 = V := by
  have hrne : r aInf ≠ 0 := ne_of_gt (by
    unfold r
    exact Real.sqrt_pos.mpr (by linarith [aInf_mem_Ioo.2]))
  have hane : aInf ≠ 0 := ne_of_gt aInf_mem_Ioo.1
  have hha : h aInf ^ 2 = aInf := Real.sq_sqrt aInf_mem_Ioo.1.le
  funext i
  have htrig := Real.sin_sq_add_cos_sq (azimuth i)
  have hsign : layerSign i ^ 2 = 1 := by fin_cases i <;> simp
  have horth : r aInf * (cos (azimuth i) * V i 0 + sin (azimuth i) * V i 1) +
      layerSign i * h aInf * V i 2 = 0 := by
    have hi := hV i
    simp [polarP, PiLp.inner_apply, Fin.sum_univ_succ, RCLike.inner_apply] at hi
    nlinarith
  ext k
  fin_cases k
  · simp [tangentVector, tangentCoordinateInverse]
    field_simp [hrne, hane]
    linear_combination (V i 0) * htrig
  · simp [tangentVector, tangentCoordinateInverse]
    field_simp [hrne, hane]
    linear_combination (V i 1) * htrig
  · simp [tangentVector, tangentCoordinateInverse]
    field_simp [hane]
    linear_combination (-layerSign i * h aInf) * horth +
      (V i 2 * h aInf ^ 2) * hsign + (V i 2) * hha

lemma tangentCoordinateInverse_continuous : Continuous tangentCoordinateInverse := by
  unfold tangentCoordinateInverse
  fun_prop

def coordinateInverse (Y : Fin 8 → ℝ³) : InfinitesimalCoordinates :=
  tangentCoordinateInverse (fun i => inverseSphereChart (polarP i) (Y i))

lemma coordinateInverse_continuous : Continuous coordinateInverse := by
  apply tangentCoordinateInverse_continuous.comp
  unfold inverseSphereChart
  fun_prop

lemma coordinateInverse_P : coordinateInverse P = 0 := by
  have hproj : (fun i => inverseSphereChart (polarP i) (P i)) = 0 := by
    funext i
    rw [P_eq_polarP]
    exact inverseSphereChart_at_center _ (polarP_norm i)
  unfold coordinateInverse
  rw [hproj]
  simp [tangentCoordinateInverse]
  rfl

lemma coordinateChart_inverse (Y : Fin 8 → ℝ³) (hY : ∀ i, ‖Y i‖ = 1)
    (hside : ∀ i, 0 ≤ inner ℝ (Y i) (polarP i)) :
    coordinateChart (coordinateInverse Y) = Y := by
  have hv := tangentCoordinateInverse_right
    (fun i => inverseSphereChart (polarP i) (Y i))
    (fun i => inverseSphereChart_orthogonal _ _ (polarP_norm i))
  funext i
  change sphereChart (polarP i) (tangentVector (coordinateInverse Y).1
    (coordinateInverse Y).2 i) = Y i
  rw [show tangentVector (coordinateInverse Y).1 (coordinateInverse Y).2 i =
    inverseSphereChart (polarP i) (Y i) from congr_fun hv i]
  exact sphereChart_inverse _ _ (polarP_norm i) (hY i) (hside i)

lemma inverseSphereChart_sphereChart (p v : ℝ³) (hp : ‖p‖ = 1)
    (hv : inner ℝ v p = 0) : inverseSphereChart p (sphereChart p v) = v := by
  simp [inverseSphereChart, sphereChart, inner_add_left, inner_smul_left, hp, hv]

lemma coordinateInverse_left (q : InfinitesimalCoordinates) :
    coordinateInverse (coordinateChart q) = q := by
  unfold coordinateInverse coordinateChart
  have hproj : (fun i => inverseSphereChart (polarP i)
      (sphereChart (polarP i) (tangentVector q.1 q.2 i))) = tangentVector q.1 q.2 := by
    funext i
    exact inverseSphereChart_sphereChart _ _ (polarP_norm i)
      (tangentVector_orthogonal q.1 q.2 i)
  rw [hproj]
  exact tangentCoordinateInverse_left q

lemma coordinateChart_injective : Function.Injective coordinateChart := by
  exact Function.LeftInverse.injective coordinateInverse_left

end SquareAntiprismVerification
