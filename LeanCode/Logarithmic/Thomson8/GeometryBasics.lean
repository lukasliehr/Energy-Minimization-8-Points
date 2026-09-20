import Thomson8.Statement
import Thomson8.RootBounds

namespace Thomson8

open scoped InnerProductSpace

theorem a_eq_nodeA : a = nodeA.eval := by
  norm_num [a, nodeA, K.eval, K.evalAt]
  ring

theorem a_pos : 0 < a := by
  rw [a_eq_nodeA]
  have h : (0 : ℚ) < (encloseK nodeA).lo := by decide +kernel
  exact (Rat.cast_pos.mpr h).trans_le (encloseK_contains nodeA).1

theorem a_lt_one : a < 1 := by
  rw [a_eq_nodeA]
  simpa [nodes] using (nodes_interior ⟨0,by decide⟩).2

theorem height_sq : height^2 = a := Real.sq_sqrt a_pos.le
theorem radius_sq : radius^2 = 1-a := Real.sq_sqrt (by linarith [a_lt_one])
theorem radius_pos : 0 < radius := Real.sqrt_pos.mpr (by linarith [a_lt_one])

theorem inner_point (x y z x' y' z' : ℝ) :
    ⟪point x y z, point x' y' z'⟫_ℝ = x*x'+y*y'+z*z' := by
  simp [point, PiLp.inner_apply, Fin.sum_univ_succ, mul_comm, add_assoc]

theorem norm_point_sq (x y z : ℝ) : ‖point x y z‖^2 = x^2+y^2+z^2 := by
  simp [point, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, add_assoc]

theorem antiprism_unit (i : Fin 8) : ‖antiprism i‖=1 := by
  have hs : ‖antiprism i‖^2=1 := by
    fin_cases i <;>
      simp [antiprism, norm_point_sq, div_pow, Real.sq_sqrt, height_sq, radius_sq]
  nlinarith [norm_nonneg (antiprism i)]

noncomputable def phi (t : ℝ) : ℝ := -Real.log (2-2*t)/2

theorem pair_energy_inner (x y : Point) (hx : ‖x‖=1) (hy : ‖y‖=1) :
    -Real.log ‖x-y‖ = phi ⟪x,y⟫_ℝ := by
  have h := norm_sub_sq_real x y
  rw [hx,hy] at h
  have heq : 2-2*⟪x,y⟫_ℝ = ‖x-y‖^2 := by nlinarith
  rw [phi,heq,Real.log_pow]
  ring

theorem inner_unit_bounds (x y : Point) (hx : ‖x‖=1) (hy : ‖y‖=1) :
    -1 ≤ ⟪x,y⟫_ℝ ∧ ⟪x,y⟫_ℝ ≤ 1 := by
  have h := abs_real_inner_le_norm x y
  rw [hx,hy,one_mul] at h
  exact abs_le.mp h

theorem inner_unit_lt_one (x y : Point) (hx : ‖x‖=1) (hy : ‖y‖=1) (hne : x ≠ y) :
    ⟪x,y⟫_ℝ < 1 := by
  have h := norm_sub_sq_real x y
  rw [hx,hy] at h
  have hp : 0 < ‖x-y‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  nlinarith

theorem admissible_inner_lt_one (x : Configuration) (hx : Admissible x)
    (i j : Fin 8) (hij : i ≠ j) : ⟪x i,x j⟫_ℝ < 1 :=
  inner_unit_lt_one _ _ (hx.1 i) (hx.1 j) (fun h => hij (hx.2 h))

end Thomson8
