import Coulomb8.NodeBounds

namespace Coulomb8

theorem phi_pos {t : ℝ} (ht : t < 1) : 0 < phi t := by
  unfold phi
  exact one_div_pos.mpr (Real.sqrt_pos.mpr (by linarith))

theorem phi_square {t : ℝ} (ht : t < 1) : (2-2*t)*(phi t)^2=1 := by
  have hd : 0 < 2-2*t := by linarith
  unfold phi
  rw [div_pow,one_pow,Real.sq_sqrt hd.le]
  exact mul_one_div_cancel hd.ne'

theorem phi_minus_one : phi (-1)=1/2 := by norm_num [phi]

theorem phi_of_squared_bound {t h : ℝ} (ht : t < 1) (hh : (2-2*t)*h^2 ≤ 1) : h ≤ phi t := by
  have hp := phi_pos ht
  have hs := phi_square ht
  have hd : 0 < 2-2*t := by linarith
  have hsq : h^2 ≤ (phi t)^2 := by nlinarith
  nlinarith

theorem phi_of_squared_strict {t h : ℝ} (ht : t < 1) (hh : (2-2*t)*h^2 < 1) : h < phi t := by
  have hp := phi_pos ht
  have hs := phi_square ht
  have hd : 0 < 2-2*t := by linarith
  have hsq : h^2 < (phi t)^2 := by nlinarith
  nlinarith

end Coulomb8
