import Thomson8.GeometryBasics

namespace Thomson8

theorem sqrt_two_inv : (Real.sqrt 2)⁻¹ = Real.sqrt 2/2 := by
  have hp : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  field_simp
  nlinarith

theorem nodeA_formula : nodeA.eval=a := a_eq_nodeA.symm
theorem nodeB_formula : nodeB.eval=2*a-1 := by
  norm_num [nodeB,K.eval,K.evalAt,a]
  ring
theorem nodeC_formula : nodeC.eval = -a+(1-a)/Real.sqrt 2 := by
  rw [div_eq_mul_inv,sqrt_two_inv]
  norm_num [nodeC,K.eval,K.evalAt,a]
  ring
theorem nodeD_formula : nodeD.eval = -a-(1-a)/Real.sqrt 2 := by
  rw [div_eq_mul_inv,sqrt_two_inv]
  norm_num [nodeD,K.eval,K.evalAt,a]
  ring

theorem contact_product : (2-2*nodeC.eval)*(2-2*nodeD.eval)=2*(1+6*a+a^2) := by
  rw [nodeC_formula,nodeD_formula,div_eq_mul_inv,sqrt_two_inv]
  ring_nf
  norm_num [Real.sq_sqrt]
  ring

end Thomson8
