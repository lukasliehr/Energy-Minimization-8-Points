import Thomson8.NodeFormulas
import Thomson8.HermiteValues

namespace Thomson8

theorem optimalEnergy_logs : optimalEnergy =
    -2*logValues 1-6*logValues 2-4*logValues 3-4*logValues 4 := by
  have hA : 0 < 1-a := by linarith [a_lt_one]
  have hC : 2-2*nodeC.eval ≠ 0 := by
    have h := (nodes_interior ⟨2,by decide⟩).2
    simp only [nodes,List.getD_cons_succ,List.getD_cons_zero] at h
    linarith
  have hD : 2-2*nodeD.eval ≠ 0 := by
    have h := (nodes_interior ⟨3,by decide⟩).2
    simp only [nodes,List.getD_cons_succ,List.getD_cons_zero] at h
    linarith
  have hP : 1+6*a+a^2 ≠ 0 := by nlinarith [a_pos,sq_nonneg a]
  have hlog := Real.log_mul hC hD
  rw [contact_product,Real.log_mul (by norm_num) hP] at hlog
  have hlogA : Real.log (2-2*nodeA.eval) = Real.log 2+Real.log (1-a) := by
    rw [nodeA_formula,show 2-2*a=2*(1-a) by ring,Real.log_mul (by norm_num) hA.ne']
  norm_num [logValues,logInput,optimalEnergy]
  rw [show (2 : ℝ)+ -(2*nodeA.eval)=2-2*nodeA.eval by ring]
  rw [hlogA]
  linear_combination -4*hlog

end Thomson8
