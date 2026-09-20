import Thomson8.HermiteChecks
import Thomson8.EvaluateK
import Thomson8.GeometryBasics
import Thomson8.LogConstants

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Thomson8

noncomputable def H (x : ℝ) : ℝ :=
  ∑ ell : Fin 5, logValues ell * (hermiteComponent Data.hermite ell).eval x 0 0

theorem hermite_value_check (i : Fin 4) (ell : Fin 5) :
    (hermiteComponent Data.hermite ell).evalK (nodes.getD i K.zero) K.zero K.zero =
      contactValue i ell := by
  fin_cases i <;> fin_cases ell <;> decide +kernel

theorem hermite_minus_one_check (ell : Fin 5) :
    (hermiteComponent Data.hermite ell).evalK (K.ofRat (-1)) K.zero K.zero =
      K.ofRat (if ell=1 then -1 else 0) := by
  fin_cases ell <;> decide +kernel

theorem H_node_formula (i : Fin 4) : H (nodes.getD i K.zero).eval =
    ∑ ell : Fin 5, logValues ell * (contactValue i ell).eval := by
  apply Finset.sum_congr rfl
  intro ell _
  congr 1
  have h := congrArg K.eval (hermite_value_check i ell)
  simpa [Poly.eval_evalK] using h

theorem H_minus_one : H (-1) = phi (-1) := by
  have h (ell : Fin 5) := congrArg K.eval (hermite_minus_one_check ell)
  simp only [Poly.eval_evalK,K.eval_ofRat,K.eval_zero,Rat.cast_neg,Rat.cast_one,
    Rat.cast_zero] at h
  simp [H,h,Fin.sum_univ_succ,logValues,logInput,phi]
  rw [show (2 : ℝ)+2=2^2 by norm_num,Real.log_pow]
  ring

theorem nodeB_log_input : 2-2*nodeB.eval = 2*(2-2*nodeA.eval) := by
  norm_num [nodeA,nodeB,K.eval,K.evalAt]
  ring

theorem H_contact (i : Fin 4) : H (nodes.getD i K.zero).eval =
    phi (nodes.getD i K.zero).eval := by
  rw [H_node_formula]
  have hp : 2-2*nodeA.eval ≠ 0 := by
    have ha := (nodes_interior ⟨0,by decide⟩).2
    simp only [nodes,List.getD_cons_zero] at ha
    linarith
  fin_cases i <;> simp [Fin.sum_univ_succ,contactValue,logValues,logInput,nodes,phi]
  all_goals try ring
  rw [mul_comm nodeB.eval 2,mul_comm nodeA.eval 2,
    nodeB_log_input,Real.log_mul (by norm_num) hp]
  ring

#print axioms H_contact
#print axioms H_minus_one

end Thomson8
