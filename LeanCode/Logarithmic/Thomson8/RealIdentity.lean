import Thomson8.IdentityChecks
import Thomson8.BlockValue
import Thomson8.EnergyConstant
import Thomson8.Symmetry

namespace Thomson8

theorem hermiteComponent_univariate (h : List Affine) (ell : ℕ) (u v t : ℝ) :
    (hermiteComponent h ell).eval u v t=(hermiteComponent h ell).eval u 0 0 := by
  simp [hermiteComponent,Poly.eval,List.map_map,Function.comp_def,Exponent.eval]

theorem target_real (u v t : ℝ) :
    (∑ ell : Fin 5, logValues ell*(targetComponent Data.hermite ell).eval u v t) =
      (H u+H v+H t)/3-optimalEnergy/28 := by
  rw [optimalEnergy_logs]
  norm_num [targetComponent,Poly.eval_symmetrize,Poly.symEval,hermiteComponent_univariate,
    H,Fin.sum_univ_succ]
  ring

theorem real_certificate_identity (u v t : ℝ) :
    (H u+H v+H t)/3-optimalEnergy/28 =
      Data.F0.value u v t+Data.F1.value u v t+Data.F2.value u v t+
        Data.F4.value u v t+Data.F5.value u v t+
        Data.S6_trivial.value u v t+Data.S7_even.value u v t := by
  rw [←target_real,certificate_identity u v t (fun ell => logValues ell)]
  simp only [rhsComponent,Data.blocks,Poly.eval_sum,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,Block.value,mul_add,mul_zero,add_zero,Finset.sum_add_distrib]
  ring

#print axioms real_certificate_identity

end Thomson8
