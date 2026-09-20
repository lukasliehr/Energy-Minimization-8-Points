import Coulomb8.HermiteConstruction

namespace Coulomb8
open Polynomial

theorem taylor4_degree : taylor4.natDegree ≤ 4 := by
  unfold taylor4
  compute_degree

theorem hermiteTerm_degree (i : Fin 4) : (hermiteTerm i).natDegree ≤ 7 := by
  have hl : (C (residualValue i)+
      C (residualSlope i-2*residualValue i*(lagrange i).derivative.eval (nodes a i))*
        (X-C (nodes a i))).natDegree ≤ 1 := by compute_degree
  have hp : ((lagrange i)^2).natDegree ≤ 6 := by
    calc
      _ ≤ 2*(lagrange i).natDegree := natDegree_pow_le
      _ = 6 := by rw [lagrange_degree]
  exact natDegree_mul_le.trans (Nat.add_le_add hl hp)

theorem residualPolynomial_degree : residualPolynomial.natDegree ≤ 7 := by
  unfold residualPolynomial
  exact natDegree_sum_le_of_forall_le _ _ (fun i _ => hermiteTerm_degree i)

theorem Hpoly_degree : Hpoly.natDegree ≤ 12 := by
  have hp : ((X+1 : Polynomial ℝ)^5).natDegree ≤ 5 := by compute_degree
  have hprod : ((X+1 : Polynomial ℝ)^5*residualPolynomial).natDegree ≤ 12 :=
    natDegree_mul_le.trans (Nat.add_le_add hp residualPolynomial_degree)
  exact (natDegree_add_le _ _).trans (max_le (taylor4_degree.trans (by decide)) hprod)

end Coulomb8

#print axioms Coulomb8.Hpoly_degree
