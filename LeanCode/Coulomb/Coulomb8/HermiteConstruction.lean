import Coulomb8.NodeBounds
import Mathlib.LinearAlgebra.Lagrange

namespace Coulomb8

open Polynomial
open scoped BigOperators

noncomputable def lagrange (i : Fin 4) : Polynomial ℝ :=
  Lagrange.basis Finset.univ (nodes a) i

theorem lagrange_eval (i j : Fin 4) : (lagrange i).eval (nodes a j)=if i=j then 1 else 0 := by
  by_cases hij : i=j
  · subst j
    simp [lagrange,Lagrange.eval_basis_self nodes_injective.injOn]
  · simp [lagrange,hij,Lagrange.eval_basis_of_ne hij]

theorem lagrange_degree (i : Fin 4) : (lagrange i).natDegree=3 := by
  simpa [lagrange] using Lagrange.natDegree_basis nodes_injective.injOn (Finset.mem_univ i)

noncomputable def taylor4 : Polynomial ℝ :=
  C (1/2)+C (1/8)*(X+1)+C (3/64)*(X+1)^2+C (5/256)*(X+1)^3+C (35/4096)*(X+1)^4

noncomputable def residualValue (i : Fin 4) : ℝ :=
  (phi (nodes a i)-taylor4.eval (nodes a i))/(nodes a i+1)^5

noncomputable def residualSlope (i : Fin 4) : ℝ :=
  (phi (nodes a i)/(2-2*nodes a i)-taylor4.derivative.eval (nodes a i)
    -5*(nodes a i+1)^4*residualValue i)/(nodes a i+1)^5

noncomputable def hermiteTerm (i : Fin 4) : Polynomial ℝ :=
  (C (residualValue i)+
    C (residualSlope i-2*residualValue i*(lagrange i).derivative.eval (nodes a i))*(X-C (nodes a i)))
      *(lagrange i)^2

theorem hermiteTerm_eval (i j : Fin 4) :
    (hermiteTerm i).eval (nodes a j)=if i=j then residualValue j else 0 := by
  by_cases hij : i=j
  · subst j
    simp [hermiteTerm,lagrange_eval]
  · simp [hermiteTerm,lagrange_eval,hij]

theorem hermiteTerm_derivative_eval (i j : Fin 4) :
    (hermiteTerm i).derivative.eval (nodes a j)=if i=j then residualSlope j else 0 := by
  by_cases hij : i=j
  · subst j
    simp [hermiteTerm,derivative_mul,derivative_pow,lagrange_eval]
    ring
  · simp [hermiteTerm,derivative_mul,derivative_pow,lagrange_eval,hij]

noncomputable def residualPolynomial : Polynomial ℝ := ∑ i : Fin 4, hermiteTerm i
noncomputable def Hpoly : Polynomial ℝ := taylor4+(X+1)^5*residualPolynomial
noncomputable def H (t : ℝ) : ℝ := Hpoly.eval t

theorem residualPolynomial_eval (i : Fin 4) :
    residualPolynomial.eval (nodes a i)=residualValue i := by
  simp [residualPolynomial,eval_finsetSum,hermiteTerm_eval]

theorem residualPolynomial_derivative_eval (i : Fin 4) :
    residualPolynomial.derivative.eval (nodes a i)=residualSlope i := by
  simp [residualPolynomial,eval_finsetSum,hermiteTerm_derivative_eval]

theorem H_contact (i : Fin 4) : H (nodes a i)=phi (nodes a i) := by
  have hn : nodes a i+1 ≠ 0 := by linarith [(nodes_interior i).1]
  simp only [H,Hpoly,eval_add,eval_mul,eval_pow,eval_X,eval_one,residualPolynomial_eval]
  unfold residualValue
  field_simp [hn]
  <;> ring

theorem H_derivative_contact (i : Fin 4) :
    Hpoly.derivative.eval (nodes a i)=phi (nodes a i)/(2-2*nodes a i) := by
  have hn : nodes a i+1 ≠ 0 := by linarith [(nodes_interior i).1]
  have hd : 2-2*nodes a i ≠ 0 := by linarith [(nodes_interior i).2]
  simp only [Hpoly,derivative_add,derivative_mul,derivative_pow,derivative_X,
    derivative_one,add_zero,eval_add,eval_mul,eval_pow,eval_X,eval_one,eval_C,
    residualPolynomial_eval,residualPolynomial_derivative_eval]
  unfold residualSlope
  field_simp [hn,hd]
  <;> ring

theorem H_minus_one : H (-1)=1/2 := by
  norm_num [H,Hpoly,taylor4]

theorem endpoint_divisibility : (X+1 : Polynomial ℝ)^5 ∣ Hpoly-taylor4 := by
  refine ⟨residualPolynomial,?_⟩
  unfold Hpoly
  ring

end Coulomb8

#print axioms Coulomb8.H_contact
#print axioms Coulomb8.H_derivative_contact
