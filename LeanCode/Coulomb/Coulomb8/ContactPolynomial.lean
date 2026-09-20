import Coulomb8.ContactEnergy
import Coulomb8.HermiteDegree

namespace Coulomb8
open Polynomial
open scoped BigOperators

theorem eval_degree_twelve (p : Polynomial ℝ) (hp : p.natDegree ≤ 12) (x : ℝ) :
    p.eval x=p.coeff 0+∑ j : Fin 12, p.coeff (j.val+1)*x^(j.val+1) := by
  have h : p.eval x=∑ j : Fin 13, p.coeff j.val*x^j.val := by
    rw [p.eval_eq_sum_range' (n:=13) (by omega)]
    exact (Fin.sum_univ_eq_sum_range (fun j => p.coeff j*x^j) 13).symm
  rw [h,Fin.sum_univ_succ]
  simp

theorem derivative_eval_degree_twelve (p : Polynomial ℝ) (hp : p.natDegree ≤ 12) (x : ℝ) :
    p.derivative.eval x=∑ j : Fin 12, p.coeff (j.val+1)*(j.val+1)*x^j.val := by
  have hd : p.derivative.natDegree < 12 := by
    have h := p.natDegree_derivative_le
    omega
  rw [p.derivative.eval_eq_sum_range' (n:=12) hd]
  rw [←Fin.sum_univ_eq_sum_range]
  simp only [Polynomial.coeff_derivative,Nat.cast_add,Nat.cast_one]

theorem contact_weighted_eval (p : Polynomial ℝ) (hp : p.natDegree ≤ 12) :
    ∑ i, contactCounts i*p.eval (nodes a i)=28*p.coeff 0+
      ∑ j : Fin 12, (∑ i, contactCounts i*nodes a i^(j.val+1))*p.coeff (j.val+1) := by
  simp_rw [eval_degree_twelve p hp,mul_add,Finset.sum_add_distrib]
  have hc : ∑ i, contactCounts i*p.coeff 0=28*p.coeff 0 := by
    rw [←Finset.sum_mul]
    congr 1
    simp only [Fin.sum_univ_succ]
    change 8+(4+(8+(8+0)))=(28 : ℝ)
    norm_num
  rw [hc]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem contact_weighted_derivative (p : Polynomial ℝ) (hp : p.natDegree ≤ 12) :
    ∑ i, contactCounts i*p.derivative.eval (nodes a i)*nodeSlopes i=
      ∑ j : Fin 12,
        (∑ i, contactCounts i*(j.val+1)*nodes a i^j.val*nodeSlopes i)*p.coeff (j.val+1) := by
  simp_rw [derivative_eval_degree_twelve p hp,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  ring

end Coulomb8
