import Coulomb8.Bernstein13

namespace Coulomb8
open Polynomial
open scoped BigOperators

theorem bernstein_reconstruction (p : Polynomial ℝ) (hp : p.natDegree ≤ 12) (t : ℝ) :
    p.eval t=∑ i : Fin 13, bernsteinCoefficients p i*bernsteinWeight i t := by
  calc
    p.eval t = ∑ j : Fin 13, p.coeff j.val*t^j.val := by
      rw [p.eval_eq_sum_range' (n := 13) (by omega)]
      exact (Fin.sum_univ_eq_sum_range (fun j => p.coeff j*t^j) 13).symm
    _ = ∑ j : Fin 13, ∑ i : Fin 13,
        p.coeff j.val*(bernsteinMatrix i j : ℝ)*bernsteinWeight i t := by
      apply Finset.sum_congr rfl
      intro j _
      rw [bernstein_monomial,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [bernsteinCoefficients,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem positive_of_bernstein (p : Polynomial ℝ) (hp : p.natDegree ≤ 12)
    (hb : ∀ i, 0 < bernsteinCoefficients p i) {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    0 < p.eval t := by
  rw [bernstein_reconstruction p hp]
  exact bernstein_sum_pos _ hb ht

end Coulomb8

#print axioms Coulomb8.positive_of_bernstein
