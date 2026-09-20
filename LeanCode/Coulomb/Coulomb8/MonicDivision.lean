import Coulomb8.RealPolynomial
import Coulomb8.SquaredFactorization

namespace Coulomb8
open Polynomial

namespace RealPoly

theorem toPolynomial_append (p q : RealPoly) :
    (p++q).toPolynomial=p.toPolynomial+X^p.length*q.toPolynomial := by
  induction p with
  | nil => simp [toPolynomial]
  | cons c p ih =>
    simp only [List.cons_append,toPolynomial,List.length_cons,ih,pow_succ]
    ring

theorem toPolynomial_zeros (k : ℕ) :
    toPolynomial (List.replicate k (0 : ℝ))=0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ,toPolynomial,ih]

theorem toPolynomial_shift (p : RealPoly) (k : ℕ) :
    toPolynomial (List.replicate k (0 : ℝ)++p)=X^k*p.toPolynomial := by
  simp [toPolynomial_append,toPolynomial_zeros]

theorem degree_lt_length {p : RealPoly} (hp : p ≠ []) : p.toPolynomial.natDegree < p.length := by
  have hpos : 0 < p.length := List.length_pos_iff.mpr hp
  have hh : p.toPolynomial.natDegree ≤ p.length-1 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    exact coeff_eq_zero_of_length_le p (by omega)
  omega

/-- One exact monic division step, with the highest coefficient removed algebraically. -/
theorem monic_step (lower divisor : RealPoly) (c : ℝ) (k : ℕ)
    (hl : lower.length=divisor.length+k) :
    (lower++[c]).toPolynomial=
      (divisor++[1]).toPolynomial*(C c*X^k)+
        (add lower (scale (-c) (List.replicate k 0++divisor))).toPolynomial := by
  simp only [toPolynomial_append,toPolynomial,toPolynomial_add,toPolynomial_scale,
    toPolynomial_shift,toPolynomial_zeros,List.length_replicate,hl]
  simp only [mul_zero,add_zero,map_one,map_neg]
  rw [pow_add]
  ring

end RealPoly
end Coulomb8

#print axioms Coulomb8.RealPoly.monic_step
