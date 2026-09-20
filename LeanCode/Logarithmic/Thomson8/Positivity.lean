import Thomson8.Interval
import Mathlib.LinearAlgebra.Matrix.PosDef

namespace Thomson8

open scoped BigOperators

def quadratic {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * M i j * x j

theorem abs_mul_le_half_squares (x y : ℝ) : |x*y| ≤ (x^2+y^2)/2 := by
  rw [abs_mul]
  nlinarith [sq_nonneg (|x|-|y|), sq_abs x, sq_abs y]

theorem quadratic_abs_bound {ι : Type*} [Fintype ι]
    (G : Matrix ι ι ℝ) (hs : ∀ i j, G i j=G j i) (x : ι → ℝ) :
    |quadratic G x| ≤ ∑ i, x i^2 * ∑ j, |G i j| := by
  classical
  calc
    |quadratic G x| ≤ ∑ i, ∑ j, |x i * G i j * x j| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro i _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |G i j| * ((x i)^2+(x j)^2)/2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have h := mul_le_mul_of_nonneg_left (abs_mul_le_half_squares (x i) (x j)) (abs_nonneg (G i j))
      simpa only [abs_mul, mul_div_assoc, mul_comm, mul_left_comm, mul_assoc] using h
    _ = ∑ i, x i^2 * ∑ j, |G i j| := by
      simp_rw [mul_add, add_div, Finset.sum_add_distrib]
      have hswap : (∑ i, ∑ j, |G i j| * x j^2 / 2) =
          ∑ i, ∑ j, |G i j| * x i^2 / 2 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hs j i]
      rw [hswap, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem posDef_of_row_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hs : ∀ i j, M i j=M j i)
    (hrow : ∀ i, ∑ j, |M i j - (if i=j then 1 else 0)| ≤ (1/2 : ℝ)) : M.PosDef := by
  let G : Matrix ι ι ℝ := fun i j => M i j - (if i=j then 1 else 0)
  have hg : ∀ i j, G i j=G j i := by
    intro i j
    simp only [G, hs i j, eq_comm]
  have hbound (x : ι → ℝ) : |quadratic G x| ≤ (1/2 : ℝ)*∑ i, x i^2 := by
    apply (quadratic_abs_bound G hg x).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg (x i))
  have hdecomp (x : ι → ℝ) : quadratic M x = (∑ i, x i^2) + quadratic G x := by
    unfold quadratic G
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
    have hdiag : (∑ i, ∑ j, x i * (if i=j then 1 else 0) * x j) = ∑ i, x i^2 := by
      apply Finset.sum_congr rfl
      intro i _
      simp [mul_ite, ite_mul, ← pow_two]
    rw [hdiag]
    ring
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    simpa using hs j i
  · intro x hx
    have hn : ∃ i, x i ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (funext h)
    obtain ⟨i,hi⟩ := hn
    have hsum : 0 < ∑ j, x j^2 := Finset.sum_pos' (fun j _ => sq_nonneg (x j))
      ⟨i,Finset.mem_univ _,sq_pos_of_ne_zero hi⟩
    have hquad : 0 < quadratic M x := by
      rw [hdecomp]
      have hb := hbound x
      have hl := neg_abs_le (quadratic G x)
      linarith
    simpa only [quadratic, Matrix.mulVec, dotProduct, star_trivial, Finset.mul_sum, mul_assoc] using hquad

theorem posDef_of_congruence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P B : Matrix ι ι ℝ) (hc : (P * B * P.transpose).PosDef) : B.PosDef := by
  have hpt : Function.Injective P.transpose.mulVec := by
    intro x y h
    apply Matrix.mulVec_injective_of_isUnit hc.isUnit
    simp only [← Matrix.mulVec_mulVec, h]
  have hu : IsUnit P.transpose := Matrix.mulVec_injective_iff_isUnit.mp hpt
  apply (Matrix.IsUnit.posDef_star_left_conjugate_iff hu).mp
  change (P * B * P.transpose).PosDef
  exact hc

#print axioms posDef_of_row_bound
#print axioms posDef_of_congruence

end Thomson8
