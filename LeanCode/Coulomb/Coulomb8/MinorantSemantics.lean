import Coulomb8.SquaredFactorization

namespace Coulomb8
open Polynomial
open scoped BigOperators

def IsContact (t : ℝ) : Prop := t = -1 ∨ ∃ i : Fin 4, t = nodes a i

theorem squared_factorization_eval (t : ℝ) :
    1-(2-2*t)*(H t)^2=(t+1)^5*(∏ i : Fin 4, (t-nodes a i)^2)*gapQuotient.eval t := by
  have hh := congrArg (Polynomial.eval t) squared_factorization
  simpa [squaredGap,H,contactFactor_eval] using hh

theorem minorant_of_quotient_positive
    (hq : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 < gapQuotient.eval t)
    {t : ℝ} (ht : t ∈ Set.Ico (-1 : ℝ) 1) : H t ≤ phi t := by
  have hx : 0 ≤ t+1 := by linarith [ht.1]
  have hp : 0 ≤ ∏ i : Fin 4, (t-nodes a i)^2 := Finset.prod_nonneg (fun i _ => sq_nonneg _)
  have hpos : 0 ≤ (t+1)^5*(∏ i : Fin 4, (t-nodes a i)^2)*gapQuotient.eval t :=
    mul_nonneg (mul_nonneg (pow_nonneg hx _) hp) (hq t ⟨ht.1,ht.2.le⟩).le
  rw [←squared_factorization_eval] at hpos
  exact phi_of_squared_bound ht.2 (by linarith)

theorem minorant_strict_of_quotient_positive
    (hq : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 < gapQuotient.eval t)
    {t : ℝ} (ht : t ∈ Set.Ico (-1 : ℝ) 1) (hc : ¬IsContact t) : H t < phi t := by
  have hx : 0 < t+1 := by
    have he : t ≠ -1 := fun h => hc (Or.inl h)
    have hlt : -1 < t := lt_of_le_of_ne ht.1 (Ne.symm he)
    linarith
  have hn (i : Fin 4) : t-nodes a i ≠ 0 := by
    intro he
    exact hc (Or.inr ⟨i,sub_eq_zero.mp he⟩)
  have hp : 0 < ∏ i : Fin 4, (t-nodes a i)^2 := Finset.prod_pos (fun i _ => sq_pos_of_ne_zero (hn i))
  have hpos : 0 < (t+1)^5*(∏ i : Fin 4, (t-nodes a i)^2)*gapQuotient.eval t :=
    mul_pos (mul_pos (pow_pos hx _) hp) (hq t ⟨ht.1,ht.2.le⟩)
  rw [←squared_factorization_eval] at hpos
  exact phi_of_squared_strict ht.2 (by linarith)

theorem minorant_equality_of_quotient_positive
    (hq : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 < gapQuotient.eval t)
    {t : ℝ} (ht : t ∈ Set.Ico (-1 : ℝ) 1) : H t=phi t ↔ IsContact t := by
  constructor
  · intro he
    by_contra hc
    have hh := minorant_strict_of_quotient_positive hq ht hc
    linarith
  · rintro (rfl | ⟨i,rfl⟩)
    · rw [H_minus_one,phi_minus_one]
    · exact H_contact i

end Coulomb8

#print axioms Coulomb8.minorant_equality_of_quotient_positive
