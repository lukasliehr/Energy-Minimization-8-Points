import Coulomb8.Embedding

namespace Coulomb8
open scoped BigOperators

theorem functional_residual {ι κ : Type*} [Fintype ι] [Fintype κ]
    (L b : ι → ℝ) (A : Matrix ι κ ℝ) (w : κ → ℝ)
    (hA : ∀ c, ∑ r, L r*A r c=0) (hb : ∑ r, L r*b r=0) :
    ∑ r, L r*(b r-∑ c, A r c*w c)=0 := by
  simp only [mul_sub,Finset.sum_sub_distrib,Finset.mul_sum,hb,zero_sub]
  have he : (∑ r, ∑ c, L r*(A r c*w c))=0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro c hc
    simp only [←mul_assoc,←Finset.sum_mul,hA,mul_zero,zero_mul]
  rw [he,neg_zero]

theorem sum_three_support (L E : Fin 102 → ℝ)
    (hE : ∀ r, r ≠ 0 → r ≠ 2 → r ≠ 57 → E r=0) :
    ∑ r, L r*E r=L 0*E 0+L 2*E 2+L 57*E 57 := by
  have he : (∑ r ∈ ({0,2,57} : Finset (Fin 102)), L r*E r)=∑ r, L r*E r := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro r hr hn
    have h0 : r ≠ 0 := by intro h; subst r; exact hn (by simp)
    have h2 : r ≠ 2 := by intro h; subst r; exact hn (by simp)
    have h57 : r ≠ 57 := by intro h; subst r; exact hn (by simp)
    rw [hE r h0 h2 h57,mul_zero]
  rw [←he,Finset.sum_insert (by decide),Finset.sum_insert (by decide),Finset.sum_singleton]
  ring

end Coulomb8
