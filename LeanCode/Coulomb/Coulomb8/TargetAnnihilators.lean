import Coulomb8.AnnihilatorContacts
import Coulomb8.ContactPolynomial
import Coulomb8.Target

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Annihilators
open scoped BigOperators

theorem target_dot_expansion (L : Fin 102 → ℝ) :
    ∑ r, L r*target r=L 0*(Hpoly.coeff 0-G a/28)+
      ∑ j : Fin 12, L (pureIndex j)*(Hpoly.coeff (j.val+1)/3) := by
  norm_num [target,pureIndex,Fin.sum_univ_succ] <;> rfl

theorem factor_thirty_six (S T : Fin 12 → ℝ) :
    (∑ j, (36*S j)*(T j/3))=12*∑ j, S j*T j := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem target0 : ∑ r, L0 r*target r=0 := by
  rw [target_dot_expansion,constant0]
  simp_rw [pure0]
  rw [factor_thirty_six]
  have he := contact_weighted_eval Hpoly Hpoly_degree
  have hc : ∑ i, contactCounts i*Hpoly.eval (nodes a i)=G a := by
    change ∑ i, contactCounts i*H (nodes a i)=G a
    simp_rw [H_contact]
    exact contact_energy
  rw [hc] at he
  linarith

theorem target1 : ∑ r, L1 r*target r=0 := by
  rw [target_dot_expansion,constant1,zero_mul,zero_add]
  simp_rw [pure1]
  rw [factor_thirty_six]
  have he := contact_weighted_derivative Hpoly Hpoly_degree
  have hc : ∑ i, contactCounts i*Hpoly.derivative.eval (nodes a i)*nodeSlopes i=0 := by
    simp_rw [H_derivative_contact]
    exact contact_stationary
  rw [hc] at he
  rw [←he,mul_zero]

theorem target_structural_zero : target 57=0 := by rfl

end Coulomb8.Annihilators

#print axioms Coulomb8.Annihilators.target0
#print axioms Coulomb8.Annihilators.target1
