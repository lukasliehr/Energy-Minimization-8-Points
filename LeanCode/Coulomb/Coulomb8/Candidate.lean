import Coulomb8.EnergySums
import Coulomb8.ContactEnergy

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8
open scoped InnerProductSpace
open Thomson8 (inner_point norm_point_sq)

theorem height_sq : height^2=a := Real.sq_sqrt a_pos.le
theorem radius_sq : radius^2=1-a := Real.sq_sqrt (sub_pos.mpr a_lt_one).le

theorem antiprism_unit (i : Fin 8) : ‖antiprism i‖=1 := by
  have hs : ‖antiprism i‖^2=1 := by
    fin_cases i
    all_goals simp [antiprism,norm_point_sq,div_pow,height_sq,radius_sq,q_sq]
  nlinarith [norm_nonneg (antiprism i)]

def candidateCode : Fin 8 → Fin 8 → Fin 5 :=
  ![![0,1,2,1,3,4,4,3],
    ![1,0,1,2,3,3,4,4],
    ![2,1,0,1,4,3,3,4],
    ![1,2,1,0,4,4,3,3],
    ![3,3,4,4,0,1,2,1],
    ![4,3,3,4,1,0,1,2],
    ![4,4,3,3,2,1,0,1],
    ![3,4,4,3,1,2,1,0]]


noncomputable def candidateValue (i : Fin 5) : ℝ := ![1,nodeA a,nodeB a,nodeC a,nodeD a] i

theorem antiprism_inner (i j : Fin 8) : ⟪antiprism i,antiprism j⟫_ℝ=
    candidateValue (candidateCode i j) := by
  by_cases hij : i=j
  · subst j
    have hc : candidateCode i i=0 := by fin_cases i <;> rfl
    rw [hc]
    simp [candidateValue,real_inner_self_eq_norm_sq,antiprism_unit]
  fin_cases i <;> fin_cases j
  all_goals try exact False.elim (hij rfl)
  all_goals simp [antiprism,inner_point,candidateCode,candidateValue,nodeA,nodeB,
    nodeC_polynomial,nodeD_polynomial,div_eq_mul_inv,q_inverse]
  all_goals try ring_nf
  all_goals try simp only [height_sq,radius_sq,q_sq]
  all_goals first | rfl | ring

theorem antiprism_inner_lt_one (i j : Fin 8) (hij : i ≠ j) :
    ⟪antiprism i,antiprism j⟫_ℝ < 1 := by
  rw [antiprism_inner]
  have hA : nodeA a<1 := (nodes_interior 0).2
  have hB : nodeB a<1 := (nodes_interior 1).2
  have hC : nodeC a<1 := (nodes_interior 2).2
  have hD : nodeD a<1 := (nodes_interior 3).2
  fin_cases i <;> fin_cases j <;>
    first | exact False.elim (hij rfl) | exact hA | exact hB | exact hC | exact hD

theorem antiprism_admissible : Admissible antiprism := by
  refine ⟨antiprism_unit,?_⟩
  intro i j heq
  by_contra hij
  have h := antiprism_inner_lt_one i j hij
  rw [heq,real_inner_self_eq_norm_sq,antiprism_unit] at h
  norm_num at h

theorem antiprism_pair_energy : coulombEnergy antiprism =
    8*phi (nodeA a)+4*phi (nodeB a)+8*phi (nodeC a)+8*phi (nodeD a) := by
  simp only [coulombEnergy,pair_energy_inner _ _ (antiprism_unit _) (antiprism_unit _),antiprism_inner]
  simp only [Finset.sum_filter,Fin.sum_univ_succ]
  change ((0+(phi (nodeA a)+(phi (nodeB a)+(phi (nodeA a)+(phi (nodeC a)+(phi (nodeD a)+(phi (nodeD a)+(phi (nodeC a)+0))))))))+((0+(0+(phi (nodeA a)+(phi (nodeB a)+(phi (nodeC a)+(phi (nodeC a)+(phi (nodeD a)+(phi (nodeD a)+0))))))))+((0+(0+(0+(phi (nodeA a)+(phi (nodeD a)+(phi (nodeC a)+(phi (nodeC a)+(phi (nodeD a)+0))))))))+((0+(0+(0+(0+(phi (nodeD a)+(phi (nodeD a)+(phi (nodeC a)+(phi (nodeC a)+0))))))))+((0+(0+(0+(0+(0+(phi (nodeA a)+(phi (nodeB a)+(phi (nodeA a)+0))))))))+((0+(0+(0+(0+(0+(0+(phi (nodeA a)+(phi (nodeB a)+0))))))))+((0+(0+(0+(0+(0+(0+(0+(phi (nodeA a)+0))))))))+((0+(0+(0+(0+(0+(0+(0+(0+0))))))))+0)))))))) = _
  ring

theorem antiprism_energy : coulombEnergy antiprism=optimalEnergy := by
  rw [antiprism_pair_energy]
  have h := contact_energy
  simp only [Fin.sum_univ_succ] at h
  change 8*phi (nodeA a)+(4*phi (nodeB a)+(8*phi (nodeC a)+(8*phi (nodeD a)+0)))=G a at h
  change _=G a
  linarith

end Coulomb8

#print axioms Coulomb8.antiprism_admissible
#print axioms Coulomb8.antiprism_energy
