import Thomson8.EnergyConstant

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Thomson8

open scoped InnerProductSpace

def candidateCode : Fin 8 → Fin 8 → Fin 5 :=
  ![![0,1,2,1,3,4,4,3],
    ![1,0,1,2,3,3,4,4],
    ![2,1,0,1,4,3,3,4],
    ![1,2,1,0,4,4,3,3],
    ![3,3,4,4,0,1,2,1],
    ![4,3,3,4,1,0,1,2],
    ![4,4,3,3,2,1,0,1],
    ![3,4,4,3,1,2,1,0]]

noncomputable def candidateValue (i : Fin 5) : ℝ :=
  ![1,nodeA.eval,nodeB.eval,nodeC.eval,nodeD.eval] i

theorem antiprism_inner (i j : Fin 8) : ⟪antiprism i,antiprism j⟫_ℝ =
    candidateValue (candidateCode i j) := by
  by_cases hij : i=j
  · subst j
    have hc : candidateCode i i=0 := by fin_cases i <;> rfl
    rw [hc]
    simp [candidateValue,real_inner_self_eq_norm_sq,antiprism_unit]
  have hs2 : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  fin_cases i <;> fin_cases j
  all_goals try exact False.elim (hij rfl)
  all_goals simp [antiprism,inner_point,candidateCode,candidateValue,nodeA_formula,
    nodeB_formula,nodeC_formula,nodeD_formula,div_eq_mul_inv,sqrt_two_inv]
  all_goals try ring_nf
  all_goals try simp only [height_sq,radius_sq,hs2]
  all_goals first | rfl | ring

theorem antiprism_inner_lt_one (i j : Fin 8) (hij : i ≠ j) :
    ⟪antiprism i,antiprism j⟫_ℝ < 1 := by
  rw [antiprism_inner]
  have hA : nodeA.eval < 1 := by simpa [nodes] using (nodes_interior ⟨0,by decide⟩).2
  have hB : nodeB.eval < 1 := by simpa [nodes] using (nodes_interior ⟨1,by decide⟩).2
  have hC : nodeC.eval < 1 := by simpa [nodes] using (nodes_interior ⟨2,by decide⟩).2
  have hD : nodeD.eval < 1 := by simpa [nodes] using (nodes_interior ⟨3,by decide⟩).2
  fin_cases i <;> fin_cases j <;>
    first | exact False.elim (hij rfl) | simpa [candidateCode,candidateValue] using hA |
      simpa [candidateCode,candidateValue] using hB | simpa [candidateCode,candidateValue] using hC |
      simpa [candidateCode,candidateValue] using hD

theorem antiprism_admissible : Admissible antiprism := by
  refine ⟨antiprism_unit,?_⟩
  intro i j heq
  by_contra hij
  have h := antiprism_inner_lt_one i j hij
  rw [heq,real_inner_self_eq_norm_sq,antiprism_unit] at h
  norm_num at h

theorem antiprism_pair_energy : logEnergy antiprism =
    8*phi nodeA.eval+4*phi nodeB.eval+8*phi nodeC.eval+8*phi nodeD.eval := by
  simp only [logEnergy,pair_energy_inner _ _ (antiprism_unit _) (antiprism_unit _),antiprism_inner]
  simp only [Finset.sum_filter,Fin.sum_univ_succ]
  change ((0+(phi nodeA.eval+(phi nodeB.eval+(phi nodeA.eval+(phi nodeC.eval+(phi nodeD.eval+(phi nodeD.eval+(phi nodeC.eval+0))))))))+((0+(0+(phi nodeA.eval+(phi nodeB.eval+(phi nodeC.eval+(phi nodeC.eval+(phi nodeD.eval+(phi nodeD.eval+0))))))))+((0+(0+(0+(phi nodeA.eval+(phi nodeD.eval+(phi nodeC.eval+(phi nodeC.eval+(phi nodeD.eval+0))))))))+((0+(0+(0+(0+(phi nodeD.eval+(phi nodeD.eval+(phi nodeC.eval+(phi nodeC.eval+0))))))))+((0+(0+(0+(0+(0+(phi nodeA.eval+(phi nodeB.eval+(phi nodeA.eval+0))))))))+((0+(0+(0+(0+(0+(0+(phi nodeA.eval+(phi nodeB.eval+0))))))))+((0+(0+(0+(0+(0+(0+(0+(phi nodeA.eval+0))))))))+((0+(0+(0+(0+(0+(0+(0+(0+0))))))))+0)))))))) = _
  ring

theorem antiprism_energy : logEnergy antiprism = optimalEnergy := by
  rw [antiprism_pair_energy,optimalEnergy_logs]
  have hp : 2-2*nodeA.eval ≠ 0 := by rw [nodeA_formula]; linarith [a_lt_one]
  simp [phi,nodeB_log_input,Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hp,
    logValues,logInput]
  ring

#print axioms antiprism_admissible
#print axioms antiprism_energy

end Thomson8
