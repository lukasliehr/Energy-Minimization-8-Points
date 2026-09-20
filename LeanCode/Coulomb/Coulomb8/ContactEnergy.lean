import Coulomb8.HermiteConstruction

namespace Coulomb8
open scoped BigOperators

def contactCounts : Fin 4 → ℝ := ![8,4,8,8]
noncomputable def nodeSlopes : Fin 4 → ℝ := ![1,2,-1-q/2,-1+q/2]

theorem q_inverse : q⁻¹=q/2 := by
  field_simp [ne_of_gt q_pos]
  nlinarith [q_sq]

theorem nodeC_polynomial (s : ℝ) : nodeC s = -s+(1-s)*q/2 := by
  simp only [nodeC,div_eq_mul_inv,q_inverse]
  ring

theorem nodeD_polynomial (s : ℝ) : nodeD s = -s-(1-s)*q/2 := by
  simp only [nodeD,div_eq_mul_inv,q_inverse]
  ring

theorem node_distance (i : Fin 4) : 2-2*nodes a i=
    (![2*(1-a),4*(1-a),dMinus a,dPlus a] : Fin 4 → ℝ) i := by
  fin_cases i
  · change 2-2*nodeA a=2*(1-a)
    simp only [nodeA]; ring
  · change 2-2*nodeB a=4*(1-a)
    simp only [nodeB]; ring
  · change 2-2*nodeC a=dMinus a
    rw [nodeC_polynomial]
    unfold dMinus; ring
  · change 2-2*nodeD a=dPlus a
    rw [nodeD_polynomial]
    unfold dPlus; ring

theorem phi_nodes (i : Fin 4) : phi (nodes a i)=
    (![q/(2*Real.sqrt (1-a)),1/(2*Real.sqrt (1-a)),
       1/Real.sqrt (dMinus a),1/Real.sqrt (dPlus a)] : Fin 4 → ℝ) i := by
  have hp : 0 < 1-a := sub_pos.mpr a_lt_one
  have hy : Real.sqrt (1-a) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  unfold phi
  rw [node_distance]
  fin_cases i
  · change 1/Real.sqrt (2*(1-a))=q/(2*Real.sqrt (1-a))
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    change 1/(q*Real.sqrt (1-a))=q/(2*Real.sqrt (1-a))
    field_simp [ne_of_gt q_pos,hy]
    nlinarith [q_sq]
  · change 1/Real.sqrt (4*(1-a))=1/(2*Real.sqrt (1-a))
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  · rfl
  · rfl

theorem contact_energy : ∑ i, contactCounts i*phi (nodes a i)=G a := by
  simp_rw [phi_nodes]
  simp only [Fin.sum_univ_succ]
  change 8*(q/(2*Real.sqrt (1-a)))+(4*(1/(2*Real.sqrt (1-a)))+
    (8*(1/Real.sqrt (dMinus a))+(8*(1/Real.sqrt (dPlus a))+0)))=G a
  unfold G
  ring

theorem contact_stationary :
    ∑ i, contactCounts i*(phi (nodes a i)/(2-2*nodes a i))*nodeSlopes i=0 := by
  have hp : 0 < 1-a := sub_pos.mpr a_lt_one
  have hy : Real.sqrt (1-a) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  have hm := dMinus_pos a_pos
  have hpl := dPlus_pos a_pos
  have hsm : Real.sqrt (dMinus a) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hm)
  have hsp : Real.sqrt (dPlus a) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpl)
  calc
    _ = F a := by
      simp_rw [phi_nodes,node_distance]
      simp only [Fin.sum_univ_succ]
      change 8*((q/(2*Real.sqrt (1-a)))/(2*(1-a)))*1+
        (4*((1/(2*Real.sqrt (1-a)))/(4*(1-a)))*2+
        (8*((1/Real.sqrt (dMinus a))/dMinus a)*(-1-q/2)+
        (8*((1/Real.sqrt (dPlus a))/dPlus a)*(-1+q/2)+0)))=F a
      unfold F
      field_simp [hp.ne',hy,hm.ne',hpl.ne',hsm,hsp]
      <;> ring
    _ = 0 := F_a

end Coulomb8

#print axioms Coulomb8.contact_energy
#print axioms Coulomb8.contact_stationary
