import AllS.Units.N_G.N_cycle34

noncomputable section
open Real
open scoped BigOperators
namespace Blueprint.Thomson.Tail.Implementation

theorem directed_pair_sum (g : Fin 8 → Fin 8 → ℝ) (hg : ∀ i,g i i=0) :
    (∑ i,∑ j,g i j)=∑ i,∑ j with i < j,(g i j+g j i) := by
  simp [Fin.sum_univ_succ,Finset.sum_filter,hg]
  ring

theorem forceFlow_mul_cost (Y : Fin 8 → Point) (hY : IsConfiguration Y)
    (p m : ℝ) (u : Point) (i j : Fin 8) (hij : i ≠ j) :
    forceFlow p u Y i j*normalizedEdgeCost m u Y i j=
    if 0 < orientedArea u Y i j then
      (sin (forceAngle m)/m)*(squaredDistance Y i j)^(-p) else 0 := by
  have hd : 0 < squaredDistance Y i j := setup_positive_distance Y hY i j hij
  by_cases ha : 0 < orientedArea u Y i j
  · rw [if_pos ha,forceFlow,normalizedEdgeCost,max_eq_left ha.le]
    have he : (squaredDistance Y i j)^(-p-1)*squaredDistance Y i j=(squaredDistance Y i j)^(-p) := by
      calc
        _ = (squaredDistance Y i j)^(-p-1)*(squaredDistance Y i j)^(1:ℝ) := by rw [Real.rpow_one]
        _ = (squaredDistance Y i j)^((-p-1)+1) := (Real.rpow_add hd _ _).symm
        _ = _ := by congr 1; ring
    calc
      _ = (sin (forceAngle m)/m)*((squaredDistance Y i j)^(-p-1)*squaredDistance Y i j) := by field_simp
      _ = _ := by rw [he]
  · simp [forceFlow,max_eq_right (le_of_not_gt ha),ha]

theorem forceFlow_total_cost_le (Y : Fin 8 → Point) (hY : IsConfiguration Y)
    (p m : ℝ) (u : Point) (hm : 0 < m) (hmmax : m ≤ 29/20) :
    (∑ i,∑ j,forceFlow p u Y i j*normalizedEdgeCost m u Y i j) ≤
      (sin (forceAngle m)/m)*squaredEnergy p Y := by
  have hθ0 : 0 < forceAngle m := by have hv := force_v_range m hm hmmax; linarith
  have hθπ : forceAngle m < π := by have hv := force_v_range m hm hmmax; linarith [Real.pi_pos]
  have hscale : 0 ≤ sin (forceAngle m)/m := (div_pos (Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ) hm).le
  rw [directed_pair_sum _ (by intro i; simp)]
  unfold squaredEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hij : i ≠ j := ne_of_lt (Finset.mem_filter.mp hj).2
  rw [forceFlow_mul_cost Y hY p m u i j hij,forceFlow_mul_cost Y hY p m u j i hij.symm,
    orientedArea_swap u Y i j,squaredDistance_symm Y j i]
  have hnonneg : 0 ≤ (sin (forceAngle m)/m)*(squaredDistance Y i j)^(-p) :=
    mul_nonneg hscale (Real.rpow_nonneg (squaredDistance_nonneg Y i j) _)
  split_ifs <;> linarith

theorem FlowCycle.unitFlow_weighted_sum (C : FlowCycle) (c : Fin 8 → Fin 8 → ℝ) :
    (∑ i,∑ j,C.unitFlow i j*c i j)=∑ k,c (C.point k) (C.point (k+1)) := by
  classical
  simp_rw [C.unitFlow_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs => enter [2,j]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [ite_mul,one_mul,zero_mul]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true]

theorem list_flow_cost_sum (L : List (ℝ × FlowCycle)) (c : Fin 8 → Fin 8 → ℝ) :
    (∑ i,∑ j,(L.map (fun b => b.1*b.2.unitFlow i j)).sum*c i j)=
      (L.map (fun b => b.1*(∑ k,c (b.2.point k) (b.2.point (k+1))))).sum := by
  induction L with
  | nil => simp
  | cons b L ih =>
    simp only [List.map_cons,List.sum_cons,add_mul,Finset.sum_add_distrib,ih]
    congr 1
    simp_rw [mul_assoc,← Finset.mul_sum]
    rw [b.2.unitFlow_weighted_sum]

#print axioms forceFlow_total_cost_le
#print axioms list_flow_cost_sum
end Blueprint.Thomson.Tail.Implementation
