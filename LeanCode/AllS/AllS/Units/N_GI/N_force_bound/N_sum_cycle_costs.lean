import AllS.Units.N_GI.N_force_bound.N_flow_energy

noncomputable section
open Real
open scoped BigOperators
namespace Blueprint.Thomson.Tail.Implementation

theorem positive_cycle_cost_lower (Y : Fin 8 → Point) (p m : ℝ) (i₀ j₀ : Fin 8)
    (hY : IsConfiguration Y) (hp : 0 < p) (hstat : Stationary p Y) (hne : i₀ ≠ j₀)
    (hm : 0 < m) (hmmax : m ≤ 29/20) (hd : squaredDistance Y i₀ j₀=m)
    (hmin : ∀ i j, i ≠ j → m ≤ squaredDistance Y i j)
    (C : FlowCycle) (hC : C.Positive (forceFlow p (forceAxis Y i₀ j₀ m) Y)) :
    forceFactor m*C.unitFlow i₀ j₀ ≤ cycleNormalizedCost m Y (forceAxis Y i₀ j₀ m) C := by
  classical
  have he := edge_cost Y p m i₀ j₀ hY hp hstat hne hm hmmax hd hmin
  have hbase : (C.size+1:ℕ) ≤ cycleNormalizedCost m Y (forceAxis Y i₀ j₀ m) C := by
    have h := Finset.sum_le_sum (s:=Finset.univ) (fun k _ => (he.1 _ _ (hC k)).2.2.2.2.2.2.1)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,cycleNormalizedCost] using h
  by_cases hcontains : ∃ k₀, C.point k₀=i₀ ∧ C.point (k₀+1)=j₀
  · rw [FlowCycle.unitFlow,if_pos hcontains,mul_one]
    by_cases hsmall : C.size+1=3 ∨ C.size+1=4
    · exact (cycle34 Y p m i₀ j₀ hY hp hstat hne hm hmmax hd hmin C hC hsmall hcontains).le
    by_cases hfive : C.size+1=5
    · exact cycle5 Y p m i₀ j₀ hY hp hstat hne hm hmmax hd hmin C hC hfive hcontains
    have hlen : 6 ≤ C.size+1 := by have h := C.length_ge; omega
    have hlenR : (6:ℝ) ≤ (C.size+1:ℕ) := by exact_mod_cast hlen
    exact (force_factor_bounds m hm hmmax).2.2.2.le.trans (hlenR.trans hbase)
  · rw [FlowCycle.unitFlow,if_neg hcontains,mul_zero]
    exact le_trans (by positivity) hbase

theorem force_bound_sum_cycle_costs (Y : Fin 8 → Point) (p m : ℝ) (i₀ j₀ : Fin 8)
    (hY : IsConfiguration Y) (hp : 0 < p) (hstat : Stationary p Y) (hne : i₀ ≠ j₀)
    (hm : 0 < m) (hmmax : m ≤ 29/20) (hd : squaredDistance Y i₀ j₀=m)
    (hmin : ∀ i j, i ≠ j → m ≤ squaredDistance Y i j) :
    forceFactor m*m^(-p) ≤ squaredEnergy p Y := by
  let u := forceAxis Y i₀ j₀ m
  let f := forceFlow p u Y
  let c := normalizedEdgeCost m u Y
  obtain ⟨hf,hclosest,_⟩ := stationary_flow Y p m i₀ j₀ hY hp hstat hne hm hmmax hd hmin
  obtain ⟨L,hL,hrecon⟩ := cycle_decomposition f hf
  have hbound : (L.map (fun b => forceFactor m*(b.1*b.2.unitFlow i₀ j₀))).sum ≤
      (L.map (fun b => b.1*cycleNormalizedCost m Y u b.2)).sum := by
    clear hrecon
    induction L with
    | nil => simp
    | cons b L ih =>
      simp only [List.map_cons,List.sum_cons]
      have hb := hL b (by simp)
      have hcost := positive_cycle_cost_lower Y p m i₀ j₀ hY hp hstat hne hm hmmax hd hmin b.2 hb.2
      have hbnd : forceFactor m*(b.1*b.2.unitFlow i₀ j₀) ≤ b.1*cycleNormalizedCost m Y u b.2 := by
        nlinarith [mul_le_mul_of_nonneg_left hcost hb.1.le]
      exact add_le_add hbnd (ih (fun a ha => hL a (by simp [ha])))
  have hleft : (L.map (fun b => forceFactor m*(b.1*b.2.unitFlow i₀ j₀))).sum=forceFactor m*f i₀ j₀ := by
    rw [hrecon i₀ j₀]
    clear hL hrecon hbound
    induction L with
    | nil => simp
    | cons b L ih => simp only [List.map_cons,List.sum_cons,mul_add,ih]
  have hright : (L.map (fun b => b.1*cycleNormalizedCost m Y u b.2)).sum=
      ∑ i,∑ j,f i j*c i j := by
    simp_rw [hrecon]
    exact (list_flow_cost_sum L c).symm
  rw [hleft,hright] at hbound
  have henergy := forceFlow_total_cost_le Y hY p m u hm hmmax
  have h := hbound.trans henergy
  have hs : 0 < sin (forceAngle m) := (forceAxis_spec Y hY m hm hmmax i₀ j₀ hd).2.1
  have hscale : 0 < sin (forceAngle m)/m := div_pos hs hm
  have he : forceFactor m*f i₀ j₀=(sin (forceAngle m)/m)*(forceFactor m*m^(-p)) := by
    change forceFactor m*forceFlow p (forceAxis Y i₀ j₀ m) Y i₀ j₀=_
    rw [hclosest]
    have hpow : m^(-p-1)=m^(-p)/m := by rw [Real.rpow_sub hm,Real.rpow_one]
    rw [hpow]
    ring
  rw [he] at h
  exact (mul_le_mul_iff_right₀ hscale).mp h

#check force_bound_sum_cycle_costs
#print axioms force_bound_sum_cycle_costs
end Blueprint.Thomson.Tail.Implementation
