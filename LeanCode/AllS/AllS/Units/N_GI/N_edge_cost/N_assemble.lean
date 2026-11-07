import AllS.Units.N_GI.N_edge_cost.N_normalized_cost

noncomputable section
open Real
open SquareAntiprismVerification (crossVec)
namespace Blueprint.Thomson.Tail.Implementation

def PositiveEdgeCostData (Y : Fin 8 → Point) (u : Point) (m : ℝ) (i j : Fin 8) : Prop :=
  let α := projectionAngle u (Y i) (Y j)
  let v := forceAngle m/2
  0 < projectionRadius u (Y i) ∧ 0 < projectionRadius u (Y j) ∧
  0 < α ∧ α < π ∧
  orientedArea u Y i j=projectionRadius u (Y i)*projectionRadius u (Y j)*sin α ∧
  inner ℝ (Y i) (Y j)=projectionRadius u (Y i)*projectionRadius u (Y j)*cos α+
    projectionHeight u (Y i)*projectionHeight u (Y j) ∧
  1 ≤ normalizedEdgeCost m u Y i j ∧
  max ((tan v)⁻¹*tan (α/2)) (tan v*(tan (α/2))⁻¹) ≤ normalizedEdgeCost m u Y i j

theorem forceFlow_pos_area (Y : Fin 8 → Point) (u : Point) (p : ℝ) (i j : Fin 8)
    (hflow : 0 < forceFlow p u Y i j) : 0 < orientedArea u Y i j := by
  by_contra hn
  have hz : forceFlow p u Y i j=0 := by simp [forceFlow,max_eq_right (le_of_not_gt hn)]
  simpa [hz] using hflow

theorem forceFlow_zero_projection (Y : Fin 8 → Point) (u : Point) (p : ℝ) (i j : Fin 8)
    (hY : IsConfiguration Y) (hu : ‖u‖=1)
    (hz : projectionRadius u (Y i)=0 ∨ projectionRadius u (Y j)=0) :
    forceFlow p u Y i j=0 := by
  have hn : orientedArea u Y i j ≤ 0 := by
    apply le_of_not_gt
    intro ha
    have h := projected_angle_spec u (Y i) (Y j) hu (hY.1 i) (hY.1 j) ha
    rcases hz with hz | hz
    · linarith [h.1]
    · linarith [h.2.1]
  simp [forceFlow,max_eq_right hn]

theorem forceFlow_antipodal (Y : Fin 8 → Point) (u : Point) (p : ℝ) (i j : Fin 8)
    (hanti : Y j= -Y i) : forceFlow p u Y i j=0 := by
  have hz : crossVec (Y i) (Y j)=0 := by
    rw [hanti]
    ext k
    fin_cases k <;> simp [crossVec] <;> ring
  simp [forceFlow,orientedArea,hz]

theorem edge_cost_assemble (Y : Fin 8 → Point) (p m : ℝ)
    (i₀ j₀ : Fin 8) (hY : IsConfiguration Y) (hp : 0 < p) (hstat : Stationary p Y)
    (hne : i₀ ≠ j₀) (hm : 0 < m) (hmmax : m ≤ 29/20)
    (hd : squaredDistance Y i₀ j₀=m) (hmin : ∀ i j, i ≠ j → m ≤ squaredDistance Y i j) :
    let u := forceAxis Y i₀ j₀ m
    (∀ i j, 0 < forceFlow p u Y i j → PositiveEdgeCostData Y u m i j) ∧
    normalizedEdgeCost m u Y i₀ j₀=1 ∧
    (∀ i j, projectionRadius u (Y i)=0 ∨ projectionRadius u (Y j)=0 ∨ Y j= -Y i →
      forceFlow p u Y i j=0) := by
  let u := forceAxis Y i₀ j₀ m
  have haxis := forceAxis_spec Y hY m hm hmmax i₀ j₀ hd
  refine ⟨?_,?_,?_⟩
  · intro i j hf
    have ha := forceFlow_pos_area Y u p i j hf
    obtain ⟨hr1,hr2,ha0,hapi,harea,hinner⟩ :=
      edge_cost_projected_angle Y p m i₀ j₀ i j hY hp hstat hne hm hmmax hd hmin ha
    obtain ⟨hc,hcmax,_⟩ := edge_cost_normalized_cost Y p m i₀ j₀ i j hY hp hstat hne hm hmmax hd hmin ha
    exact ⟨hr1,hr2,ha0,hapi,harea,hinner,hc,hcmax⟩
  · change (sin (forceAngle m)/m)*(squaredDistance Y i₀ j₀/orientedArea u Y i₀ j₀)=1
    rw [hd,haxis.2.2.2]
    field_simp [hm.ne',haxis.2.1.ne']
  · intro i j hz
    rcases hz with hz | hz | hz
    · exact forceFlow_zero_projection Y u p i j hY haxis.2.2.1 (Or.inl hz)
    · exact forceFlow_zero_projection Y u p i j hY haxis.2.2.1 (Or.inr hz)
    · exact forceFlow_antipodal Y u p i j hz

#check edge_cost_assemble
#print axioms edge_cost_assemble
end Blueprint.Thomson.Tail.Implementation
