import AllS.Units.N_GI.N_cycle_winding.N_winding_cases

noncomputable section
open Real
open scoped BigOperators
namespace Blueprint.Thomson.Tail.Implementation

theorem cycle_winding_assemble (Y : Fin 8 → Point) (p m : ℝ)
    (i₀ j₀ : Fin 8) (hY : IsConfiguration Y) (hm : 0 < m) (hmmax : m ≤ 29/20)
    (hd : squaredDistance Y i₀ j₀=m) (C : FlowCycle)
    (hC : C.Positive (forceFlow p (forceAxis Y i₀ j₀ m) Y)) :
    let u := forceAxis Y i₀ j₀ m
    ∃ q : ℤ, 1 ≤ q ∧ (∑ i,cycleProjectedAngle Y u C i)=2*π*q ∧
    (∀ i, 0 < cycleProjectedAngle Y u C i ∧ cycleProjectedAngle Y u C i < π) ∧
    ((C.size+1=3 ∨ C.size+1=4) → q=1) ∧ (C.size+1=5 → q=1 ∨ q=2) ∧
    (∀ k, C.point k=i₀ → C.point (k+1)=j₀ →
      cycleProjectedAngle Y u C k=2*(forceAngle m/2)) := by
  have hu := (forceAxis_spec Y hY m hm hmmax i₀ j₀ hd).2.2.1
  obtain ⟨q,hq,hs⟩ := cycle_winding_angle_sum_integer Y _ p hY hu C hC
  obtain ⟨h34,h5,he⟩ := cycle_winding_winding_cases Y p m i₀ j₀ hY hm hmmax hd C hC q hq hs
  refine ⟨q,hq,hs,?_,h34,h5,he⟩
  intro i
  have h := projected_angle_spec _ _ _ hu (hY.1 _) (hY.1 _)
    (forceFlow_pos_area Y _ p _ _ (hC i))
  exact ⟨h.2.2.1,h.2.2.2.1⟩

#check cycle_winding_assemble
#print axioms cycle_winding_assemble
end Blueprint.Thomson.Tail.Implementation
