import AllS.Units.N_GI.N_cycle_winding.N_assemble

noncomputable section
open Real
open scoped BigOperators
namespace Blueprint.Thomson.Tail
open Implementation

theorem cycle_winding (Y : Fin 8 → Point) (p m : ℝ)
    (i₀ j₀ : Fin 8) (hY : IsConfiguration Y) (hm : 0 < m) (hmmax : m ≤ 29/20)
    (hd : squaredDistance Y i₀ j₀=m) (C : FlowCycle)
    (hC : C.Positive (forceFlow p (forceAxis Y i₀ j₀ m) Y)) :
    let u := forceAxis Y i₀ j₀ m
    ∃ q : ℤ, 1 ≤ q ∧ (∑ i,cycleProjectedAngle Y u C i)=2*π*q ∧
    (∀ i, 0 < cycleProjectedAngle Y u C i ∧ cycleProjectedAngle Y u C i < π) ∧
    ((C.size+1=3 ∨ C.size+1=4) → q=1) ∧ (C.size+1=5 → q=1 ∨ q=2) ∧
    (∀ k, C.point k=i₀ → C.point (k+1)=j₀ →
      cycleProjectedAngle Y u C k=2*(forceAngle m/2)) :=
  cycle_winding_assemble Y p m i₀ j₀ hY hm hmmax hd C hC

#check cycle_winding
#print axioms cycle_winding
end Blueprint.Thomson.Tail
