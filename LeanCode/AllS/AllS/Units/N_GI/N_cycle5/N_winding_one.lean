import AllS.Units.N_GI.N_cycle5.N_cost_jensen
import AllS.Units.N_GI.N_cycle5.N_factor_bounds

noncomputable section
open Real
open scoped BigOperators
namespace Blueprint.Thomson.Tail.Implementation

theorem cycle5_winding_one (Y : Fin 8 → Point) (p m : ℝ) (i₀ j₀ : Fin 8)
    (hY : IsConfiguration Y) (hp : 0 < p) (hstat : Stationary p Y) (hne : i₀ ≠ j₀)
    (hm : 0 < m) (hmmax : m ≤ 29/20) (hd : squaredDistance Y i₀ j₀=m)
    (hmin : ∀ i j, i ≠ j → m ≤ squaredDistance Y i j)
    (C : FlowCycle) (hC : C.Positive (forceFlow p (forceAxis Y i₀ j₀ m) Y))
    (hlen : C.size+1=5) (k₀ : Fin (C.size+1)) (hk₀ : C.point k₀=i₀) (hk₁ : C.point (k₀+1)=j₀)
    (hsum : ∑ i,cycleProjectedAngle Y (forceAxis Y i₀ j₀ m) C i=2*π) :
    let v := forceAngle m/2
    1+4*tan v*(tan ((π-v)/4))⁻¹=forceFactor m ∧
      forceFactor m ≤ cycleNormalizedCost m Y (forceAxis Y i₀ j₀ m) C := by
  have hj := (positive_cycle_jensen Y p m i₀ j₀ hY hp hstat hne hm hmmax hd hmin C hC
    k₀ hk₀ hk₁ 1 (by simpa using hsum)).2
  have hn : C.size=4 := by omega
  simp only [hn,Nat.cast_ofNat,Int.cast_one,mul_one] at hj
  refine ⟨force_factor_cot_identity m hm hmmax,?_⟩
  rw [← force_factor_cot_identity m hm hmmax]
  nlinarith

#check cycle5_winding_one
#print axioms cycle5_winding_one
end Blueprint.Thomson.Tail.Implementation
