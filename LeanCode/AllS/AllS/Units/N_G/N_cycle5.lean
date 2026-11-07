import AllS.Units.N_GI.N_cycle5.N_assemble

noncomputable section
namespace Blueprint.Thomson.Tail
open Implementation

theorem cycle5 (Y : Fin 8 → Point) (p m : ℝ) (i₀ j₀ : Fin 8)
    (hY : IsConfiguration Y) (hp : 0 < p) (hstat : Stationary p Y) (hne : i₀ ≠ j₀)
    (hm : 0 < m) (hmmax : m ≤ 29/20) (hd : squaredDistance Y i₀ j₀=m)
    (hmin : ∀ i j, i ≠ j → m ≤ squaredDistance Y i j)
    (C : FlowCycle) (hC : C.Positive (forceFlow p (forceAxis Y i₀ j₀ m) Y))
    (hlen : C.size+1=5) (hcontains : ∃ k₀, C.point k₀=i₀ ∧ C.point (k₀+1)=j₀) :
    forceFactor m ≤ cycleNormalizedCost m Y (forceAxis Y i₀ j₀ m) C :=
  cycle5_assemble Y p m i₀ j₀ hY hp hstat hne hm hmmax hd hmin C hC hlen hcontains

#check cycle5
#print axioms cycle5
end Blueprint.Thomson.Tail
