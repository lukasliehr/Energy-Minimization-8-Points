import AllS.Units.N_GI.N_edge_cost.N_assemble

noncomputable section
namespace Blueprint.Thomson.Tail
open Implementation

theorem edge_cost (Y : Fin 8 → Point) (p m : ℝ)
    (i₀ j₀ : Fin 8) (hY : IsConfiguration Y) (hp : 0 < p) (hstat : Stationary p Y)
    (hne : i₀ ≠ j₀) (hm : 0 < m) (hmmax : m ≤ 29/20)
    (hd : squaredDistance Y i₀ j₀=m) (hmin : ∀ i j, i ≠ j → m ≤ squaredDistance Y i j) :
    let u := forceAxis Y i₀ j₀ m
    (∀ i j, 0 < forceFlow p u Y i j → PositiveEdgeCostData Y u m i j) ∧
    normalizedEdgeCost m u Y i₀ j₀=1 ∧
    (∀ i j, projectionRadius u (Y i)=0 ∨ projectionRadius u (Y j)=0 ∨ Y j= -Y i →
      forceFlow p u Y i j=0) :=
  edge_cost_assemble Y p m i₀ j₀ hY hp hstat hne hm hmmax hd hmin

#check edge_cost
#print axioms edge_cost
end Blueprint.Thomson.Tail
