import AllS.Units.N_GI.N_cycle5.N_winding_two

noncomputable section
open Real
open scoped BigOperators
namespace Blueprint.Thomson.Tail.Implementation

theorem cycle5_assemble (Y : Fin 8 → Point) (p m : ℝ) (i₀ j₀ : Fin 8)
    (hY : IsConfiguration Y) (hp : 0 < p) (hstat : Stationary p Y) (hne : i₀ ≠ j₀)
    (hm : 0 < m) (hmmax : m ≤ 29/20) (hd : squaredDistance Y i₀ j₀=m)
    (hmin : ∀ i j, i ≠ j → m ≤ squaredDistance Y i j)
    (C : FlowCycle) (hC : C.Positive (forceFlow p (forceAxis Y i₀ j₀ m) Y))
    (hlen : C.size+1=5) (hcontains : ∃ k₀, C.point k₀=i₀ ∧ C.point (k₀+1)=j₀) :
    forceFactor m ≤ cycleNormalizedCost m Y (forceAxis Y i₀ j₀ m) C := by
  obtain ⟨k₀,hk₀,hk₁⟩ := hcontains
  obtain ⟨q,hq,hsum,_,_,hcases,_⟩ := cycle_winding Y p m i₀ j₀ hY hm hmmax hd C hC
  rcases hcases hlen with rfl|rfl
  · have hs : ∑ i,cycleProjectedAngle Y (forceAxis Y i₀ j₀ m) C i=2*π := by simpa using hsum
    exact (cycle5_winding_one Y p m i₀ j₀ hY hp hstat hne hm hmmax hd hmin C hC hlen k₀ hk₀ hk₁ hs).2
  · have hs : ∑ i,cycleProjectedAngle Y (forceAxis Y i₀ j₀ m) C i=2*π*2 := by simpa using hsum
    obtain ⟨hG,h6,hcost⟩ := cycle5_winding_two Y p m i₀ j₀ hY hp hstat hne hm hmmax hd hmin C hC hlen k₀ hk₀ hk₁ hs
    exact (hG.trans (h6.trans hcost)).le

#check cycle5_assemble
#print axioms cycle5_assemble
end Blueprint.Thomson.Tail.Implementation
