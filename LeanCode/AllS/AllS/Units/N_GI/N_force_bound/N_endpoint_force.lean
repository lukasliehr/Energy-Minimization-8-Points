import AllS.Units.N_GI.N_force_bound.N_endpoint_monotone

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem force_bound_endpoint_force (Y : Fin 8 → Point) (p m m₀ : ℝ) (i₀ j₀ : Fin 8)
    (hY : IsConfiguration Y) (hp : 3/2 ≤ p) (hstat : Stationary p Y) (hne : i₀ ≠ j₀)
    (hm : 0 < m) (hmm₀ : m ≤ m₀) (hm₀max : m₀ ≤ 29/20)
    (hd : squaredDistance Y i₀ j₀=m)
    (hmin : ∀ i j, i ≠ j → m ≤ squaredDistance Y i j) :
    forceFactor m₀*m₀^(-p) ≤ squaredEnergy p Y := by
  have hmm : m ≤ 29/20 := hmm₀.trans hm₀max
  have hmono := (force_bound_endpoint_monotone p hp).antitoneOn
    (show m ∈ Set.Ioc (0:ℝ) (29/20) from ⟨hm,hmm⟩)
    (show m₀ ∈ Set.Ioc (0:ℝ) (29/20) from ⟨hm.trans_le hmm₀,hm₀max⟩) hmm₀
  exact hmono.trans (force_bound_sum_cycle_costs Y p m i₀ j₀ hY (by linarith)
    hstat hne hm hmm hd hmin)

#check force_bound_endpoint_force
#print axioms force_bound_endpoint_force
end Blueprint.Thomson.Tail.Implementation
