import AllS.Units.N_GI.N_force_bound.N_endpoint_force

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem force_bound_assemble : ForceSpec ∧ ForceEndpointSpec := by
  constructor
  · intro p m Y hY hp hstat hm hmmax hmin hattain
    obtain ⟨i,j,hij,hd⟩ := hattain
    exact force_bound_sum_cycle_costs Y p m i j hY hp hstat hij hm hmmax hd hmin
  · intro p m m₀ Y hY hp hstat hm hmm₀ hm₀max hmin hattain
    obtain ⟨i,j,hij,hd⟩ := hattain
    exact force_bound_endpoint_force Y p m m₀ i j hY hp hstat hij hm hmm₀ hm₀max hd hmin

#check force_bound_assemble
#print axioms force_bound_assemble
end Blueprint.Thomson.Tail.Implementation
