import AllS.Units.N_GI.N_force_bound.N_assemble

namespace Blueprint.Thomson.Tail

theorem force_bound : ForceSpec ∧ ForceEndpointSpec := Implementation.force_bound_assemble

#check force_bound
#print axioms force_bound
end Blueprint.Thomson.Tail
