import AllS.Units.N_GI.N_incident_bound.N_all_incident

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem incident_bound_assemble (p : ℝ) (hp : (97:ℝ)/2≤p) (q : TangentCoordinates)
    (hq : q∈convexTailDomain p) :
    ∀ i, (∑ j∈Finset.univ.erase i, (tau/squaredDistance (orthographicChart q) i j)^(p+1))<(31:ℝ)/5 :=
  incident_bound_all_incident p hp q hq

#print axioms incident_bound_assemble
end Blueprint.Thomson.Tail.Implementation
