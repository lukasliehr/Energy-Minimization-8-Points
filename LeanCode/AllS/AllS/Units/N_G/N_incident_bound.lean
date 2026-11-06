import AllS.Units.N_GI.N_incident_bound.N_assemble

noncomputable section
namespace Blueprint.Thomson.Tail
open Implementation

theorem incident_bound (p : ℝ) (hp : pStart≤p) (q : TangentCoordinates)
    (hq : q∈convexTailDomain p) :
    ∀ i, (∑ j∈Finset.univ.erase i, (tau/squaredDistance (orthographicChart q) i j)^(p+1))<(31:ℝ)/5 :=
  incident_bound_assemble p hp q hq

#print axioms incident_bound
end Blueprint.Thomson.Tail
