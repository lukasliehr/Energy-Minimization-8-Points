import AllS.Units.N_GI.N_tail_range.N_conditional_range
import AllS.Units.N_GI.N_variance_basic.N_quadratic_bridge
import AllS.Units.N_GI.N_variance_sharp.N_quartic_bridge
import AllS.Units.N_GI.N_balanced_energy.N_mean_bridge

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

/-- Assembly from the four remaining actual certificate statements. Each input
is an explicit hypothesis; none is postulated as an axiom or a completed result. -/
theorem tail_range_of_tensor_certificates
    (hboundary : BoundarySOSInfeasible)
    (hQ : ∀ q : TangentCoordinates, q∈rotationSlice →
      (∑ e : ContactIndex, contactWeight e *
        ‖sliceProjection (contactM e q-contactMeanM q)‖^2) ≤ 4*‖q‖^2)
    (hmean : MeanCubicAbsorption)
    (hvariance : VarianceCubicAbsorption) : TailRangeSpec := by
  apply tail_range_of_boundary_and_local_bounds hboundary
  constructor
  · intro q hq _
    exact variance_quadratic_norm_of_projected_bound q hq (hQ q hq)
  · intro q hq hr
    exact sharp_variance_of_cubic hvariance q hq hr
  · intro p hp q _ hr
    exact balancedMean_bound_of_cubic hmean p (by linarith) q hr

#print axioms tail_range_of_tensor_certificates
end Blueprint.Thomson.Tail.Implementation
