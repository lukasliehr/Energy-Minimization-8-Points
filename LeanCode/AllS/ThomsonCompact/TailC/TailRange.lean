import AllS.Units.N_GI.N_tail_range.N_tensor_assembly
import AllS.Units.N_GI.N_signed_mean.N_cubic_absorbed
import AllS.Units.N_GI.N_variance_sharp.N_cubic_absorbed
import ThomsonCompact.TailC.Boundary.Sound
import ThomsonCompact.TailC.Centered.Final

/-!
# TailC: the tail range from the compact certificates (workstream TC1)

Drop-in replacement of `Blueprint.Thomson.Tail.Implementation.tail_range_assemble` (old `N_tail_range.N_assemble`):
the same generic assembly `tail_range_of_tensor_certificates`, with the compact
`Boundary.boundary_sos_infeasible_compact` and `Centered.centered_quadratic_bound_four_compact` in place of the old
`boundary_sos_infeasible` and `centered_quadratic_bound_four`. The old `N_AI/N_boundary_arithmetic` products and the
136 `N_centered_quadratic.N_qentry_*` entry proofs are no longer imported (closure 9.150 GB → 0.875 GB of old oleans;
`TailC/PLAN.md`). The signed-mean and variance certificates are still the old ones (0.107 GB).
-/

namespace ThomsonCompact.TailC
open Blueprint.Thomson.Tail Blueprint.Thomson.Tail.Implementation

theorem tail_range_compact : TailRangeSpec :=
  tail_range_of_tensor_certificates Boundary.boundary_sos_infeasible_compact
    (fun q _ => Centered.centered_quadratic_bound_four_compact q) mean_cubic_absorption variance_cubic_absorption

#print axioms tail_range_compact

end ThomsonCompact.TailC
