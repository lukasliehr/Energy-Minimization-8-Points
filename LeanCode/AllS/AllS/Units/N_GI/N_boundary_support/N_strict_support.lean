import AllS.Units.N_GI.N_boundary_support.N_orbit_weak_support
import Lean_Code.WeakBoundarySupport

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem boundary_support_strict_support {Y : Fin 8 → Point} {c : ℝ}
    {hY : IsConfiguration Y} {hc : c ∈ Set.Ioo (0 : ℝ) 1}
    (C : ContactBoundaryCycle Y c hY hc) (hcupper : c < 3/10)
    (hbound : PackingInnerBound c Y) (hirr : PackingIrreducible c Y) : C.StrictSupport :=
  C.strict_support_of_weak_support hirr hbound
    (boundary_support_orbit_weak_support C hcupper hbound hirr)

#print axioms boundary_support_strict_support

end Blueprint.Thomson.Tail.Implementation
