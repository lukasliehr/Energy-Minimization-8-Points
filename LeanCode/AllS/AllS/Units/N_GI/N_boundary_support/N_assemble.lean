import AllS.Units.N_GI.N_boundary_support.N_strict_support

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem boundary_support_assemble {Y : Fin 8 → Point} {c : ℝ}
    {hY : IsConfiguration Y} {hc : c ∈ Set.Ioo (0 : ℝ) 1}
    (C : ContactBoundaryCycle Y c hY hc) (hcupper : c < 3/10)
    (hbound : PackingInnerBound c Y) (hirr : PackingIrreducible c Y) : C.StrictSupport :=
  boundary_support_strict_support C hcupper hbound hirr

end Blueprint.Thomson.Tail.Implementation
