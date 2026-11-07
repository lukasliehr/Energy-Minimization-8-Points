import AllS.Units.N_GI.N_weak_euler.N_weak_count
import AllS.Units.N_GI.N_covering.N_no_rattlers

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem weak_euler_assemble (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c < 3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport) :
    2 * Fintype.card (ContactBoundaryOrbit Y c hY hc) + 12 ≤ Fintype.card (ContactDart Y c) := by
  exact weak_euler_weak_count Y c hY hc hcupper hirr
    (covering_no_rattlers Y c hY hc hcupper hirr hbound hne hsupport)

#print axioms weak_euler_assemble

end Blueprint.Thomson.Tail.Implementation
