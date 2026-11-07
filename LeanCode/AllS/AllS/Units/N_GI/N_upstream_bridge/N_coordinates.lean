import Blueprint.RootBridge
import Blueprint.Tail

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem upstream_bridge_coordinates (a : ℝ) :
    X a = SquareAntiprismVerification.X a := (Blueprint.antiprism_coordinates a).symm

theorem packingReference_eq_upstream (i : Fin 8) :
    packingReference i = SquareAntiprismVerification.P (cyclicIndex i) := by
  unfold packingReference SquareAntiprismVerification.P
  rw [Blueprint.antiprism_coordinates]
  rfl

theorem cyclicIndex_bijective : Function.Bijective cyclicIndex := by decide

def cyclicIndexEquiv : Equiv.Perm (Fin 8) := Equiv.ofBijective cyclicIndex cyclicIndex_bijective

@[simp] theorem cyclicIndexEquiv_apply (i : Fin 8) : cyclicIndexEquiv i = cyclicIndex i := rfl

#print axioms upstream_bridge_coordinates
#print axioms packingReference_eq_upstream
#print axioms cyclicIndex_bijective
end Blueprint.Thomson.Tail.Implementation
