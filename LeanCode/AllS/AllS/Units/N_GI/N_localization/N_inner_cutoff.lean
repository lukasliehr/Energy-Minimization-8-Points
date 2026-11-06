import AllS.Units.N_GI.N_constants.N_algebra
import Lean_Code.PackingMaximum

noncomputable section
open SquareAntiprismVerification (packingMaxInner packingMaxInner_le_iff)
namespace Blueprint.Thomson.Tail.Implementation

theorem localization_inner_cutoff (Y : Fin 8 → Point) (hY : ∀i,‖Y i‖=1)
    (hd : ∀i j,i≠j → tau-gap≤ squaredDistance Y i j) : packingMaxInner Y≤packingHeight+33/2000 := by
  apply (packingMaxInner_le_iff Y _).mpr
  intro i j hij
  have h := hd i j hij
  rw [squaredDistance,norm_sub_sq_real,hY i,hY j] at h
  dsimp [tau,gap] at h
  nlinarith

#print axioms localization_inner_cutoff
end Blueprint.Thomson.Tail.Implementation
