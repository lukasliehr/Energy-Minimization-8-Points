import AllS.Units.N_G.N_setup
import Lean_Code.ContactRotationInvariants

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem weak_euler_rotation_constant (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    {β : Type*} (v : ContactDart Y c → β)
    (hv : ∀ d, v (contactRotate Y c hY hc d) = v d)
    (i : Fin 8) (j k : ContactNeighbor Y c i) : v ⟨i, j⟩ = v ⟨i, k⟩ := by
  classical
  have hne : ∃ j, j ≠ i ∧ inner ℝ (Y i) (Y j) = c := ⟨j, j.property⟩
  let D := Classical.choice (contact_order_exists Y c i hY hc hne)
  apply D.successor_invariant_constant (fun j => v ⟨i, j⟩) _ j k
  intro l
  have h := hv ⟨i, l⟩
  change v ⟨i, contactRotateAt Y c hY hc i l⟩ = v ⟨i, l⟩ at h
  simpa only [contactRotateAt, dif_pos hne] using h

def contactBaseDart (Y : Fin 8 → Point) (c : ℝ)
    (hne : ∀ i, ∃ j, j ≠ i ∧ inner ℝ (Y i) (Y j) = c) (i : Fin 8) : ContactDart Y c :=
  ⟨i, ⟨Classical.choose (hne i), Classical.choose_spec (hne i)⟩⟩

#print axioms weak_euler_rotation_constant

end Blueprint.Thomson.Tail.Implementation
