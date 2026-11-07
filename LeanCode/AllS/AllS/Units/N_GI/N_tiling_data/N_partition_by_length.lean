import AllS.Units.N_GI.N_face_lengths.N_length_three_four
import Lean_Code.BoundaryFaceArrays

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem tiling_data_partition_by_length (Y : Fin 8 → Point) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c < 3/10) (hirr : PackingIrreducible c Y)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport)
    {M : Type*} [AddCommMonoid M] (w : ContactBoundaryOrbit Y c hY hc → M) :
    (∑ f : BoundaryOfLength Y c hY hc 3, w f.val) +
      (∑ f : BoundaryOfLength Y c hY hc 4, w f.val) = ∑ f, w f := by
  classical
  let p := fun f : ContactBoundaryOrbit Y c hY hc => (boundaryOrbitCycle Y c hY hc f).size + 1 = 3
  have hiff (f : ContactBoundaryOrbit Y c hY hc) :
      ¬ p f ↔ (boundaryOrbitCycle Y c hY hc f).size + 1 = 4 := by
    have h := face_lengths_length_three_four (boundaryOrbitCycle Y c hY hc f) hirr hcupper
      (hsupport (boundaryOrbitCycle Y c hY hc f))
    dsimp [p]
    omega
  let e := Equiv.subtypeEquivRight hiff
  have heq : (∑ f : {f // ¬ p f}, w f.val) = ∑ f : BoundaryOfLength Y c hY hc 4, w f.val :=
    Equiv.sum_comp e (fun f => w f.val)
  have h := Fintype.sum_subtype_add_sum_subtype p w
  rw [heq] at h
  exact h

#print axioms tiling_data_partition_by_length

end Blueprint.Thomson.Tail.Implementation
