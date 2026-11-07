import AllS.Units.N_GI.N_boundary_support.N_strict_support
import Lean_Code.BoundaryPolygons

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem face_lengths_supported_polygon {Y : Fin 8 → Point} {c : ℝ}
    {hY : IsConfiguration Y} {hc : c ∈ Set.Ioo (0 : ℝ) 1}
    (C : ContactBoundaryCycle Y c hY hc) (hcupper : c < 3/10)
    (hbound : PackingInnerBound c Y) (hirr : PackingIrreducible c Y) :
    C.StrictSupport ∧ Function.Injective C.vertex ∧ 3 ≤ C.size + 1 := by
  have hs := boundary_support_strict_support C hcupper hbound hirr
  exact ⟨hs,C.vertex_injective_of_support hs,C.length_ge_three hirr⟩

/-- The supported orbit, reindexed once its length is written n+3, is an actual
strict spherical polygon. Its hemisphere/perimeter results are the generic API. -/
def face_lengths_polygon {n : ℕ} {Y : Fin 8 → Point} {c : ℝ}
    {hY : IsConfiguration Y} {hc : c ∈ Set.Ioo (0 : ℝ) 1}
    (C : ContactBoundaryCycle Y c hY hc) (hsize : C.size + 1 = n + 3)
    (hs : C.StrictSupport) : StrictSphericalPolygon n where
  vertex j := Y (C.vertex (Fin.cast hsize.symm j))
  unit j := hY.1 _
  support := by
    intro i j hji hjnext
    have heq : Fin.cast hsize.symm (i+1) = Fin.cast hsize.symm i + 1 := by
      apply Fin.ext
      simp [Fin.val_add, hsize]
    rw [heq]
    apply hs
    · intro h
      exact hji (Fin.cast_injective _ h)
    · intro h
      exact hjnext (Fin.cast_injective _ (h.trans heq.symm))

#print axioms face_lengths_supported_polygon

end Blueprint.Thomson.Tail.Implementation
