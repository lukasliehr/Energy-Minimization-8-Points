import Lean_Code.ContactBoundary
import Lean_Code.PolygonExcess
import Lean_Code.ContactSector

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace ContactBoundaryCycle

variable {Y : Fin 8 → ℝ³} {c : ℝ} {hY : IsConfiguration Y} {hc : c ∈ Set.Ioo (0 : ℝ) 1}

/-- The strict geometric support condition still to be proved for actual
boundary cycles. In particular, this definition is not an existence claim. -/
def StrictSupport (C : ContactBoundaryCycle Y c hY hc) : Prop :=
  ∀ i j, j ≠ i → j ≠ i + 1 →
    0 < inner ℝ (crossVec (Y (C.vertex i)) (Y (C.vertex (i + 1)))) (Y (C.vertex j))

theorem vertex_injective_of_support (C : ContactBoundaryCycle Y c hY hc)
    (hsupport : C.StrictSupport) : Function.Injective C.vertex := by
  intro i j heq
  by_contra hij
  by_cases hjnext : j = i + 1
  · subst j
    exact C.adjacent_ne i heq
  · have h := hsupport i j (Ne.symm hij) hjnext
    rw [← heq, crossVec_inner_left] at h
    exact (lt_irrefl 0) h

lemma length_le_eight_of_support (C : ContactBoundaryCycle Y c hY hc)
    (hsupport : C.StrictSupport) : C.size + 1 ≤ 8 := by
  simpa using Fintype.card_le_of_injective C.vertex (C.vertex_injective_of_support hsupport)

theorem three_or_four_of_support (C : ContactBoundaryCycle Y c hY hc)
    (hirr : PackingIrreducible c Y) (hcupper : c ≤ aInf) (hsupport : C.StrictSupport) :
    C.size + 1 = 3 ∨ C.size + 1 = 4 := by
  have hlength := C.length_ge_three hirr
  rcases C with ⟨m, point, hinj, hstep⟩
  change 3 ≤ m + 1 at hlength
  cases m with
  | zero => omega
  | succ m =>
    cases m with
    | zero => omega
    | succ n =>
      let C : ContactBoundaryCycle Y c hY hc := ⟨n + 2, point, hinj, hstep⟩
      let Q : StrictSphericalPolygon n := {
        vertex := fun j => Y (C.vertex j)
        unit := fun j => hY.1 (C.vertex j)
        support := hsupport }
      exact contact_polygon_three_or_four Q c hc.1 hcupper C.contact

theorem nonadjacent_inner_lt (C : ContactBoundaryCycle Y c hY hc)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hsupport : C.StrictSupport) (i j : Fin (C.size + 1))
    (hji : j ≠ i) (hjnext : j ≠ i + 1) (hjprev : j ≠ i - 1) :
    inner ℝ (Y (C.vertex i)) (Y (C.vertex j)) < c := by
  have hstep : contactFaceNext Y c hY hc (C.point (i - 1)) = C.point i := by
    simpa only [sub_add_cancel] using C.step (i - 1)
  have htip : (C.point (i - 1)).2.val = C.vertex i := by
    simpa only [sub_add_cancel] using (C.vertex_next (i - 1)).symm
  have hleft : 0 < inner ℝ
      (crossVec (Y (C.point (i - 1)).2.val)
        (Y (contactFaceNext Y c hY hc (C.point (i - 1))).2.val)) (Y (C.vertex j)) := by
    rw [htip, hstep, ← C.vertex_next i]
    exact hsupport i j hji hjnext
  have hright : 0 < inner ℝ (crossVec (Y (C.point (i - 1)).2.val) (Y (C.vertex j)))
      (Y (C.point (i - 1)).1) := by
    rw [htip]
    have h := hsupport (i - 1) j hjprev (by simpa only [sub_add_cancel] using hji)
    rw [sub_add_cancel, triple_cyclic] at h
    exact h
  have h := contact_corner_interior_strict Y c hY hc hirr hbound (C.point (i - 1))
    (C.vertex j) hleft hright
  rwa [htip] at h

end ContactBoundaryCycle

end SquareAntiprismVerification
