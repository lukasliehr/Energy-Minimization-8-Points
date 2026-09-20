import Lean_Code.SphericalCone
import Lean_Code.BoundaryPolygons

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace StrictSphericalPolygon

/-- The closed spherical region cut out by the oriented edge planes. -/
def closedRegion {n : ℕ} (Q : StrictSphericalPolygon n) : Set ℝ³ :=
  {z | ‖z‖ = 1 ∧ ∀ i, 0 ≤ inner ℝ (crossVec (Q.vertex i) (Q.vertex (i + 1))) z}

theorem triangle_region_covering (Q : StrictSphericalPolygon 0) (c : ℝ)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hcontact : ∀ i, inner ℝ (Q.vertex i) (Q.vertex (i + 1)) = c)
    (z : ℝ³) (hz : z ∈ Q.closedRegion) :
    ∃ i, c < inner ℝ z (Q.vertex i) := by
  have hab : inner ℝ (Q.vertex 0) (Q.vertex 1) = c := hcontact 0
  have hbd : inner ℝ (Q.vertex 1) (Q.vertex 2) = c := hcontact 1
  have hda : inner ℝ (Q.vertex 2) (Q.vertex 0) = c := hcontact 2
  have ht : 0 < inner ℝ (crossVec (Q.vertex 0) (Q.vertex 1)) (Q.vertex 2) := Q.turn_pos 0
  rcases contact_triangle_halfspace_covering (Q.vertex 0) (Q.vertex 1) (Q.vertex 2) z c
    (Q.unit 0) (Q.unit 1) (Q.unit 2) hz.1 hc hab
    ((real_inner_comm (Q.vertex 2) (Q.vertex 0)).trans hda) hbd ht
    (hz.2 0) (hz.2 1) (hz.2 2) with h | h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · exact ⟨2, h⟩

theorem quadrilateral_region_covering (Q : StrictSphericalPolygon 1) (c : ℝ)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hcontact : ∀ i, inner ℝ (Q.vertex i) (Q.vertex (i + 1)) = c)
    (z : ℝ³) (hz : z ∈ Q.closedRegion) :
    ∃ i, c < inner ℝ z (Q.vertex i) := by
  by_cases hb : z = Q.vertex 1
  · exact ⟨1, by rw [hb]; simpa [Q.unit 1] using hc.2⟩
  by_cases he : z = Q.vertex 3
  · exact ⟨3, by rw [he]; simpa [Q.unit 3] using hc.2⟩
  have h012 : 0 < inner ℝ (crossVec (Q.vertex 0) (Q.vertex 1)) (Q.vertex 2) := Q.turn_pos 0
  have h023 : 0 < inner ℝ (crossVec (Q.vertex 0) (Q.vertex 2)) (Q.vertex 3) := by
    rw [triple_cyclic]
    exact Q.support 2 0 (by decide) (by decide)
  rcases contact_rhombus_halfspace_covering (Q.vertex 0) (Q.vertex 1) (Q.vertex 2)
    (Q.vertex 3) z c (Q.unit 0) (Q.unit 1) (Q.unit 2) (Q.unit 3) hz.1 hc.1
    (hcontact 0) (hcontact 1) (hcontact 2) (hcontact 3) h012 h023
    (hz.2 0) (hz.2 1) (hz.2 2) (hz.2 3) hb he with h | h
  · exact ⟨0, h⟩
  · exact ⟨2, h⟩

/-- Every point of a short contact polygon is strictly within contact
distance of one of its vertices. This includes its boundary. -/
theorem contact_region_covering {n : ℕ} (Q : StrictSphericalPolygon n) (c : ℝ)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c ≤ aInf)
    (hcontact : ∀ i, inner ℝ (Q.vertex i) (Q.vertex (i + 1)) = c)
    (z : ℝ³) (hz : z ∈ Q.closedRegion) :
    ∃ i, c < inner ℝ z (Q.vertex i) := by
  have hn := contact_polygon_three_or_four Q c hc.1 hcupper hcontact
  have hn' : n = 0 ∨ n = 1 := by omega
  rcases hn' with rfl | rfl
  · exact Q.triangle_region_covering c hc hcontact z hz
  · exact Q.quadrilateral_region_covering c hc hcontact z hz

end StrictSphericalPolygon

namespace ContactBoundaryCycle

variable {Y : Fin 8 → ℝ³} {c : ℝ} {hY : IsConfiguration Y} {hc : c ∈ Set.Ioo (0 : ℝ) 1}

def closedRegion (C : ContactBoundaryCycle Y c hY hc) : Set ℝ³ :=
  {z | ‖z‖ = 1 ∧ ∀ i,
    0 ≤ inner ℝ (crossVec (Y (C.vertex i)) (Y (C.vertex (i + 1)))) z}

theorem region_covering (C : ContactBoundaryCycle Y c hY hc)
    (hirr : PackingIrreducible c Y) (hcupper : c ≤ aInf) (hsupport : C.StrictSupport)
    (z : ℝ³) (hz : z ∈ C.closedRegion) :
    ∃ i, c < inner ℝ z (Y (C.vertex i)) := by
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
      exact Q.contact_region_covering c hc hcupper C.contact z hz

/-- No additional packing vertex can lie in the closed region of a
supported contact boundary. Global coverage is still a separate obligation. -/
theorem region_configuration_vertex (C : ContactBoundaryCycle Y c hY hc)
    (hirr : PackingIrreducible c Y) (hcupper : c ≤ aInf) (hbound : PackingInnerBound c Y)
    (hsupport : C.StrictSupport) (k : Fin 8) (hk : Y k ∈ C.closedRegion) :
    ∃ i, C.vertex i = k := by
  obtain ⟨i, hi⟩ := C.region_covering hirr hcupper hsupport (Y k) hk
  refine ⟨i, ?_⟩
  by_contra hne
  exact (not_lt_of_ge (hbound k (C.vertex i) (Ne.symm hne))) hi

end ContactBoundaryCycle

end SquareAntiprismVerification
