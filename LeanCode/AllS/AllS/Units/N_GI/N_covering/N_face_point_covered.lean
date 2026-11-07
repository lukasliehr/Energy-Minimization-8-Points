import AllS.Units.N_GI.N_face_lengths.N_length_three_four
import Lean_Code.ContactFaceRegions

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem covering_polygon_point {n : ℕ} (Q : StrictSphericalPolygon n) (c : ℝ)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c < 3/10)
    (hcontact : ∀ i, inner ℝ (Q.vertex i) (Q.vertex (i + 1)) = c)
    (z : Point) (hz : z ∈ Q.closedRegion) :
    ∃ i, c < inner ℝ z (Q.vertex i) := by
  have hn := face_lengths_polygon_three_four Q c hc.1 hcupper hcontact
  have hn' : n = 0 ∨ n = 1 := by omega
  rcases hn' with rfl | rfl
  · exact Q.triangle_region_covering c hc hcontact z hz
  · exact Q.quadrilateral_region_covering c hc hcontact z hz

variable {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y} {hc : c ∈ Set.Ioo (0 : ℝ) 1}

theorem covering_face_point_covered (C : ContactBoundaryCycle Y c hY hc)
    (hirr : PackingIrreducible c Y) (hcupper : c < 3/10) (hsupport : C.StrictSupport)
    (z : Point) (hz : z ∈ C.closedRegion) :
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
      exact covering_polygon_point Q c hc hcupper C.contact z hz

theorem covering_region_configuration_vertex (C : ContactBoundaryCycle Y c hY hc)
    (hirr : PackingIrreducible c Y) (hcupper : c < 3/10) (hbound : PackingInnerBound c Y)
    (hsupport : C.StrictSupport) (k : Fin 8) (hk : Y k ∈ C.closedRegion) :
    ∃ i, C.vertex i = k := by
  obtain ⟨i, hi⟩ := covering_face_point_covered C hirr hcupper hsupport (Y k) hk
  refine ⟨i, ?_⟩
  by_contra hne
  exact (not_lt_of_ge (hbound k (C.vertex i) (Ne.symm hne))) hi

#print axioms covering_face_point_covered

end Blueprint.Thomson.Tail.Implementation
