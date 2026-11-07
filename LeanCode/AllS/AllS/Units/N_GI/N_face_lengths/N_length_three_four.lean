import AllS.Units.N_GI.N_face_lengths.N_supported_polygon
import AllS.Units.N_GI.N_constants.N_angle_cutoff

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

variable {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y} {hc : c ∈ Set.Ioo (0 : ℝ) 1}

theorem face_lengths_polygon_three_four {n : ℕ} (Q : StrictSphericalPolygon n) (c : ℝ)
    (hc : 0 < c) (hcupper : c < 3/10)
    (hcontact : ∀ i, inner ℝ (Q.vertex i) (Q.vertex (i + 1)) = c) :
    n + 3 = 3 ∨ n + 3 = 4 := by
  have hperim := Q.perimeter_lt_two_pi
  simp only [StrictSphericalPolygon.perimeter, sphereAngle, hcontact,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hperim
  have hangle := (constants_angle_cutoff c hc hcupper).1
  have hn : ((n + 3 : ℕ) : ℝ) < 5 := by
    have hapos : 0 < Real.arccos c := by linarith [Real.pi_pos]
    nlinarith
  have hn' : n + 3 < 5 := by exact_mod_cast hn
  omega

theorem face_lengths_length_three_four (C : ContactBoundaryCycle Y c hY hc)
    (hirr : PackingIrreducible c Y) (hcupper : c < 3/10) (hsupport : C.StrictSupport) :
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
      exact face_lengths_polygon_three_four Q c hc.1 hcupper C.contact

#print axioms face_lengths_length_three_four

end Blueprint.Thomson.Tail.Implementation
