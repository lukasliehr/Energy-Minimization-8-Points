import AllS.Units.N_GI.N_covering.N_face_point_covered
import Lean_Code.BoundaryCoverage

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem covering_polygon_maximal_corner {n : ℕ} (Q : StrictSphericalPolygon n) (c : ℝ)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c < 3/10)
    (hcontact : ∀ i, inner ℝ (Q.vertex i) (Q.vertex (i + 1)) = c)
    (z : Point) (hz : ‖z‖ = 1)
    (hmax : ∀ j, inner ℝ (Q.vertex j) z ≤ inner ℝ (Q.vertex 0) z)
    (hleft : 0 ≤ inner ℝ (crossVec (Q.vertex 0) (Q.vertex 1)) z)
    (hright : 0 ≤ inner ℝ (crossVec (Q.vertex (0 - 1)) (Q.vertex 0)) z) :
    z ∈ Q.closedRegion := by
  have hn := face_lengths_polygon_three_four Q c hc.1 hcupper hcontact
  have hn' : n = 0 ∨ n = 1 := by omega
  rcases hn' with rfl | rfl
  · have h02 : inner ℝ (Q.vertex 0) (Q.vertex 2) = c :=
      (real_inner_comm (Q.vertex 2) (Q.vertex 0)).trans (hcontact 2)
    obtain ⟨l, μ, ν, hl, hμ, hν, hrep⟩ := triangle_maximal_corner_cone
      (Q.vertex 0) (Q.vertex 1) (Q.vertex 2) z c (Q.unit 0) (Q.unit 1) hc.2
      (hcontact 0) h02 (hcontact 1) (Q.turn_pos 0) hleft hright (hmax 1)
    exact Q.cone_mem_closedRegion 0 1 2 z hz l μ ν hl hμ hν hrep
  · have h02 : Q.vertex 0 ≠ Q.vertex 2 := by
      intro heq
      have ht := Q.turn_pos 0
      change 0 < inner ℝ (crossVec (Q.vertex 0) (Q.vertex 1)) (Q.vertex 2) at ht
      rw [← heq, crossVec_inner_left] at ht
      exact lt_irrefl 0 ht
    have h03 : inner ℝ (Q.vertex 0) (Q.vertex 3) = c :=
      (real_inner_comm (Q.vertex 3) (Q.vertex 0)).trans (hcontact 3)
    have h21 : inner ℝ (Q.vertex 2) (Q.vertex 1) = c :=
      (real_inner_comm (Q.vertex 1) (Q.vertex 2)).trans (hcontact 1)
    obtain ⟨l, μ, ν, hl, hμ, hν, hrep⟩ := rhombus_maximal_corner_cone
      (Q.vertex 0) (Q.vertex 1) (Q.vertex 2) (Q.vertex 3) z c (Q.unit 0)
      (unit_inner_lt_one _ _ (Q.unit 0) (Q.unit 2) h02) (hcontact 0) h21 h03 (hcontact 2)
      (Q.support 0 3 (by decide) (by decide)) hleft hright (hmax 2)
    exact Q.cone_mem_closedRegion 0 1 3 z hz l μ ν hl hμ hν hrep

variable {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y} {hc : c ∈ Set.Ioo (0 : ℝ) 1}

theorem covering_boundary_maximal_corner (C : ContactBoundaryCycle Y c hY hc)
    (hirr : PackingIrreducible c Y) (hcupper : c < 3/10) (hsupport : C.StrictSupport)
    (z : Point) (hz : ‖z‖ = 1)
    (hmax : ∀ j, inner ℝ (Y (C.vertex j)) z ≤ inner ℝ (Y (C.vertex 0)) z)
    (hleft : 0 ≤ inner ℝ (crossVec (Y (C.vertex 0)) (Y (C.vertex 1))) z)
    (hright : 0 ≤ inner ℝ (crossVec (Y (C.vertex (0 - 1))) (Y (C.vertex 0))) z) :
    z ∈ C.closedRegion := by
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
      exact covering_polygon_maximal_corner Q c hc hcupper C.contact z hz hmax hleft hright

theorem covering_sphere_covered (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c < 3/10)
    (hirr : PackingIrreducible c Y) (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport)
    (z : Point) (hz : ‖z‖ = 1) :
    ∃ C : ContactBoundaryCycle Y c hY hc, z ∈ C.closedRegion := by
  classical
  let V : Finset (Fin 8) := Finset.univ.filter
    (fun i => ∃ j, j ≠ i ∧ inner ℝ (Y i) (Y j) = c)
  have hV : V.Nonempty := by
    obtain ⟨⟨i, j⟩, hij⟩ := hne
    have hh := (mem_packingContacts c Y (i, j)).mp hij
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, j, hh.1.symm, hh.2⟩⟩
  obtain ⟨p, hpV, hmax⟩ := Finset.exists_max_image V (fun i => inner ℝ (Y i) z) hV
  have hpne : ∃ j, j ≠ p ∧ inner ℝ (Y p) (Y j) = c := (Finset.mem_filter.mp hpV).2
  obtain ⟨j, hleft, hright⟩ := contactRotateAt_sectors_cover Y c hY hc hirr p hpne z
  let d : ContactDart Y c := ⟨p, j⟩
  obtain ⟨C, hC⟩ := contact_boundary_cycle_exists Y c hY hc d
  have hzero : C.vertex 0 = p := congrArg Sigma.fst hC
  have hone : C.vertex 1 = j.val := by
    have h : C.vertex 1 = (C.point 0).2.val := by simpa only [zero_add] using C.vertex_next 0
    exact h.trans (congrArg (fun e : ContactDart Y c => e.2.val) hC)
  have hprev : C.vertex (0 - 1) = (contactRotateAt Y c hY hc p j).val := by
    rw [C.previous_vertex, hC]
    rfl
  refine ⟨C, covering_boundary_maximal_corner C hirr hcupper (hsupport C) z hz ?_ ?_ ?_⟩
  · intro k
    rw [hzero]
    exact hmax (C.vertex k) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, C.vertex_nonisolated k⟩)
  · simpa only [hzero, hone] using hleft
  · simpa only [hzero, hprev] using hright

#print axioms covering_sphere_covered

end Blueprint.Thomson.Tail.Implementation
