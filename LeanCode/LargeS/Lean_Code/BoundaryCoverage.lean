import Lean_Code.VoronoiRegions
import Lean_Code.ContactSectorCover

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace ContactBoundaryCycle

variable {Y : Fin 8 → ℝ³} {c : ℝ} {hY : IsConfiguration Y} {hc : c ∈ Set.Ioo (0 : ℝ) 1}

lemma previous_vertex (C : ContactBoundaryCycle Y c hY hc) (i : Fin (C.size + 1)) :
    C.vertex (i - 1) = (contactRotate Y c hY hc (C.point i)).2.val := by
  have hstep : contactFaceNext Y c hY hc (C.point (i - 1)) = C.point i := by
    simpa only [sub_add_cancel] using C.step (i - 1)
  have hrot : contactRotate Y c hY hc (C.point i) = contactReverse Y c (C.point (i - 1)) := by
    rw [← hstep]
    exact (contactRotate Y c hY hc).apply_symm_apply _
  exact (congrArg (fun d : ContactDart Y c => d.2.val) hrot).symm

lemma vertex_nonisolated (C : ContactBoundaryCycle Y c hY hc) (i : Fin (C.size + 1)) :
    ∃ j, j ≠ C.vertex i ∧ inner ℝ (Y (C.vertex i)) (Y j) = c :=
  ⟨C.vertex (i + 1), (C.adjacent_ne i).symm, C.contact i⟩

theorem maximal_corner_mem_region (C : ContactBoundaryCycle Y c hY hc)
    (hirr : PackingIrreducible c Y) (hcupper : c ≤ aInf) (hsupport : C.StrictSupport)
    (z : ℝ³) (hz : ‖z‖ = 1)
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
      exact Q.maximal_corner_mem_region c hc hcupper C.contact z hz hmax hleft hright

end ContactBoundaryCycle

/-- The closed regions of supported actual boundary cycles cover the
sphere. The proof chooses a nearest nonisolated vertex and a consecutive
contact sector; it does not assume global coverage or an Euler formula. -/
theorem supported_boundary_regions_cover (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c ≤ aInf)
    (hirr : PackingIrreducible c Y) (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport)
    (z : ℝ³) (hz : ‖z‖ = 1) :
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
  refine ⟨C, C.maximal_corner_mem_region hirr hcupper (hsupport C) z hz ?_ ?_ ?_⟩
  · intro k
    rw [hzero]
    exact hmax (C.vertex k) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, C.vertex_nonisolated k⟩)
  · simpa only [hzero, hone] using hleft
  · simpa only [hzero, hprev] using hright

/-- Covering excludes every isolated packing vertex, once strict support
of the actual boundary cycles is supplied. -/
theorem no_isolated_vertices_of_boundary_support (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c ≤ aInf)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport) :
    ∀ k, ∃ j, j ≠ k ∧ inner ℝ (Y k) (Y j) = c := by
  intro k
  obtain ⟨C, hk⟩ := supported_boundary_regions_cover Y c hY hc hcupper hirr hne hsupport
    (Y k) (hY.1 k)
  obtain ⟨i, hi⟩ := C.region_configuration_vertex hirr hcupper hbound (hsupport C) k hk
  simpa only [hi] using C.vertex_nonisolated i

end SquareAntiprismVerification
