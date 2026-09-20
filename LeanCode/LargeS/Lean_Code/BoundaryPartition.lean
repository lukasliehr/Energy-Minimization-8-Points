import Lean_Code.BoundaryPolygons
import Lean_Code.PermutationPartition

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The orbits of the actual directed-edge boundary permutation. Geometric
face support and global coverage are separate obligations. -/
abbrev ContactBoundaryOrbit (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) :=
  PermutationOrbit (contactFaceNext Y c hY hc)

abbrev boundaryOrbitCycle (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (f : ContactBoundaryOrbit Y c hY hc) : ContactBoundaryCycle Y c hY hc :=
  orbitPermutationCycle (contactFaceNext Y c hY hc) f

def dartCorner (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (d : ContactDart Y c) : ℝ :=
  contactAngle c (Y d.2.val) (Y (contactRotateAt Y c hY hc d.1 d.2).val)

theorem boundaryCycle_dartCorner {Y : Fin 8 → ℝ³} {c : ℝ}
    {hY : IsConfiguration Y} {hc : c ∈ Set.Ioo (0 : ℝ) 1}
    (C : ContactBoundaryCycle Y c hY hc) (i : Fin (C.size + 1)) :
    dartCorner Y c hY hc (C.point i) =
      contactAngle c (Y (C.vertex (i + 1))) (Y (C.vertex (i - 1))) := by
  have hstep : contactFaceNext Y c hY hc (C.point (i - 1)) = C.point i := by
    simpa only [sub_add_cancel] using C.step (i - 1)
  have hrot : contactRotate Y c hY hc (C.point i) = contactReverse Y c (C.point (i - 1)) := by
    rw [← hstep]
    exact (contactRotate Y c hY hc).apply_symm_apply _
  have htip := congrArg (fun d : ContactDart Y c => d.2.val) hrot
  change (contactRotateAt Y c hY hc (C.point i).1 (C.point i).2).val = (C.point (i - 1)).1 at htip
  rw [dartCorner, htip, ← C.vertex_next i]
  rfl

theorem boundary_cycles_count_darts (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) :
    ∑ f : ContactBoundaryOrbit Y c hY hc, ((boundaryOrbitCycle Y c hY hc f).size + 1) =
      Fintype.card (ContactDart Y c) := by
  classical
  exact sum_permutation_cycle_lengths (contactFaceNext Y c hY hc)

theorem boundary_corner_sum_reindex (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1) (w : Fin 8 → ℝ) :
    (∑ f : ContactBoundaryOrbit Y c hY hc, ∑ i,
      w ((boundaryOrbitCycle Y c hY hc f).vertex i) *
        contactAngle c (Y ((boundaryOrbitCycle Y c hY hc f).vertex (i + 1)))
          (Y ((boundaryOrbitCycle Y c hY hc f).vertex (i - 1)))) =
      ∑ d : ContactDart Y c, w d.1 * dartCorner Y c hY hc d := by
  classical
  have h := sum_over_permutation_cycles (contactFaceNext Y c hY hc)
    (fun d => w d.1 * dartCorner Y c hY hc d)
  convert h using 1
  apply Finset.sum_congr rfl
  intro f _
  apply Finset.sum_congr rfl
  intro i _
  rw [boundaryCycle_dartCorner]
  rfl

theorem dart_corner_sum_at_vertex (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hirr : PackingIrreducible c Y) (v : Fin 8)
    (hne : ∃ j, j ≠ v ∧ inner ℝ (Y v) (Y j) = c) :
    (∑ d : ContactDart Y c, (if d.1 = v then (1 : ℝ) else 0) * dartCorner Y c hY hc d) =
      2 * Real.pi := by
  classical
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single v]
  · simpa only [↓reduceIte, one_mul, dartCorner] using contactRotateAt_angle_sum Y c hY hc hirr v hne
  · intro i _ hiv
    simp [hiv]
  · simp

theorem boundary_corner_sum_at_vertex (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0 : ℝ) 1)
    (hirr : PackingIrreducible c Y) (v : Fin 8)
    (hne : ∃ j, j ≠ v ∧ inner ℝ (Y v) (Y j) = c) :
    (∑ f : ContactBoundaryOrbit Y c hY hc, ∑ i,
      (if (boundaryOrbitCycle Y c hY hc f).vertex i = v then (1 : ℝ) else 0) *
        contactAngle c (Y ((boundaryOrbitCycle Y c hY hc f).vertex (i + 1)))
          (Y ((boundaryOrbitCycle Y c hY hc f).vertex (i - 1)))) = 2 * Real.pi := by
  classical
  rw [boundary_corner_sum_reindex Y c hY hc (fun i => if i = v then 1 else 0)]
  exact dart_corner_sum_at_vertex Y c hY hc hirr v hne

end SquareAntiprismVerification
