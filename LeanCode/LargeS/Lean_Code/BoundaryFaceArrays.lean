import Lean_Code.BoundaryReindex
import Lean_Code.ContactEulerBound
import Lean_Code.FaceIncidence

noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

abbrev BoundaryOfLength (Y : Fin 8 → ℝ³) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (n : ℕ) :=
  {f : ContactBoundaryOrbit Y c hY hc // (boundaryOrbitCycle Y c hY hc f).size + 1 = n}

def boundaryArray (Y : Fin 8 → ℝ³) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (n : ℕ) :
    Fin (Fintype.card (BoundaryOfLength Y c hY hc n)) → Fin n → Fin 8 :=
  fun f => (boundaryOrbitCycle Y c hY hc ((Fintype.equivFin (BoundaryOfLength Y c hY hc n)).symm f).val).reindex
    ((Fintype.equivFin (BoundaryOfLength Y c hY hc n)).symm f).property

def boundaryCornerSum {Y : Fin 8 → ℝ³} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0 : ℝ) 1} (C : ContactBoundaryCycle Y c hY hc) (v : Fin 8) : ℝ :=
  ∑ i, (if C.vertex i = v then (1 : ℝ) else 0) *
    contactAngle c (Y (C.vertex (i + 1))) (Y (C.vertex (i - 1)))

theorem boundaryArray_corner_sum (Y : Fin 8 → ℝ³) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (n : ℕ) [NeZero n] (v : Fin 8) :
    (∑ f, ∑ j, (if boundaryArray Y c hY hc n f j = v then (1 : ℝ) else 0) *
      contactAngle c (Y (boundaryArray Y c hY hc n f (j + 1)))
        (Y (boundaryArray Y c hY hc n f (j - 1)))) =
      ∑ f : BoundaryOfLength Y c hY hc n, boundaryCornerSum (boundaryOrbitCycle Y c hY hc f.val) v := by
  classical
  let e := (Fintype.equivFin (BoundaryOfLength Y c hY hc n)).symm
  calc
    _ = ∑ f, boundaryCornerSum (boundaryOrbitCycle Y c hY hc (e f).val) v := by
      apply Finset.sum_congr rfl
      intro f _
      exact (boundaryOrbitCycle Y c hY hc (e f).val).reindex_corner_sum (e f).property v
    _ = _ := Equiv.sum_comp e (fun f => boundaryCornerSum (boundaryOrbitCycle Y c hY hc f.val) v)

theorem boundary_sum_by_length (Y : Fin 8 → ℝ³) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c ≤ aInf) (hirr : PackingIrreducible c Y)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport)
    {M : Type*} [AddCommMonoid M] (w : ContactBoundaryOrbit Y c hY hc → M) :
    (∑ f : BoundaryOfLength Y c hY hc 3, w f.val) +
      (∑ f : BoundaryOfLength Y c hY hc 4, w f.val) = ∑ f, w f := by
  classical
  let p := fun f : ContactBoundaryOrbit Y c hY hc => (boundaryOrbitCycle Y c hY hc f).size + 1 = 3
  have hiff (f : ContactBoundaryOrbit Y c hY hc) :
      ¬ p f ↔ (boundaryOrbitCycle Y c hY hc f).size + 1 = 4 := by
    have h := (boundaryOrbitCycle Y c hY hc f).three_or_four_of_support hirr hcupper
      (hsupport (boundaryOrbitCycle Y c hY hc f))
    dsimp [p]
    omega
  let e := Equiv.subtypeEquivRight hiff
  have heq : (∑ f : {f // ¬ p f}, w f.val) = ∑ f : BoundaryOfLength Y c hY hc 4, w f.val :=
    Equiv.sum_comp e (fun f => w f.val)
  have h := Fintype.sum_subtype_add_sum_subtype p w
  rw [heq] at h
  exact h

theorem boundary_length_counts (Y : Fin 8 → ℝ³) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c ≤ aInf) (hirr : PackingIrreducible c Y)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport) :
    Fintype.card (BoundaryOfLength Y c hY hc 3) + Fintype.card (BoundaryOfLength Y c hY hc 4) =
      Fintype.card (ContactBoundaryOrbit Y c hY hc) ∧
    3 * Fintype.card (BoundaryOfLength Y c hY hc 3) + 4 * Fintype.card (BoundaryOfLength Y c hY hc 4) =
      Fintype.card (ContactDart Y c) := by
  classical
  constructor
  · simpa using boundary_sum_by_length Y c hY hc hcupper hirr hsupport (fun _ => (1 : ℕ))
  · have h := boundary_sum_by_length Y c hY hc hcupper hirr hsupport
      (fun f => (boundaryOrbitCycle Y c hY hc f).size + 1)
    have h3 : ∀ f : BoundaryOfLength Y c hY hc 3, (boundaryOrbitCycle Y c hY hc f.val).size + 1 = 3 :=
      fun f => f.property
    have h4 : ∀ f : BoundaryOfLength Y c hY hc 4, (boundaryOrbitCycle Y c hY hc f.val).size + 1 = 4 :=
      fun f => f.property
    simp only [h3, h4, Finset.sum_const, Finset.card_univ, smul_eq_mul, boundary_cycles_count_darts] at h
    simpa [mul_comm] using h

theorem boundary_array_euler_bound (Y : Fin 8 → ℝ³) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c ≤ aInf) (hirr : PackingIrreducible c Y)
    (hbound : PackingInnerBound c Y) (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport) :
    12 ≤ Fintype.card (BoundaryOfLength Y c hY hc 3) + 2 * Fintype.card (BoundaryOfLength Y c hY hc 4) := by
  have hEuler := contact_euler_upper_bound_of_support Y c hY hc hcupper hirr hbound hne hsupport
  have hcounts := boundary_length_counts Y c hY hc hcupper hirr hsupport
  omega

lemma faceIncidentSum_eq_indicator {g m : ℕ} (V : Fin g → Fin m → Fin 8)
    (f : Fin g → Fin m → ℝ) (v : Fin 8) :
    faceIncidentSum V f v = ∑ i, ∑ j, (if V i j = v then (1 : ℝ) else 0) * f i j := by
  classical
  simp [faceIncidentSum, faceCornersAt, Finset.sum_filter, Fintype.sum_prod_type, ite_mul]

theorem boundary_array_angle_sum (Y : Fin 8 → ℝ³) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c ≤ aInf) (hirr : PackingIrreducible c Y)
    (hbound : PackingInnerBound c Y) (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport) (v : Fin 8) :
    (faceCornerCount (boundaryArray Y c hY hc 3) v : ℝ) * Real.arccos (c / (1 + c)) +
      faceIncidentSum (boundaryArray Y c hY hc 4)
        (fun f j => quadrilateralAngle c (fun k => Y (boundaryArray Y c hY hc 4 f k)) j) v =
      2 * Real.pi := by
  classical
  have htri (f) (j : Fin 3) :
      contactAngle c (Y (boundaryArray Y c hY hc 3 f (j + 1)))
        (Y (boundaryArray Y c hY hc 3 f (j - 1))) = Real.arccos (c / (1 + c)) := by
    unfold boundaryArray
    apply ContactBoundaryCycle.reindex_triangle_angle
  have hquad (f) (j : Fin 4) :
      contactAngle c (Y (boundaryArray Y c hY hc 4 f (j + 1)))
        (Y (boundaryArray Y c hY hc 4 f (j - 1))) =
      quadrilateralAngle c (fun k => Y (boundaryArray Y c hY hc 4 f k)) j := by
    unfold boundaryArray
    apply ContactBoundaryCycle.reindex_quadrilateral_angle
  have h3 := boundaryArray_corner_sum Y c hY hc 3 v
  have h4 := boundaryArray_corner_sum Y c hY hc 4 v
  simp_rw [htri] at h3
  simp_rw [hquad] at h4
  rw [← faceIncidentSum_eq_indicator, faceIncidentSum_const] at h3
  rw [← faceIncidentSum_eq_indicator] at h4
  rw [h3, h4, boundary_sum_by_length Y c hY hc hcupper hirr hsupport
    (fun f => boundaryCornerSum (boundaryOrbitCycle Y c hY hc f) v)]
  exact boundary_corner_sum_at_vertex Y c hY hc hirr v
    (no_isolated_vertices_of_boundary_support Y c hY hc hcupper hirr hbound hne hsupport v)

end SquareAntiprismVerification
