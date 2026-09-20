import Lean_Code.PackingConstants
import Lean_Code.PackingReduction

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

def packingIndexPairs : Finset (Fin 8 × Fin 8) :=
  Finset.univ.filter (fun ij => ij.1 ≠ ij.2)

@[simp] lemma mem_packingIndexPairs (ij : Fin 8 × Fin 8) :
    ij ∈ packingIndexPairs ↔ ij.1 ≠ ij.2 := by simp [packingIndexPairs]

lemma packingIndexPairs_nonempty : packingIndexPairs.Nonempty :=
  ⟨(0, 1), (mem_packingIndexPairs _).mpr (by decide)⟩

def packingMaxInner (Y : Fin 8 → ℝ³) : ℝ :=
  packingIndexPairs.sup' packingIndexPairs_nonempty (fun ij => inner ℝ (Y ij.1) (Y ij.2))

lemma inner_le_packingMaxInner (Y : Fin 8 → ℝ³) (i j : Fin 8) (hij : i ≠ j) :
    inner ℝ (Y i) (Y j) ≤ packingMaxInner Y :=
  Finset.le_sup' (fun ij => inner ℝ (Y ij.1) (Y ij.2)) ((mem_packingIndexPairs (i, j)).mpr hij)

lemma packingMaxInner_le_iff (Y : Fin 8 → ℝ³) (c : ℝ) :
    packingMaxInner Y ≤ c ↔ PackingInnerBound c Y := by
  constructor
  · intro h i j hij
    exact (inner_le_packingMaxInner Y i j hij).trans h
  · intro h
    exact Finset.sup'_le packingIndexPairs_nonempty _
      (fun ij hij => h ij.1 ij.2 ((mem_packingIndexPairs ij).mp hij))

lemma packingMaxInner_attained (Y : Fin 8 → ℝ³) :
    ∃ i j, i ≠ j ∧ inner ℝ (Y i) (Y j) = packingMaxInner Y := by
  obtain ⟨ij, hij, heq⟩ := Finset.exists_mem_eq_sup' packingIndexPairs_nonempty
    (fun ij => inner ℝ (Y ij.1) (Y ij.2))
  exact ⟨ij.1, ij.2, (mem_packingIndexPairs ij).mp hij, heq.symm⟩

set_option maxRecDepth 4000 in
lemma packingMaxInner_continuous : Continuous packingMaxInner := by
  have hc := Continuous.finset_sup' packingIndexPairs_nonempty
    (f := fun ij (Y : Fin 8 → ℝ³) => inner ℝ (Y ij.1) (Y ij.2))
    (by intro ij hij; fun_prop)
  convert hc using 1
  funext Y
  simp only [packingMaxInner, Finset.sup'_apply]

lemma sphere_sq_distance (x y : ℝ³) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ‖x - y‖ ^ 2 = 2 - 2 * inner ℝ x y := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right]
  rw [real_inner_comm y x]
  simp only [real_inner_self_eq_norm_sq, hx, hy, one_pow]
  ring

lemma packingMaxInner_P_le : packingMaxInner P ≤ aInf := by
  apply (packingMaxInner_le_iff P aInf).mpr
  intro i j hij
  have h := P_pair_sq_ge_tau i j hij
  rw [sphere_sq_distance _ _ (P_isConfiguration.1 i) (P_isConfiguration.1 j)] at h
  unfold tau at h
  linarith

lemma packingMaxInner_pos (Y : Fin 8 → ℝ³) (hY : ∀ i, ‖Y i‖ = 1) :
    0 < packingMaxInner Y := by
  obtain ⟨i, j, hij, hpos⟩ := eight_points_have_positive_inner Y hY
  exact hpos.trans_le (inner_le_packingMaxInner Y i j hij)

lemma packingInnerBound_configuration (Y : Fin 8 → ℝ³) (c : ℝ)
    (hY : ∀ i, ‖Y i‖ = 1) (hc : c < 1) (hb : PackingInnerBound c Y) :
    IsConfiguration Y := by
  refine ⟨hY, ?_⟩
  intro i j heq
  by_contra hij
  have h := hb i j hij
  rw [heq, real_inner_self_eq_norm_sq, hY j] at h
  norm_num at h
  linarith

/-- Compactness produces a best packing, with positive maximal inner
product at most the reference antiprism value. -/
theorem packing_maximum_exists :
    ∃ Y : Fin 8 → ℝ³, IsConfiguration Y ∧
      0 < packingMaxInner Y ∧ packingMaxInner Y ≤ aInf ∧
      ∀ Z : Fin 8 → ℝ³, (∀ i, ‖Z i‖ = 1) → packingMaxInner Y ≤ packingMaxInner Z := by
  let f : SphereTuple → ℝ := fun Z => packingMaxInner (fromSphereTuple Z)
  have hcont : Continuous f := packingMaxInner_continuous.comp (by unfold fromSphereTuple; fun_prop)
  have hnonempty : (Set.univ : Set SphereTuple).Nonempty :=
    ⟨toSphereTuple P P_isConfiguration.1, Set.mem_univ _⟩
  obtain ⟨Z, hZ, hmin⟩ := isCompact_univ.exists_isMinOn hnonempty hcont.continuousOn
  let Y := fromSphereTuple Z
  have hY : ∀ i, ‖Y i‖ = 1 := fromSphereTuple_sphere Z
  have hmin' : ∀ W : Fin 8 → ℝ³, (∀ i, ‖W i‖ = 1) → packingMaxInner Y ≤ packingMaxInner W := by
    intro W hW
    exact hmin (Set.mem_univ (toSphereTuple W hW))
  have hupper : packingMaxInner Y ≤ aInf := (hmin' P P_isConfiguration.1).trans packingMaxInner_P_le
  refine ⟨Y, packingInnerBound_configuration Y (packingMaxInner Y) hY
    (hupper.trans_lt aInf_mem_Ioo.2) ((packingMaxInner_le_iff Y _).mp le_rfl),
    packingMaxInner_pos Y hY, hupper, hmin'⟩

theorem maximizing_irreducible_reduction (Y : Fin 8 → ℝ³)
    (hY : ∀ i, ‖Y i‖ = 1)
    (hmin : ∀ Z : Fin 8 → ℝ³, (∀ i, ‖Z i‖ = 1) → packingMaxInner Y ≤ packingMaxInner Z)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Z : Fin 8 → ℝ³, (∀ i, ‖Z i‖ = 1) ∧ dist Z Y < ε ∧
      packingMaxInner Z = packingMaxInner Y ∧ PackingIrreducible (packingMaxInner Y) Z ∧
      (packingContacts (packingMaxInner Y) Z).Nonempty := by
  obtain ⟨Z, hZ, hb, hd, hirr⟩ := arbitrarily_close_irreducible_reduction Y
    (packingMaxInner Y) hY (packingMaxInner_pos Y hY)
    ((packingMaxInner_le_iff Y _).mp le_rfl) ε hε
  have heq := le_antisymm ((packingMaxInner_le_iff Z _).mpr hb) (hmin Z hZ)
  obtain ⟨i, j, hij, hcontact⟩ := packingMaxInner_attained Z
  rw [heq] at hcontact
  exact ⟨Z, hZ, hd, heq, hirr, (i, j), (mem_packingContacts _ _ _).mpr ⟨hij, hcontact⟩⟩

end SquareAntiprismVerification
