import Lean_Code.CompactArcPatches

noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Local compact convex models, before extracting a finite cover. This is
the precise condition to be verified at face interior points, edge points,
and vertices separately. -/
def HasCompactArcNeighborhoods (D : Set ℝ³) : Prop :=
  ∀ x : D, ∃ K : Set ℝ³, IsCompact K ∧ K ⊆ D ∧
    (∀ a ∈ K, ∀ b ∈ K, a ≠ -b) ∧ ShortArcClosed K ∧
    {y : D | y.val ∈ K} ∈ nhds x

/-- Compactness turns the local models into the finite compact-patch cover
needed by the checked shortest-chain construction. -/
theorem compact_arc_patch_cover_exists (D : Set ℝ³) (hD : IsCompact D)
    (hlocal : HasCompactArcNeighborhoods D) : Nonempty (CompactArcPatchCover D) := by
  classical
  letI : CompactSpace D := isCompact_iff_compactSpace.mp hD
  choose K hKc hKD hKa hKs hKn using hlocal
  have hopen : ∀ x : D, ∃ U : Set D, U ⊆ {y : D | y.val ∈ K x} ∧ IsOpen U ∧ x ∈ U := by
    intro x
    exact mem_nhds_iff.mp (hKn x)
  choose U hUK hUo hxU using hopen
  have hcover : (Set.univ : Set D) ⊆ ⋃ x : D, U x := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨x, hxU x⟩
  obtain ⟨I, hI⟩ := isCompact_univ.elim_finite_subcover U hUo hcover
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let Q : Fin (Fintype.card I) → Set ℝ³ := fun i => K (e.symm i).val
  refine ⟨{ count := Fintype.card I
            patch := Q
            compact := fun i => hKc (e.symm i).val
            subset := fun i => hKD (e.symm i).val
            nonantipodal := fun i => hKa (e.symm i).val
            arcClosed := fun i => hKs (e.symm i).val
            localCover := ?_ }⟩
  intro x
  obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (hI (Set.mem_univ x))
  obtain ⟨hyI, hxy⟩ := Set.mem_iUnion.mp hy
  let i : Fin (Fintype.card I) := e ⟨y, hyI⟩
  refine ⟨i, ?_⟩
  have hQ : Q i = K y := by simp [Q, i]
  change {z : D | z.val ∈ Q i} ∈ nhds x
  rw [hQ]
  exact Filter.mem_of_superset ((hUo y).mem_nhds hxy) (hUK y)

end SquareAntiprismVerification
