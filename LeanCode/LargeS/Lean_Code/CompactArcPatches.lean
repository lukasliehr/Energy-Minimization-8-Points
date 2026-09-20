import Lean_Code.PatchChainMinimization

noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Finite compact local convex patches, with interiors covering the region
in its subspace topology. Constructing these patches for the actual face is
a separate obligation; this structure contains no global convexity claim. -/
structure CompactArcPatchCover (D : Set ℝ³) where
  count : ℕ
  patch : Fin count → Set ℝ³
  compact : ∀ i, IsCompact (patch i)
  subset : ∀ i, patch i ⊆ D
  nonantipodal : ∀ i, ∀ a ∈ patch i, ∀ b ∈ patch i, a ≠ -b
  arcClosed : ∀ i, ShortArcClosed (patch i)
  localCover : ∀ x : D, ∃ i, {y : D | y.val ∈ patch i} ∈ nhds x

namespace CompactArcPatchCover

variable {D : Set ℝ³}

lemma patch_unit (P : CompactArcPatchCover D) (hunit : ∀ x ∈ D, ‖x‖ = 1)
    (i : Fin P.count) (x : ℝ³) (hx : x ∈ P.patch i) : ‖x‖ = 1 :=
  hunit x (P.subset i hx)

lemma covered (P : CompactArcPatchCover D) (x : D) : ∃ i, x.val ∈ P.patch i := by
  obtain ⟨i, hi⟩ := P.localCover x
  have hx : x ∈ {y : D | y.val ∈ P.patch i} := mem_of_mem_nhds hi
  exact ⟨i, hx⟩

lemma local_relation (P : CompactArcPatchCover D) (x : D) :
    ∀ᶠ y : D in nhds x, ∃ i, x.val ∈ P.patch i ∧ y.val ∈ P.patch i := by
  obtain ⟨i, hi⟩ := P.localCover x
  have hx : x ∈ {y : D | y.val ∈ P.patch i} := mem_of_mem_nhds hi
  filter_upwards [hi] with y hy
  exact ⟨i, hx, hy⟩

theorem chain_exists (P : CompactArcPatchCover D) [PreconnectedSpace D]
    (hunit : ∀ x ∈ D, ‖x‖ = 1) (a b : D) :
    Nonempty (PatchArcChain P.patch a.val b.val) := by
  have h := reflTransGen_of_local_relation
    (fun x y : D => ∃ i, x.val ∈ P.patch i ∧ y.val ∈ P.patch i)
    (by intro x y h; obtain ⟨i, hx, hy⟩ := h; exact ⟨i, hy, hx⟩)
    P.local_relation a b
  induction h with
  | refl => exact ⟨.point (hunit a.val a.property)⟩
  | @tail y z hpath hstep ih =>
    obtain ⟨p⟩ := ih
    obtain ⟨i, hy, hz⟩ := hstep
    exact ⟨.tail p i z.val hy hz⟩

theorem shortest_chain_exists (P : CompactArcPatchCover D) [PreconnectedSpace D]
    (hunit : ∀ x ∈ D, ‖x‖ = 1) (a b : D) :
    ∃ p : PatchArcChain P.patch a.val b.val,
      ∀ q : PatchArcChain P.patch a.val b.val, p.length ≤ q.length := by
  obtain ⟨p₀⟩ := P.chain_exists hunit a b
  exact shortest_patch_chain_exists P.patch P.compact (P.patch_unit hunit)
    a.val b.val (hunit a.val a.property) p₀

lemma link_in_region (P : CompactArcPatchCover D) (i : Fin P.count)
    (a b : ℝ³) (ha : a ∈ P.patch i) (hb : b ∈ P.patch i) : RegionArcLink D a b := by
  refine ⟨P.nonantipodal i a ha b hb, ?_⟩
  intro t ht
  exact P.subset i (P.arcClosed i a ha b hb (P.nonantipodal i a ha b hb) t ht)

/-- The minimizing objects really are chains of arcs in `D`, not merely
finite sequences whose endpoints happen to lie in the region. -/
def toRegionChain (P : CompactArcPatchCover D) {a b : ℝ³} (ha : a ∈ D)
    (p : PatchArcChain P.patch a b) : RegionArcChain D a b := by
  induction p with
  | point => exact .point a ha
  | @tail y p i z hy hz ih =>
    exact .tail ih z (P.subset i hz) (P.link_in_region i y z hy hz)

lemma toRegionChain_length (P : CompactArcPatchCover D) {a b : ℝ³} (ha : a ∈ D)
    (p : PatchArcChain P.patch a b) : (P.toRegionChain ha p).length = p.length := by
  induction p with
  | point => rfl
  | tail p i z hy hz ih =>
    change (P.toRegionChain ha p).length + _ = p.length + _
    rw [ih]

end CompactArcPatchCover
end SquareAntiprismVerification
