import Lean_Code.SphericalArcStability

noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma shortSphereArc_reverse (a b : ℝ³) (t : ℝ) :
    shortSphereArc a b t = shortSphereArc b a (1 - t) := by
  unfold shortSphereArc
  congr 1
  module

/-- The elementary clopen argument giving finite-chain connectivity from a
locally available symmetric relation on a connected space. -/
theorem reflTransGen_of_local_relation {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] (r : X → X → Prop)
    (hsymm : ∀ x y, r x y → r y x)
    (hlocal : ∀ x, ∀ᶠ y in nhds x, r x y) (a b : X) :
    Relation.ReflTransGen r a b := by
  let R : Set X := {x | Relation.ReflTransGen r a x}
  have hRo : IsOpen R := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    filter_upwards [hlocal x] with y hxy
    exact hx.tail hxy
  have hRco : IsOpen Rᶜ := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    filter_upwards [hlocal x] with y hxy
    intro hy
    exact hx (hy.tail (hsymm x y hxy))
  by_contra hb
  have h := isPreconnected_univ R Rᶜ hRo hRco
    (by intro x hx; exact Classical.em (x ∈ R))
    ⟨a, Set.mem_univ _, Relation.ReflTransGen.refl⟩
    ⟨b, Set.mem_univ _, hb⟩
  simpa using h

/-- A link is an actual nonantipodal shorter arc inside the specified region. -/
def RegionArcLink (D : Set ℝ³) (a b : ℝ³) : Prop :=
  a ≠ -b ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, shortSphereArc a b t ∈ D

lemma RegionArcLink.symm {D : Set ℝ³} {a b : ℝ³} (h : RegionArcLink D a b) :
    RegionArcLink D b a := by
  refine ⟨?_, ?_⟩
  · intro heq
    exact h.1 (by rw [heq, neg_neg])
  · intro t ht
    rw [shortSphereArc_reverse]
    exact h.2 (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩

/-- Local shorter-arc access is taken in the subspace topology of the actual
closed region. This is weaker than, and supplied by, its local convex models. -/
def LocallyArcConnectedRegion (D : Set ℝ³) : Prop :=
  ∀ x : D, ∀ᶠ y : D in nhds x, RegionArcLink D x.val y.val

theorem region_arc_chain_connected (D : Set ℝ³) [PreconnectedSpace D]
    (hlocal : LocallyArcConnectedRegion D) (a b : D) :
    Relation.ReflTransGen (fun x y : D => RegionArcLink D x.val y.val) a b := by
  apply reflTransGen_of_local_relation _ _ hlocal a b
  intro x y h
  exact h.symm

/-- A finite sequence of genuine shorter-arc links. No shortest-path existence
is encoded in this type. Its length is the actual sum of angular link lengths. -/
inductive RegionArcChain (D : Set ℝ³) : ℝ³ → ℝ³ → Type
  | point (a : ℝ³) (ha : a ∈ D) : RegionArcChain D a a
  | tail {a b : ℝ³} (p : RegionArcChain D a b) (z : ℝ³) (hz : z ∈ D)
      (hlink : RegionArcLink D b z) : RegionArcChain D a z

def RegionArcChain.length {D : Set ℝ³} {a b : ℝ³} : RegionArcChain D a b → ℝ
  | .point _ _ => 0
  | .tail (b := y) p z _ _ => p.length + sphereAngle y z

lemma RegionArcChain.length_nonneg {D : Set ℝ³} {a b : ℝ³} (p : RegionArcChain D a b) :
    0 ≤ p.length := by
  induction p with
  | point => exact le_rfl
  | @tail b p z hz hlink ih => exact add_nonneg ih (sphereAngle_range b z).1

theorem region_arc_chain_exists (D : Set ℝ³) [PreconnectedSpace D]
    (hlocal : LocallyArcConnectedRegion D) (a b : D) :
    Nonempty (RegionArcChain D a.val b.val) := by
  have h := region_arc_chain_connected D hlocal a b
  induction h with
  | refl => exact ⟨.point a.val a.property⟩
  | @tail b z hpath hstep ih =>
    obtain ⟨p⟩ := ih
    exact ⟨.tail p z.val z.property hstep⟩

end SquareAntiprismVerification
