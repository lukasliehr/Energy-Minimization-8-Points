import Lean_Code.ShortestChainCorners

noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma sphereAngle_self_unit (a : ℝ³) (ha : ‖a‖ = 1) : sphereAngle a a = 0 := by
  simp [sphereAngle, ha]

namespace PatchArcChain

variable {ι : Type*} {patch : ι → Set ℝ³} {a b : ℝ³}

def NoZeroLinks : {b : ℝ³} → PatchArcChain patch a b → Prop
  | _, .point _ => True
  | _, .tail (b := y) p _ z _ _ => p.NoZeroLinks ∧ y ≠ z

lemma start_unit (p : PatchArcChain patch a b) : ‖a‖ = 1 := by
  induction p with
  | point ha => exact ha
  | tail p i z hy hz ih => exact ih

/-- Repeated consecutive endpoints can be removed without changing angular
length. This eliminates degenerate links before propagating tangent data. -/
theorem remove_zero_links (hunit : ∀ i x, x ∈ patch i → ‖x‖ = 1)
    (p : PatchArcChain patch a b) :
    ∃ q : PatchArcChain patch a b, q.NoZeroLinks ∧ q.length = p.length := by
  classical
  induction p with
  | point ha => exact ⟨.point ha, trivial, rfl⟩
  | @tail b p i z hb hz ih =>
    obtain ⟨q, hq, hlen⟩ := ih
    by_cases hbz : b = z
    · subst z
      refine ⟨q, hq, ?_⟩
      change q.length = p.length + sphereAngle b b
      rw [sphereAngle_self_unit b (hunit i b hb), add_zero, hlen]
    · refine ⟨.tail q i z hb hz, ⟨hq, hbz⟩, ?_⟩
      change q.length + sphereAngle b z = p.length + sphereAngle b z
      rw [hlen]

lemma shortest_of_tail (p : PatchArcChain patch a b) (i : ι) (z : ℝ³)
    (hb : b ∈ patch i) (hz : z ∈ patch i) (hmin : (p.tail i z hb hz).IsShortest) :
    p.IsShortest := by
  intro q
  have h := hmin (q.tail i z hb hz)
  change p.length + sphereAngle b z ≤ q.length + sphereAngle b z at h
  linarith

end PatchArcChain

theorem reduced_shortest_patch_chain_exists {D : Set ℝ³} (P : CompactArcPatchCover D)
    [PreconnectedSpace D] (hunit : ∀ x ∈ D, ‖x‖ = 1) (a b : D) :
    ∃ p : PatchArcChain P.patch a.val b.val, p.NoZeroLinks ∧ p.IsShortest := by
  obtain ⟨p, hp⟩ := P.shortest_chain_exists hunit a b
  obtain ⟨q, hq, hlen⟩ := p.remove_zero_links (P.patch_unit hunit)
  exact ⟨q, hq, p.shortest_of_same_length q hp hlen⟩

end SquareAntiprismVerification
