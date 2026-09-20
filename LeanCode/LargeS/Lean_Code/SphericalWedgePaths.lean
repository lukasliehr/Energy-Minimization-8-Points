import Lean_Code.SphericalCapPaths

set_option maxHeartbeats 1500000
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

def sphericalWedgeTrace (n₁ n₂ : ℝ³) : Set ℝ³ :=
  {x | (inner ℝ n₁ x = 0 ∧ 0 ≤ inner ℝ n₂ x) ∨
    (inner ℝ n₂ x = 0 ∧ 0 ≤ inner ℝ n₁ x)}

lemma wedge_interior_off_trace (n₁ n₂ x : ℝ³)
    (hx₁ : 0 < inner ℝ n₁ x) (hx₂ : 0 < inner ℝ n₂ x) :
    x ∉ sphericalWedgeTrace n₁ n₂ := by
  rintro (h | h)
  · linarith [h.1]
  · linarith [h.1]

lemma wedge_exterior_off_trace (n₁ n₂ x : ℝ³)
    (hx : inner ℝ n₁ x < 0 ∨ inner ℝ n₂ x < 0) :
    x ∉ sphericalWedgeTrace n₁ n₂ := by
  rintro (h | h) <;> rcases hx with hx | hx <;> linarith [h.1, h.2]

lemma wedge_complement_cases (n₁ n₂ x : ℝ³) (hx : x ∉ sphericalWedgeTrace n₁ n₂) :
    (0 < inner ℝ n₁ x ∧ 0 < inner ℝ n₂ x) ∨
      (inner ℝ n₁ x < 0 ∨ inner ℝ n₂ x < 0) := by
  by_cases h₁ : inner ℝ n₁ x < 0
  · exact Or.inr (Or.inl h₁)
  by_cases h₂ : inner ℝ n₂ x < 0
  · exact Or.inr (Or.inr h₂)
  have hn₁ := le_of_not_gt h₁
  have hn₂ := le_of_not_gt h₂
  have hne₁ : inner ℝ n₁ x ≠ 0 := fun h => hx (Or.inl ⟨h, hn₂⟩)
  have hne₂ : inner ℝ n₂ x ≠ 0 := fun h => hx (Or.inr ⟨h, hn₁⟩)
  exact Or.inl ⟨lt_of_le_of_ne hn₁ hne₁.symm, lt_of_le_of_ne hn₂ hne₂.symm⟩

lemma joinedIn_cap_wedge_interior (p n₁ n₂ : ℝ³) (δ : ℝ) (hδ : 0 < δ)
    (D : Set ℝ³)
    (hin : ∀ x ∈ sphericalOpenCap p δ, 0 < inner ℝ n₁ x → 0 < inner ℝ n₂ x → x ∈ D)
    (a b : ℝ³) (ha : a ∈ sphericalOpenCap p δ) (hb : b ∈ sphericalOpenCap p δ)
    (ha₁ : 0 < inner ℝ n₁ a) (ha₂ : 0 < inner ℝ n₂ a)
    (hb₁ : 0 < inner ℝ n₁ b) (hb₂ : 0 < inner ℝ n₂ b) : JoinedIn D a b := by
  let normal : Bool → ℝ³ := fun i => if i then n₁ else n₂
  apply joinedIn_cap_strict_halfspaces normal p δ hδ D
    (fun x hx hN => hin x hx (hN true) (hN false)) a b ha hb
  · intro i; cases i <;> simp [normal, ha₁, ha₂]
  · intro i; cases i <;> simp [normal, hb₁, hb₂]

/-- The outside of a convex wedge in a cap is the union of two negative
halfcaps. A point in their intersection connects any pair by at most two
short arcs. -/
lemma joinedIn_cap_wedge_exterior (p n₁ n₂ : ℝ³) (δ : ℝ) (hδ : 0 < δ)
    (D : Set ℝ³)
    (hin : ∀ x ∈ sphericalOpenCap p δ, (inner ℝ n₁ x < 0 ∨ inner ℝ n₂ x < 0) → x ∈ D)
    (z : ℝ³) (hz : z ∈ sphericalOpenCap p δ)
    (hz₁ : inner ℝ n₁ z < 0) (hz₂ : inner ℝ n₂ z < 0)
    (a b : ℝ³) (ha : a ∈ sphericalOpenCap p δ) (hb : b ∈ sphericalOpenCap p δ)
    (haN : inner ℝ n₁ a < 0 ∨ inner ℝ n₂ a < 0)
    (hbN : inner ℝ n₁ b < 0 ∨ inner ℝ n₂ b < 0) : JoinedIn D a b := by
  have hpath (x : ℝ³) (hx : x ∈ sphericalOpenCap p δ)
      (hxN : inner ℝ n₁ x < 0 ∨ inner ℝ n₂ x < 0) : JoinedIn D x z := by
    rcases hxN with h₁ | h₂
    · apply joinedIn_cap_strict_halfspaces (fun _ : Unit => -n₁) p δ hδ D
        (fun y hy hN => hin y hy (Or.inl (by have hh := hN (); simpa using hh))) x z hx hz
      · intro i; simpa using h₁
      · intro i; simpa using hz₁
    · apply joinedIn_cap_strict_halfspaces (fun _ : Unit => -n₂) p δ hδ D
        (fun y hy hN => hin y hy (Or.inr (by have hh := hN (); simpa using hh))) x z hx hz
      · intro i; simpa using h₂
      · intro i; simpa using hz₂
  exact (hpath a ha haN).trans (hpath b hb hbN).symm

/-- Local path-connectedness propagates one known separation across an
edge to all points in the two vertex sectors. -/
theorem cap_wedge_separation (T : Set ℝ³) (p n₁ n₂ : ℝ³) (δ : ℝ) (hδ : 0 < δ)
    (htrace : ∀ x ∈ sphericalOpenCap p δ, x ∈ T ↔ x ∈ sphericalWedgeTrace n₁ n₂)
    (z : ℝ³) (hz : z ∈ sphericalOpenCap p δ)
    (hz₁ : inner ℝ n₁ z < 0) (hz₂ : inner ℝ n₂ z < 0)
    (x₀ y₀ : ℝ³) (hx₀ : x₀ ∈ sphericalOpenCap p δ) (hy₀ : y₀ ∈ sphericalOpenCap p δ)
    (hx₁ : 0 < inner ℝ n₁ x₀) (hx₂ : 0 < inner ℝ n₂ x₀)
    (hy₀N : inner ℝ n₁ y₀ < 0 ∨ inner ℝ n₂ y₀ < 0)
    (hsep : ¬JoinedIn (openSphericalRegion Tᶜ) x₀ y₀) :
    ∀ x ∈ sphericalOpenCap p δ, ∀ y ∈ sphericalOpenCap p δ,
      0 < inner ℝ n₁ x → 0 < inner ℝ n₂ x →
      (inner ℝ n₁ y < 0 ∨ inner ℝ n₂ y < 0) →
      ¬JoinedIn (openSphericalRegion Tᶜ) x y := by
  intro x hx y hy hxN₁ hxN₂ hyN hxy
  have hin (w : ℝ³) (hw : w ∈ sphericalOpenCap p δ)
      (hw₁ : 0 < inner ℝ n₁ w) (hw₂ : 0 < inner ℝ n₂ w) :
      w ∈ openSphericalRegion Tᶜ :=
    ⟨hw.1, fun ht => wedge_interior_off_trace n₁ n₂ w hw₁ hw₂ ((htrace w hw).mp ht)⟩
  have hout (w : ℝ³) (hw : w ∈ sphericalOpenCap p δ)
      (hwN : inner ℝ n₁ w < 0 ∨ inner ℝ n₂ w < 0) :
      w ∈ openSphericalRegion Tᶜ :=
    ⟨hw.1, fun ht => wedge_exterior_off_trace n₁ n₂ w hwN ((htrace w hw).mp ht)⟩
  have hleft := joinedIn_cap_wedge_interior p n₁ n₂ δ hδ _ hin x₀ x hx₀ hx hx₁ hx₂ hxN₁ hxN₂
  have hright := joinedIn_cap_wedge_exterior p n₁ n₂ δ hδ _ hout z hz hz₁ hz₂
    y y₀ hy hy₀ hyN hy₀N
  exact hsep ((hleft.trans hxy).trans hright)

end SquareAntiprismVerification
