import Lean_Code.VertexConcavity

open Real
noncomputable section
namespace SquareAntiprismVerification

lemma strictConcave_rescale (V : ℝ → ℝ) (α L : ℝ) (hα : 0 < α)
    (hV : StrictConcaveOn ℝ (Set.Icc α (2 * α)) V) :
    StrictConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun t => V (α * (1 + t)) - L) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hx' : α * (1 + x) ∈ Set.Icc α (2 * α) := by
    constructor <;> nlinarith [hx.1, hx.2]
  have hy' : α * (1 + y) ∈ Set.Icc α (2 * α) := by
    constructor <;> nlinarith [hy.1, hy.2]
  have hne : α * (1 + x) ≠ α * (1 + y) := by
    intro h
    have hh := mul_left_cancel₀ hα.ne' h
    apply hxy
    linarith
  have h := hV.2 hx' hy' hne ha hb hab
  have harg : α * (1 + (a * x + b * y)) = a * (α * (1 + x)) + b * (α * (1 + y)) := by
    have hh : α * (a + b) = α := by rw [hab, mul_one]
    nlinarith
  change a * (V (α * (1 + x)) - L) + b * (V (α * (1 + y)) - L) <
    V (α * (1 + (a * x + b * y))) - L
  rw [harg]
  have hL : (a + b) * L = L := by rw [hab, one_mul]
  change a * V (α * (1 + x)) + b * V (α * (1 + y)) <
    V (a * (α * (1 + x)) + b * (α * (1 + y))) at h
  nlinarith

/-- The paper's one-vertex area inequality and its equality condition.
Only the scalar strict-concavity and endpoint-area properties are assumed;
there is no contact-graph or global packing assumption here. -/
theorem one_vertex_area_reduction {ι : Type*} [Fintype ι]
    (V : ℝ → ℝ) (α L : ℝ) (hα : 2 * Real.pi / 5 < α) (hαupper : α < Real.pi / 2)
    (hV : StrictConcaveOn ℝ (Set.Icc α (2 * α)) V)
    (hleft : V α = L) (hright : V (2 * α) = L)
    (h₃ : ℕ) (θ : ι → ℝ) (hθ : ∀ i, θ i ∈ Set.Icc α (2 * α))
    (hangle : (h₃ : ℝ) * α + ∑ i, θ i = 2 * Real.pi) :
    let β₀ := 2 * Real.pi - 3 * α
    0 < V β₀ - L ∧
      (Fintype.card ι : ℝ) * L + (V β₀ - L) ≤ ∑ i, V (θ i) ∧
      ((∀ i, θ i ∈ Set.Ioo α (2 * α)) →
        (∑ i, V (θ i)) = (Fintype.card ι : ℝ) * L + (V β₀ - L) →
        Fintype.card ι = 1 ∧ h₃ = 3 ∧ ∀ i, θ i = β₀) := by
  let β₀ := 2 * Real.pi - 3 * α
  let ρ := 2 * Real.pi / α - 4
  let f : ℝ → ℝ := fun t => V (α * (1 + t)) - L
  let x : ι → ℝ := fun i => θ i / α - 1
  let m : ℤ := 4 - (h₃ : ℤ) - (Fintype.card ι : ℤ)
  have hαpos : 0 < α := by linarith [Real.pi_pos]
  have hρ : ρ ∈ Set.Ioo (0 : ℝ) 1 := by
    have hlo : 4 < 2 * Real.pi / α := (lt_div_iff₀ hαpos).mpr (by linarith)
    have hhi : 2 * Real.pi / α < 5 := (div_lt_iff₀ hαpos).mpr (by linarith)
    dsimp [ρ]
    constructor <;> linarith
  have hmapρ : α * (1 + ρ) = β₀ := by
    dsimp [ρ, β₀]
    field_simp [hαpos.ne']
    ring
  have hfx (i : ι) : f (x i) = V (θ i) - L := by
    have hm : α * (1 + (θ i / α - 1)) = θ i := by field_simp; ring
    change V (α * (1 + (θ i / α - 1))) - L = V (θ i) - L
    rw [hm]
  have hfzero : f 0 = 0 := by simp [f, hleft]
  have hfone : f 1 = 0 := by
    change V (α * (1 + 1)) - L = 0
    rw [show α * (1 + 1) = 2 * α by ring, hright, sub_self]
  have hfρ : f ρ = V β₀ - L := by change V (α * (1 + ρ)) - L = _; rw [hmapρ]
  have hf : StrictConcaveOn ℝ (Set.Icc (0 : ℝ) 1) f := strictConcave_rescale V α L hαpos hV
  have hfpos : 0 < f ρ := by
    have h := hf.2 (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
      (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1) zero_ne_one
      (by linarith [hρ.2] : 0 < 1 - ρ) hρ.1 (by ring)
    simpa [hfzero, hfone] using h
  have hx (i : ι) : x i ∈ Set.Icc (0 : ℝ) 1 := by
    have hlo : 1 ≤ θ i / α := (le_div_iff₀ hαpos).mpr (by simpa using (hθ i).1)
    have hhi : θ i / α ≤ 2 := (div_le_iff₀ hαpos).mpr (hθ i).2
    dsimp [x]
    constructor <;> linarith
  have hsum : ∑ i, x i = (m : ℝ) + ρ := by
    have hs : ∑ i, θ i = 2 * Real.pi - (h₃ : ℝ) * α := by linarith
    dsimp [x]
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, hs]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    dsimp [m, ρ]
    push_cast
    field_simp [hαpos.ne']
    ring
  have hbound := one_vertex_concavity_bound f ρ hf.concaveOn hfzero hfone hρ hfpos.le x hx m hsum
  have hsfx : (∑ i, f (x i)) = (∑ i, V (θ i)) - (Fintype.card ι : ℝ) * L := by
    simp only [hfx, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change 0 < V β₀ - L ∧ _
  refine ⟨by simpa [hfρ] using hfpos, ?_, ?_⟩
  · rw [hfρ, hsfx] at hbound
    linarith
  · intro hinterior heq
    have hxopen (i : ι) : x i ∈ Set.Ioo (0 : ℝ) 1 := by
      have hlo : 1 < θ i / α := (lt_div_iff₀ hαpos).mpr (by simpa using (hinterior i).1)
      have hhi : θ i / α < 2 := (div_lt_iff₀ hαpos).mpr (hinterior i).2
      dsimp [x]
      constructor <;> linarith
    have heqf : (∑ i, f (x i)) = f ρ := by rw [hsfx, hfρ, heq]; ring
    obtain ⟨hcard, hall⟩ := one_vertex_concavity_equality f ρ hf hfzero hfone hρ hfpos x hxopen m hsum heqf
    have hθeq : ∀ i, θ i = β₀ := by
      intro i
      have h := congrArg (fun t : ℝ => α * (1 + t)) (hall i)
      rw [hmapρ] at h
      dsimp [x] at h
      have hm : α * (1 + (θ i / α - 1)) = θ i := by field_simp; ring
      rwa [hm] at h
    have hsθ : (∑ i, θ i) = β₀ := by simp [hθeq, hcard]
    rw [hsθ] at hangle
    have hh₃ : (h₃ : ℝ) = 3 := by dsimp [β₀] at hangle; nlinarith
    exact ⟨hcard, by exact_mod_cast hh₃, hθeq⟩

end SquareAntiprismVerification
