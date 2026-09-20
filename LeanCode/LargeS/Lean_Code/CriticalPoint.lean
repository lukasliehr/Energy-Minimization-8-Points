import Lean_Code.StrictConvexity

open Real
noncomputable section
namespace SquareAntiprismVerification

lemma convex_min_of_fderiv_zero (D : Set InfinitesimalCoordinates)
    (f : InfinitesimalCoordinates → ℝ) (hconv : ConvexOn ℝ D f)
    (x : InfinitesimalCoordinates) (hx : x ∈ D) (hdiff : DifferentiableAt ℝ f x)
    (hzero : fderiv ℝ f x = 0) : IsMinOn f D x := by
  intro y hy
  let v := y - x
  let g : ℝ → ℝ := fun t => f (x + t • v)
  have hline_eq (t : ℝ) : x + t • v = (1 - t) • x + t • y := by
    dsimp [v]
    module
  have hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • v ∈ D := by
    intro t ht
    rw [hline_eq]
    exact hconv.1 hx hy (by linarith [ht.2]) ht.1 (by ring)
  have hg : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) g := by
    refine ⟨convex_Icc _ _, ?_⟩
    intro t ht u hu a b ha hb hab
    have harg : x + (a * t + b * u) • v = a • (x + t • v) + b • (x + u • v) := by
      calc
        _ = (a + b) • x + (a * t + b * u) • v := by rw [hab, one_smul]
        _ = _ := by module
    change f (x + (a * t + b * u) • v) ≤ a * f (x + t • v) + b * f (x + u • v)
    rw [harg]
    exact hconv.2 (hmem t ht) (hmem u hu) ha hb hab
  have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using HasDerivAt.const_add x ((hasDerivAt_id (0 : ℝ)).smul_const v)
  have hD : HasFDerivAt f (0 : InfinitesimalCoordinates →L[ℝ] ℝ)
      (x + (0 : ℝ) • v) := by
    simpa [hzero] using hdiff.hasFDerivAt
  have hderiv : HasDerivAt g 0 0 := by
    simpa [g, Function.comp_def] using hD.comp_hasDerivAt (0 : ℝ) hline
  have hslope := hg.le_slope_of_hasDerivAt
    (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
    (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1) zero_lt_one hderiv
  simpa [slope, g, v] using hslope

theorem strictConvex_stationary_minimum (D : Set InfinitesimalCoordinates)
    (f : InfinitesimalCoordinates → ℝ) (hconv : StrictConvexOn ℝ D f)
    (x : InfinitesimalCoordinates) (hx : x ∈ D) (hdiff : DifferentiableAt ℝ f x)
    (hzero : fderiv ℝ f x = 0) :
    ∀ y ∈ D, f x ≤ f y ∧ (f y = f x ↔ y = x) := by
  have hmin := convex_min_of_fderiv_zero D f hconv.convexOn x hx hdiff hzero
  intro y hy
  refine ⟨hmin hy, ?_⟩
  constructor
  · intro heq
    have hymin : IsMinOn f D y := by
      intro z hz
      rw [heq]
      exact hmin hz
    exact (hconv.eq_of_isMinOn hmin hymin hx hy).symm
  · rintro rfl
    rfl

end SquareAntiprismVerification
