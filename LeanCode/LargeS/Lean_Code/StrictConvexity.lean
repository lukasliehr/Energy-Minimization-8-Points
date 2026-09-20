import Lean_Code.EventualHessian

open Real Filter
noncomputable section
namespace SquareAntiprismVerification

lemma affine_line_second_deriv (f : InfinitesimalCoordinates → ℝ)
    (x v : InfinitesimalCoordinates) (t : ℝ)
    (hf : ContDiffAt ℝ 2 f (x + t • v)) :
    deriv (deriv (fun u : ℝ => f (x + u • v))) t =
      fderiv ℝ (fderiv ℝ f) (x + t • v) v v := by
  have hline : ∀ u : ℝ, HasDerivAt (fun s : ℝ => x + s • v) v u := by
    intro u
    simpa using HasDerivAt.const_add x ((hasDerivAt_id u).smul_const v)
  have hDf : ContDiffAt ℝ 1 (fderiv ℝ f) (x + t • v) :=
    hf.fderiv_right (by norm_num)
  have happly := (hDf.differentiableAt (by norm_num)).hasFDerivAt.clm_apply
    (hasFDerivAt_const v (x + t • v))
  have hcomp := happly.comp_hasDerivAt t (hline t)
  have hnear : ∀ᶠ u in nhds t, ContDiffAt ℝ 2 f (x + u • v) :=
    (hline t).continuousAt.tendsto.eventually (hf.eventually (by norm_num))
  have heq : deriv (fun u : ℝ => f (x + u • v)) =ᶠ[nhds t]
      (fun u => fderiv ℝ f (x + u • v) v) := by
    filter_upwards [hnear] with u hu
    simpa [Function.comp_def] using
      ((hu.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt u (hline u)).deriv
  have hcomp' : HasDerivAt (fun u : ℝ => fderiv ℝ f (x + u • v) v)
      (fderiv ℝ (fderiv ℝ f) (x + t • v) v v) t := by
    simpa [Function.comp_def] using hcomp
  exact (hcomp'.congr_of_eventuallyEq heq).deriv

def GaugeBall (r : ℝ) : Set InfinitesimalCoordinates :=
  {q | InContactGauge q ∧ ‖q‖ ≤ r}

lemma inContactGauge_sub {x y : InfinitesimalCoordinates}
    (hx : InContactGauge x) (hy : InContactGauge y) : InContactGauge (x - y) := by
  rcases hx with ⟨hx₁, hx₂, hx₃⟩
  rcases hy with ⟨hy₁, hy₂, hy₃⟩
  simp [InContactGauge, hx₁, hx₂, hx₃, hy₁, hy₂, hy₃]

lemma gaugeBall_convex (r : ℝ) : Convex ℝ (GaugeBall r) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_⟩
  · rcases hx.1 with ⟨hx₁, hx₂, hx₃⟩
    rcases hy.1 with ⟨hy₁, hy₂, hy₃⟩
    simp [InContactGauge, hx₁, hx₂, hx₃, hy₁, hy₂, hy₃]
  · have hxball : x ∈ Metric.closedBall 0 r := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hx.2
    have hyball : y ∈ Metric.closedBall 0 r := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hy.2
    simpa [Metric.mem_closedBall, dist_zero_right] using
      (convex_closedBall (0 : InfinitesimalCoordinates) r) hxball hyball ha hb hab

lemma strictConvexOn_of_gauge_hessian (r : ℝ) (f : InfinitesimalCoordinates → ℝ)
    (hreg : ∀ z ∈ GaugeBall r, ContDiffAt ℝ 2 f z)
    (hpos : ∀ z ∈ GaugeBall r, ∀ v : InfinitesimalCoordinates,
      InContactGauge v → v ≠ 0 → 0 < fderiv ℝ (fderiv ℝ f) z v v) :
    StrictConvexOn ℝ (GaugeBall r) f := by
  refine ⟨gaugeBall_convex r, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  let v : InfinitesimalCoordinates := y - x
  let g : ℝ → ℝ := fun t => f (x + t • v)
  have hv : InContactGauge v := inContactGauge_sub hy.1 hx.1
  have hvne : v ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  have hline_eq (t : ℝ) : x + t • v = (1 - t) • x + t • y := by
    dsimp [v]
    module
  have hline_mem : ∀ t ∈ Set.Icc (0 : ℝ) 1, x + t • v ∈ GaugeBall r := by
    intro t ht
    rw [hline_eq]
    exact (gaugeBall_convex r) hx hy (by linarith [ht.2]) ht.1 (by ring)
  have hgcont : ContinuousOn g (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    have hline : ContinuousAt (fun u : ℝ => x + u • v) t := by fun_prop
    have hfcont : ContinuousAt f (x + t • v) := (hreg _ (hline_mem t ht)).continuousAt
    have hcomp := ContinuousAt.comp (f := fun u : ℝ => x + u • v) hfcont hline
    exact hcomp.continuousWithinAt
  have hgsecond : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1), 0 < deriv^[2] g t := by
    intro t ht
    have htm := hline_mem t (interior_subset ht)
    change 0 < deriv (deriv (fun u : ℝ => f (x + u • v))) t
    rw [affine_line_second_deriv f x v t (hreg _ htm)]
    exact hpos _ htm v hv hvne
  have hg : StrictConvexOn ℝ (Set.Icc (0 : ℝ) 1) g :=
    strictConvexOn_of_deriv2_pos (convex_Icc _ _) hgcont hgsecond
  have h := hg.2 (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
    (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1) (by norm_num : (0 : ℝ) ≠ 1) ha hb hab
  have hbline : x + b • v = a • x + b • y := by
    rw [hline_eq]
    congr 1
    congr 1
    linarith
  simpa [g, hbline, v] using h

theorem chartEnergy_eventually_strictConvex (K : ℝ) (hK : 0 < K) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p ≥ p₀,
      StrictConvexOn ℝ (GaugeBall (2 * K / p)) (chartEnergy p) := by
  obtain ⟨p₀, hp₀, h⟩ := chartEnergy_eventually_regular K hK
  refine ⟨p₀, hp₀, fun p hp => ?_⟩
  apply strictConvexOn_of_gauge_hessian
  · intro z hz
    exact (h p hp z hz.2).1
  · intro z hz
    exact (h p hp z hz.2).2

end SquareAntiprismVerification
