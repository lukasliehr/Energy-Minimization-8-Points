import Lean_Code.ChartBounds
import Lean_Code.ShrinkingWeights

open Real Filter
noncomputable section
namespace SquareAntiprismVerification

/-- The second directional derivative of a real power, as an equality of
actual Fréchet derivatives rather than an assumed Hessian formula. -/
lemma rpow_second_directional (f : InfinitesimalCoordinates → ℝ)
    (x v : InfinitesimalCoordinates) (r : ℝ) (hf : ContDiffAt ℝ 2 f x)
    (hx : f x ≠ 0) :
    fderiv ℝ (fderiv ℝ (fun z => f z ^ r)) x v v =
      r * (r - 1) * f x ^ (r - 2) * (fderiv ℝ f x v) ^ 2 +
      r * f x ^ (r - 1) * fderiv ℝ (fderiv ℝ f) x v v := by
  have hd := (hf.differentiableAt (by norm_num)).hasFDerivAt
  have hDf : ContDiffAt ℝ 1 (fderiv ℝ f) x := hf.fderiv_right (by norm_num)
  have hD := (hDf.differentiableAt (by norm_num)).hasFDerivAt
  have hscalar := (hd.rpow_const (p := r - 1) (Or.inl hx)).const_mul r
  have hprod := hscalar.smul hD
  have hnear : ∀ᶠ z in nhds x, f z ≠ 0 := hf.continuousAt.eventually_ne hx
  have heq : fderiv ℝ (fun z => f z ^ r) =ᶠ[nhds x]
      (fun z => r * f z ^ (r - 1)) • fderiv ℝ f := by
    filter_upwards [hf.eventually (by norm_num), hnear] with z hsz hnz
    exact ((hsz.differentiableAt (by norm_num)).hasFDerivAt.rpow_const
      (Or.inl hnz)).fderiv
  have hfinal := (hprod.congr_of_eventuallyEq heq).fderiv
  rw [hfinal]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  rw [show r - 1 - 1 = r - 2 by ring]
  ring

lemma finite_sum_second_directional {ι : Type} (s : Finset ι)
    (f : ι → InfinitesimalCoordinates → ℝ) (x v : InfinitesimalCoordinates)
    (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) x) :
    fderiv ℝ (fderiv ℝ (∑ i ∈ s, f i)) x v v =
      ∑ i ∈ s, fderiv ℝ (fderiv ℝ (f i)) x v v := by
  have hnear : ∀ᶠ z in nhds x, ∀ i ∈ s, DifferentiableAt ℝ (f i) z := by
    rw [Filter.eventually_all_finset]
    intro i hi
    filter_upwards [(hf i hi).eventually (by norm_num)] with z hz
    exact hz.differentiableAt (by norm_num)
  have heq : fderiv ℝ (∑ i ∈ s, f i) =ᶠ[nhds x]
      (fun z => ∑ i ∈ s, fderiv ℝ (f i) z) := by
    filter_upwards [hnear] with z hz
    exact fderiv_sum hz
  have hfd : ∀ i ∈ s, DifferentiableAt ℝ (fderiv ℝ (f i)) x := by
    intro i hi
    have h : ContDiffAt ℝ 1 (fderiv ℝ (f i)) x :=
      (hf i hi).fderiv_right (by norm_num)
    exact h.differentiableAt (by norm_num)
  rw [heq.fderiv_eq]
  have heqfun : (fun z => ∑ i ∈ s, fderiv ℝ (f i) z) =
      ∑ i ∈ s, fderiv ℝ (f i) := by funext z; simp only [Finset.sum_apply]
  rw [heqfun, fderiv_sum hfd]
  simp

def energyPairs : Finset (Fin 8 × Fin 8) := Finset.univ.filter (fun ij => ij.1 < ij.2)

@[simp] lemma mem_energyPairs (ij : Fin 8 × Fin 8) :
    ij ∈ energyPairs ↔ ij.1 < ij.2 := by simp [energyPairs]

lemma energyPairs_card : energyPairs.card = 28 := by decide

def chartEnergy (p : ℝ) : InfinitesimalCoordinates → ℝ :=
  ∑ ij ∈ energyPairs, (fun z => chartPairDistance z ij ^ (-p))

lemma chartEnergy_eq (p : ℝ) (z : InfinitesimalCoordinates) :
    chartEnergy p z = E (2 * p) (coordinateChart z) := by
  simp only [chartEnergy, Finset.sum_apply, E, energyPairs, Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs
  · exact (norm_rpow_two_mul _ p).symm
  · rfl

lemma chartEnergy_contDiffAt (p : ℝ) (z : InfinitesimalCoordinates)
    (hsmooth : ∀ ij ∈ energyPairs, ContDiffAt ℝ 2 (fun q => chartPairDistance q ij) z)
    (hpos : ∀ ij ∈ energyPairs, 0 < chartPairDistance z ij) :
    ContDiffAt ℝ 2 (chartEnergy p) z := by
  have h := ContDiffAt.sum (s := energyPairs) (fun ij hij =>
    (hsmooth ij hij).rpow (contDiffAt_const (c := -p)) (ne_of_gt (hpos ij hij)))
  convert! h using 1

theorem chartEnergy_hessian (p : ℝ) (z v : InfinitesimalCoordinates)
    (hsmooth : ∀ ij ∈ energyPairs, ContDiffAt ℝ 2 (fun q => chartPairDistance q ij) z)
    (hpos : ∀ ij ∈ energyPairs, 0 < chartPairDistance z ij) :
    fderiv ℝ (fderiv ℝ (chartEnergy p)) z v v =
      p * (p + 1) * (∑ ij ∈ energyPairs,
        chartPairDistance z ij ^ (-p - 2) *
          (fderiv ℝ (fun q => chartPairDistance q ij) z v) ^ 2) -
      p * (∑ ij ∈ energyPairs, chartPairDistance z ij ^ (-p - 1) *
        fderiv ℝ (fderiv ℝ (fun q => chartPairDistance q ij)) z v v) := by
  have hs : ∀ ij ∈ energyPairs,
      ContDiffAt ℝ 2 (fun q => chartPairDistance q ij ^ (-p)) z := by
    intro ij hij
    exact (hsmooth ij hij).rpow contDiffAt_const (ne_of_gt (hpos ij hij))
  unfold chartEnergy
  rw [finite_sum_second_directional energyPairs _ z v hs]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [rpow_second_directional _ z v (-p) (hsmooth ij hij) (ne_of_gt (hpos ij hij))]
  ring

end SquareAntiprismVerification
