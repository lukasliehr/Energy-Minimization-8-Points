import Lean_Code.StationarityAlgebra
import Lean_Code.StationarityCalculus

open Real Filter
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma antiprism_tangent_energy_zero (p a : ℝ) (ha : a ∈ Set.Ioo (0 : ℝ) 1)
    (hF : F (2 * p) a = 0) (V : Fin 8 → ℝ³)
    (hV : ∀ i, inner ℝ (X a i) (V i) = 0) :
    (∑ ij ∈ energyPairs, (‖X a ij.1 - X a ij.2‖ ^ 2) ^ (-p - 1) *
      inner ℝ (X a ij.1 - X a ij.2) (V ij.1 - V ij.2)) = 0 := by
  rw [show -p - 1 = -q (2 * p) by unfold q; ring, pair_tangent_sum (X a) V _ hV]
  simp only [antiprism_weighted_sum_radial (2 * p) a ha hF, inner_smul_left,
    hV, mul_zero, Finset.sum_const_zero, neg_zero]

theorem antiprism_curve_stationary (p a : ℝ) (ha : a ∈ Set.Ioo (0 : ℝ) 1)
    (hF : F (2 * p) a = 0) (γ : ℝ → Fin 8 → ℝ³)
    (hγzero : γ 0 = X a) (hγ : ∀ i, DifferentiableAt ℝ (fun t => γ t i) 0)
    (hsphere : ∀ᶠ t in nhds 0, ∀ i, ‖γ t i‖ = 1) :
    HasDerivAt (fun t => E (2 * p) (γ t)) 0 0 := by
  let V : Fin 8 → ℝ³ := fun i => deriv (fun t => γ t i) 0
  have hderiv : ∀ i, HasDerivAt (fun t => γ t i) (V i) 0 :=
    fun i => (hγ i).hasDerivAt
  have htangent : ∀ i, inner ℝ (X a i) (V i) = 0 := by
    intro i
    have hd := (hderiv i).norm_sq
    have heq : (fun t => ‖γ t i‖ ^ 2) =ᶠ[nhds 0] (fun _ => (1 : ℝ)) := by
      filter_upwards [hsphere] with t ht
      rw [ht i]
      norm_num
    have hz : HasDerivAt (fun t => ‖γ t i‖ ^ 2) 0 0 :=
      (hasDerivAt_const (0 : ℝ) (1 : ℝ)).congr_of_eventuallyEq heq
    have hh := hd.unique hz
    rw [hγzero] at hh
    linarith
  have h := energy_curve_hasDerivAt p (X a) V γ (X_isConfiguration a ha) hγzero hderiv
  simpa only [antiprism_tangent_energy_zero p a ha hF V htangent, mul_zero] using h

theorem congruent_curve_stationary (p a : ℝ) (ha : a ∈ Set.Ioo (0 : ℝ) 1)
    (hF : F (2 * p) a = 0) (γ : ℝ → Fin 8 → ℝ³)
    (hcong : Congruent (γ 0) (X a)) (hγ : ∀ i, DifferentiableAt ℝ (fun t => γ t i) 0)
    (hsphere : ∀ᶠ t in nhds 0, ∀ i, ‖γ t i‖ = 1) :
    HasDerivAt (fun t => E (2 * p) (γ t)) 0 0 := by
  obtain ⟨Q, σ, hQ⟩ := hcong
  let γ' : ℝ → Fin 8 → ℝ³ := fun t i => Q (γ t (σ i))
  have hzero : γ' 0 = X a := by funext i; exact (hQ i).symm
  have hdiff : ∀ i, DifferentiableAt ℝ (fun t => γ' t i) 0 := by
    intro i
    exact Q.toContinuousLinearMap.differentiableAt.comp 0 (hγ (σ i))
  have hsphere' : ∀ᶠ t in nhds 0, ∀ i, ‖γ' t i‖ = 1 := by
    filter_upwards [hsphere] with t ht
    intro i
    exact (Q.norm_map _).trans (ht (σ i))
  have h := antiprism_curve_stationary p a ha hF γ' hzero hdiff hsphere'
  have heq : (fun t => E (2 * p) (γ' t)) = (fun t => E (2 * p) (γ t)) := by
    funext t
    change E (2 * p) (fun i => Q (γ t (σ i))) = _
    rw [energy_linearIsometry, energy_permutation]
  rw [heq] at h
  exact h

end SquareAntiprismVerification
