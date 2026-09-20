import Lean_Code.LocalSlice
import Lean_Code.EnergyBounds

open Real

noncomputable section

namespace SquareAntiprismVerification

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)


/-- Paper Lemma 6.2, abstracted over the exact best-packing rigidity
statement.  Compactness upgrades pointwise packing uniqueness to uniform
localization of the whole energy sublevel. -/
theorem qualitative_uniform_orbit_localization
    (hpacking : ∀ Y : Fin 8 → ℝ³, (∀ i, Y i ∈ unitSphere) →
      (∀ i j, i ≠ j → tau ≤ ‖Y i - Y j‖ ^ 2) → Congruent Y P)
    (U : Set SphereTuple) (hUopen : IsOpen U) (hUorbit : OrbitNeighborhood U) :
    ∃ pU : ℝ, 0 < pU ∧ ∀ p ≥ pU, ∀ Y : Fin 8 → ℝ³,
      ∀ hY : IsConfiguration Y, E (2 * p) Y ≤ E (2 * p) P →
        toSphereTuple Y hY.1 ∈ U := by
  by_contra hgoal
  push_neg at hgoal
  have hex : ∀ n : ℕ, ∃ p : ℝ, (n : ℝ) + 1 ≤ p ∧
      ∃ Y : Fin 8 → ℝ³, ∃ hY : IsConfiguration Y,
        E (2 * p) Y ≤ E (2 * p) P ∧ toSphereTuple Y hY.1 ∉ U := by
    intro n
    exact hgoal ((n : ℝ) + 1) (by positivity)
  choose p hp Y hY hsub hnot using hex
  let Z : ℕ → SphereTuple := fun n => toSphereTuple (Y n) (hY n).1
  letI : (Filter.atTop : Filter ℕ).NeBot := inferInstance
  have hp_atTop : Filter.Tendsto p Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono' Filter.atTop
      (Filter.Eventually.of_forall fun n : ℕ =>
        show (n : ℝ) ≤ p n by linarith [hp n])
    exact tendsto_natCast_atTop_atTop
  have hfreq : ∃ᶠ n : ℕ in Filter.atTop, Z n ∈ Set.univ := by
    apply Filter.Eventually.frequently
    exact Filter.Eventually.of_forall fun n => Set.mem_univ (Z n)
  obtain ⟨Zlim, hZlim_univ, φ, hφ, hconv⟩ :=
    isCompact_univ.isSeqCompact.subseq_of_frequently_in (x := Z) hfreq
  have hpφ : Filter.Tendsto (fun n => p (φ n)) Filter.atTop Filter.atTop :=
    hp_atTop.comp hφ.tendsto_atTop
  have hrecip : Filter.Tendsto (fun n => (p (φ n))⁻¹)
      Filter.atTop (nhds 0) := tendsto_inv_atTop_zero.comp hpφ
  have hexponent : Filter.Tendsto (fun n => -1 / p (φ n))
      Filter.atTop (nhds 0) := by
    have heq : (fun n => -1 / p (φ n)) = (fun n => -(p (φ n))⁻¹) := by
      funext n
      ring
    rw [heq]
    simpa only [neg_zero] using hrecip.neg
  have hfactor : Filter.Tendsto (fun n => (28 : ℝ) ^ (-1 / p (φ n)))
      Filter.atTop (nhds 1) := by
    have ht := (Real.continuousAt_const_rpow (a := (28 : ℝ)) (b := 0)
      (by norm_num)).tendsto.comp hexponent
    change Filter.Tendsto
      ((fun x : ℝ => (28 : ℝ) ^ x) ∘ (fun n => -1 / p (φ n)))
      Filter.atTop (nhds 1)
    simpa only [Real.rpow_zero] using ht
  have hlower : Filter.Tendsto
      (fun n => tau * (28 : ℝ) ^ (-1 / p (φ n)))
      Filter.atTop (nhds tau) := by
    simpa only [mul_one] using tendsto_const_nhds.mul hfactor
  have hsepLimit : ∀ i j : Fin 8, i ≠ j →
      tau ≤ ‖fromSphereTuple Zlim i - fromSphereTuple Zlim j‖ ^ 2 := by
    intro i j hij
    have hcoord_i : Filter.Tendsto
        (fun n => (Z (φ n) i : ℝ³)) Filter.atTop (nhds (Zlim i : ℝ³)) := by
      exact continuous_subtype_val.continuousAt.tendsto.comp
        ((tendsto_pi_nhds.mp hconv) i)
    have hcoord_j : Filter.Tendsto
        (fun n => (Z (φ n) j : ℝ³)) Filter.atTop (nhds (Zlim j : ℝ³)) := by
      exact continuous_subtype_val.continuousAt.tendsto.comp
        ((tendsto_pi_nhds.mp hconv) j)
    have hdist : Filter.Tendsto
        (fun n => ‖(Z (φ n) i : ℝ³) - (Z (φ n) j : ℝ³)‖ ^ 2)
        Filter.atTop (nhds (‖(Zlim i : ℝ³) - (Zlim j : ℝ³)‖ ^ 2)) :=
      ((hcoord_i.sub hcoord_j).norm).pow 2
    apply le_of_tendsto_of_tendsto hlower hdist
    exact Filter.Eventually.of_forall fun n => by
      change tau * (28 : ℝ) ^ (-1 / p (φ n)) ≤
        ‖Y (φ n) i - Y (φ n) j‖ ^ 2
      exact pairwise_sublevel_bound (p (φ n)) (by linarith [hp (φ n)])
        (Y (φ n)) (hY (φ n)) (hsub (φ n)) i j hij
  have hcong : Congruent (fromSphereTuple Zlim) P :=
    hpacking (fromSphereTuple Zlim) (fromSphereTuple_sphere Zlim) hsepLimit
  have hZlimU : Zlim ∈ U := by
    simpa using hUorbit (fromSphereTuple Zlim) (fromSphereTuple_sphere Zlim) hcong
  have heventually : ∀ᶠ n in Filter.atTop, Z (φ n) ∈ U :=
    hconv (hUopen.mem_nhds hZlimU)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 heventually
  exact (hnot (φ N)) (hN N le_rfl)

/-- Sections 4--6, in the exact sublevel form used in the paper.  Qualitative
packing localization and the local shrinking-ball classification supply one
uniform exponent threshold. -/
theorem eventual_sublevel_classification :
    ∃ S₀ : ℝ, 1 ≤ S₀ ∧ ∀ s ≥ S₀,
      ∀ Y : Fin 8 → ℝ³, IsConfiguration Y → E s Y ≤ E s P →
        E s Y ≥ E s (X (aStar s)) ∧
        (E s Y = E s (X (aStar s)) ↔ Congruent Y (X (aStar s))) := by
  obtain ⟨U, hUopen, hUorbit, p₀, hp₀, hlocal⟩ :=
    eventual_local_sublevel_classification
  obtain ⟨pU, hpU, hqual⟩ := qualitative_uniform_orbit_localization
    eight_point_best_packing_rigidity U hUopen hUorbit
  let pbar : ℝ := max (max p₀ pU) 1
  let S₀ : ℝ := 2 * pbar
  refine ⟨S₀, ?_, ?_⟩
  · dsimp [S₀, pbar]
    have h : (1 : ℝ) ≤ max (max p₀ pU) 1 := le_max_right _ _
    linarith
  · intro s hs Y hY hsub
    let p : ℝ := s / 2
    have hpbar : pbar ≤ p := by
      dsimp [S₀] at hs
      dsimp [p]
      linarith
    have hp₀p : p₀ ≤ p := (le_max_left p₀ pU).trans
      ((le_max_left (max p₀ pU) 1).trans hpbar)
    have hpUp : pU ≤ p := (le_max_right p₀ pU).trans
      ((le_max_left (max p₀ pU) 1).trans hpbar)
    have htwo : 2 * p = s := by dsimp [p]; ring
    have hnear := hqual p hpUp Y hY (by simpa only [htwo] using hsub)
    have hresult := hlocal p hp₀p Y hY hnear (by simpa only [htwo] using hsub)
    simpa only [htwo] using hresult

/-- The sublevel classification implies the unrestricted inequality because
the optimized antiprism itself lies below `P`. -/
theorem eventual_energy_optimality :
    ∃ S₀ : ℝ, 0 ≤ S₀ ∧ ∀ s ≥ S₀,
      ∀ Y : Fin 8 → ℝ³, IsConfiguration Y →
        E s Y ≥ E s (X (aStar s)) ∧
        (E s Y = E s (X (aStar s)) ↔ Congruent Y (X (aStar s))) := by
  obtain ⟨S₀, hS₀, hsublevel⟩ := eventual_sublevel_classification
  refine ⟨S₀, by linarith, ?_⟩
  intro s hs Y hY
  by_cases hYP : E s Y ≤ E s P
  · exact hsublevel s hs Y hY hYP
  · have hspos : 0 < s := by linarith
    have hcandidateP := antiprism_sublevel s hspos
    have hPY : E s P < E s Y := lt_of_not_ge hYP
    have hstrict : E s (X (aStar s)) < E s Y :=
      lt_of_le_of_lt hcandidateP hPY
    refine ⟨le_of_lt hstrict, ?_⟩
    constructor
    · intro heq
      linarith
    · intro hcong
      exact (congruent_energy hcong).symm

theorem large_exponent_conclusion :
    ∃ S₀ : ℝ, ∀ s ≥ S₀,
      (∀ Y : Fin 8 → ℝ³, IsConfiguration Y →
        E s Y ≥ E s (X (aStar s)) ∧
        (E s Y = E s (X (aStar s)) ↔ Congruent Y (X (aStar s)))) ∧
      ℰ s = E s (X (aStar s)) := by
  obtain ⟨S₀, hS₀, hglobal⟩ := eventual_energy_optimality
  refine ⟨S₀, ?_⟩
  intro s hs
  have hs0 : 0 ≤ s := hS₀.trans hs
  have hmain := hglobal s hs
  refine ⟨hmain, ?_⟩
  apply minimalEnergy_eq_of_global s (aStar s)
  · exact X_isConfiguration (aStar s) (aStar_spec s hs0).1
  · intro Y hY
    exact (hmain Y hY).1

end SquareAntiprismVerification
