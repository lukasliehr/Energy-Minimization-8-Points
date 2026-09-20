import Lean_Code.HessianBounds

open Real
noncomputable section
namespace SquareAntiprismVerification

@[simp] lemma chartPairDistance_zero (ij : Fin 8 × Fin 8) :
    chartPairDistance 0 ij = ‖P ij.1 - P ij.2‖ ^ 2 := by
  simp only [chartPairDistance, coordinateChart_zero, ← P_eq_polarP]

lemma chartPairDistance_zero_ge (ij : Fin 8 × Fin 8) (hij : ij ∈ energyPairs) :
    tau ≤ chartPairDistance 0 ij := by
  rw [chartPairDistance_zero]
  exact P_pair_sq_ge_tau _ _ (ne_of_lt ((mem_energyPairs ij).mp hij))

lemma chartPairDistance_contact_zero (e : Fin 16) :
    chartPairDistance 0 (contactPair e) = tau := by
  exact chartContactDistance_zero e

/-- The actual energy Hessian is positive on any prescribed `2K/p` ball
in the gauge, once the exponent is sufficiently large. -/
theorem chartEnergy_eventually_regular (K : ℝ) (hK : 0 < K) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p ≥ p₀,
      ∀ z : InfinitesimalCoordinates, ‖z‖ ≤ 2 * K / p →
      ContDiffAt ℝ 2 (chartEnergy p) z ∧
        ∀ v : InfinitesimalCoordinates, InContactGauge v → v ≠ 0 →
          0 < fderiv ℝ (fderiv ℝ (chartEnergy p)) z v v := by
  obtain ⟨L, M, ε, hL, hM, hε, hest⟩ := chart_pair_local_estimates
  obtain ⟨c, ρ, hc, hρ, hrank⟩ := chart_contact_rank_uniform
  have htau : 0 < tau := by unfold tau; linarith [aInf_mem_Ioo.2]
  let B : ℝ := 2 * L * K / tau
  have hB : 0 < B := by dsimp [B]; positivity
  let a : ℝ := Real.exp (-3 * B) * c ^ 2
  let D : ℝ := 28 * M * tau * Real.exp (4 * B)
  have ha : 0 < a := mul_pos (Real.exp_pos _) (sq_pos_of_pos hc)
  obtain ⟨p₁, hp₁, hbracket⟩ := hessian_bracket_eventually_positive a D ha
  let p₀ := max (max 1 (2 * B)) (max p₁ (max (2 * K / ε + 1) (2 * K / ρ + 1)))
  have hbase : 1 ≤ p₀ := (le_max_left _ _).trans (le_max_left _ _)
  refine ⟨p₀, zero_lt_one.trans_le hbase, ?_⟩
  intro p hp z hz
  have hpone : 1 ≤ p := hbase.trans hp
  have hppos : 0 < p := zero_lt_one.trans_le hpone
  have hpB : 2 * B ≤ p :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans hp
  have hpp₁ : p₁ ≤ p :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hp
  have hpε : 2 * K / ε + 1 ≤ p :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hp
  have hpρ : 2 * K / ρ + 1 ≤ p :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hp
  have hzε : ‖z‖ < ε := by
    apply hz.trans_lt
    apply (div_lt_iff₀ hppos).mpr
    have h := (div_lt_iff₀ hε).mp (show 2 * K / ε < p by linarith)
    nlinarith
  have hzρ : ‖z‖ < ρ := by
    apply hz.trans_lt
    apply (div_lt_iff₀ hppos).mpr
    have h := (div_lt_iff₀ hρ).mp (show 2 * K / ρ < p by linarith)
    nlinarith
  have hBrel : tau * (B / p) = L * (2 * K / p) := by
    dsimp [B]
    field_simp
  have hLip : ∀ ij : Fin 8 × Fin 8,
      |chartPairDistance z ij - chartPairDistance 0 ij| ≤ L * (2 * K / p) := by
    intro ij
    exact (hest z hzε ij).2.1.trans (mul_le_mul_of_nonneg_left hz hL.le)
  have hlower : ∀ ij ∈ energyPairs,
      tau * (1 - B / p) ≤ chartPairDistance z ij := by
    intro ij hij
    have h := (abs_le.mp (hLip ij)).1
    have hzero := chartPairDistance_zero_ge ij hij
    nlinarith
  have ht_half : B / p ≤ 1 / 2 := (div_le_iff₀ hppos).mpr (by linarith)
  have hpositive : ∀ ij ∈ energyPairs, 0 < chartPairDistance z ij := by
    intro ij hij
    exact (mul_pos htau (show 0 < 1 - B / p by linarith)).trans_le (hlower ij hij)
  refine ⟨chartEnergy_contDiffAt p z (fun ij hij => (hest z hzε ij).1) hpositive, ?_⟩
  intro v hv hvne
  obtain ⟨e, he⟩ := hrank z hzρ v hv
  have hemem : contactPair e ∈ energyPairs := (mem_energyPairs _).mpr (contactPair_lt e)
  have hupper : chartPairDistance z (contactPair e) ≤ tau * (1 + B / p) := by
    have h := (abs_le.mp (hLip (contactPair e))).2
    rw [chartPairDistance_contact_zero] at h
    nlinarith
  have hweights : ∀ ij ∈ energyPairs,
      chartPairDistance z ij ^ (-p - 1) ≤ tau ^ (-p - 1) * Real.exp (4 * B) := by
    intro ij hij
    exact shrinking_pair_weight_upper tau B p _ htau hB.le hpone hpB (hlower ij hij)
  have hcontact := shrinking_contact_weight_lower tau B p
    (chartPairDistance z (contactPair e)) htau hB.le hpone (hpositive _ hemem) hupper
  have hsecond : ∀ ij ∈ energyPairs,
      |fderiv ℝ (fderiv ℝ (fun q => chartPairDistance q ij)) z v v| ≤ M * ‖v‖ ^ 2 := by
    intro ij hij
    exact (hest z hzε ij).2.2 v
  have hbound := finite_hessian_lower_bound energyPairs
    (fun ij => chartPairDistance z ij)
    (fun ij => fderiv ℝ (fun q => chartPairDistance q ij) z v)
    (fun ij => fderiv ℝ (fderiv ℝ (fun q => chartPairDistance q ij)) z v v)
    p (tau ^ (-p - 2) * Real.exp (-3 * B))
    (tau ^ (-p - 1) * Real.exp (4 * B)) M c ‖v‖ hppos.le
    (by positivity) (by positivity) hc.le (norm_nonneg v)
    (fun ij hij => (hpositive ij hij).le) hweights hsecond
    (contactPair e) hemem hcontact he
  rw [← chartEnergy_hessian p z v (fun ij hij => (hest z hzε ij).1) hpositive] at hbound
  have hpow : tau ^ (-p - 1) = tau ^ (-p - 2) * tau := by
    rw [show -p - 1 = (-p - 2) + 1 by ring, Real.rpow_add htau, Real.rpow_one]
  have hfactor : p * ((p + 1) * (tau ^ (-p - 2) * Real.exp (-3 * B)) * c ^ 2 -
      energyPairs.card * (tau ^ (-p - 1) * Real.exp (4 * B)) * M) * ‖v‖ ^ 2 =
      p * tau ^ (-p - 2) * ((p + 1) * a - D) * ‖v‖ ^ 2 := by
    rw [energyPairs_card, hpow]
    dsimp [a, D]
    norm_num only [Nat.cast_ofNat]
    ring
  rw [hfactor] at hbound
  apply lt_of_lt_of_le _ hbound
  exact mul_pos (mul_pos (mul_pos hppos (Real.rpow_pos_of_pos htau _))
    (hbracket p hpp₁)) (sq_pos_of_pos (norm_pos_iff.mpr hvne))

theorem chartEnergy_hessian_eventually_positive (K : ℝ) (hK : 0 < K) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p ≥ p₀,
      ∀ z : InfinitesimalCoordinates, ‖z‖ ≤ 2 * K / p →
      ∀ v : InfinitesimalCoordinates, InContactGauge v → v ≠ 0 →
        0 < fderiv ℝ (fderiv ℝ (chartEnergy p)) z v v := by
  obtain ⟨p₀, hp₀, h⟩ := chartEnergy_eventually_regular K hK
  exact ⟨p₀, hp₀, fun p hp z hz => (h p hp z hz).2⟩

end SquareAntiprismVerification
