import LeanCode.Monotonic.Definitions

noncomputable section
open Set Filter
open scoped Topology
namespace SquareAntiprismCounterexample

lemma interval_continuous {F F1 : ℝ → ℝ} {l r : ℝ}
    (hF : ∀ x ∈ Ioo l r, HasDerivAt F (F1 x) x) {a b : ℝ}
    (ha : l < a) (hb : b < r) : ContinuousOn F (Icc a b) := by
  intro x hx
  exact (hF x ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩).continuousAt.continuousWithinAt

lemma stationary_minimum {F F1 F2 : ℝ → ℝ} {a0 : ℝ}
    (ha0 : a0 ∈ Ioo (0:ℝ) 1)
    (hF : ∀ x ∈ Ioo (0:ℝ) 1, HasDerivAt F (F1 x) x)
    (hF1 : ∀ x ∈ Ioo (0:ℝ) 1, HasDerivAt F1 (F2 x) x)
    (hF2 : ∀ x ∈ Ioo (0:ℝ) 1, 0 < F2 x)
    (hzero : F1 a0 = 0) : ∀ a ∈ Ioo (0:ℝ) 1, F a0 ≤ F a := by
  have hmono : StrictMonoOn F1 (Ioo (0:ℝ) 1) := by
    intro x hx y hy hxy
    obtain ⟨c, hc, he⟩ := exists_hasDerivAt_eq_slope F1 F2 hxy
      (interval_continuous hF1 hx.1 hy.2)
      (fun t ht => hF1 t ⟨lt_trans hx.1 ht.1, lt_trans ht.2 hy.2⟩)
    have hp := hF2 c ⟨lt_trans hx.1 hc.1, lt_trans hc.2 hy.2⟩
    have : 0 < (F1 y - F1 x) / (y-x) := he ▸ hp
    have := (div_pos_iff_of_pos_right (sub_pos.mpr hxy)).mp this
    linarith
  intro a ha
  rcases lt_trichotomy a a0 with h | rfl | h
  · obtain ⟨c, hc, he⟩ := exists_hasDerivAt_eq_slope F F1 h
      (interval_continuous hF ha.1 ha0.2)
      (fun t ht => hF t ⟨lt_trans ha.1 ht.1, lt_trans ht.2 ha0.2⟩)
    have hp : F1 c < 0 := by
      rw [← hzero]
      exact hmono ⟨lt_trans ha.1 hc.1, lt_trans hc.2 ha0.2⟩ ha0 hc.2
    have : (F a0 - F a) / (a0-a) < 0 := he ▸ hp
    have := (div_lt_iff₀ (sub_pos.mpr h)).mp this
    linarith
  · exact le_rfl
  · obtain ⟨c, hc, he⟩ := exists_hasDerivAt_eq_slope F F1 h
      (interval_continuous hF ha0.1 ha.2)
      (fun t ht => hF t ⟨lt_trans ha0.1 ht.1, lt_trans ht.2 ha.2⟩)
    have hp : 0 < F1 c := by
      rw [← hzero]
      exact hmono ha0 ⟨lt_trans ha0.1 hc.1, lt_trans hc.2 ha.2⟩ hc.1
    have : 0 < (F a - F a0) / (a-a0) := he ▸ hp
    have := (div_pos_iff_of_pos_right (sub_pos.mpr h)).mp this
    linarith

lemma local_descent {H H1 H2 : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hH : ∀ x ∈ Ioo (-δ) δ, HasDerivAt H (H1 x) x)
    (hH1 : ∀ x ∈ Ioo (-δ) δ, HasDerivAt H1 (H2 x) x)
    (hH2 : ContinuousAt H2 0) (hz : H1 0 = 0) (hn : H2 0 < 0) :
    ∃ u, 0 < u ∧ u < δ ∧ H u < H 0 := by
  have hev : ∀ᶠ x in nhds (0:ℝ), H2 x < 0 :=
    hH2.eventually_lt continuousAt_const hn
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp hev
  let ρ := min δ ε / 2
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρδ : ρ < δ := by dsimp [ρ]; linarith [min_le_left δ ε]
  have hρε : ρ < ε := by dsimp [ρ]; linarith [min_le_right δ ε]
  have hneg : ∀ t ∈ Ioo (0:ℝ) ρ, H1 t < 0 := by
    intro t ht
    obtain ⟨c, hc, hce⟩ := exists_hasDerivAt_eq_slope H1 H2 ht.1
      (interval_continuous hH1 (by linarith) (by linarith [ht.2]))
      (fun x hx => hH1 x ⟨by linarith [hx.1], by linarith [hx.2, ht.2]⟩)
    have hcn : H2 c < 0 := he (by simpa [Real.dist_eq, abs_of_pos hc.1] using
      (show c < ε by linarith [hc.2, ht.2]))
    rw [hz, sub_zero, sub_zero] at hce
    have := (div_lt_iff₀ ht.1).mp (hce ▸ hcn)
    simpa using this
  let u := ρ/2
  have hu : 0 < u := by dsimp [u]; positivity
  have huρ : u < ρ := by dsimp [u]; linarith
  obtain ⟨c, hc, hce⟩ := exists_hasDerivAt_eq_slope H H1 hu
    (interval_continuous hH (by linarith) (by linarith))
    (fun x hx => hH x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  have hcn := hneg c ⟨hc.1, lt_trans hc.2 huρ⟩
  rw [sub_zero] at hce
  have := (div_lt_iff₀ hu).mp (hce ▸ hcn)
  exact ⟨u, hu, by linarith, by linarith⟩

end SquareAntiprismCounterexample
