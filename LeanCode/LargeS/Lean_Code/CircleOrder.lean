import Lean_Code.CirclePhase

open Real
noncomputable section
namespace SquareAntiprismVerification

/-- Positive-angle gaps in an increasing enumeration of circle phases.
The last edge includes the wrap at the chosen phase cut. -/
def circleGap {n : ℕ} (θ : Fin (n + 1) → ℝ) (i : Fin (n + 1)) : ℝ :=
  θ (i + 1) - θ i + if i = Fin.last n then 2 * Real.pi else 0

lemma circleGap_sum {n : ℕ} (θ : Fin (n + 1) → ℝ) :
    ∑ i, circleGap θ i = 2 * Real.pi := by
  classical
  have hshift : ∑ i : Fin (n + 1), θ (i + 1) = ∑ i, θ i :=
    Equiv.sum_comp (Equiv.addRight (1 : Fin (n + 1))) θ
  simp only [circleGap, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hshift, sub_self, zero_add]
  simp

lemma circleGap_pos {n : ℕ} (θ : Fin (n + 1) → ℝ)
    (hmono : StrictMono θ) (hrange : ∀ i, θ i ∈ Set.Ioc (-Real.pi) Real.pi)
    (i : Fin (n + 1)) : 0 < circleGap θ i := by
  by_cases hi : i = Fin.last n
  · subst i
    simp only [circleGap, Fin.last_add_one, ↓reduceIte]
    linarith [(hrange 0).1, (hrange (Fin.last n)).2]
  · have hlt : i < i + 1 := by
      apply Fin.lt_def.mpr
      rw [Fin.val_add_one, if_neg hi]
      omega
    simpa only [circleGap, if_neg hi, add_zero] using sub_pos.mpr (hmono hlt)

lemma circleGap_cos {n : ℕ} (θ : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    Real.cos (circleGap θ i) = Real.cos (θ i - θ (i + 1)) := by
  unfold circleGap
  split_ifs
  · rw [Real.cos_add_two_pi]
    simp only [Real.cos_sub]
    ring
  · rw [add_zero]
    simp only [Real.cos_sub]
    ring

lemma circleGap_sin {n : ℕ} (θ : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    Real.sin (circleGap θ i) = Real.sin (θ (i + 1) - θ i) := by
  unfold circleGap
  split_ifs
  · exact Real.sin_add_two_pi _
  · rw [add_zero]

/-- A gap at least a semicircle leaves all the listed phases in the
opposite closed semicircle. This includes the wraparound gap. -/
theorem large_circleGap_semicircle {n : ℕ} (θ : Fin (n + 1) → ℝ)
    (hmono : StrictMono θ) (hrange : ∀ i, θ i ∈ Set.Ioc (-Real.pi) Real.pi)
    (i : Fin (n + 1)) (hgap : Real.pi ≤ circleGap θ i) :
    ∃ t : ℝ, ∀ j, Real.cos (t - θ j) ≤ 0 := by
  by_cases hi : i = Fin.last n
  · subst i
    simp only [circleGap, Fin.last_add_one, ↓reduceIte] at hgap
    refine ⟨(θ (Fin.last n) + θ 0 + 2 * Real.pi) / 2, ?_⟩
    intro j
    have hlo : θ 0 ≤ θ j := hmono.monotone (Fin.zero_le j)
    have hhi : θ j ≤ θ (Fin.last n) := hmono.monotone (Fin.le_last j)
    apply Real.cos_nonpos_of_pi_div_two_le_of_le <;> linarith
  · simp only [circleGap, if_neg hi, add_zero] at hgap
    refine ⟨(θ i + θ (i + 1)) / 2, ?_⟩
    intro j
    by_cases hji : j ≤ i
    · have hj := hmono.monotone hji
      apply Real.cos_nonpos_of_pi_div_two_le_of_le
      · linarith
      · linarith [(hrange j).1, (hrange (i + 1)).2]
    · have hnext : i + 1 ≤ j := by
        apply Fin.le_def.mpr
        rw [Fin.val_add_one, if_neg hi]
        have hij : i < j := lt_of_not_ge hji
        exact Nat.succ_le_of_lt (Fin.lt_def.mp hij)
      have hj := hmono.monotone hnext
      rw [show Real.cos ((θ i + θ (i + 1)) / 2 - θ j) =
        Real.cos (θ j - (θ i + θ (i + 1)) / 2) by
          simp only [Real.cos_sub]; ring]
      apply Real.cos_nonpos_of_pi_div_two_le_of_le
      · linarith
      · linarith [(hrange j).2, (hrange i).1]

end SquareAntiprismVerification
