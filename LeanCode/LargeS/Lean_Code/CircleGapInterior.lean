import Lean_Code.CircleOrder

open Real
noncomputable section
namespace SquareAntiprismVerification

def positiveCircleDifference (a b : ℝ) : ℝ := b - a + if b < a then 2 * Real.pi else 0

lemma positiveCircleDifference_range (a b : ℝ)
    (ha : a ∈ Set.Ioc (-Real.pi) Real.pi) (hb : b ∈ Set.Ioc (-Real.pi) Real.pi) :
    positiveCircleDifference a b ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := by
  unfold positiveCircleDifference
  split_ifs with h <;> constructor <;> linarith [ha.1, ha.2, hb.1, hb.2, Real.pi_pos]

lemma positiveCircleDifference_sin (a b : ℝ) :
    Real.sin (positiveCircleDifference a b) = Real.sin (b - a) := by
  unfold positiveCircleDifference
  split_ifs
  · exact Real.sin_add_two_pi _
  · rw [add_zero]

lemma positiveCircleDifference_cos (a b : ℝ) :
    Real.cos (positiveCircleDifference a b) = Real.cos (a - b) := by
  unfold positiveCircleDifference
  split_ifs
  · rw [Real.cos_add_two_pi]
    simp only [Real.cos_sub]
    ring
  · rw [add_zero]
    simp only [Real.cos_sub]
    ring

lemma arccos_positiveCircleDifference (a b : ℝ)
    (ha : a ∈ Set.Ioc (-Real.pi) Real.pi) (hb : b ∈ Set.Ioc (-Real.pi) Real.pi)
    (hsin : 0 < Real.sin (b - a)) :
    Real.arccos (Real.cos (a - b)) = positiveCircleDifference a b := by
  have hrange := positiveCircleDifference_range a b ha hb
  have hpos : 0 < Real.sin (positiveCircleDifference a b) := by
    rwa [positiveCircleDifference_sin]
  have hlt : positiveCircleDifference a b < Real.pi := by
    by_contra h
    have hnonneg := Real.sin_nonneg_of_mem_Icc
      (show positiveCircleDifference a b - Real.pi ∈ Set.Icc (0 : ℝ) Real.pi from
        ⟨by linarith, by linarith [hrange.2]⟩)
    rw [Real.sin_sub, Real.cos_pi, Real.sin_pi] at hnonneg
    nlinarith
  rw [← positiveCircleDifference_cos, Real.arccos_cos hrange.1 hlt.le]

theorem circleGap_le_positiveDifference {n : ℕ} (θ : Fin (n + 1) → ℝ)
    (hmono : StrictMono θ) (hrange : ∀ i, θ i ∈ Set.Ioc (-Real.pi) Real.pi)
    (i j : Fin (n + 1)) (hji : j ≠ i) :
    circleGap θ i ≤ positiveCircleDifference (θ i) (θ j) := by
  by_cases hi : i = Fin.last n
  · subst i
    have hjlt : j < Fin.last n := lt_of_le_of_ne (Fin.le_last j) hji
    have hjθ : θ j < θ (Fin.last n) := hmono hjlt
    have hlo : θ 0 ≤ θ j := hmono.monotone (Fin.zero_le j)
    simp only [circleGap, Fin.last_add_one, ↓reduceIte, positiveCircleDifference, if_pos hjθ]
    linarith
  · simp only [circleGap, if_neg hi, add_zero]
    by_cases hji' : j < i
    · have hjθ := hmono hji'
      simp only [positiveCircleDifference, if_pos hjθ]
      linarith [(hrange j).1, (hrange (i + 1)).2]
    · have hij : i < j := lt_of_le_of_ne (le_of_not_gt hji') (Ne.symm hji)
      have hnext : i + 1 ≤ j := by
        apply Fin.le_def.mpr
        rw [Fin.val_add_one, if_neg hi]
        exact Nat.succ_le_of_lt (Fin.lt_def.mp hij)
      have hle := hmono.monotone hnext
      have hjθ : ¬ θ j < θ i := not_lt_of_ge (hmono hij).le
      simp only [positiveCircleDifference, if_neg hjθ, add_zero]
      linarith

theorem circleGap_le_angle_of_positive_sin {n : ℕ} (θ : Fin (n + 1) → ℝ)
    (hmono : StrictMono θ) (hrange : ∀ i, θ i ∈ Set.Ioc (-Real.pi) Real.pi)
    (i j : Fin (n + 1)) (hji : j ≠ i) (hsin : 0 < Real.sin (θ j - θ i)) :
    circleGap θ i ≤ Real.arccos (Real.cos (θ i - θ j)) := by
  rw [arccos_positiveCircleDifference (θ i) (θ j) (hrange i) (hrange j) hsin]
  exact circleGap_le_positiveDifference θ hmono hrange i j hji

theorem circleGap_lt_positiveDifference {n : ℕ} (θ : Fin (n + 1) → ℝ)
    (hmono : StrictMono θ) (hrange : ∀ i, θ i ∈ Set.Ioc (-Real.pi) Real.pi)
    (i j : Fin (n + 1)) (hji : j ≠ i) (hjnext : j ≠ i + 1) :
    circleGap θ i < positiveCircleDifference (θ i) (θ j) := by
  by_cases hi : i = Fin.last n
  · subst i
    have hjlt : j < Fin.last n := lt_of_le_of_ne (Fin.le_last j) hji
    have hjθ : θ j < θ (Fin.last n) := hmono hjlt
    have hj0 : j ≠ 0 := by simpa only [Fin.last_add_one] using hjnext
    have hlo : θ 0 < θ j := hmono (lt_of_le_of_ne (Fin.zero_le j) hj0.symm)
    simp only [circleGap, Fin.last_add_one, ↓reduceIte, positiveCircleDifference, if_pos hjθ]
    linarith
  · simp only [circleGap, if_neg hi, add_zero]
    by_cases hji' : j < i
    · have hjθ : θ j < θ i := hmono hji'
      simp only [positiveCircleDifference, if_pos hjθ]
      linarith [(hrange j).1, (hrange (i + 1)).2]
    · have hij : i < j := lt_of_le_of_ne (le_of_not_gt hji') (Ne.symm hji)
      have hnext : i + 1 ≤ j := by
        apply Fin.le_def.mpr
        rw [Fin.val_add_one, if_neg hi]
        exact Nat.succ_le_of_lt (Fin.lt_def.mp hij)
      have hlt := hmono (lt_of_le_of_ne hnext hjnext.symm)
      have hjθ : ¬ θ j < θ i := not_lt_of_ge (hmono hij).le
      simp only [positiveCircleDifference, if_neg hjθ, add_zero]
      linarith

theorem circleGap_lt_angle_of_positive_sin {n : ℕ} (θ : Fin (n + 1) → ℝ)
    (hmono : StrictMono θ) (hrange : ∀ i, θ i ∈ Set.Ioc (-Real.pi) Real.pi)
    (i j : Fin (n + 1)) (hji : j ≠ i) (hjnext : j ≠ i + 1)
    (hsin : 0 < Real.sin (θ j - θ i)) :
    circleGap θ i < Real.arccos (Real.cos (θ i - θ j)) := by
  rw [arccos_positiveCircleDifference (θ i) (θ j) (hrange i) (hrange j) hsin]
  exact circleGap_lt_positiveDifference θ hmono hrange i j hji hjnext

end SquareAntiprismVerification
