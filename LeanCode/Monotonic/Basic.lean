import LeanCode.Monotonic.Definitions

noncomputable section
open Real Set
open scoped BigOperators ContDiff
namespace SquareAntiprismCounterexample

lemma sqrt_two_pos : 0 < √(2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
lemma sqrt_two_sq : (√(2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
lemma sqrt_two_bounds : 1 < √(2 : ℝ) ∧ √(2 : ℝ) < 10 / 7 := by
  have hp := sqrt_two_pos
  have hs := sqrt_two_sq
  constructor <;> nlinarith
lemma sqrt_two_lt_two : √(2 : ℝ) < 2 := by linarith [sqrt_two_bounds.2]
lemma inv_sqrt_two : (√(2 : ℝ))⁻¹ = √2 / 2 := by
  apply (inv_eq_iff_eq_inv).2
  field_simp
  nlinarith [sqrt_two_sq]
lemma aStar_mem : aStar ∈ Ioo (0 : ℝ) 1 := by norm_num [aStar]
lemma n_pos : (0 : ℝ) < n := by norm_num [n]
lemma dStar_pos : 0 < dStar := by norm_num [dStar]
lemma dStar_gt_one : 1 < dStar := by norm_num [dStar]

lemma distance_domains {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    dA a ∈ Ioo (0 : ℝ) 4 ∧ dB a ∈ Ioo (0 : ℝ) 4 ∧
    dC a ∈ Ioo (0 : ℝ) 4 ∧ dD a ∈ Ioo (0 : ℝ) 4 := by
  have hs := sqrt_two_pos
  have ht := sqrt_two_lt_two
  have hc : 0 < (2 - √(2 : ℝ)) * (1 - a) := mul_pos (by linarith) (by linarith [ha.2])
  have hd : 0 < (2 + √(2 : ℝ)) * (1 - a) := mul_pos (by linarith) (by linarith [ha.2])
  have hc' : 0 < (2 + √(2 : ℝ)) * (1 - a) := hd
  have hd' : 0 < (2 - √(2 : ℝ)) * (1 - a) := hc
  dsimp [dA, dB, dC, dD, Set.mem_Ioo]
  constructor
  · constructor <;> linarith [ha.1, ha.2]
  constructor
  · constructor <;> linarith [ha.1, ha.2]
  constructor <;> constructor <;> nlinarith [ha.1, ha.2]

lemma distances_at_star : dA aStar = dStar ∧ dB aStar = 2*dStar ∧
    dC aStar = (46-13*√2)/18 ∧ dD aStar = (46+13*√2)/18 := by
  dsimp [dA, dB, dC, dD, aStar, dStar]
  constructor
  · norm_num
  constructor
  · norm_num
  constructor <;> ring

lemma norm_sq_coordinates (p : Point) : ‖p‖ ^ 2 = p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 := by
  simpa [Fin.sum_univ_succ, add_assoc] using EuclideanSpace.real_norm_sq_eq p

lemma two_mul_energy (v : ℝ → ℝ) (Y : Fin 8 → Point) :
    2 * Ef v Y = ∑ i : Fin 8, ∑ j : Fin 8,
      if i = j then 0 else v (‖Y i - Y j‖ ^ 2) := by
  have hp (i j : Fin 8) :
      (if i = j then 0 else v (‖Y i - Y j‖ ^ 2)) =
      (if i < j then v (‖Y i - Y j‖ ^ 2) else 0) +
      (if j < i then v (‖Y j - Y i‖ ^ 2) else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · simp [h]
    · simp [h, ne_of_gt h, not_lt_of_ge h.le, norm_sub_rev]
  simp_rw [hp, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j : Fin 8 => if j < i then v (‖Y j - Y i‖ ^ 2) else 0)]
  simp only [Ef, Finset.sum_filter]
  ring

lemma energy_congruent (v : ℝ → ℝ) {Y Z : Fin 8 → Point} (hYZ : Congruent Y Z) :
    Ef v Y = Ef v Z := by
  obtain ⟨U, σ, hU⟩ := hYZ
  apply (mul_left_cancel₀ (by norm_num : (2:ℝ) ≠ 0))
  rw [two_mul_energy, two_mul_energy]
  simp_rw [hU, ← U.map_sub, U.norm_map]
  calc
    _ = ∑ i : Fin 8, ∑ j : Fin 8,
        if σ i = σ j then 0 else v (‖Z (σ i) - Z (σ j)‖ ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i = j <;> simp [hij, σ.injective.eq_iff]
    _ = ∑ i : Fin 8, ∑ j : Fin 8,
        if σ i = j then 0 else v (‖Z (σ i) - Z j‖ ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Equiv.sum_comp σ (fun j => if σ i = j then 0 else v (‖Z (σ i) - Z j‖ ^ 2))
    _ = _ := Equiv.sum_comp σ (fun i => ∑ j : Fin 8,
        if i = j then 0 else v (‖Z i - Z j‖ ^ 2))

end SquareAntiprismCounterexample
