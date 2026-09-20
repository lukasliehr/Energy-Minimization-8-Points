import Lean_Code.Definitions

set_option maxHeartbeats 800000

open Real

noncomputable section

namespace SquareAntiprismVerification

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The trigonometric definition of `X` evaluated at the eight displayed
angles. -/
def Xc (a : ℝ) : Fin 8 → ℝ³ :=
  ![!₂[r a, 0, h a],
    !₂[0, r a, h a],
    !₂[-r a, 0, h a],
    !₂[0, -r a, h a],
    !₂[r a * (√2 / 2), r a * (√2 / 2), -h a],
    !₂[-r a * (√2 / 2), r a * (√2 / 2), -h a],
    !₂[-r a * (√2 / 2), -r a * (√2 / 2), -h a],
    !₂[r a * (√2 / 2), -r a * (√2 / 2), -h a]]

theorem X_eq_Xc (a : ℝ) : X a = Xc a := by
  funext i
  rcases finEight_split i with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [X, Fin.append_left]
    fin_cases j <;>
      simp [Xc, Real.cos_add, Real.sin_add, show (2 : ℝ) * π / 2 = π by ring,
        show (3 : ℝ) * π / 2 = π + π / 2 by ring]
  · rw [X, Fin.append_right]
    fin_cases j <;>
      simp [Xc, Real.cos_add, Real.sin_add, show (2 : ℝ) * π / 2 = π by ring,
        show (3 : ℝ) * π / 2 = π + π / 2 by ring] <;> ring

lemma norm_vec3 (x y z : ℝ) :
    ‖(!₂[x, y, z] : ℝ³)‖ = √(x ^ 2 + y ^ 2 + z ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs]
  congr 1
  ring

lemma norm_vec3_sub (x y z u v w : ℝ) :
    ‖(!₂[x, y, z] : ℝ³) - !₂[u, v, w]‖ =
      √((x - u) ^ 2 + (y - v) ^ 2 + (z - w) ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  simp [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs]
  congr 1
  ring

lemma finEight_pair_sum (f : Fin 8 → Fin 8 → ℝ) :
    (∑ i : Fin 8, ∑ j : Fin 8 with i < j, f i j) =
      f 0 1 + f 0 2 + f 0 3 + f 0 4 + f 0 5 + f 0 6 + f 0 7 +
      f 1 2 + f 1 3 + f 1 4 + f 1 5 + f 1 6 + f 1 7 +
      f 2 3 + f 2 4 + f 2 5 + f 2 6 + f 2 7 +
      f 3 4 + f 3 5 + f 3 6 + f 3 7 +
      f 4 5 + f 4 6 + f 4 7 + f 5 6 + f 5 7 + f 6 7 := by
  simp_rw [Finset.sum_filter]
  simp only [Fin.sum_univ_eight]
  simp +decide
  ring

theorem energy_linearIsometry (s : ℝ) (Y : Fin 8 → ℝ³)
    (U : ℝ³ ≃ₗᵢ[ℝ] ℝ³) : E s (fun i => U (Y i)) = E s Y := by
  unfold E
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [← map_sub]
  rw [U.norm_map]

lemma two_mul_pairSum_of_symmetric (f : Fin 8 → Fin 8 → ℝ)
    (hsymm : ∀ i j, f i j = f j i) :
    2 * (∑ i : Fin 8, ∑ j : Fin 8 with i < j, f i j) =
      ∑ i : Fin 8, ∑ j : Fin 8, if i = j then 0 else f i j := by
  rw [finEight_pair_sum]
  simp only [Fin.sum_univ_eight]
  simp [hsymm]
  ring

lemma offDiagSum_perm (σ : Equiv.Perm (Fin 8)) (f : Fin 8 → Fin 8 → ℝ) :
    (∑ i : Fin 8, ∑ j : Fin 8, if i = j then 0 else f (σ i) (σ j)) =
      ∑ i : Fin 8, ∑ j : Fin 8, if i = j then 0 else f i j := by
  have hrewrite :
      (∑ i : Fin 8, ∑ j : Fin 8, if i = j then 0 else f (σ i) (σ j)) =
        ∑ i : Fin 8, ∑ j : Fin 8,
          if σ i = σ j then 0 else f (σ i) (σ j) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply if_congr (σ.injective.eq_iff.symm)
    · rfl
    · rfl
  rw [hrewrite]
  rw [Equiv.sum_comp σ
    (fun k => ∑ j : Fin 8, if k = σ j then 0 else f k (σ j))]
  apply Finset.sum_congr rfl
  intro i hi
  exact Equiv.sum_comp σ (fun k => if i = k then 0 else f i k)

theorem energy_permutation (s : ℝ) (Y : Fin 8 → ℝ³)
    (σ : Equiv.Perm (Fin 8)) : E s (fun i => Y (σ i)) = E s Y := by
  let f : Fin 8 → Fin 8 → ℝ := fun i j => ‖Y i - Y j‖ ^ (-s)
  have hsymm : ∀ i j, f i j = f j i := by
    intro i j
    simp only [f]
    have hsub : Y j - Y i = -(Y i - Y j) := by abel
    rw [hsub, norm_neg]
  have h₁ := two_mul_pairSum_of_symmetric (fun i j => f (σ i) (σ j))
    (fun i j => hsymm (σ i) (σ j))
  have h₂ := two_mul_pairSum_of_symmetric f hsymm
  have hp := offDiagSum_perm σ f
  unfold E
  dsimp only [f] at h₁ h₂ hp ⊢
  linarith

theorem congruent_energy {s : ℝ} {Y Z : Fin 8 → ℝ³}
    (hYZ : Congruent Y Z) : E s Z = E s Y := by
  obtain ⟨U, σ, h⟩ := hYZ
  have hz : Z = fun i => U (Y (σ i)) := funext h
  rw [hz, energy_linearIsometry, energy_permutation]

lemma sqrt_rpow_neg (x s : ℝ) (hx : 0 ≤ x) :
    (√x) ^ (-s) = x ^ (-s / 2) := by
  rw [Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul hx]
  congr 1
  ring

theorem energy_X_eq_G (s a : ℝ) (ha : a ∈ Set.Ioo (0 : ℝ) 1) : E s (X a) = G s a := by
  rw [X_eq_Xc]
  have hra : (√(1 - a)) ^ 2 = 1 - a := Real.sq_sqrt (by linarith [ha.2])
  have hha : (√a) ^ 2 = a := Real.sq_sqrt (le_of_lt ha.1)
  have hs2 : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold E
  rw [finEight_pair_sum]
  simp [Xc, norm_vec3_sub, r, h, hra, hha, hs2]
  ring_nf
  simp_rw [hra, hha, hs2]
  ring_nf
  have hdouble : √(1 - a) * 2 = √(dB a) := by
    rw [← Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 2))]
    congr 1
    rw [mul_pow, hra]
    unfold dB
    ring
  rw [hdouble]
  rw [show 2 - a * 2 = dA a by unfold dA; ring]
  rw [show 2 + a * 2 + a * √2 - √2 = dC a by unfold dC; ring]
  rw [show 2 + a * 2 - a * √2 + √2 = dD a by unfold dD; ring]
  rw [show 4 - a * 4 = dB a by unfold dB; ring]
  have hs2nonneg : 0 ≤ √(2 : ℝ) := Real.sqrt_nonneg 2
  have hs2lt : √(2 : ℝ) < 2 := by nlinarith [hs2]
  have hAn : 0 ≤ dA a := by unfold dA; linarith [ha.2]
  have hBn : 0 ≤ dB a := by unfold dB; linarith [ha.2]
  have hCn : 0 ≤ dC a := by unfold dC; nlinarith [ha.1]
  have hDn : 0 ≤ dD a := by unfold dD; nlinarith [ha.1]
  rw [sqrt_rpow_neg (dA a) s hAn, sqrt_rpow_neg (dB a) s hBn,
    sqrt_rpow_neg (dC a) s hCn, sqrt_rpow_neg (dD a) s hDn]
  unfold G
  ring

end SquareAntiprismVerification
