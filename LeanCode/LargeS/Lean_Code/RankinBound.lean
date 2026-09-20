import Lean_Code.PackingGeometry

open Real
noncomputable section
namespace SquareAntiprismVerification

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma inner_coordinate_sum (x y : ℝ³) :
    inner ℝ x y = ∑ k : Fin 3, x k * y k := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

/-- The Gram/Frobenius identity, proved by interchanging finite sums. -/
lemma gram_square_sum {ι : Type*} [Fintype ι] (Y : ι → ℝ³) :
    (∑ i, ∑ j, (inner ℝ (Y i) (Y j)) ^ 2) =
      ∑ k : Fin 3, ∑ l : Fin 3, (∑ i, Y i k * Y i l) ^ 2 := by
  calc
    _ = ∑ i, ∑ j, ∑ k : Fin 3, ∑ l : Fin 3,
        (Y i k * Y i l) * (Y j k * Y j l) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [inner_coordinate_sum, pow_two, Finset.sum_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      ring
    _ = ∑ i, ∑ k : Fin 3, ∑ l : Fin 3, ∑ j,
        (Y i k * Y i l) * (Y j k * Y j l) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_comm]
    _ = ∑ k : Fin 3, ∑ l : Fin 3, ∑ i, ∑ j,
        (Y i k * Y i l) * (Y j k * Y j l) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro l hl
      rw [pow_two, Finset.sum_mul]
      simp only [Finset.mul_sum]

lemma gram_square_lower_bound {ι : Type*} [Fintype ι] (Y : ι → ℝ³)
    (hY : ∀ i, ‖Y i‖ = 1) :
    (Fintype.card ι : ℝ) ^ 2 ≤ 3 * ∑ i, ∑ j, (inner ℝ (Y i) (Y j)) ^ 2 := by
  let A : Fin 3 → Fin 3 → ℝ := fun k l => ∑ i, Y i k * Y i l
  have htrace : ∑ k : Fin 3, A k k = (Fintype.card ι : ℝ) := by
    dsimp [A]
    rw [Finset.sum_comm]
    have hnorm (i : ι) : (∑ k : Fin 3, Y i k * Y i k) = 1 := by
      rw [← inner_coordinate_sum, real_inner_self_eq_norm_sq, hY i]
      norm_num
    simp only [hnorm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3))
    (fun _ => (1 : ℝ)) (fun k => A k k)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, mul_one, htrace] at hcs
  have hdiag : (∑ k : Fin 3, A k k ^ 2) ≤ ∑ k : Fin 3, ∑ l : Fin 3, A k l ^ 2 := by
    apply Finset.sum_le_sum
    intro k hk
    exact Finset.single_le_sum (fun l hl => sq_nonneg _) (Finset.mem_univ k)
  rw [gram_square_sum]
  exact hcs.trans (mul_le_mul_of_nonneg_left hdiag (by norm_num))

/-- Rankin's elementary bound in dimension three: at most six unit vectors
can have pairwise nonpositive inner products. -/
theorem rankin_nonacute_bound {ι : Type*} [Fintype ι] (Y : ι → ℝ³)
    (hY : ∀ i, ‖Y i‖ = 1)
    (hsep : ∀ i j, i ≠ j → inner ℝ (Y i) (Y j) ≤ 0) : Fintype.card ι ≤ 6 := by
  classical
  have hsum : 0 ≤ ∑ i, ∑ j, inner ℝ (Y i) (Y j) := by
    have h := sq_nonneg ‖∑ i, Y i‖
    rw [← real_inner_self_eq_norm_sq] at h
    rw [sum_inner] at h
    simpa only [inner_sum] using h
  have hpoint (i j : ι) :
      inner ℝ (Y i) (Y j) ^ 2 ≤ (if i = j then 2 else 0) - inner ℝ (Y i) (Y j) := by
    by_cases hij : i = j
    · subst j
      norm_num [real_inner_self_eq_norm_sq, hY]
    · have hlow : -1 ≤ inner ℝ (Y i) (Y j) := by
        have h := abs_real_inner_le_norm (Y i) (Y j)
        rw [hY i, hY j, one_mul] at h
        exact (abs_le.mp h).1
      have hhigh := hsep i j hij
      simp only [if_neg hij]
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ inner ℝ (Y i) (Y j) + 1) hhigh]
  have hupp : (∑ i, ∑ j, inner ℝ (Y i) (Y j) ^ 2) ≤ 2 * (Fintype.card ι : ℝ) := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) =>
      Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) => hpoint i j))
    simp only [Finset.sum_sub_distrib] at h
    have hdiag : (∑ i : ι, ∑ j : ι, if i = j then (2 : ℝ) else 0) =
        2 * (Fintype.card ι : ℝ) := by simp [mul_comm]
    rw [hdiag] at h
    linarith
  have hlow := gram_square_lower_bound Y hY
  have hcard : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hcardle : (Fintype.card ι : ℝ) ≤ 6 := by nlinarith
  exact_mod_cast hcardle

theorem eight_points_have_positive_inner (Y : Fin 8 → ℝ³)
    (hY : ∀ i, ‖Y i‖ = 1) : ∃ i j, i ≠ j ∧ 0 < inner ℝ (Y i) (Y j) := by
  by_contra h
  push_neg at h
  have hbound := rankin_nonacute_bound Y hY h
  norm_num at hbound

end SquareAntiprismVerification
