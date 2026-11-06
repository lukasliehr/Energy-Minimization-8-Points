import ThomsonNegative.Reduction.SelectiveEquality
import ThomsonNegative.GramFactors

/-!
# Weighted row bounds replace all corrected-block spectral tests

The finite checker only has to bound weighted absolute row sums of the
correction after congruence by the floor metric. Everything connecting those
bounds to positivity is an ordinary real-algebra theorem, independent of cells.
-/
noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Reduction

lemma weighted_two_mul_abs_le (x y a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    2 * |x| * |y| ≤ b / a * x^2 + a / b * y^2 := by
  apply (mul_le_mul_iff_of_pos_right (mul_pos ha hb)).mp
  have hs := sq_nonneg (b * |x| - a * |y|)
  have he : (b / a * x^2 + a / b * y^2) * (a*b) =
      b^2*x^2+a^2*y^2 := by field_simp
  rw [he]
  nlinarith [sq_abs x, sq_abs y]

/-- The weighted row-sum bound controls the quadratic form in the ordinary
Euclidean metric because the real correction is symmetric. -/
theorem quadratic_abs_le_weighted_rows {n : ℕ} (C : Mat n)
    (hC : ∀ i j, C i j = C j i) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (ρ : ℝ) (hrow : ∀ i, ∑ j, |C i j| * w j / w i ≤ ρ)
    (v : Fin n → ℝ) : |quadratic C v| ≤ ρ * ∑ i, (v i)^2 := by
  have hp (i j : Fin n) :
      2 * (|C i j| * |v i| * |v j|) ≤
        |C i j| * (w j / w i * (v i)^2 + w i / w j * (v j)^2) := by
    have h := mul_le_mul_of_nonneg_left
      (weighted_two_mul_abs_le (v i) (v j) (w i) (w j) (hw i) (hw j))
      (abs_nonneg (C i j))
    nlinarith
  have he :
      ∑ i, ∑ j, |C i j| * (w i / w j * (v j)^2) =
      ∑ i, ∑ j, |C i j| * (w j / w i * (v i)^2) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hC j i]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hp i j))
  simp only [Finset.sum_add_distrib, mul_add, ← Finset.mul_sum] at hsum
  rw [he] at hsum
  have hbound :
      ∑ i, ∑ j, |C i j| * (w j / w i * (v i)^2) ≤
      ρ * ∑ i, (v i)^2 := by
    calc
      _ = ∑ i, (∑ j, |C i j| * w j / w i) * (v i)^2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ ≤ ∑ i, ρ * (v i)^2 := Finset.sum_le_sum
        (fun i _ => mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg (v i)))
      _ = _ := (Finset.mul_sum _ _ _).symm
  have habs : |quadratic C v| ≤ ∑ i, ∑ j, |C i j| * |v i| * |v j| := by
    simp only [quadratic, dotProduct, Matrix.mulVec, Finset.mul_sum]
    calc
      _ ≤ ∑ i, |∑ j, v i * (C i j * v j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |v i * (C i j * v j)| :=
        Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ = _ := by simp [abs_mul, mul_comm, mul_left_comm]
  linarith

/-- An arbitrary symmetric entrywise majorant suffices. The positive integer
weights in a certificate need no trusted optimization algorithm. -/
theorem quadratic_abs_le_of_majorant {n : ℕ} (C M : Mat n)
    (hC : ∀ i j, C i j = C j i) (hM : ∀ i j, |C i j| ≤ M i j)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (ρ : ℝ)
    (hrow : ∀ i, ∑ j, M i j * w j / w i ≤ ρ)
    (v : Fin n → ℝ) : |quadratic C v| ≤ ρ * ∑ i, (v i)^2 := by
  apply quadratic_abs_le_weighted_rows C hC w hw ρ _ v
  intro i
  exact le_trans (Finset.sum_le_sum (fun j _ =>
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hM i j) (hw j).le) (hw i).le)) (hrow i)

/-- The strict correction/floor inequality is a positive-definiteness proof. -/
theorem corrected_identity_posDef {n : ℕ} (C : Mat n)
    (hC : ∀ i j, C i j = C j i) (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (ρ δ : ℝ) (hrow : ∀ i, ∑ j, |C i j| * w j / w i ≤ ρ)
    (hgap : ρ < δ) : (δ • (1 : Mat n) + C).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · apply Matrix.IsHermitian.add
    · exact (Matrix.isHermitian_one (α := ℝ)).smul (IsSelfAdjoint.all δ)
    · ext i j
      simp only [Matrix.conjTranspose_apply, star_trivial]
      exact hC j i
  · intro v hv
    have hs : 0 < ∑ i, (v i)^2 := by
      apply (Finset.sum_pos_iff_of_nonneg (fun i _ => sq_nonneg (v i))).mpr
      have hv' : ∃ i, v i ≠ 0 := by
        by_contra! h
        exact hv (funext h)
      obtain ⟨i, hi⟩ := hv'
      exact ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
    have hb := quadratic_abs_le_weighted_rows C hC w hw ρ hrow v
    have hl := neg_abs_le (quadratic C v)
    have he : star v ⬝ᵥ ((δ • (1 : Mat n) + C).mulVec v) =
        δ * ∑ i, (v i)^2 + quadratic C v := by
      simp [quadratic, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct,
        Finset.mul_sum, pow_two, mul_add, Finset.sum_add_distrib, mul_left_comm]
    rw [he]
    nlinarith

/-- The floor metric can be any exactly invertible matrix. Initial factors
are arbitrary: their construction is not a premise of the proof. -/
theorem corrected_factor_block_posDef {n r k : ℕ} (K C : Mat n)
    (hK : IsUnit K) (hC : ∀ i j, C i j = C j i)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (ρ δ : ℝ)
    (hrow : ∀ i, ∑ j, |C i j| * w j / w i ≤ ρ) (hgap : ρ < δ)
    (b : Fin k → ℝ) (hb : ∀ i, 0 ≤ b i)
    (L : Fin k → Matrix (Fin n) (Fin r) ℝ) :
    ((∑ i, b i • (L i * (L i).transpose)) +
      K * (δ • (1 : Mat n) + C) * K.transpose).PosDef := by
  have hc := corrected_identity_posDef C hC w hw ρ δ hrow hgap
  have h := hc.mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit hK)
  simpa using h.posSemidef_add (weighted_factor_gram_psd b L hb)

/-- Direct interface for a stored inverse metric. Checking its exact product
identity and weighted row bounds proves positivity of the corrected block. -/
theorem corrected_block_of_inverse {n r k : ℕ} (K J Δ : Mat n)
    (hKJ : K * J = 1) (hΔ : ∀ i j, Δ i j = Δ j i)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (ρ δ : ℝ)
    (hrow : ∀ i, ∑ j, |(J * Δ * J.transpose) i j| * w j / w i ≤ ρ)
    (hgap : ρ < δ) (b : Fin k → ℝ) (hb : ∀ i, 0 ≤ b i)
    (L : Fin k → Matrix (Fin n) (Fin r) ℝ) :
    ((∑ i, b i • (L i * (L i).transpose)) +
      δ • (K * K.transpose) + Δ).PosDef := by
  have hDt : Δ.transpose = Δ := by ext i j; exact hΔ j i
  have hCt : (J * Δ * J.transpose).transpose = J * Δ * J.transpose := by
    simp [Matrix.transpose_mul, hDt, Matrix.mul_assoc]
  have hC (i j : Fin n) : (J * Δ * J.transpose) i j =
      (J * Δ * J.transpose) j i := by
    exact congrArg (fun A : Mat n => A j i) hCt
  have he : K * (J * Δ * J.transpose) * K.transpose = Δ := by
    calc
      _ = (K * J) * Δ * (K * J).transpose := by
        simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Δ := by rw [hKJ]; simp
  have h := corrected_factor_block_posDef K (J * Δ * J.transpose)
    (IsUnit.of_mul_eq_one _ hKJ) hC w hw ρ δ hrow hgap b hb L
  simpa only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, he, add_assoc] using h

/-- Nonnegativity of all Bernstein factor weights is analytic on the cell. -/
theorem bernstein_weight_nonneg (N i : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    0 ≤ (Nat.choose N i : ℝ) * ((1+t)/2)^i * ((1-t)/2)^(N-i) := by
  have ha : 0 ≤ (1+t)/2 := by linarith [ht.1]
  have hb : 0 ≤ (1-t)/2 := by linarith [ht.2]
  positivity

#print axioms quadratic_abs_le_weighted_rows
#print axioms quadratic_abs_le_of_majorant
#print axioms corrected_identity_posDef
#print axioms corrected_factor_block_posDef
#print axioms corrected_block_of_inverse
#print axioms bernstein_weight_nonneg
end ThomsonNegative.Reduction
