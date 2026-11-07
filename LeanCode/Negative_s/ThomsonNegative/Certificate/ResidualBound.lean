import ThomsonNegative.Reduction.CorrectionFloor

/-!
# A single soundness interface for all residual corrections

Contract the exact polynomial centers before bounding them. Retain the entire
independent error box. No cancellation between centers is discarded early.
-/
noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Certificate

def unitVector (n : ℕ) (i : Fin n) : Fin n → ℝ := Pi.single i 1

lemma sum_unitVector (n : ℕ) (x : Fin n → ℝ) :
    (∑ i, x i • unitVector n i) = x := by
  classical
  ext j
  simp [unitVector,Finset.sum_apply,Pi.single_apply]

lemma linearMap_coordinates {n : ℕ} (L : (Fin n → ℝ) →ₗ[ℝ] ℝ) (x : Fin n → ℝ) :
    L x = ∑ i, x i * L (unitVector n i) := by
  calc
    L x = L (∑ i, x i • unitVector n i) := congrArg L (sum_unitVector n x).symm
    _ = _ := by rw [map_sum]; simp only [map_smul,smul_eq_mul]

/-- Error propagation uses absolute column bounds of the exact linear map. -/
theorem linearMap_box_bound {n : ℕ} (L : (Fin n → ℝ) →ₗ[ℝ] ℝ)
    (x e m : Fin n → ℝ) (hx : ∀ i, |x i| ≤ e i)
    (hm : ∀ i, |L (unitVector n i)| ≤ m i) :
    |L x| ≤ ∑ i, e i * m i := by
  rw [linearMap_coordinates]
  calc
    _ ≤ ∑ i, |x i * L (unitVector n i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul (hx i) (hm i) (abs_nonneg _) ((abs_nonneg _).trans (hx i))

/-- One exact-center calculation and a full error box suffice for each scalar
entry of every corrected block, including after a fixed congruence. -/
theorem residual_correction_bound {n d : ℕ} (L : (Fin n → ℝ) →ₗ[ℝ] ℝ)
    (r : Fin n → ℝ) (center : Fin d → Fin n → ℝ)
    (error column : Fin n → ℝ) (centerBound : Fin d → ℝ) (t : ℝ)
    (ht : |t| ≤ 1)
    (hr : ∀ i, |r i - ∑ k : Fin d, center k i * t^(k:ℕ)| ≤ error i)
    (hc : ∀ k, |L (center k)| ≤ centerBound k)
    (he : ∀ i, |L (unitVector n i)| ≤ column i) :
    |L r| ≤ (∑ k, centerBound k) + ∑ i, error i * column i := by
  let p : Fin n → ℝ := ∑ k : Fin d, t^(k:ℕ) • center k
  have hp (i : Fin n) : p i = ∑ k : Fin d, center k i * t^(k:ℕ) := by
    simp only [p,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_comm]
  have herr : ∀ i, |(r-p) i| ≤ error i := by
    intro i
    simpa only [Pi.sub_apply,hp] using hr i
  have he' := linearMap_box_bound L (r-p) error column herr he
  have hpoly : |L p| ≤ ∑ k, centerBound k := by
    simp only [p,map_sum,map_smul,smul_eq_mul]
    calc
      _ ≤ ∑ k : Fin d, |t^(k:ℕ) * L (center k)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k hk
        rw [abs_mul,abs_pow]
        have ht' : |t|^(k:ℕ) ≤ 1 := pow_le_one₀ (abs_nonneg _) ht
        have h := mul_le_mul ht' (hc k) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
        simpa only [one_mul] using h
  have heq : L r = L p + L (r-p) := by simp only [map_sub]; ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add hpoly he')

#print axioms residual_correction_bound
end ThomsonNegative.Certificate
