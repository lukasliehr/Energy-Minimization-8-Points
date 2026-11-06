import AllS.Units.N_AI.N_gram_replay.ShortMetricSupport

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

/-- The short metric may be approximate; the checked error and correction bounds
still imply positive definiteness in the original coordinates. -/
def CorrectedShortMetricSupportStatement : Prop :=
  ∀ {n : ℕ} (G E K Z F : Matrix (Fin n) (Fin n) ℝ) (δ θ γ : ℝ),
    G.IsHermitian → E.IsHermitian → 0 ≤ δ →
    (G - δ • (K*K.transpose)).PosSemidef →
    F = Z*K-1 → QuadraticBound (F+F.transpose) θ →
    QuadraticBound (Z*E*Z.transpose) γ →
    γ < δ*(1-θ) → (G+E).PosDef

private theorem quadratic_sub' {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) : quadratic (A-B) v = quadratic A v - quadratic B v := by
  simp [quadratic, mul_sub, sub_mul, Finset.sum_sub_distrib]

private theorem quadratic_smul' {n : ℕ} (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) : quadratic (c • A) v = c * quadratic A v := by
  simp only [quadratic, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem correctedShortMetricSupport : CorrectedShortMetricSupportStatement := by
  intro n G E K Z F δ θ γ hG hE hδ hrem hF hmetric hcorrection hgap
  have hremZ : (Z*(G-δ • (K*K.transpose))*Z.transpose).PosSemidef := by
    simpa using hrem.mul_mul_conjTranspose_same Z
  have hsplit : Z*(G-δ • (K*K.transpose))*Z.transpose =
      Z*G*Z.transpose - δ • (Z*K*K.transpose*Z.transpose) := by
    simp [Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_assoc]
  have hfloor (v : Fin n → ℝ) :
      (δ*(1-θ))*squaredEuclidean v ≤ quadratic (Z*G*Z.transpose) v := by
    have h := hremZ.dotProduct_mulVec_nonneg v
    rw [←quadratic_eq_dotProduct, hsplit, quadratic_sub', quadratic_smul'] at h
    have hm := mul_le_mul_of_nonneg_left (shortMetricFloorSupport K Z F θ hF hmetric v) hδ
    nlinarith
  have hGZ : (Z*G*Z.transpose).IsHermitian := by
    simpa using Matrix.isHermitian_mul_mul_conjTranspose Z hG
  have hEZ : (Z*E*Z.transpose).IsHermitian := by
    simpa using Matrix.isHermitian_mul_mul_conjTranspose Z hE
  have hpositive : (Z*(G+E)*Z.transpose).PosDef := by
    simpa only [Matrix.mul_add, Matrix.add_mul] using
      correctionFloorSupport (Z*G*Z.transpose) (Z*E*Z.transpose)
        (δ*(1-θ)) γ hGZ hEZ hfloor hcorrection hgap
  have hZ : IsUnit Z := by
    apply (Matrix.isUnit_iff_isUnit_det Z).mpr
    apply isUnit_iff_ne_zero.mpr
    intro hz
    have hd := (Matrix.isUnit_iff_isUnit_det _).mp hpositive.isUnit
    exact (isUnit_iff_ne_zero.mp hd) (by simp [Matrix.det_mul, hz])
  apply (Matrix.IsUnit.posDef_star_right_conjugate_iff hZ).mp
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    using hpositive

#print CorrectedShortMetricSupportStatement
#print axioms correctedShortMetricSupport
end Blueprint.CAP
