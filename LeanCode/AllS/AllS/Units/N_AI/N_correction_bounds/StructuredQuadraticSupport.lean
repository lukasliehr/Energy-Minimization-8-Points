import AllS.Units.N_AI.N_correction_bounds.StructuredLinearSupport
import AllS.Units.N_AI.N_correction_bounds.PowerQuadraticSupport

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def matrixCongruenceLinear {m n : ℕ} (Z : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ where
  toFun E := Z * E * Z.transpose
  map_add' E F := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c E := by simp

theorem structuredQuadraticCombinedSupport {r n t m : ℕ}
    (L : (Fin r → ℝ) →ₗ[ℝ] Matrix (Fin m) (Fin m) ℝ)
    (c : Fin r → Fin (n+1) → ℝ) (q : Fin r → Fin t → ℝ)
    (v ε : Fin r → ℝ) (e : Fin t → ℝ) (x : ℝ)
    (hv : ∀ i, v i = scalarEval (c i) x + (∑ j, q i j * e j) + ε i)
    (hx : x ∈ cellDomain) (γ : Fin (n+1) → ℝ) (η : ℝ)
    (hc : ∀ k, QuadraticBound (L (fun i => c i k)) (γ k))
    (he : QuadraticBound (L ((∑ j, e j • (fun i => q i j)) + ε)) η) :
    QuadraticBound (L v) ((∑ k, γ k) + η) := by
  have hp : ∀ k : Fin (n+1), |x ^ k.val| ≤ 1 := by
    intro k
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg x) (abs_le.mpr hx)
  have hpoly := quadraticBound_sum_smul_of_abs_le_one (fun k : Fin (n+1) => x ^ k.val)
    (fun k => L (fun i => c i k)) γ hp hc
  have herr : L ((∑ j, e j • (fun i => q i j)) + ε) =
      (∑ j, e j • L (fun i => q i j)) + L ε := by
    simp only [map_add, map_sum, map_smul]
  have hdecomp : L v = (∑ k : Fin (n+1), x ^ k.val • L (fun i => c i k)) +
      L ((∑ j, e j • (fun i => q i j)) + ε) := by
    rw [herr, structuredLinearExpansion L c q v ε e x hv, add_assoc]
  rw [hdecomp]
  exact quadraticBound_add _ _ _ _ hpoly he

#print axioms matrixCongruenceLinear
#print axioms structuredQuadraticCombinedSupport
end Blueprint.CAP
