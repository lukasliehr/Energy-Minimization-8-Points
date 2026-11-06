import AllS.Units.N_AI.N_correction_bounds.StructuredQuadraticSupport
import AllS.Units.N_AI.N_correction_bounds.OutputInsertionSupport

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

/-- Apply the inverse, insert its coordinates into a symmetric block, and
transport the combined structured error bound through a fixed congruence. -/
theorem structuredInverseInsertionQuadraticSupport {r s n t m d : ℕ}
    (A : (Fin r → ℝ) →ₗ[ℝ] (Fin s → ℝ))
    (coordinates : Fin s → String × ℕ × ℕ) (name : String)
    (Z : Matrix (Fin m) (Fin d) ℝ)
    (c : Fin r → Fin (n+1) → ℝ) (q : Fin r → Fin t → ℝ)
    (v ε : Fin r → ℝ) (e : Fin t → ℝ) (x : ℝ)
    (hv : ∀ i, v i = scalarEval (c i) x + (∑ j, q i j * e j) + ε i)
    (hx : x ∈ cellDomain) (γ : Fin (n+1) → ℝ) (η : ℝ)
    (hc : ∀ k, QuadraticBound
      (Z * outputInsertion (n := d) coordinates name (A (fun i => c i k)) * Z.transpose) (γ k))
    (he : QuadraticBound
      (Z * outputInsertion (n := d) coordinates name (A ((∑ j, e j • (fun i => q i j)) + ε)) *
        Z.transpose) η) :
    QuadraticBound (Z * outputInsertion (n := d) coordinates name (A v) * Z.transpose)
      ((∑ k, γ k) + η) := by
  exact structuredQuadraticCombinedSupport
    ((matrixCongruenceLinear Z).comp ((outputInsertionLinear (n := d) coordinates name).comp A))
    c q v ε e x hv hx γ η hc he

#print axioms structuredInverseInsertionQuadraticSupport
end Blueprint.CAP
