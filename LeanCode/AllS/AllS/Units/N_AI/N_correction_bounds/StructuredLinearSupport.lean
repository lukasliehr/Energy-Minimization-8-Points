import Blueprint.CAPContracts
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

/-- Linear correction preserves the common power controls and shared error
variables. The independent error remains one explicit vector term. -/
theorem structuredLinearExpansion {V : Type*} [AddCommMonoid V] [Module ℝ V]
    {r n t : ℕ} (L : (Fin r → ℝ) →ₗ[ℝ] V)
    (c : Fin r → Fin (n+1) → ℝ) (q : Fin r → Fin t → ℝ)
    (v ε : Fin r → ℝ) (e : Fin t → ℝ) (x : ℝ)
    (hv : ∀ i, v i = scalarEval (c i) x + (∑ j, q i j * e j) + ε i) :
    L v = (∑ k : Fin (n+1), x^k.val • L (fun i => c i k)) +
      (∑ j : Fin t, e j • L (fun i => q i j)) + L ε := by
  classical
  have he : v = (∑ k : Fin (n+1), x^k.val • (fun i => c i k)) +
      (∑ j : Fin t, e j • (fun i => q i j)) + ε := by
    funext i
    simpa only [scalarEval,Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_comm]
      using hv i
  rw [he,map_add,map_add]
  simp only [map_sum,map_smul]

#print axioms structuredLinearExpansion
end Blueprint.CAP
