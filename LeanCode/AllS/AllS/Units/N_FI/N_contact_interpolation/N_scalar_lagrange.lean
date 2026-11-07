import AllS.Units.N_F.N_contact_order
import AllS.Units.N_F.N_sympoly

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

def scalarLagrange {n : ℕ} (z v : Fin n → ℝ) : Polynomial ℝ :=
  Lagrange.interpolate Finset.univ z v

def ScalarLagrangeContract : Prop := ∀ n : ℕ, ∀ z v : Fin n → ℝ,
  Function.Injective z →
    (scalarLagrange z v).degree < n ∧ (∀ i, (scalarLagrange z v).eval (z i) = v i) ∧
    scalarLagrange z v = ∑ i, Polynomial.C (v i) *
      ∏ j ∈ Finset.univ.erase i,
        (Polynomial.X-Polynomial.C (z j))*Polynomial.C ((z i-z j)⁻¹)

theorem scalarLagrange_degree {n : ℕ} (z v : Fin n → ℝ) (hz : Function.Injective z) :
    (scalarLagrange z v).degree < n := by
  simpa [scalarLagrange] using Lagrange.degree_interpolate_lt (s := Finset.univ) v hz.injOn

theorem scalarLagrange_eval {n : ℕ} (z v : Fin n → ℝ) (hz : Function.Injective z) (i : Fin n) :
    (scalarLagrange z v).eval (z i) = v i :=
  Lagrange.eval_interpolate_at_node v hz.injOn (Finset.mem_univ i)

theorem scalarLagrange_formula {n : ℕ} (z v : Fin n → ℝ) :
    scalarLagrange z v = ∑ i, Polynomial.C (v i) *
      ∏ j ∈ Finset.univ.erase i,
        (Polynomial.X-Polynomial.C (z j))*Polynomial.C ((z i-z j)⁻¹) := by
  simp [scalarLagrange,Lagrange.interpolate_apply,Lagrange.basis,Lagrange.basisDivisor,mul_comm]

theorem contact_interpolation_scalar_lagrange : ScalarLagrangeContract := by
  intro n z v hz
  exact ⟨scalarLagrange_degree z v hz, scalarLagrange_eval z v hz, scalarLagrange_formula z v⟩

#check contact_interpolation_scalar_lagrange
#print axioms contact_interpolation_scalar_lagrange
#check ScalarLagrangeContract
#print axioms ScalarLagrangeContract
end Blueprint.Thomson.Finite
