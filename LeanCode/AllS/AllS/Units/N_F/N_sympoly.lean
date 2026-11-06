import AllS.Units.N_F.N_definitions
import AllS.Units.N_FI.N_sympoly.N_bounded_inverse
import AllS.Units.N_FI.N_sympoly.N_component_commutation
import AllS.Units.N_FI.N_sympoly.N_elementary_bridge
import AllS.Units.N_FI.N_sympoly.N_finite_equivalence
import AllS.Units.N_FI.N_sympoly.N_monomial_grade
import AllS.Units.N_FI.N_sympoly.N_reynolds_coefficient
import Blueprint.FiniteDefinitions
import Blueprint.Target

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

def invariantGeneratorsRat : Fin 3 → MvPolynomial (Fin 3) ℚ :=
  ![MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 2,
    MvPolynomial.X 0 * MvPolynomial.X 1 + MvPolynomial.X 0 * MvPolynomial.X 2 +
      MvPolynomial.X 1 * MvPolynomial.X 2,
    MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2]

def invariantSubstRat : MvPolynomial (Fin 3) ℚ →ₐ[ℚ] MvPolynomial (Fin 3) ℚ :=
  MvPolynomial.aeval invariantGeneratorsRat

def RationalInvariantBridge : Prop :=
  ∀ p : MvPolynomial (Fin 3) ℚ,
    MvPolynomial.map (Rat.castHom ℝ) (invariantSubstRat p) =
      invariantSubst (MvPolynomial.map (Rat.castHom ℝ) p)

def InvariantCoordinateContract : Prop :=
  (∀ D : ℕ, Nonempty ((TagIndex D → ℝ) ≃ₗ[ℝ] boundedSymmetric D)) ∧
  (∀ (D : ℕ) (c : TagIndex D → ℝ),
    (sympoly_finite_equivalence D c).val = ∑ t : TagIndex D, c t • invariantMonomial t.val) ∧
  (∀ (p : Poly3) (α : Fin 3 →₀ ℕ),
    (reynolds p).coeff α = (∑ β ∈ exponentOrbit α, p.coeff β)/(exponentOrbit α).card) ∧
  (∀ (p : Poly3), p.IsSymmetric → reynolds p = p) ∧ RationalInvariantBridge

theorem invariantSubst_ratCast (p : MvPolynomial (Fin 3) ℚ) :
    MvPolynomial.map (Rat.castHom ℝ) (invariantSubstRat p) =
      invariantSubst (MvPolynomial.map (Rat.castHom ℝ) p) := by
  change MvPolynomial.map (Rat.castHom ℝ) (MvPolynomial.bind₁ invariantGeneratorsRat p) =
    MvPolynomial.bind₁ (fun i : Fin 3 => ![sigma,e2,e3] i)
      (MvPolynomial.map (Rat.castHom ℝ) p)
  rw [MvPolynomial.map_bind₁]
  congr 2
  funext i
  fin_cases i <;> simp [invariantGeneratorsRat, sigma, e2, e3]

theorem invariant_coordinate_basis : InvariantCoordinateContract := by
  exact ⟨fun D => ⟨sympoly_finite_equivalence D⟩,
    sympoly_finite_equivalence_apply, sympoly_reynolds_coefficient,
    reynolds_of_symmetric, invariantSubst_ratCast⟩

#check invariantSubst_ratCast
#print axioms invariantSubst_ratCast
#check invariant_coordinate_basis
#print axioms invariant_coordinate_basis
end Blueprint.Thomson.Finite
