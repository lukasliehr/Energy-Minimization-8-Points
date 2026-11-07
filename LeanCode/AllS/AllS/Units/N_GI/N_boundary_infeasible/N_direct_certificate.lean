import AllS.Units.N_GI.N_boundary_infeasible.N_certificate_interface

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

def boundaryNormPolynomial (y : Fin 13 → ℝ) : ℝ :=
  ∑ j, boundaryDiagonal j * y j ^ 2

theorem boundaryDiagonal_one_le (j : Fin 13) : 1 ≤ boundaryDiagonal j := by
  have h : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  fin_cases j <;> dsimp [boundaryDiagonal, boundaryM, boundaryZ, boundaryT] <;> nlinarith

theorem boundary_coordinate_abs_le_one (y : Fin 13 → ℝ)
    (hy : boundaryNormPolynomial y ≤ 1) (j : Fin 13) : |y j| ≤ 1 := by
  have hterm : boundaryDiagonal j * y j ^ 2 ≤ boundaryNormPolynomial y :=
    Finset.single_le_sum (fun k _ => mul_nonneg (boundaryDiagonal_pos k).le (sq_nonneg _))
      (Finset.mem_univ j)
  have hsq : y j ^ 2 ≤ 1 := by
    have := mul_le_mul_of_nonneg_right (boundaryDiagonal_one_le j) (sq_nonneg (y j))
    nlinarith
  exact abs_le.mpr ⟨by nlinarith [sq_nonneg (y j + 1)], by nlinarith [sq_nonneg (y j - 1)]⟩

/-- A checked residual bound on the actual bounded annulus suffices for the exact
boundary exclusion. Every multiplier and the residual remain explicit inputs. -/
theorem boundary_infeasible_of_bounded_residual
    (free upper lower : (Fin 13 → ℝ) → ℝ)
    (edge : ContactIndex → (Fin 13 → ℝ) → ℝ)
    (residual : (Fin 13 → ℝ) → ℝ)
    (hfree : ∀ y, 0 ≤ free y) (hupper : ∀ y, 0 ≤ upper y)
    (hlower : ∀ y, 0 ≤ lower y) (hedge : ∀ e y, 0 ≤ edge e y)
    (hidentity : ∀ y, -1 = free y + upper y * (1 - boundaryNormPolynomial y) +
      lower y * (boundaryNormPolynomial y - 3620 / 3721) +
      (∑ e, edge e y * boundaryContactPolynomial e y) + residual y)
    (hresidual : ∀ y, (∀ j, |y j| ≤ 1) → |residual y| < 1) :
    BoundarySOSInfeasible := by
  rintro ⟨y, hlo, hup, he⟩
  have hnormlo : (3620 : ℝ) / 3721 ≤ boundaryNormPolynomial y := hlo
  have hnormup : boundaryNormPolynomial y ≤ 1 := hup
  have hr := hresidual y (boundary_coordinate_abs_le_one y hnormup)
  have hu := mul_nonneg (hupper y) (sub_nonneg.mpr hnormup)
  have hl := mul_nonneg (hlower y) (sub_nonneg.mpr hnormlo)
  have hs : 0 ≤ ∑ e, edge e y * boundaryContactPolynomial e y :=
    Finset.sum_nonneg (fun e _ => mul_nonneg (hedge e y) (he e))
  have hi := hidentity y
  have hf := hfree y
  have habs := (abs_lt.mp hr).1
  linarith

#print axioms boundary_coordinate_abs_le_one
#print axioms boundary_infeasible_of_bounded_residual
end Blueprint.Thomson.Tail.Implementation
