import Lean_Code.VertexArea

open Real
noncomputable section
namespace SquareAntiprismVerification

/-- The finite incidence-counting step of the eight-vertex area argument.
The geometric construction must supply the local inequalities, incidence
identities, total spherical area, and Euler identity appearing here. -/
theorem area_inequality_from_incidence
    (α β γ S₃ S₄ : ℝ) (g₃ g₄ : ℕ) (h₃ h₄ : Fin 8 → ℕ) (S : Fin 8 → ℝ)
    (hlocal : ∀ i, ((h₃ i : ℝ) + 2 * (h₄ i : ℝ)) * (3 * α - Real.pi) +
      (2 * β + 2 * γ - 6 * α) ≤ S i)
    (hincident : ∑ i, S i = 3 * S₃ + 4 * S₄)
    (htri : ∑ i, (h₃ i : ℝ) = 3 * (g₃ : ℝ))
    (hquad : ∑ i, (h₄ i : ℝ) = 4 * (g₄ : ℝ))
    (htriArea : S₃ = (g₃ : ℝ) * (3 * α - Real.pi))
    (htotal : S₃ + S₄ = 4 * Real.pi)
    (hEuler : g₃ + 2 * g₄ = 12) :
    6 * α + β + γ ≤ 4 * Real.pi ∧
      (6 * α + β + γ = 4 * Real.pi →
        ∀ i, S i = ((h₃ i : ℝ) + 2 * (h₄ i : ℝ)) * (3 * α - Real.pi) +
          (2 * β + 2 * γ - 6 * α)) := by
  let Δ := 3 * α - Real.pi
  let f := 2 * β + 2 * γ - 6 * α
  let L : Fin 8 → ℝ := fun i => ((h₃ i : ℝ) + 2 * (h₄ i : ℝ)) * Δ + f
  have hL : (∑ i, L i) = (3 * (g₃ : ℝ) + 8 * (g₄ : ℝ)) * Δ + 8 * f := by
    dsimp [L]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, htri, hquad]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
    ring
  have hE : (g₃ : ℝ) + 2 * (g₄ : ℝ) = 12 := by exact_mod_cast hEuler
  have hEΔ := congrArg (fun x : ℝ => x * Δ) hE
  have hbound : (∑ i, L i) ≤ ∑ i, S i :=
    Finset.sum_le_sum (fun i hi => hlocal i)
  rw [hL, hincident] at hbound
  constructor
  · dsimp [Δ, f] at hbound hEΔ
    nlinarith
  · intro heq
    have heqsum : (∑ i, S i) = ∑ i, L i := by
      rw [hincident, hL]
      dsimp [Δ, f] at hEΔ ⊢
      nlinarith
    have hgap : (∑ i, (S i - L i)) = 0 := by rw [Finset.sum_sub_distrib, heqsum, sub_self]
    have hnonneg (i : Fin 8) (_ : i ∈ (Finset.univ : Finset (Fin 8))) : 0 ≤ S i - L i :=
      sub_nonneg.mpr (hlocal i)
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hgap
    intro i
    have hi := hall i (Finset.mem_univ i)
    exact sub_eq_zero.mp hi

end SquareAntiprismVerification
