import Lean_Code.AreaSummation
import Lean_Code.RhombusScalar

open Real
noncomputable section
namespace SquareAntiprismVerification

/-- The incidence summation before imposing Euler equality. Its dependence
on the excess corner count is retained explicitly. -/
theorem area_inequality_before_euler
    (α β γ S₃ S₄ : ℝ) (g₃ g₄ : ℕ) (h₃ h₄ : Fin 8 → ℕ) (S : Fin 8 → ℝ)
    (hlocal : ∀ i, ((h₃ i : ℝ) + 2 * (h₄ i : ℝ)) * (3 * α - Real.pi) +
      (2 * β + 2 * γ - 6 * α) ≤ S i)
    (hincident : ∑ i, S i = 3 * S₃ + 4 * S₄)
    (htri : ∑ i, (h₃ i : ℝ) = 3 * (g₃ : ℝ))
    (hquad : ∑ i, (h₄ i : ℝ) = 4 * (g₄ : ℝ))
    (htriArea : S₃ = (g₃ : ℝ) * (3 * α - Real.pi))
    (htotal : S₃ + S₄ = (16 - ((g₃ : ℝ) + 2 * (g₄ : ℝ))) * Real.pi) :
    3 * ((g₃ : ℝ) + 2 * (g₄ : ℝ) - 12) * α +
      4 * (6 * α + β + γ) ≤ 16 * Real.pi := by
  let L : Fin 8 → ℝ := fun i => ((h₃ i : ℝ) + 2 * (h₄ i : ℝ)) * (3 * α - Real.pi) +
    (2 * β + 2 * γ - 6 * α)
  have hL : (∑ i, L i) = (3 * (g₃ : ℝ) + 8 * (g₄ : ℝ)) * (3 * α - Real.pi) +
      8 * (2 * β + 2 * γ - 6 * α) := by
    dsimp [L]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, htri, hquad]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
    ring
  have hbound : (∑ i, L i) ≤ ∑ i, S i := Finset.sum_le_sum (fun i _ => hlocal i)
  rw [hL, hincident] at hbound
  nlinarith [htotal, htriArea]

/-- The Euler upper bound suffices: the same packing-angle endgame forces
both the optimal packing constant and the exact Euler corner count. -/
theorem packing_euler_count_eq (c : ℝ) (K : ℕ) (hc : 0 < c) (hcupper : c ≤ aInf)
    (hK : 12 ≤ K)
    (hangle :
      let α := Real.arccos (c / (1 + c))
      let β := 2 * Real.pi - 3 * α
      let γ := rhombusDelta (1 / c) β
      3 * ((K : ℝ) - 12) * α + 4 * (6 * α + β + γ) ≤ 16 * Real.pi) :
    c = aInf ∧ K = 12 := by
  let α := Real.arccos (c / (1 + c))
  let β := 2 * Real.pi - 3 * α
  let γ := rhombusDelta (1 / c) β
  have hcI : c ∈ Set.Ioo (0 : ℝ) 1 := ⟨hc, hcupper.trans_lt aInf_mem_Ioo.2⟩
  have hα := packing_equilateral_angle_range c hc hcupper
  have hαpos : 0 < α := by dsimp [α]; linarith [hα.1, Real.pi_pos]
  have hβ : β ∈ Set.Ioo (0 : ℝ) Real.pi := by
    dsimp [β, α]
    constructor <;> linarith [hα.1, hα.2.1, Real.pi_pos]
  have hγ : γ ∈ Set.Ioo (0 : ℝ) Real.pi := rhombusDelta_mem_Ioo (1 / c) β (one_div_pos.mpr hc) hβ
  have htan : Real.tan (β / 2) * Real.tan (γ / 2) = 1 / c :=
    rhombusDelta_tan_relation (1 / c) β hβ
  have hKr : (12 : ℝ) ≤ K := by exact_mod_cast hK
  have hstrong : 3 * ((K : ℝ) - 12) * α + 4 * (6 * α + β + γ) ≤ 16 * Real.pi := hangle
  have hbound : 6 * α + β + γ ≤ 4 * Real.pi := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hKr) hαpos.le]
  have hcback : aInf ≤ c := packing_bound_from_angles c α β γ hcI hα.2.2 rfl hβ hγ htan hbound
  have hceq : c = aInf := le_antisymm hcupper hcback
  have heq : 6 * α + β + γ = 4 * Real.pi := by
    have hcos : Real.cos α = aInf / (1 + aInf) := by simpa only [← hceq] using hα.2.2
    have htan' : Real.tan (β / 2) * Real.tan (γ / 2) = 1 / aInf := by rwa [← hceq]
    exact (packing_angles_equality α β γ hcos rfl hβ hγ htan').2
  have hKeq : (K : ℝ) = 12 := by nlinarith
  exact ⟨hceq, by exact_mod_cast hKeq⟩

end SquareAntiprismVerification
