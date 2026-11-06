import AllS.Units.N_AI.N_data.ReducedPointExpGates
import AllS.Units.N_AI.N_elementary_series.PointExpSupport
import AllS.Units.N_AI.N_scalar_models.IntervalExpressionSupport

noncomputable section
namespace Blueprint.CAP

theorem reducedPointExpSupport (R : QInterval) (z : ℚ) (r n : ℕ)
    (I : Fin (r+1) → QInterval) (hg : R.ReducedExpPointGate z r n I) :
    R.asBox.Contains (Real.exp (z:ℝ)) := by
  have h0 := pointExpSupport (I 0) (z/2^r) n hg.1
  have hchain : ∀ j : ℕ, ∀ hj : j ≤ r,
      (I ⟨j,Nat.lt_succ_of_le hj⟩).asBox.Contains
        (Real.exp ((2:ℝ)^j*((z:ℝ)/2^r))) := by
    intro j
    induction j with
    | zero =>
      intro hj
      have hi : (⟨0,Nat.lt_succ_of_le hj⟩ : Fin (r+1)) = 0 := by
        apply Fin.ext
        simp
      rw [hi]
      simpa only [pow_zero,one_mul,Rat.cast_div,Rat.cast_pow,Rat.cast_ofNat] using h0
    | succ j ih =>
      intro hj
      have hjr : j < r := by omega
      have hp := ih (Nat.le_of_lt hjr)
      have hprod := QInterval.subset_contains (QInterval.mul_contains hp hp) (hg.2.1 ⟨j,hjr⟩)
      have he : Real.exp ((2:ℝ)^j*((z:ℝ)/2^r))*Real.exp ((2:ℝ)^j*((z:ℝ)/2^r)) =
          Real.exp ((2:ℝ)^(j+1)*((z:ℝ)/2^r)) := by
        rw [←Real.exp_add]
        congr 1
        rw [pow_succ]
        ring
      have hi : (⟨j,hjr⟩ : Fin r).succ = ⟨j+1,Nat.lt_succ_of_le hj⟩ := by
        apply Fin.ext
        rfl
      rw [he,hi] at hprod
      exact hprod
  have h := QInterval.subset_contains (hchain r le_rfl) hg.2.2
  have hz : (2:ℝ)^r*((z:ℝ)/2^r) = z := by field_simp
  simpa only [hz] using h

#print axioms reducedPointExpSupport
end Blueprint.CAP
