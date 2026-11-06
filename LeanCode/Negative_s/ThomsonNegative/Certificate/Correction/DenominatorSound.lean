import ThomsonNegative.Certificate.Correction.RowSound

noncomputable section
namespace ThomsonNegative.Certificate.Correction
open ThomsonNegative.Compact.Packed

/-- The direct reciprocal check also certifies the structural table's actual
common denominator. No additional factor-sign certificate is needed. -/
theorem RowCertified.denominator_ne_zero {A : TM} {residual : ℕ → TM} {r : RowWitness}
    (h : RowCertified A residual r) {a : ℝ → ℝ} (ha : Encl context A a)
    (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    Structure.Packed.evalZ (Structure.Exact.recCoeffs r.denominator) (a t)≠0 := by
  have hok : (denominatorInverse context A r.denominator r.normalizer).ok=true := by
    have hh := h.inverse_checked
    simp only [sameTM,Bool.and_eq_true] at hh
    exact hh.1.2
  have hd : (recordTM context A r.denominator r.normalizer).ok=true :=
    (mul_ok (recip_ok hok).2).2
  have hinv := invN_sound context_good
    (recordTM_sound context_good ha r.denominator r.normalizer hd) 9 1 hok
  intro hz
  apply hinv.1 t ht
  rw [hz,zero_div]

#print axioms RowCertified.denominator_ne_zero
end ThomsonNegative.Certificate.Correction
