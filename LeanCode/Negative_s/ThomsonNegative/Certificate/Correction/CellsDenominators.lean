import ThomsonNegative.Certificate.Correction.Cells
import ThomsonNegative.Certificate.Correction.DenominatorSound

noncomputable section
namespace ThomsonNegative.Certificate.Correction.Cells

theorem denominator_nonzero (c : Fin 5) (r : Fin 68) (t : ℝ)
    (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    Structure.Packed.evalZ (Structure.Exact.recCoeffs (Source.rowDenominator r)) (heightArgument c t)≠0 := by
  fin_cases c
  · have h := (Correction.q01.witness_certified r).denominator_ne_zero Correction.q01.argument_encl t ht
    rw [Correction.q01.witness_denominator] at h
    exact h
  · have h := (Correction.q03.witness_certified r).denominator_ne_zero Correction.q03.argument_encl t ht
    rw [Correction.q03.witness_denominator] at h
    exact h
  · have h := (Correction.q05.witness_certified r).denominator_ne_zero Correction.q05.argument_encl t ht
    rw [Correction.q05.witness_denominator] at h
    exact h
  · have h := (Correction.q07.witness_certified r).denominator_ne_zero Correction.q07.argument_encl t ht
    rw [Correction.q07.witness_denominator] at h
    exact h
  · have h := (Correction.q09.witness_certified r).denominator_ne_zero Correction.q09.argument_encl t ht
    rw [Correction.q09.witness_denominator] at h
    exact h
#print axioms denominator_nonzero
end ThomsonNegative.Certificate.Correction.Cells
