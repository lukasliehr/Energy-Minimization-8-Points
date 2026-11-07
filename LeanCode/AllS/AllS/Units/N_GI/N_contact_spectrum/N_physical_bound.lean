import AllS.Units.N_GI.N_contact_spectrum.N_gram_exact
import AllS.Units.N_GI.N_contact_spectrum.N_block_positivity

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem contactBlockSum_bound (w L : ℝ) (hc : ContactSpectrumConditions w L) (x : Fin 13 → ℝ) :
    L*contactRawNormSquare x ≤ contactBlockSum w x := by
  obtain ⟨h0,h9,h11,h12,hA1,hD1,hA2,hD2⟩ := hc
  have h0' := mul_le_mul_of_nonneg_right h0 (sq_nonneg (x 0))
  have h9' := mul_le_mul_of_nonneg_right h9 (add_nonneg (sq_nonneg (x 9)) (sq_nonneg (x 10)))
  have h11' := mul_le_mul_of_nonneg_right h11 (sq_nonneg (x 11))
  have h12' := mul_le_mul_of_nonneg_right h12 (sq_nonneg (x 12))
  have h14 := contactBlock_lower _ _ _ L (x 1) (x 4) hA1 hD1
  have h23 := contactBlock_lower _ _ (-contactGramMixed1 w) L (x 2) (x 3) hA1 (by simpa using hD1)
  have h58 := contactBlock_lower _ _ _ L (x 5) (x 8) hA2 hD2
  have h67 := contactBlock_lower _ _ (-contactGramMixed2) L (x 6) (x 7) hA2 (by simpa using hD2)
  unfold contactRawNormSquare contactBlockSum contactBlockValue
  linarith

theorem contactGram_slice_bound (w L : ℝ) (hc : ContactSpectrumConditions w L)
    (q : TangentCoordinates) (hq : q∈rotationSlice) : L*‖q‖^2 ≤ contactGram w q q := by
  obtain ⟨x,rfl⟩ := contactRawSynthesis_surjective q hq
  rw [contactRawSynthesis_norm_formula,contactGram_block_sum]
  exact contactBlockSum_bound w L hc x

#print axioms contactGram_slice_bound
end Blueprint.Thomson.Tail.Implementation
