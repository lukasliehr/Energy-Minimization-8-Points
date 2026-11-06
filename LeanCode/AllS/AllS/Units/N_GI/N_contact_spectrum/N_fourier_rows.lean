import AllS.Units.N_GI.N_contact_spectrum.N_gram_exact

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

/-- Real Fourier form of the contact Gram: all exact entries, slice synthesis,
and slice synthesis. The raw basis is explicitly frequency ordered. -/
theorem contact_spectrum_fourier_rows :
    (∀ (w : ℝ) (j k : Fin 13),
      contactGram w (contactRawVector j) (contactRawVector k)=contactGramEntry w j k) ∧
    (∀ q : TangentCoordinates, q∈rotationSlice → ∃ x : Fin 13 → ℝ, contactRawSynthesis x=q) ∧
    (∀ (w : ℝ) (x : Fin 13 → ℝ),
      contactGram w (contactRawSynthesis x) (contactRawSynthesis x)=contactBlockSum w x) :=
  ⟨contactGram_raw,contactRawSynthesis_surjective,contactGram_block_sum⟩

#print axioms contact_spectrum_fourier_rows
end Blueprint.Thomson.Tail.Implementation
