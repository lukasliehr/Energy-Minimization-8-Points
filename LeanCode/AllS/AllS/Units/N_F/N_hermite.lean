import AllS.Units.N_FI.N_hermite.N_minorant_equality

noncomputable section
namespace Blueprint.Thomson.Finite

/-- The exact Hermite minorant, including the zero endpoint multiplicity case,
the complete equality set, and first derivative matching at interior contacts. -/
theorem hermite_minorant (s a : ℝ) (D : ℕ) (m : Fin 5 → ℕ)
    (hs : 0 ≤ s) (ha : physical a) (hm : Profile.Valid D m) :
    (∀ t, -1 ≤ t → t < 1 →
      (hermitePolynomial s a m).eval t ≤ phi s t ∧
      ((hermitePolynomial s a m).eval t=phi s t ↔
        ∃ i, 0 < m i ∧ t=canonicalNodes a i)) ∧
    (∀ i, i ≠ 0 →
      (hermitePolynomial s a m).eval (canonicalNodes a i)=phi s (canonicalNodes a i) ∧
      HasDerivAt (fun x => (hermitePolynomial s a m).eval x)
        (potentialJet s 1 (canonicalNodes a i)) (canonicalNodes a i)) := by
  constructor
  · intro t htl htu
    exact ⟨(hermite_minorant_equality s a t D m hs ha hm ⟨htl,htu⟩).1,
      (hermite_minorant_equality s a t D m hs ha hm ⟨htl,htu⟩).2.1⟩
  · exact (hermite_minorant_equality s a (-1) D m hs ha hm ⟨le_rfl,by norm_num⟩).2.2

#check hermite_minorant
#print axioms hermite_minorant
end Blueprint.Thomson.Finite
