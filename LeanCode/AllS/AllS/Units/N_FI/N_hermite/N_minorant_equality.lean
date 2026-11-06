import AllS.Units.N_FI.N_hermite.N_remainder

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

theorem hermite_minorant_equality (s a t : ℝ) (D : ℕ) (m : Fin 5 → ℕ)
    (hs : 0 ≤ s) (ha : physical a) (hm : Profile.Valid D m) (ht : -1 ≤ t ∧ t < 1) :
    (hermitePolynomial s a m).eval t ≤ phi s t ∧
    ((hermitePolynomial s a m).eval t=phi s t ↔
      ∃ i, 0 < m i ∧ t=canonicalNodes a i) ∧
    (∀ i, i ≠ 0 →
      (hermitePolynomial s a m).eval (canonicalNodes a i)=phi s (canonicalNodes a i) ∧
      HasDerivAt (fun x => (hermitePolynomial s a m).eval x)
        (potentialJet s 1 (canonicalNodes a i)) (canonicalNodes a i)) := by
  have hvalue (i : Fin 5) (hi : 0 < m i) :
      (hermitePolynomial s a m).eval (canonicalNodes a i)=phi s (canonicalNodes a i) :=
    hermitePolynomial_jets s a m ha i 0 hi
  have hinterior (i : Fin 5) (hi : i ≠ 0) :
      (hermitePolynomial s a m).eval (canonicalNodes a i)=phi s (canonicalNodes a i) ∧
      HasDerivAt (fun x => (hermitePolynomial s a m).eval x)
        (potentialJet s 1 (canonicalNodes a i)) (canonicalNodes a i) := by
    refine ⟨hvalue i (hm.2 i hi).1,?_⟩
    have h := polynomialJets_hasDerivAt (hermitePolynomial s a m) 0 (canonicalNodes a i)
    rw [hermitePolynomial_jets s a m ha i 1 (profile_interior_ge_two hm i hi)] at h
    exact h
  by_cases hnode : ∃ i, 0 < m i ∧ t=canonicalNodes a i
  · obtain ⟨i,hi,rfl⟩ := hnode
    exact ⟨(hvalue i hi).le,⟨fun _ => ⟨i,hi,rfl⟩,fun _ => hvalue i hi⟩,hinterior⟩
  · have hne : ∀ i, 0 < m i → t ≠ canonicalNodes a i := by
      intro i hi he
      exact hnode ⟨i,hi,he⟩
    obtain ⟨ξ,hξlo,hξhi,hrem⟩ := hermite_remainder s a t D m hs ha hm ht hne
    have hN : 0 < ∑ i,m i := by rw [hm.1]; omega
    have hpos : 0 < phi s t-(hermitePolynomial s a m).eval t := by
      rw [hrem]
      exact div_pos (mul_pos ((potential_jets_tower s ξ (∑ i,m i) hs hξhi).2.2 hN)
        (hermite_omega_sign a t D m ha hm ht hne).1) (by positivity)
    exact ⟨le_of_lt (sub_pos.mp hpos),⟨fun he => (ne_of_lt (sub_pos.mp hpos) he).elim,
      fun he => (hnode he).elim⟩,hinterior⟩

#check hermite_minorant_equality
#print axioms hermite_minorant_equality
end Blueprint.Thomson.Finite
