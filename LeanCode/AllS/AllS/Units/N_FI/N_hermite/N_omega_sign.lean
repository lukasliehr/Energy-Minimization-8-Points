import AllS.Units.N_F.N_newton_hermite

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

def hermiteOmega (a : ℝ) (m : Fin 5 → ℕ) : Polynomial ℝ :=
  ∏ i, (Polynomial.X-Polynomial.C (canonicalNodes a i))^(m i)

theorem hermiteOmega_monic (a : ℝ) (m : Fin 5 → ℕ) : (hermiteOmega a m).Monic := by
  apply Polynomial.monic_prod_of_monic
  intro i hi
  exact (Polynomial.monic_X_sub_C _).pow _

theorem hermiteOmega_degree (a : ℝ) (m : Fin 5 → ℕ) :
    (hermiteOmega a m).degree = (∑ i, m i : ℕ) := by
  rw [hermiteOmega, Polynomial.degree_prod_of_monic]
  · simp [Polynomial.degree_pow]
  · intro i hi
    exact (Polynomial.monic_X_sub_C _).pow _

theorem monic_top_polynomial_jet (P : Polynomial ℝ) (N : ℕ)
    (hP : P.Monic) (hN : P.degree=N) (x : ℝ) : polynomialJets P N x = N.factorial := by
  have hn : P.natDegree=N := Polynomial.natDegree_eq_of_degree_eq_some hN
  have he : (Polynomial.derivative^[N]) P = Polynomial.C (N.factorial : ℝ) := by
    ext k
    rw [Polynomial.coeff_iterate_derivative]
    by_cases hk : k=0
    · subst k
      have hc : P.coeff N=1 := hn ▸ hP.coeff_natDegree
      simp [hc, Nat.descFactorial_self]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      simp [hk]
  simp [polynomialJets,he]

theorem hermiteOmega_jet_top (a : ℝ) (m : Fin 5 → ℕ) (t : ℝ) :
    polynomialJets (hermiteOmega a m) (∑ i, m i) t = (∑ i, m i).factorial :=
  monic_top_polynomial_jet _ _ (hermiteOmega_monic a m) (hermiteOmega_degree a m) t

theorem hermiteOmega_jets_zero (a : ℝ) (m : Fin 5 → ℕ) (i : Fin 5) (k : ℕ)
    (hk : k < m i) : polynomialJets (hermiteOmega a m) k (canonicalNodes a i)=0 := by
  classical
  have hd : (Polynomial.X-Polynomial.C (canonicalNodes a i))^(m i) ∣ hermiteOmega a m :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  obtain ⟨Q,hQ⟩ := hd
  rw [hQ]
  exact power_jet_zero _ _ _ _ hk

theorem hermite_omega_sign (a t : ℝ) (D : ℕ) (m : Fin 5 → ℕ)
    (ha : physical a) (hm : Profile.Valid D m) (ht : -1 ≤ t ∧ t < 1)
    (hne : ∀ i, 0 < m i → t ≠ canonicalNodes a i) :
    0 < (hermiteOmega a m).eval t ∧
    (hermiteOmega a m).degree = (∑ i, m i : ℕ) ∧
    polynomialJets (hermiteOmega a m) (∑ i, m i) t = (∑ i, m i).factorial := by
  refine ⟨?_,hermiteOmega_degree a m,hermiteOmega_jet_top a m t⟩
  simp only [hermiteOmega,Polynomial.eval_prod,Polynomial.eval_pow,
    Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
  apply Finset.prod_pos
  intro i hi
  by_cases hi0 : i=0
  · subst i
    by_cases hm0 : m 0=0
    · simp [hm0]
    · apply pow_pos
      have hh := hne 0 (Nat.pos_of_ne_zero hm0)
      change t ≠ -1 at hh
      change 0 < t-(-1)
      exact sub_pos.mpr (lt_of_le_of_ne ht.1 hh.symm)
  · exact (hm.2 i hi0).2.pow_pos (sub_ne_zero.mpr (hne i (hm.2 i hi0).1))

#check hermite_omega_sign
#print axioms hermite_omega_sign
end Blueprint.Thomson.Finite
