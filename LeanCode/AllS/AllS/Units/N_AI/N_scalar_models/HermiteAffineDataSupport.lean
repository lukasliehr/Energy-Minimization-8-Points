import AllS.Units.N_F.N_newton_hermite

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

/-- Jets of an affine rescaling of a polynomial, including its constant shift. -/
theorem polynomialJets_affine (P : Polynomial ℝ) (β c : ℝ) (k : ℕ) (t : ℝ) :
    polynomialJets (Polynomial.C β * P + Polynomial.C c) k t =
      β * polynomialJets P k t + if k = 0 then c else 0 := by
  have hadd : (Polynomial.derivative^[k]) (Polynomial.C β * P + Polynomial.C c) =
      (Polynomial.derivative^[k]) (Polynomial.C β * P) +
        (Polynomial.derivative^[k]) (Polynomial.C c) := by
    simp only [← Module.End.pow_apply, map_add]
  unfold polynomialJets
  rw [hadd, Polynomial.iterate_derivative_C_mul, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C]
  cases k with
  | zero => simp
  | succ k => simp [Polynomial.iterate_derivative_C (Nat.succ_pos k)]

/-- Exact matching affine jet data determine the affine rescaling of the
Hermite polynomial. A nonempty profile is needed to retain the constant term. -/
theorem profileHermite_affine_of_jets
    (z : Fin 5 → ℝ) (m : Fin 5 → ℕ) (J Jalt : ℕ → ℝ → ℝ) (β c : ℝ)
    (hz : Function.Injective z) (hm : 0 < ∑ i, m i)
    (hJ : ∀ i k, k < m i →
      Jalt k (z i) = β * J k (z i) + if k = 0 then c else 0) :
    profileHermite z m Jalt =
      Polynomial.C β * profileHermite z m J + Polynomial.C c := by
  symm
  apply profileHermite_unique z m Jalt hz
  · apply (Polynomial.degree_add_le _ _).trans_lt
    apply max_lt
    · simpa only [Polynomial.smul_eq_C_mul] using
        (Polynomial.degree_smul_le β (profileHermite z m J)).trans_lt
          (profileHermite_degree z m J)
    · exact (Polynomial.degree_C_le).trans_lt (WithBot.coe_lt_coe.mpr hm)
  · intro i k hk
    rw [polynomialJets_affine, profileHermite_jets z m J hz i k hk]
    exact (hJ i k hk).symm

/-- Affine rescaling commutes with a Hermite interpolant on any nonempty profile. -/
theorem profileHermite_affine
    (z : Fin 5 → ℝ) (m : Fin 5 → ℕ) (J : ℕ → ℝ → ℝ) (β c : ℝ)
    (hz : Function.Injective z) (hm : 0 < ∑ i, m i) :
    profileHermite z m (fun k t => β * J k t + if k = 0 then c else 0) =
      Polynomial.C β * profileHermite z m J + Polynomial.C c :=
  profileHermite_affine_of_jets z m J _ β c hz hm (fun _ _ _ => rfl)

#print axioms polynomialJets_affine
#print axioms profileHermite_affine_of_jets
#print axioms profileHermite_affine
end Blueprint.Thomson.Finite
