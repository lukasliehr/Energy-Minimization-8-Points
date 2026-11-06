import AllS.Units.N_AI.N_data.RawSparseLookup
import AllS.Units.N_FI.N_raw_projection.RawScalarCatalogueSupport
import AllS.Units.N_FI.N_sympoly.N_finite_equivalence

noncomputable section
namespace Blueprint.CAP
open Blueprint.Thomson.Finite

theorem sparseTerm_monomial (t : Tag) (c : ℚ) :
    MvPolynomial.C c*MvPolynomial.X (0:Fin 3)^t.1*
      MvPolynomial.X 1^t.2.1*MvPolynomial.X 2^t.2.2 =
        MvPolynomial.monomial (tagExponent t) c := by
  have he : Finsupp.single (0:Fin 3) t.1+Finsupp.single 1 t.2.1+
      Finsupp.single 2 t.2.2=tagExponent t := by
    ext i
    fin_cases i <;> simp [tagExponent,Finsupp.single_apply]
  simpa only [MvPolynomial.X_pow_eq_monomial,MvPolynomial.C_mul_monomial,
    MvPolynomial.monomial_mul,mul_one] using
    congrArg (fun e : Fin 3 →₀ ℕ => MvPolynomial.monomial e c) he

theorem sparsePolynomial_coeff_lookup (p : RawCatalogue.SparsePoly) (t : Tag) :
    MvPolynomial.coeff (tagExponent t) (RawCatalogue.sparsePolynomial p)=
      rawRationalLookup p t := by
  induction p with
  | nil => simp [RawCatalogue.sparsePolynomial,rawRationalLookup]
  | cons e p ih =>
    rcases e with ⟨u,c⟩
    change MvPolynomial.coeff (tagExponent t)
      (MvPolynomial.C c*MvPolynomial.X 0^u.1*MvPolynomial.X 1^u.2.1*
        MvPolynomial.X 2^u.2.2+RawCatalogue.sparsePolynomial p) =
      (if u=t then c else 0)+rawRationalLookup p t
    rw [MvPolynomial.coeff_add,sparseTerm_monomial,MvPolynomial.coeff_monomial,ih]
    simp only [tagExponent_injective.eq_iff]

theorem rawRationalLookup_normalize (p : List (Tag × ℤ)) (den : ℕ) (t : Tag) :
    rawRationalLookup (normalizeIntegerRawEntry den p) t =
      (rawIntegerLookup p t:ℚ)/(den:ℚ) := by
  induction p with
  | nil => simp [rawRationalLookup,rawIntegerLookup,normalizeIntegerRawEntry]
  | cons e p ih =>
    rcases e with ⟨u,c⟩
    change (if u=t then (c:ℚ)/(den:ℚ) else 0)+
      rawRationalLookup (normalizeIntegerRawEntry den p) t =
      (((if u=t then c else 0)+rawIntegerLookup p t:ℤ):ℚ)/(den:ℚ)
    rw [ih,Int.cast_add,add_div]
    by_cases h : u=t <;> simp [h]

theorem integerSparsePolynomial_coeff (p : List (Tag × ℤ)) (den : ℕ) (t : Tag) :
    MvPolynomial.coeff (tagExponent t)
      (RawCatalogue.ratToReal (RawCatalogue.sparsePolynomial (normalizeIntegerRawEntry den p))) =
        (rawIntegerLookup p t:ℝ)/(den:ℝ) := by
  change MvPolynomial.coeff (tagExponent t)
    (MvPolynomial.map (Rat.castHom ℝ) (RawCatalogue.sparsePolynomial (normalizeIntegerRawEntry den p))) = _
  rw [MvPolynomial.coeff_map,sparsePolynomial_coeff_lookup,rawRationalLookup_normalize]
  norm_cast

#print axioms sparsePolynomial_coeff_lookup
#print axioms rawRationalLookup_normalize
#print axioms integerSparsePolynomial_coeff
end Blueprint.CAP
