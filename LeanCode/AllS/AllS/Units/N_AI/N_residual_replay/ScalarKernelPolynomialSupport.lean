import AllS.Units.N_FI.N_raw_projection.RawContractionSupport

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP
open Blueprint.Thomson.Finite

/-- For a one-component representation, the second component vanishes by its
exact zero weight; no fictitious second-column identity is required. -/
theorem scalarCoordinateKernel_subst_nonstandard {n : ℕ}
    (a : ℝ) (b : ScalarBlockName) (d : ℕ)
    (tags : Fin n → StandardTag)
    (K : Matrix (Fin n) (Fin (scalarBlockDimension b d)) ℝ)
    (Q : Matrix (Fin n) (Fin n) Poly3)
    (hb : scalarBlockStandard b=false)
    (hQ : ∀ r c,invariantSubst (Q r c)=rawScalarBilinear b (tags r) (tags c))
    (hF : ∀ i,scalarFeature b a d 0 i=
      ∑ r,MvPolynomial.C (K r i)*rawScalarBasis b false (tags r))
    (i j : Fin (scalarBlockDimension b d)) :
    invariantSubst (scalarCoordinateKernel b d K Q i j)=scalarBilinearKernel b a d i j := by
  simp only [scalarCoordinateKernel,map_sum,map_mul,hQ]
  simp only [invariantSubst,MvPolynomial.aeval_C]
  have h := rawScalarBilinear_sum b tags (fun r => K r i) (fun r => K r j)
  simp only [hb,Bool.false_eq_true,ite_false,MvPolynomial.C_0,zero_mul,add_zero] at h
  rw [scalarBilinearKernel,hF,hF]
  simp only [hb,Bool.false_eq_true,ite_false,MvPolynomial.C_0,zero_mul,add_zero]
  simpa only [MvPolynomial.algebraMap_eq,map_mul] using h.symm

#print axioms scalarCoordinateKernel_subst_nonstandard
end Blueprint.CAP
