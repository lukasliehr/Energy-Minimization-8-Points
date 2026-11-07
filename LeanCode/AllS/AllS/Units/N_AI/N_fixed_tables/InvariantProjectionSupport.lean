import AllS.Units.N_FI.N_raw_projection.RawContractionSupport

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite
set_option maxHeartbeats 0

def invariantCoordinateColumn {n : ℕ} (tags : Fin n → Tag) (v : Fin n → ℝ) : Poly3 :=
  ∑ i,MvPolynomial.C (v i)*coordinateMonomial (tags i)

theorem invariantCoordinateColumn_subst {n : ℕ} (tags : Fin n → Tag) (v : Fin n → ℝ) :
    invariantSubst (invariantCoordinateColumn tags v)=∑ i,MvPolynomial.C (v i)*invariantMonomial (tags i) := by
  simp only [invariantCoordinateColumn,map_sum,map_mul,coordinateMonomial_subst]
  simp [invariantSubst]

theorem invariantCoordinateProduct_kernel (a : ℝ) (d : ℕ)
    (i j : Fin (scalarBlockDimension .m0Plus d)) (P Q : Poly3)
    (hP : invariantSubst P=scalarFeature .m0Plus a d 0 i)
    (hQ : invariantSubst Q=scalarFeature .m0Plus a d 0 j) :
    invariantSubst (P*Q)=scalarBilinearKernel .m0Plus a d i j := by
  simp only [scalarBilinearKernel,scalarWeightPoly,scalarBlockStandard,Bool.false_eq_true,
    ite_false,map_zero,zero_mul,add_zero,one_mul]
  rw [← hP,← hQ,← map_mul]
  exact (reynolds_of_symmetric _ (invariantSubst_symmetric _)).symm

theorem clear_ratio (E e q v : ℝ) (he : e≠0) (hE : E=e*q) : E*(v/e)=v*q := by
  rw [hE]
  field_simp

theorem clearCoordinateColumn {n : ℕ} (tags : Fin n → Tag) (p e q : Fin n → ℝ) (E : ℝ)
    (he : ∀ i,e i≠0) (hE : ∀ i,E=e i*q i) :
    MvPolynomial.C E*invariantCoordinateColumn tags (fun i => p i/e i)=
      invariantCoordinateColumn tags (fun i => p i*q i) := by
  unfold invariantCoordinateColumn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← mul_assoc,← map_mul,clear_ratio E (e i) (q i) (p i) (he i) (hE i)]

theorem clearPolynomialProduct (Ei Ej factor : ℝ) (hEi : Ei≠0) (hEj : Ej≠0)
    (S CS P Q NP NQ : Poly3)
    (hS : MvPolynomial.C (Ei*Ej)*S=CS)
    (hCS : CS=MvPolynomial.C factor*(NP*NQ))
    (hP : MvPolynomial.C Ei*P=NP) (hQ : MvPolynomial.C Ej*Q=NQ) :
    S=MvPolynomial.C factor*(P*Q) := by
  have hC : MvPolynomial.C (Ei*Ej)≠(0:Poly3) := by
    intro hz
    apply mul_ne_zero hEi hEj
    exact (MvPolynomial.C_injective _ _) (hz.trans (map_zero MvPolynomial.C).symm)
  apply mul_left_cancel₀ hC
  rw [hS,hCS,← hP,← hQ,map_mul]
  ring

#print axioms clearCoordinateColumn
#print axioms clearPolynomialProduct
#print axioms invariantCoordinateColumn_subst
#print axioms invariantCoordinateProduct_kernel
end Blueprint.Thomson.Finite
