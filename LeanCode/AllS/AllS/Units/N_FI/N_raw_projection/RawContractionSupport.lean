import AllS.Units.N_FI.N_raw_projection.RawTensorSupport
import AllS.Units.N_FI.N_gram_map.N_linear_degree
import AllS.Units.N_FI.N_raw_projection.RawScalarTensorSupport

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite
set_option maxHeartbeats 0

theorem rawScalarBilinear_sum {n : ℕ} (b : ScalarBlockName)
    (tags : Fin n → StandardTag) (v w : Fin n → ℝ) :
    reynolds (scalarWeightPoly b*
      ((∑ r,MvPolynomial.C (v r)*rawScalarBasis b false (tags r))*
       (∑ c,MvPolynomial.C (w c)*rawScalarBasis b false (tags c))+
       MvPolynomial.C (if scalarBlockStandard b then (1/3:ℝ) else 0)*
       ((∑ r,MvPolynomial.C (v r)*rawScalarBasis b true (tags r))*
        (∑ c,MvPolynomial.C (w c)*rawScalarBasis b true (tags c)))))=
      ∑ r,∑ c,MvPolynomial.C (v r*w c)*rawScalarBilinear b (tags r) (tags c) := by
  have he : scalarWeightPoly b*
      ((∑ r,MvPolynomial.C (v r)*rawScalarBasis b false (tags r))*
       (∑ c,MvPolynomial.C (w c)*rawScalarBasis b false (tags c))+
       MvPolynomial.C (if scalarBlockStandard b then (1/3:ℝ) else 0)*
       ((∑ r,MvPolynomial.C (v r)*rawScalarBasis b true (tags r))*
        (∑ c,MvPolynomial.C (w c)*rawScalarBasis b true (tags c))))=
      ∑ r,∑ c,MvPolynomial.C (v r*w c)*(scalarWeightPoly b*
        (rawScalarBasis b false (tags r)*rawScalarBasis b false (tags c)+
         MvPolynomial.C (if scalarBlockStandard b then (1/3:ℝ) else 0)*
           rawScalarBasis b true (tags r)*rawScalarBasis b true (tags c))) := by
    rw [Finset.sum_mul_sum,Finset.sum_mul_sum]
    simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum,map_mul]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro r hr <;>
      apply Finset.sum_congr rfl <;> intro c hc <;> ring
  rw [he]
  simp only [map_sum,reynolds_C_mul,rawScalarBilinear]

def scalarCoordinateKernel {n : ℕ} (b : ScalarBlockName) (d : ℕ)
    (K : Matrix (Fin n) (Fin (scalarBlockDimension b d)) ℝ)
    (Q : Matrix (Fin n) (Fin n) Poly3)
    (i j : Fin (scalarBlockDimension b d)) : Poly3 :=
  ∑ r,∑ c,MvPolynomial.C (K r i*K c j)*Q r c

theorem scalarCoordinateKernel_subst {n : ℕ} (a : ℝ) (b : ScalarBlockName) (d : ℕ)
    (tags : Fin n → StandardTag)
    (K : Matrix (Fin n) (Fin (scalarBlockDimension b d)) ℝ)
    (Q : Matrix (Fin n) (Fin n) Poly3)
    (hQ : ∀ r c,invariantSubst (Q r c)=rawScalarBilinear b (tags r) (tags c))
    (hF0 : ∀ i,scalarFeature b a d 0 i=∑ r,MvPolynomial.C (K r i)*rawScalarBasis b false (tags r))
    (hF1 : ∀ i,scalarFeature b a d 1 i=∑ r,MvPolynomial.C (K r i)*rawScalarBasis b true (tags r))
    (i j : Fin (scalarBlockDimension b d)) :
    invariantSubst (scalarCoordinateKernel b d K Q i j)=scalarBilinearKernel b a d i j := by
  simp only [scalarCoordinateKernel,map_sum,map_mul,hQ]
  simp only [invariantSubst,MvPolynomial.aeval_C]
  rw [scalarBilinearKernel,hF0,hF0,hF1,hF1]
  simpa only [MvPolynomial.algebraMap_eq,map_mul] using
    (rawScalarBilinear_sum b tags (fun r => K r i) (fun c => K c j)).symm

def momentCoordinateKernel (a : ℝ) (d : ℕ) (p : MomentPivots d) (k : Fin d)
    (Q : Matrix (Fin (d-k.val+1)) (Fin (d-k.val+1)) Poly3)
    (i j : Fin (d-k.val)) : Poly3 :=
  ∑ r,∑ c,MvPolynomial.C (momentKernelMatrix a d p k r i*momentKernelMatrix a d p k c j)*Q r c

theorem momentCoordinateKernel_subst (a : ℝ) (d : ℕ) (p : MomentPivots d) (k : Fin d)
    (Q : Matrix (Fin (d-k.val+1)) (Fin (d-k.val+1)) Poly3)
    (hQ : ∀ r c,invariantSubst (Q r c)=kernelRPoly k.val r.val c.val)
    (i j : Fin (d-k.val)) :
    invariantSubst (momentCoordinateKernel a d p k Q i j)=momentBilinearKernel a d p k i j := by
  simp only [momentCoordinateKernel,momentBilinearKernel,map_sum,map_mul,hQ]
  simp [invariantSubst]

def gramCoordinatePolynomial (d : ℕ)
    (G : ∀ b : GramBlock d,Matrix (Fin (gramBlockDimension d b)) (Fin (gramBlockDimension d b)) Poly3)
    (W : GramFamily d) : Poly3 :=
  ∑ b,∑ i,∑ j,MvPolynomial.C (W.val b i j)*G b i j

theorem gramCoordinatePolynomial_subst (a : ℝ) (d : ℕ) (p : MomentPivots d)
    (G : ∀ b : GramBlock d,Matrix (Fin (gramBlockDimension d b)) (Fin (gramBlockDimension d b)) Poly3)
    (hG : ∀ b i j,invariantSubst (G b i j)=gramKernel a d p b i j)
    (W : GramFamily d) : invariantSubst (gramCoordinatePolynomial d G W)=gramPoly a d p W := by
  simp only [gramCoordinatePolynomial,gramPoly,map_sum,map_mul,hG]
  simp [invariantSubst]

def boundedGramPolynomial (a : ℝ) (ha : physical a) (d : ℕ) (hd : 6≤d)
    (p : MomentPivots d) (W : GramFamily d) : boundedSymmetric (2*d) :=
  ⟨gramPoly a d p W,(mem_boundedSymmetric (2*d) _).mpr
    ⟨gramPoly_isSymmetric a d p W,gramPoly_degree a ha d hd p W⟩⟩

theorem gramCoordinatePolynomial_retained (a : ℝ) (ha : physical a) (d : ℕ) (hd : 6≤d)
    (p : MomentPivots d)
    (G : ∀ b : GramBlock d,Matrix (Fin (gramBlockDimension d b)) (Fin (gramBlockDimension d b)) Poly3)
    (hG : ∀ b i j,invariantSubst (G b i j)=gramKernel a d p b i j)
    (W : GramFamily d) (t : RetainedIndex (2*d)) :
    retainedCoordinates (2*d) (boundedGramPolynomial a ha d hd p W) t=
      ∑ b,∑ i,∑ j,W.val b i j*MvPolynomial.coeff (tagExponent t.val) (G b i j) := by
  rw [retained_coordinates_of_invariantSubst (2*d)
    (boundedGramPolynomial a ha d hd p W) (gramCoordinatePolynomial d G W)
    (gramCoordinatePolynomial_subst a d p G hG W)]
  simp only [gramCoordinatePolynomial,MvPolynomial.coeff_sum,MvPolynomial.coeff_C_mul]

#print axioms momentCoordinateKernel_subst
#print axioms scalarCoordinateKernel_subst
#print axioms gramCoordinatePolynomial_retained
end Blueprint.Thomson.Finite
