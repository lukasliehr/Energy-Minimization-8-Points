import AllS.Units.N_F.N_definitions
import AllS.Units.N_FI.N_sympoly.N_reynolds_coefficient

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite
open MvPolynomial

/-- The actual three-variable zonal recurrence used by the certificate. -/
def kernelQPoly : ℕ → Poly3
  | 0 => 1
  | 1 => MvPolynomial.X 2-MvPolynomial.X 0*MvPolynomial.X 1
  | k+2 => C 2*(MvPolynomial.X 2-MvPolynomial.X 0*MvPolynomial.X 1)*kernelQPoly (k+1) -
      (1-MvPolynomial.X 0^2)*(1-MvPolynomial.X 1^2)*kernelQPoly k

def kernelSPoly (k i j : ℕ) : Poly3 := reynolds (MvPolynomial.X 0^i*MvPolynomial.X 1^j*kernelQPoly k)

def repeatSubst (x : Fin 3) : Poly3 →ₐ[ℝ] Poly3 := aeval ![MvPolynomial.X x,MvPolynomial.X x,1]

def kernelRPoly (k i j : ℕ) : Poly3 :=
  C 6*kernelSPoly k i j + repeatSubst 0 (kernelSPoly k i j) +
    repeatSubst 1 (kernelSPoly k i j) + repeatSubst 2 (kernelSPoly k i j) +
    C (if k=0 then (1/7 : ℝ) else 0)

def CanonicalKernelContract : Prop :=
  (∀ k, (kernelQPoly k).totalDegree ≤ 2*k) ∧
  (∀ k i j, (kernelSPoly k i j).totalDegree ≤ i+j+2*k) ∧
  (∀ k i j, (kernelRPoly k i j).totalDegree ≤ i+j+2*k)


theorem polyDegree_add_le (p q : Poly3) (D : ℕ)
    (hp : p.totalDegree ≤ D) (hq : q.totalDegree ≤ D) :
    (p+q).totalDegree ≤ D := (totalDegree_add p q).trans (max_le hp hq)

theorem polyDegree_sub_le (p q : Poly3) (D : ℕ)
    (hp : p.totalDegree ≤ D) (hq : q.totalDegree ≤ D) :
    (p-q).totalDegree ≤ D := (totalDegree_sub p q).trans (max_le hp hq)

theorem polyDegree_mul_le (p q : Poly3) (D E : ℕ)
    (hp : p.totalDegree ≤ D) (hq : q.totalDegree ≤ E) :
    (p*q).totalDegree ≤ D+E := (totalDegree_mul p q).trans (Nat.add_le_add hp hq)

theorem polyDegree_C_mul_le (c : ℝ) (p : Poly3) :
    (C c*p).totalDegree ≤ p.totalDegree := by
  simpa using totalDegree_mul (C c) p

theorem kernelQPoly_degree (k : ℕ) : (kernelQPoly k).totalDegree ≤ 2*k := by
  have hB : ((MvPolynomial.X 2-MvPolynomial.X 0*MvPolynomial.X 1) : Poly3).totalDegree ≤ 2 := by
    apply polyDegree_sub_le
    · simp
    · simpa using totalDegree_mul (MvPolynomial.X 0 : Poly3) (MvPolynomial.X 1)
  have hT (i : Fin 3) : ((1-MvPolynomial.X i^2) : Poly3).totalDegree ≤ 2 := by
    apply polyDegree_sub_le <;> simp
  induction k using Nat.twoStepInduction with
  | zero => simp [kernelQPoly]
  | one => simpa [kernelQPoly] using hB
  | more k hk hk1 =>
    rw [kernelQPoly]
    apply polyDegree_sub_le
    · have h := polyDegree_mul_le (C 2*(MvPolynomial.X 2-MvPolynomial.X 0*MvPolynomial.X 1))
        (kernelQPoly (k+1)) 2 (2*(k+1)) ((polyDegree_C_mul_le _ _).trans hB) hk1
      omega
    · have ht := polyDegree_mul_le _ _ 2 2 (hT 0) (hT 1)
      have h := polyDegree_mul_le _ _ (2+2) (2*k) ht hk
      omega

theorem reynolds_degree (p : Poly3) : (reynolds p).totalDegree ≤ p.totalDegree := by
  change ((6 : ℝ)⁻¹ • ∑ σ : Equiv.Perm (Fin 3), rename σ p).totalDegree ≤ p.totalDegree
  apply (totalDegree_smul_le _ _).trans
  apply totalDegree_finsetSum_le
  intro σ hσ
  exact totalDegree_rename_le σ p

/-- Substitution of affine polynomials does not increase total degree. -/
theorem affine_subst_degree (g : Fin 3 → Poly3) (hg : ∀ i, (g i).totalDegree ≤ 1)
    (p : Poly3) : (aeval g p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intro d hd
  rw [aeval_monomial]
  change (C (p.coeff d) * ∏ i ∈ d.support, g i ^ d i).totalDegree ≤ p.totalDegree
  calc
    _ ≤ (∏ i ∈ d.support, g i ^ d i).totalDegree := polyDegree_C_mul_le _ _
    _ ≤ ∑ i ∈ d.support, (g i ^ d i).totalDegree := totalDegree_finsetProd _ _
    _ ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (totalDegree_pow (g i) (d i)).trans (by simpa using Nat.mul_le_mul_left (d i) (hg i))
    _ ≤ p.totalDegree := le_totalDegree hd

theorem repeatSubst_degree (x : Fin 3) (p : Poly3) :
    (repeatSubst x p).totalDegree ≤ p.totalDegree := by
  apply affine_subst_degree
  intro i
  fin_cases i <;> simp

theorem kernelSPoly_degree (k i j : ℕ) : (kernelSPoly k i j).totalDegree ≤ i+j+2*k := by
  apply (reynolds_degree _).trans
  apply polyDegree_mul_le
  · simpa using totalDegree_mul (MvPolynomial.X 0^i : Poly3) (MvPolynomial.X 1^j)
  · exact kernelQPoly_degree k

theorem kernelRPoly_degree (k i j : ℕ) : (kernelRPoly k i j).totalDegree ≤ i+j+2*k := by
  have hs := kernelSPoly_degree k i j
  unfold kernelRPoly
  apply polyDegree_add_le
  · apply polyDegree_add_le
    · apply polyDegree_add_le
      · apply polyDegree_add_le
        · exact (polyDegree_C_mul_le _ _).trans hs
        · exact (repeatSubst_degree _ _).trans hs
      · exact (repeatSubst_degree _ _).trans hs
    · exact (repeatSubst_degree _ _).trans hs
  · simp

theorem moment_kernels_canonical_QSR : CanonicalKernelContract :=
  ⟨kernelQPoly_degree,kernelSPoly_degree,kernelRPoly_degree⟩

#check moment_kernels_canonical_QSR
#print axioms moment_kernels_canonical_QSR

#check kernelQPoly
#check kernelSPoly
#check kernelRPoly
#check CanonicalKernelContract
#print axioms CanonicalKernelContract
end Blueprint.Thomson.Finite
