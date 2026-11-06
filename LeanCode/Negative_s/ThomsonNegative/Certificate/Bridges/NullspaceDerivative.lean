import ThomsonNegative.Structure.Functionals

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure

theorem coefficientEll_hasDerivAt (v : FullSpace) (a : ℝ) :
    HasDerivAt (fun t => coefficientEll0 t v) (coefficientEll1 a v) a :=
  (familyPolynomial (physicalSynthesize v)).hasDerivAt a

theorem matrix_nullspace_derivative {ι κ : Type*} [Fintype ι] [Fintype κ]
    (T : ℝ → Matrix ι ι ℝ) (U : ℝ → Matrix ι κ ℝ)
    (T1 : Matrix ι ι ℝ) (U1 : Matrix ι κ ℝ) (a : ℝ)
    (hs : (T a).IsSymm)
    (hT : ∀ r s,HasDerivAt (fun t => T t r s) (T1 r s) a)
    (hU : ∀ s j,HasDerivAt (fun t => U t s j) (U1 s j) a)
    (hnull : ∀ t,T t*U t=0) :
    (U a).transpose*T1*U a=0 := by
  classical
  have hd : T1*U a+T a*U1=0 := by
    ext r j
    have hf : (fun t => ∑ s,T t r s*U t s j)=(fun _ : ℝ => 0) := by
      funext t
      exact congrFun (congrFun (hnull t) r) j
    have hh := HasDerivAt.fun_sum (fun s (_ : s ∈ Finset.univ) => (hT r s).mul (hU s j))
    simp only [Pi.mul_apply] at hh
    rw [hf] at hh
    have he := hh.unique (hasDerivAt_const a (0:ℝ))
    simpa only [Matrix.add_apply,Matrix.mul_apply,Matrix.zero_apply,Finset.sum_add_distrib] using he
  have hleft : (U a).transpose*T a=0 := by
    have hh := congrArg Matrix.transpose (hnull a)
    simpa only [Matrix.transpose_mul,hs.eq,Matrix.transpose_zero] using hh
  have hh := congrArg (fun M => (U a).transpose*M) hd
  simpa only [Matrix.mul_add,← Matrix.mul_assoc,hleft,Matrix.zero_mul,add_zero,Matrix.mul_zero] using hh

theorem differentiable_matrix_nullspace_derivative {ι κ : Type*} [Fintype ι] [Fintype κ]
    (T : ℝ → Matrix ι ι ℝ) (U : ℝ → Matrix ι κ ℝ)
    (T1 : Matrix ι ι ℝ) (a : ℝ)
    (hs : (T a).IsSymm)
    (hT : ∀ r s,HasDerivAt (fun t => T t r s) (T1 r s) a)
    (hU : ∀ s j,DifferentiableAt ℝ (fun t => U t s j) a)
    (hnull : ∀ t,T t*U t=0) :
    (U a).transpose*T1*U a=0 :=
  matrix_nullspace_derivative T U T1 (fun s j => deriv (fun t => U t s j) a) a hs hT
    (fun s j => (hU s j).hasDerivAt) hnull

#print axioms matrix_nullspace_derivative
#print axioms coefficientEll_hasDerivAt
end ThomsonNegative.Certificate.Bridges
