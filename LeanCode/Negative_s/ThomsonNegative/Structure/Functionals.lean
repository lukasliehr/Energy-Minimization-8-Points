import ThomsonNegative.Structure.Coordinates
import ThomsonNegative.Geometry.Target

/-! The two exact candidate-family compatibility forms, with frozen polynomial coefficients. -/

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Structure

def contactPolynomial : Fin 4 → Polynomial ℝ :=
  ![Polynomial.X, 2*Polynomial.X-1,
    -Polynomial.X+Polynomial.C (Real.sqrt 2/2)*(1-Polynomial.X),
    -Polynomial.X-Polynomial.C (Real.sqrt 2/2)*(1-Polynomial.X)]

def orbitLabels : Fin 5 → Fin 3 → Fin 4 :=
  ![![0,0,1],![0,2,2],![0,3,3],![0,2,3],![1,2,3]]

def orbitCount : Fin 5 → ℝ := ![8,8,8,16,16]

def orbitSubstitution (r : Fin 5) : Poly3 →ₐ[ℝ] Polynomial ℝ :=
  MvPolynomial.aeval (fun i => contactPolynomial (orbitLabels r i))

def familyPolynomial : Poly3 →ₗ[ℝ] Polynomial ℝ :=
  ∑ r : Fin 5, orbitCount r • (orbitSubstitution r).toLinearMap

def ell0 (a : ℝ) : Poly3 →ₗ[ℝ] ℝ where
  toFun p := (familyPolynomial p).eval a
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def ell1 (a : ℝ) : Poly3 →ₗ[ℝ] ℝ where
  toFun p := (familyPolynomial p).derivative.eval a
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def coefficientEll0 (a : ℝ) : FullSpace →ₗ[ℝ] ℝ := (ell0 a).comp physicalSynthesize
def coefficientEll1 (a : ℝ) : FullSpace →ₗ[ℝ] ℝ := (ell1 a).comp physicalSynthesize

theorem contactPolynomial_eval (a : ℝ) (i : Fin 4) :
    (contactPolynomial i).eval a = ThomsonNegative.Geometry.contacts a i := by
  have hs := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hn : Real.sqrt (2:ℝ)≠0 := by positivity
  have hi : (Real.sqrt (2:ℝ))⁻¹=Real.sqrt 2/2 := by field_simp; nlinarith
  fin_cases i <;> simp [contactPolynomial, ThomsonNegative.Geometry.contacts,div_eq_mul_inv,hi] <;> ring

theorem familyPolynomial_apply (p : Poly3) :
    familyPolynomial p=∑ r : Fin 5, orbitCount r • orbitSubstitution r p := by
  simp only [familyPolynomial, LinearMap.sum_apply, LinearMap.smul_apply, AlgHom.toLinearMap_apply]

theorem familyPolynomial_one : familyPolynomial (1 : Poly3)=Polynomial.C 56 := by
  apply Polynomial.funext
  intro a
  norm_num [familyPolynomial_apply, orbitCount, orbitSubstitution, Fin.sum_univ_succ]

theorem familyPolynomial_sigma_square : familyPolynomial (sigma^2)=
    192*Polynomial.X^2-128*Polynomial.X+56 := by
  apply Polynomial.funext
  intro a
  simp [familyPolynomial_apply, orbitCount, orbitSubstitution, sigma, contactPolynomial,
    orbitLabels, Fin.sum_univ_succ]
  ring_nf
  norm_num [Real.sq_sqrt] <;> ring

theorem ell0_one (a : ℝ) : ell0 a (1 : Poly3)=56 := by
  simp [ell0,familyPolynomial_one]

theorem ell1_one (a : ℝ) : ell1 a (1 : Poly3)=0 := by
  simp [ell1,familyPolynomial_one]

theorem ell0_sigma_square (a : ℝ) : ell0 a (sigma^2)=192*a^2-128*a+56 := by
  simp [ell0,familyPolynomial_sigma_square]

theorem ell1_sigma_square (a : ℝ) : ell1 a (sigma^2)=128*(3*a-1) := by
  simp [ell1,familyPolynomial_sigma_square]
  ring

theorem physicalSynthesize_single (i : Fin 102) (c : ℝ) :
    physicalSynthesize (Pi.single i c)=c • invariantMonomial (fullTag i) := by
  classical
  change invariantSubst (synthesize (Pi.single i c))=_
  simp [synthesize, Pi.single_apply, invariantSubst_coordinateMonomial, MvPolynomial.smul_eq_C_mul]
  have hh (x : Fin 102) : MvPolynomial.C (if x=i then c else 0) * invariantMonomial (fullTag x) =
      if x=i then MvPolynomial.C c * invariantMonomial (fullTag i) else 0 := by
    by_cases hx : x=i <;> simp [hx]
  simp_rw [hh]
  simp

theorem physicalSynthesize_one : physicalSynthesize (Pi.single (0:Fin 102) (1:ℝ))=1 := by
  rw [physicalSynthesize_single]
  simp [fullTag,invariantMonomial]

theorem physicalSynthesize_square : physicalSynthesize (Pi.single (3:Fin 102) (1:ℝ))=sigma^2 := by
  rw [physicalSynthesize_single]
  simp [fullTag,invariantMonomial]

def coefficientCompatibility (a : ℝ) (ha : a<1/3) : CompatibilityData FullSpace where
  ell0 := coefficientEll0 a
  ell1 := coefficientEll1 a
  one := Pi.single (0:Fin 102) 1
  square := Pi.single (3:Fin 102) 1
  kappa := 192*a^2-128*a+56
  tau := 128*(3*a-1)
  tau_ne_zero := by nlinarith
  ell0_one := by simp [coefficientEll0,physicalSynthesize_one,ell0_one]
  ell1_one := by simp [coefficientEll1,physicalSynthesize_one,ell1_one]
  ell0_square := by simp [coefficientEll0,physicalSynthesize_square,ell0_sigma_square]
  ell1_square := by simp [coefficientEll1,physicalSynthesize_square,ell1_sigma_square]

end ThomsonNegative.Structure
