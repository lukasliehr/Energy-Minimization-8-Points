import Mathlib

/-! The fixed eight-block interface shared by the structural and geometric lanes. -/

noncomputable section
open scoped BigOperators

namespace ThomsonNegative.Structure

abbrev Poly3 := MvPolynomial (Fin 3) ℝ
abbrev Tag := ℕ × ℕ × ℕ
abbrev Block := Fin 8

def blockSize : Block → ℕ := ![6, 5, 4, 3, 2, 1, 11, 11]

abbrev GramFamily := ∀ b : Block,
  Matrix (Fin (blockSize b)) (Fin (blockSize b)) ℝ

abbrev PolynomialFamily := ∀ b : Block,
  Matrix (Fin (blockSize b)) (Fin (blockSize b)) Poly3

def gramPolynomial (P : PolynomialFamily) (W : GramFamily) : Poly3 :=
  ∑ b, ∑ i, ∑ j, MvPolynomial.C (W b i j) * P b i j

def gramLinear (P : PolynomialFamily) : GramFamily →ₗ[ℝ] Poly3 where
  toFun := gramPolynomial P
  map_add' W V := by
    simp only [gramPolynomial, Pi.add_apply, Matrix.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' c W := by
    simp only [gramPolynomial, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
    simp only [MvPolynomial.smul_eq_C_mul, Finset.mul_sum, mul_assoc, RingHom.id_apply]

@[simp] theorem gramLinear_apply (P : PolynomialFamily) (W : GramFamily) :
    gramLinear P W = gramPolynomial P W := rfl

theorem gramPolynomial_add (P : PolynomialFamily) (W V : GramFamily) :
    gramPolynomial P (W + V) = gramPolynomial P W + gramPolynomial P V :=
  (gramLinear P).map_add W V

def sigma : Poly3 := MvPolynomial.X 0 + MvPolynomial.X 1 + MvPolynomial.X 2
def e2 : Poly3 := MvPolynomial.X 0 * MvPolynomial.X 1 +
  MvPolynomial.X 0 * MvPolynomial.X 2 + MvPolynomial.X 1 * MvPolynomial.X 2
def e3 : Poly3 := MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2

def invariantSubst : Poly3 →ₐ[ℝ] Poly3 :=
  MvPolynomial.aeval (fun i : Fin 3 => ![sigma, e2, e3] i)

def tagWeight (t : Tag) : ℕ := t.1 + 2 * t.2.1 + 3 * t.2.2

def tagExponent (t : Tag) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 t.1 + Finsupp.single 1 t.2.1 + Finsupp.single 2 t.2.2

def invariantMonomial (t : Tag) : Poly3 := sigma ^ t.1 * e2 ^ t.2.1 * e3 ^ t.2.2

def coordinateMonomial (t : Tag) : Poly3 :=
  MvPolynomial.X 0 ^ t.1 * MvPolynomial.X 1 ^ t.2.1 * MvPolynomial.X 2 ^ t.2.2

@[simp] theorem invariantSubst_coordinateMonomial (t : Tag) :
    invariantSubst (coordinateMonomial t) = invariantMonomial t := by
  simp [coordinateMonomial, invariantSubst, invariantMonomial]

def compatible (ell0 ell1 : Poly3 →ₗ[ℝ] ℝ) (f : Poly3) : Prop :=
  ell0 f = 0 ∧ ell1 f = 0

theorem compatible_sub {ell0 ell1 : Poly3 →ₗ[ℝ] ℝ} {f g : Poly3}
    (hf : compatible ell0 ell1 f) (hg : compatible ell0 ell1 g) :
    compatible ell0 ell1 (f - g) := by
  constructor <;> simp only [map_sub] <;> simp [hf.1, hf.2, hg.1, hg.2]

end ThomsonNegative.Structure
