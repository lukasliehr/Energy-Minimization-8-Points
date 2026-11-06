import ThomsonNegative.Structure.Packed.MatrixKernel
import ThomsonNegative.Structure.Packed.IdentitySound
import Mathlib

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Structure.Exact
open ThomsonNegative.Structure.Packed

def EncodedMatrix.eval {m n : Nat} (A : EncodedMatrix m n) (a : ℝ) :
    Matrix (Fin m) (Fin n) ℝ := fun i j =>
  evalZ (recCoeffs (A.numerator i.val j.val)) a / evalZ (recCoeffs A.denominator) a

def EncodedMatrix.RegularAt {m n : Nat} (A : EncodedMatrix m n) (a : ℝ) : Prop :=
  evalZ (recCoeffs A.denominator) a ≠ 0

theorem zeroRecord_decode : recCoeffs zeroRecord=[] := by decide +kernel
theorem oneRecord_decode : recCoeffs oneRecord=[1] := by decide +kernel

@[simp] theorem EncodedMatrix.identity_regular (n : Nat) (a : ℝ) :
    (EncodedMatrix.identity n).RegularAt a := by
  simp [EncodedMatrix.RegularAt, EncodedMatrix.identity, oneRecord_decode, evalZ, horner]

@[simp] theorem EncodedMatrix.zero_regular (m n : Nat) (a : ℝ) :
    (EncodedMatrix.zero m n).RegularAt a := by
  simp [EncodedMatrix.RegularAt, EncodedMatrix.zero, oneRecord_decode, evalZ, horner]

@[simp] theorem EncodedMatrix.eval_identity (n : Nat) (a : ℝ) :
    (EncodedMatrix.identity n).eval a = 1 := by
  ext i j
  by_cases hij : i=j
  · subst j
    simp [EncodedMatrix.eval, EncodedMatrix.identity, Matrix.one_apply,
      zeroRecord_decode, oneRecord_decode, evalZ, horner]
  · have hval : i.val≠j.val := fun h => hij (Fin.ext h)
    simp [EncodedMatrix.eval, EncodedMatrix.identity, Matrix.one_apply,
      zeroRecord_decode, oneRecord_decode, evalZ, horner, hij, hval]

@[simp] theorem EncodedMatrix.eval_zero (m n : Nat) (a : ℝ) :
    (EncodedMatrix.zero m n).eval a = 0 := by
  ext i j
  simp [EncodedMatrix.eval, EncodedMatrix.zero, zeroRecord_decode, oneRecord_decode, evalZ, horner]

theorem product_entry_sound {m n p : Nat} (A : EncodedMatrix m n)
    (B : EncodedMatrix n p) (C : EncodedMatrix m p) (R L W : Nat)
    (i : Fin m) (j : Fin p) (a : ℝ)
    (hA : A.RegularAt a) (hB : B.RegularAt a) (hC : C.RegularAt a)
    (h : (productEquation A B C R L W i.val j.val).check=true) :
    (A.eval a * B.eval a) i j = C.eval a i j := by
  have he := (productEquation A B C R L W i.val j.val).sound h a
  change (∑ k∈Finset.range n,
      evalZ (recCoeffs (A.numerator i.val k)) a * evalZ (recCoeffs (B.numerator k j.val)) a) *
      evalZ (recCoeffs C.denominator) a =
    evalZ (recCoeffs (C.numerator i.val j.val)) a *
      evalZ (recCoeffs A.denominator) a * evalZ (recCoeffs B.denominator) a at he
  rw [← Fin.sum_univ_eq_sum_range] at he
  simp only [Matrix.mul_apply, EncodedMatrix.eval]
  have hs : (∑ k : Fin n,
      evalZ (recCoeffs (A.numerator i.val k.val)) a / evalZ (recCoeffs A.denominator) a *
      (evalZ (recCoeffs (B.numerator k.val j.val)) a / evalZ (recCoeffs B.denominator) a)) =
      (∑ k : Fin n, evalZ (recCoeffs (A.numerator i.val k.val)) a *
        evalZ (recCoeffs (B.numerator k.val j.val)) a) /
          (evalZ (recCoeffs A.denominator) a * evalZ (recCoeffs B.denominator) a) := by
    simp_rw [div_mul_div_comm]
    rw [Finset.sum_div]
  rw [hs]
  apply (div_eq_div_iff (mul_ne_zero hA hB) hC).mpr
  simpa only [mul_assoc] using he

theorem product_matrix_sound {m n p : Nat} (A : EncodedMatrix m n)
    (B : EncodedMatrix n p) (C : EncodedMatrix m p) (R L W : Nat)
    (a : ℝ) (hA : A.RegularAt a) (hB : B.RegularAt a) (hC : C.RegularAt a)
    (h : ∀ j : Fin p, productColumnCheck A B C R L W j.val=true) :
    A.eval a * B.eval a = C.eval a := by
  ext i j
  exact product_entry_sound A B C R L W i j a hA hB hC
    (allBelow_spec m _ (h j) i.val i.isLt)

end ThomsonNegative.Structure.Exact
