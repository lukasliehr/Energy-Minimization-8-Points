import ThomsonNegative.Structure.Packed.PolynomialLift
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Rational functions of height, with explicit integer polynomial semantics.
The lists occur only in the mathematical interface; arithmetic leaves may use
packed naturals and prove their decoded polynomial identities separately. -/

noncomputable section
open scoped BigOperators

namespace ThomsonNegative.Structure

open Packed PolynomialLift

structure RF where
  numerator : List ℤ
  denominator : List ℤ

def RF.eval (r : RF) (a : ℝ) : ℝ :=
  evalZ r.numerator a / evalZ r.denominator a

def RF.RegularAt (r : RF) (a : ℝ) : Prop := evalZ r.denominator a ≠ 0

def RF.Represents (r : RF) (f : ℝ → ℝ) : Prop :=
  ∀ a : ℝ, (5 / 16 : ℝ) < a → a < 1 / 3 → r.eval a = f a

abbrev RFMatrix (m n : ℕ) := Matrix (Fin m) (Fin n) RF

def RFMatrix.eval {m n : ℕ} (A : RFMatrix m n) (a : ℝ) :
    Matrix (Fin m) (Fin n) ℝ := fun i j => (A i j).eval a

theorem RF.eval_eq_of_cross_identity (r s : RF) (a : ℝ)
    (hr : r.RegularAt a) (hs : s.RegularAt a)
    (h : evalZ (convL r.numerator s.denominator) a =
      evalZ (convL s.numerator r.denominator) a) : r.eval a = s.eval a := by
  rw [evalZ_convL, evalZ_convL] at h
  exact (div_eq_div_iff hr hs).mpr h

theorem RF.eval_mul_denominator (r : RF) (a : ℝ) (hr : r.RegularAt a) :
    r.eval a * evalZ r.denominator a = evalZ r.numerator a := by
  exact div_mul_cancel₀ _ hr

theorem RF.eval_eq_zero (r : RF) (a : ℝ) (h : evalZ r.numerator a = 0) :
    r.eval a = 0 := by simp [RF.eval, h]

end ThomsonNegative.Structure
