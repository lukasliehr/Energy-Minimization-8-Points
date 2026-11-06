import Mathlib

/-! Exact recovery of the constant and sigma-squared coordinates. -/

noncomputable section

namespace ThomsonNegative.Structure

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

structure CompatibilityData (V : Type*) [AddCommGroup V] [Module ℝ V] where
  ell0 : V →ₗ[ℝ] ℝ
  ell1 : V →ₗ[ℝ] ℝ
  one : V
  square : V
  kappa : ℝ
  tau : ℝ
  tau_ne_zero : tau ≠ 0
  ell0_one : ell0 one = 56
  ell1_one : ell1 one = 0
  ell0_square : ell0 square = kappa
  ell1_square : ell1 square = tau

def CompatibilityData.sigmaCoefficient (D : CompatibilityData V) (v : V) : ℝ :=
  -D.ell1 v / D.tau

def CompatibilityData.constantCoefficient (D : CompatibilityData V) (v : V) : ℝ :=
  -(D.ell0 v + D.kappa * D.sigmaCoefficient v) / 56

def CompatibilityData.recover (D : CompatibilityData V) (v : V) : V :=
  v + D.sigmaCoefficient v • D.square + D.constantCoefficient v • D.one

theorem CompatibilityData.recover_ell (D : CompatibilityData V) (v : V) :
    D.ell0 (D.recover v) = 0 ∧ D.ell1 (D.recover v) = 0 := by
  simp only [CompatibilityData.recover, map_add, map_smul, smul_eq_mul,
    D.ell0_one, D.ell1_one, D.ell0_square, D.ell1_square]
  constructor
  · simp only [CompatibilityData.constantCoefficient]
    ring
  · simp only [CompatibilityData.sigmaCoefficient, mul_zero, add_zero]
    field_simp [D.tau_ne_zero]
    ring

theorem CompatibilityData.recover_unique (D : CompatibilityData V) (v f : V)
    (h0 : D.ell0 f = 0) (h1 : D.ell1 f = 0) (c0 c2 : ℝ)
    (hf : f = v + c2 • D.square + c0 • D.one) : D.recover v = f := by
  have he0 := congrArg D.ell0 hf
  have he1 := congrArg D.ell1 hf
  simp only [map_add, map_smul, smul_eq_mul, D.ell0_one, D.ell1_one,
    D.ell0_square, D.ell1_square, h0, h1, mul_zero, add_zero] at he0 he1
  have hc2 : D.sigmaCoefficient v = c2 := by
    apply (div_eq_iff D.tau_ne_zero).mpr
    linarith
  have hc0 : D.constantCoefficient v = c0 := by
    dsimp [CompatibilityData.constantCoefficient]
    rw [hc2]
    apply (div_eq_iff (by norm_num : (56 : ℝ) ≠ 0)).mpr
    linarith
  rw [CompatibilityData.recover, hc2, hc0]
  exact hf.symm

theorem CompatibilityData.equal_of_two_missing (D : CompatibilityData V) (f g : V)
    (hf0 : D.ell0 f = 0) (hf1 : D.ell1 f = 0)
    (hg0 : D.ell0 g = 0) (hg1 : D.ell1 g = 0)
    (c0 c2 : ℝ) (h : f - g = c2 • D.square + c0 • D.one) : f = g := by
  have hf : f = g + c2 • D.square + c0 • D.one := by
    have := (sub_eq_iff_eq_add).mp h
    rw [this]
    abel
  have hrecover := D.recover_unique g f hf0 hf1 c0 c2 hf
  have hg : D.recover g = g := by
    simp [CompatibilityData.recover, CompatibilityData.sigmaCoefficient,
      CompatibilityData.constantCoefficient, hg0, hg1]
  exact hrecover.symm.trans hg

end ThomsonNegative.Structure
