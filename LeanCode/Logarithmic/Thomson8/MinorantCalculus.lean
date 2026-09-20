import Thomson8.HermiteValues
import Thomson8.MinorantArithmetic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Thomson8

noncomputable def Hprime (x : ℝ) : ℝ := ∑ ell : Fin 5,
  logValues ell * (Poly.derivU (hermiteComponent Data.hermite ell)).eval x 0 0

theorem hasDerivAt_H (x : ℝ) : HasDerivAt H (Hprime x) x := by
  exact HasDerivAt.fun_sum fun ell _ =>
    (Poly.hasDerivAt_eval (hermiteComponent Data.hermite ell) x 0 0).const_mul (logValues ell)

theorem H_continuous : Continuous H := continuous_iff_continuousAt.mpr fun x =>
  (hasDerivAt_H x).continuousAt

theorem hasDerivAt_phi {x : ℝ} (hx : x < 1) :
    HasDerivAt phi (1/(2*(1-x))) x := by
  have hp : 2-2*x ≠ 0 := by linarith
  have h := (((hasDerivAt_id x).const_mul 2).const_sub 2).log hp
  convert! h.neg.div_const 2 using 1
  dsimp
  field_simp [show 1-x ≠ 0 by linarith] <;> ring

noncomputable def minorantGap (x : ℝ) : ℝ := phi x-H x

theorem qComponent_eval (ell : ℕ) (x : ℝ) : (qComponent ell).eval x 0 0 =
    quartic (qCoeff 0 ell).eval (qCoeff 1 ell).eval (qCoeff 2 ell).eval
      (qCoeff 3 ell).eval (qCoeff 4 ell).eval x := by
  norm_num [qComponent,List.range_succ,Poly.eval,Exponent.eval,quartic]
  ring

theorem derivativeNumerator_eval (ell : ℕ) (x : ℝ) :
    (derivativeNumerator ell).eval x 0 0 = (if ell=0 then 1 else 0) +
      2*(x-1)*(Poly.derivU (hermiteComponent Data.hermite ell)).eval x 0 0 := by
  by_cases he : ell=0 <;> simp [derivativeNumerator,linearFactor,Exponent.eval,he] <;> ring

theorem contactFactor_eval (x : ℝ) : contactFactor.eval x 0 0 =
    (x+1)^4*(x-nodeA.eval)*(x-nodeB.eval)*(x-nodeC.eval)*(x-nodeD.eval) := by
  simp [contactFactor,linearFactor,Exponent.eval]
  ring

theorem derivative_numerator_identity (x : ℝ) :
    1-2*(1-x)*Hprime x =
      (x+1)^4*(x-nodeA.eval)*(x-nodeB.eval)*(x-nodeC.eval)*(x-nodeD.eval)*minorantQ x := by
  have h (ell : Fin 5) := derivative_factor_component ell x
  simp only [derivativeNumerator_eval,contactFactor_eval,qComponent_eval] at h
  have hs := congrArg (fun f : Fin 5 → ℝ => ∑ ell : Fin 5, logValues ell * f ell) (funext h)
  simp only [Hprime,minorantQ,qRealCoeff,quartic,Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ,
    Finset.univ_eq_empty,Finset.sum_empty] at hs ⊢
  norm_num [logValues] at hs ⊢
  linear_combination hs

noncomputable def gapDerivative (x : ℝ) : ℝ :=
  (x+1)^4*(x-nodeA.eval)*(x-nodeB.eval)*(x-nodeC.eval)*(x-nodeD.eval)*minorantQ x /
    (2*(1-x))

theorem hasDerivAt_gap {x : ℝ} (hx : x < 1) :
    HasDerivAt minorantGap (gapDerivative x) x := by
  have h := (hasDerivAt_phi hx).sub (hasDerivAt_H x)
  convert! h using 1
  rw [gapDerivative,←derivative_numerator_identity]
  have hp : 2*(1-x) ≠ 0 := by positivity
  field_simp [show 1-x ≠ 0 by linarith] <;> ring

theorem gap_continuousOn {b : ℝ} (hb : b < 1) (a : ℝ) :
    ContinuousOn minorantGap (Set.Icc a b) := by
  intro x hx
  exact (hasDerivAt_gap (hx.2.trans_lt hb)).continuousAt.continuousWithinAt

theorem gap_minus_one : minorantGap (-1)=0 := by rw [minorantGap,H_minus_one]; ring

theorem gap_contact (i : Fin 4) : minorantGap (nodes.getD i K.zero).eval=0 := by
  rw [minorantGap,H_contact]; ring

#print axioms derivative_numerator_identity
#print axioms hasDerivAt_gap

end Thomson8
