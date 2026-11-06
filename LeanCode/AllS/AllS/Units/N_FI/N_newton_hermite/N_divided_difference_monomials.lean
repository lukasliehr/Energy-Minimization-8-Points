import AllS.Units.N_F.N_contact_order
import AllS.Units.N_F.N_definitions
import AllS.Units.N_F.N_potential_jets
import AllS.Units.N_FI.N_newton_hermite.N_power_jets
import Blueprint.FiniteDefinitions
import Blueprint.Target

/-! Root-authorized implementation repair: exact repeated monic deflation replaces
an auxiliary complete-homogeneous polynomial construction. The source confluent
recurrence and its repeated-node factorial branch remain the same. -/
noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

def polynomialDeflate (x : ℝ) (P : Polynomial ℝ) : Polynomial ℝ :=
  P /ₘ (Polynomial.X-Polynomial.C x)

theorem polynomialDeflate_decomposition (x : ℝ) (P : Polynomial ℝ) :
    P = Polynomial.C (P.eval x)+(Polynomial.X-Polynomial.C x)*polynomialDeflate x P := by
  have h := (Polynomial.modByMonic_add_div P (Polynomial.X-Polynomial.C x)).symm
  rw [Polynomial.modByMonic_X_sub_C_eq_C_eval] at h
  exact h

theorem polynomialDeflate_eval_relation (x y : ℝ) (P : Polynomial ℝ) :
    P.eval y = P.eval x+(y-x)*(polynomialDeflate x P).eval y := by
  have h := congrArg (Polynomial.eval y) (polynomialDeflate_decomposition x P)
  simpa only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_X] using h

theorem polynomialDeflate_eval_swap (x y : ℝ) (P : Polynomial ℝ) :
    (polynomialDeflate x P).eval y = (polynomialDeflate y P).eval x := by
  by_cases hxy : x = y
  · subst y; rfl
  have h₁ := polynomialDeflate_eval_relation x y P
  have h₂ := polynomialDeflate_eval_relation y x P
  apply mul_left_cancel₀ (sub_ne_zero.mpr (Ne.symm hxy))
  nlinarith [h₁, h₂]

theorem polynomialDeflate_commute (x y : ℝ) (P : Polynomial ℝ) :
    polynomialDeflate x (polynomialDeflate y P) = polynomialDeflate y (polynomialDeflate x P) := by
  have hX := polynomialDeflate_decomposition x P
  have hY := polynomialDeflate_decomposition y P
  have hXY := polynomialDeflate_decomposition y (polynomialDeflate x P)
  have hYX := polynomialDeflate_decomposition x (polynomialDeflate y P)
  rw [← polynomialDeflate_eval_swap x y P] at hYX
  have hC := congrArg (Polynomial.C : ℝ → Polynomial ℝ) (polynomialDeflate_eval_relation x y P)
  simp only [Polynomial.C_add, Polynomial.C_mul, Polynomial.C_sub] at hC
  apply mul_left_cancel₀
    (mul_ne_zero (Polynomial.X_sub_C_ne_zero x) (Polynomial.X_sub_C_ne_zero y))
  linear_combination hX-hY+(Polynomial.X-Polynomial.C x)*hXY-
    (Polynomial.X-Polynomial.C y)*hYX-hC

theorem polynomialDeflate_difference (x y : ℝ) (P : Polynomial ℝ) :
    polynomialDeflate x P-polynomialDeflate y P =
      Polynomial.C (x-y)*polynomialDeflate x (polynomialDeflate y P) := by
  have hXY := polynomialDeflate_decomposition y (polynomialDeflate x P)
  have hYX := polynomialDeflate_decomposition x (polynomialDeflate y P)
  rw [← polynomialDeflate_eval_swap x y P] at hYX
  rw [← polynomialDeflate_commute x y P] at hXY
  rw [Polynomial.C_sub]
  linear_combination hXY-hYX

theorem polynomialDeflate_taylor_coeff (x : ℝ) (P : Polynomial ℝ) (n : ℕ) :
    (Polynomial.taylor x (polynomialDeflate x P)).coeff n = (Polynomial.taylor x P).coeff (n+1) := by
  have h := congrArg (Polynomial.taylor x) (polynomialDeflate_decomposition x P)
  simp only [map_add, Polynomial.taylor_C, Polynomial.taylor_mul, map_sub,
    Polynomial.taylor_X, add_sub_cancel_right] at h
  have hc := congrArg (fun Q : Polynomial ℝ => Q.coeff (n+1)) h
  simpa only [Polynomial.coeff_add, Polynomial.coeff_C, Nat.add_one_ne_zero, ite_false,
    Polynomial.coeff_X_mul, zero_add] using hc.symm

theorem polynomialDeflate_iterate_taylor_coeff (x : ℝ) (P : Polynomial ℝ) (k n : ℕ) :
    (Polynomial.taylor x ((polynomialDeflate x)^[k] P)).coeff n =
      (Polynomial.taylor x P).coeff (n+k) := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', polynomialDeflate_taylor_coeff, ih]
    congr 1
    omega

theorem polynomialDeflate_iterate_eval (x : ℝ) (P : Polynomial ℝ) (k : ℕ) :
    ((polynomialDeflate x)^[k] P).eval x =
      ((Polynomial.derivative^[k]) P).eval x / (k.factorial : ℝ) := by
  have h := polynomialDeflate_iterate_taylor_coeff x P k 0
  simp only [zero_add, Polynomial.taylor_coeff, Polynomial.hasseDeriv_zero, LinearMap.id_apply] at h
  rw [h, eq_div_iff (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))]
  have hf := congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℝ) (k := k)) P
  have hev := congrArg (Polynomial.eval x) hf
  change (k.factorial • Polynomial.hasseDeriv k P).eval x =
    ((Polynomial.derivative^[k]) P).eval x at hev
  simpa only [nsmul_eq_mul, Polynomial.eval_mul, Polynomial.eval_natCast, mul_comm] using hev

theorem newton_hermite_divided_difference_monomials (x y : ℝ) (P : Polynomial ℝ) :
    (polynomialDeflate x P).eval y = (polynomialDeflate y P).eval x ∧
    polynomialDeflate x (polynomialDeflate y P) = polynomialDeflate y (polynomialDeflate x P) ∧
    polynomialDeflate x P-polynomialDeflate y P =
      Polynomial.C (x-y)*polynomialDeflate x (polynomialDeflate y P) ∧
    ∀ k : ℕ, ((polynomialDeflate x)^[k] P).eval x =
      ((Polynomial.derivative^[k]) P).eval x / (k.factorial : ℝ) :=
  ⟨polynomialDeflate_eval_swap x y P, polynomialDeflate_commute x y P,
    polynomialDeflate_difference x y P, polynomialDeflate_iterate_eval x P⟩

#check newton_hermite_divided_difference_monomials
#print axioms newton_hermite_divided_difference_monomials
end Blueprint.Thomson.Finite
