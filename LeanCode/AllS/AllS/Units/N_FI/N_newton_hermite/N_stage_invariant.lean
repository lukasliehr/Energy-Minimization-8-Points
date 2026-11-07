import AllS.Units.N_F.N_contact_order
import AllS.Units.N_F.N_definitions
import AllS.Units.N_F.N_potential_jets
import AllS.Units.N_FI.N_newton_hermite.N_basis_jet
import Blueprint.FiniteDefinitions
import Blueprint.Target

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

def newtonHermite (z : ℕ → ℝ) (J : ℕ → ℝ → ℝ) : ℕ → Polynomial ℝ
  | 0 => 0
  | l+1 =>
    let H := newtonHermite z J l
    let r := priorMultiplicity z l (z l)
    let c := (J r (z l)-((Polynomial.derivative^[r]) H).eval (z l)) /
      ((Polynomial.derivative^[r]) (newtonBasis z l)).eval (z l)
    H + Polynomial.C c * newtonBasis z l

@[simp] theorem priorMultiplicity_zero (z : ℕ → ℝ) (x : ℝ) :
    priorMultiplicity z 0 x = 0 := by simp [priorMultiplicity]

theorem priorMultiplicity_succ (z : ℕ → ℝ) (l : ℕ) (x : ℝ) :
    priorMultiplicity z (l+1) x = priorMultiplicity z l x + if z l = x then 1 else 0 := by
  classical
  by_cases h : z l = x <;> simp [priorMultiplicity, Finset.range_add_one, Finset.filter_insert, h]

theorem newtonHermite_jet_update (z : ℕ → ℝ) (J : ℕ → ℝ → ℝ)
    (l k : ℕ) (x : ℝ) :
    ((Polynomial.derivative^[k]) (newtonHermite z J (l+1))).eval x =
    ((Polynomial.derivative^[k]) (newtonHermite z J l)).eval x +
    ((J (priorMultiplicity z l (z l)) (z l) -
      ((Polynomial.derivative^[priorMultiplicity z l (z l)]) (newtonHermite z J l)).eval (z l)) /
      ((Polynomial.derivative^[priorMultiplicity z l (z l)]) (newtonBasis z l)).eval (z l)) *
      ((Polynomial.derivative^[k]) (newtonBasis z l)).eval x := by
  simp only [newtonHermite, ← Module.End.pow_apply, map_add]
  simp only [Module.End.pow_apply, Polynomial.iterate_derivative_C_mul,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]

theorem newton_hermite_stage_invariant (z : ℕ → ℝ) (J : ℕ → ℝ → ℝ) (l : ℕ) :
    (newtonHermite z J l).degree < l ∧
    ∀ (x : ℝ) (k : ℕ), k < priorMultiplicity z l x →
      ((Polynomial.derivative^[k]) (newtonHermite z J l)).eval x = J k x := by
  induction l with
  | zero => simp [newtonHermite]
  | succ l ih =>
    constructor
    · let c := (J (priorMultiplicity z l (z l)) (z l) -
        ((Polynomial.derivative^[priorMultiplicity z l (z l)]) (newtonHermite z J l)).eval (z l)) /
        ((Polynomial.derivative^[priorMultiplicity z l (z l)]) (newtonBasis z l)).eval (z l)
      change (newtonHermite z J l + Polynomial.C c * newtonBasis z l).degree < _
      have hc : (Polynomial.C c * newtonBasis z l).degree ≤ (l : WithBot ℕ) := by
        rw [← newtonBasis_degree z l]
        simpa only [Polynomial.smul_eq_C_mul] using Polynomial.degree_smul_le c (newtonBasis z l)
      have hl : (l : WithBot ℕ) < (l+1 : ℕ) := WithBot.coe_lt_coe.mpr (Nat.lt_succ_self l)
      exact (Polynomial.degree_add_le _ _).trans_lt (max_lt (ih.1.trans hl) (hc.trans_lt hl))
    · intro x k hk
      rw [newtonHermite_jet_update]
      by_cases hold : k < priorMultiplicity z l x
      · rw [newtonBasis_jet_zero z l x k hold, mul_zero, add_zero]
        exact ih.2 x k hold
      · have hx : z l = x := by
          by_contra hn
          rw [priorMultiplicity_succ, if_neg hn, add_zero] at hk
          exact hold hk
        subst x
        have hk' : k = priorMultiplicity z l (z l) := by
          rw [priorMultiplicity_succ, if_pos rfl] at hk
          omega
        subst k
        rw [div_mul_cancel₀ _ (newtonBasis_jet_diagonal_ne_zero z l (z l))]
        ring

#check newton_hermite_stage_invariant
#print axioms newton_hermite_stage_invariant
end Blueprint.Thomson.Finite
