import AllS.Units.N_F.N_contact_order
import AllS.Units.N_F.N_definitions
import AllS.Units.N_F.N_potential_jets
import Blueprint.FiniteDefinitions
import Blueprint.Target

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

theorem power_jet_zero (z : ℝ) (j k : ℕ) (Q : Polynomial ℝ) (hk : k < j) :
    ((Polynomial.derivative^[k]) ((Polynomial.X-Polynomial.C z)^j * Q)).eval z = 0 := by
  have hdiv : (Polynomial.X-Polynomial.C z)^(j-k) ∣
      (Polynomial.derivative^[k]) ((Polynomial.X-Polynomial.C z)^j * Q) :=
    Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd k (dvd_mul_right _ _)
  have hx : Polynomial.X-Polynomial.C z ∣
      (Polynomial.derivative^[k]) ((Polynomial.X-Polynomial.C z)^j * Q) := by
    apply dvd_trans _ hdiv
    simpa only [pow_one] using
      (pow_dvd_pow (Polynomial.X-Polynomial.C z) (show 1 ≤ j-k by omega))
  exact Polynomial.dvd_iff_isRoot.mp hx

theorem power_jet_diagonal (z : ℝ) (j : ℕ) (Q : Polynomial ℝ) :
    ((Polynomial.derivative^[j]) ((Polynomial.X-Polynomial.C z)^j * Q)).eval z =
      (j.factorial : ℝ)*Q.eval z := by
  rw [Polynomial.iterate_derivative_mul, Polynomial.eval_finset_sum]
  rw [Finset.sum_eq_single 0]
  · simp [Polynomial.iterate_derivative_X_sub_pow_self]
  · intro b hb hb0
    have hb' : b ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hb)
    have hz : ((Polynomial.derivative^[j-b]) ((Polynomial.X-Polynomial.C z)^j)).eval z = 0 := by
      simpa only [mul_one] using power_jet_zero z j (j-b) 1 (by omega)
    simp [Polynomial.eval_smul, Polynomial.eval_mul, hz]
  · simp

theorem newton_hermite_power_jets (z : ℝ) (j k : ℕ) (Q : Polynomial ℝ) :
    (k < j → ((Polynomial.derivative^[k]) ((Polynomial.X-Polynomial.C z)^j * Q)).eval z = 0) ∧
    ((Polynomial.derivative^[j]) ((Polynomial.X-Polynomial.C z)^j * Q)).eval z =
      (j.factorial : ℝ)*Q.eval z :=
  ⟨power_jet_zero z j k Q, power_jet_diagonal z j Q⟩

#check newton_hermite_power_jets
#print axioms newton_hermite_power_jets
end Blueprint.Thomson.Finite
