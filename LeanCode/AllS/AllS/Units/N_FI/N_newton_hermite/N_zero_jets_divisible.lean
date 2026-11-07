import AllS.Units.N_F.N_contact_order
import AllS.Units.N_F.N_definitions
import AllS.Units.N_F.N_potential_jets
import Blueprint.FiniteDefinitions
import Blueprint.Target

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

theorem newton_hermite_zero_jets_divisible (P : Polynomial ℝ) (z : ℝ) (m : ℕ)
    (hjets : ∀ j < m, ((Polynomial.derivative^[j]) P).eval z = 0) :
    (Polynomial.X-Polynomial.C z)^m ∣ P := by
  by_cases hP : P = 0
  · simp [hP]
  cases m with
  | zero => simp
  | succ m =>
    have hm : m < P.rootMultiplicity z :=
      Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative hP
        (fun j hj => hjets j (by omega))
    exact (pow_dvd_pow (Polynomial.X-Polynomial.C z) (Nat.succ_le_of_lt hm)).trans
      (Polynomial.pow_rootMultiplicity_dvd P z)

#check newton_hermite_zero_jets_divisible
#print axioms newton_hermite_zero_jets_divisible
end Blueprint.Thomson.Finite
