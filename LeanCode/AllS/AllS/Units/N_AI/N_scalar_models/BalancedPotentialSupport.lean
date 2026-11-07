import AllS.Units.N_AI.N_scalar_models.PotentialSourceSupport
import AllS.Units.N_AI.N_scalar_models.HermiteAffineDataSupport

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP
open Blueprint.Thomson.Finite

def balancedMultiplier (c s : ℝ) : ℝ :=
  (s/c) * Real.exp (((s-c)/2) * Real.log (3/2))

def balancedShift (c s : ℝ) : ℝ :=
  Real.exp (((s-c)/2) * Real.log (3/2)) / c

def balancedJet (c s : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  balancedMultiplier c s * potentialJet s k t + if k = 0 then balancedShift c s else 0

theorem balancedMultiplier_pos (c s : ℝ) (hc : 0 < c) (hs : 0 < s) :
    0 < balancedMultiplier c s :=
  mul_pos (div_pos hs hc) (Real.exp_pos _)

theorem balancedJet_zero_factor (c s t : ℝ) :
    balancedJet c s 0 t =
      (Real.exp (((s-c)/2) * Real.log (3/2)) / c) * (1+s*phi s t) := by
  simp [balancedJet, balancedMultiplier, balancedShift]
  <;> ring

theorem balancedSourceValue (c s t : ℝ) (ht : t < 1) :
    Real.exp ((-c/2)*Real.log (3/2)) / c *
        Real.exp ((-s/2)*Real.log ((2-2*t)/(3/2))) =
      balancedJet c s 0 t := by
  have hd : 0 < 2-2*t := by linarith
  rw [balancedJet_zero_factor, potential_value_factor, Real.rpow_def_of_pos hd]
  calc
    _ = Real.exp ((-c/2)*Real.log (3/2) +
          (-s/2)*Real.log ((2-2*t)/(3/2))) / c := by
      rw [Real.exp_add]
      ring
    _ = Real.exp (((s-c)/2)*Real.log (3/2) + Real.log (2-2*t)*(-s/2)) / c := by
      congr 2
      rw [Real.log_div hd.ne' (by norm_num : (3/2:ℝ) ≠ 0)]
      ring
    _ = _ := by rw [Real.exp_add]; ring

theorem balancedSourceRecurrence (c s t : ℝ) (k : ℕ) (ht : t < 1) :
    ((s+2*(k:ℝ))*balancedJet c s k t)/(2-2*t) = balancedJet c s (k+1) t := by
  have hd : 0 < 2-2*t := by linarith
  cases k with
  | zero =>
    rw [balancedJet_zero_factor, potential_value_factor]
    simp only [Nat.cast_zero, mul_zero, add_zero, balancedJet, Nat.reduceAdd,
      Nat.one_ne_zero, if_false, potentialJet_one]
    rw [show (-1-s/2:ℝ) = -1+(-s/2) by ring, Real.rpow_add hd, Real.rpow_neg_one]
    unfold balancedMultiplier
    ring
  | succ k =>
    simp only [balancedJet, Nat.succ_ne_zero, if_false, add_zero]
    rw [potentialJet_recurrence s t k ht]
    push_cast
    ring

theorem balancedHermite_affine (z : Fin 5 → ℝ) (m : Fin 5 → ℕ)
    (c s : ℝ) (hz : Function.Injective z) (hm : 0 < ∑ i, m i) :
    profileHermite z m (balancedJet c s) =
      Polynomial.C (balancedMultiplier c s) * profileHermite z m (potentialJet s) +
        Polynomial.C (balancedShift c s) :=
  profileHermite_affine z m (potentialJet s) (balancedMultiplier c s) (balancedShift c s) hz hm

#print axioms balancedMultiplier_pos
#print axioms balancedSourceValue
#print axioms balancedSourceRecurrence
#print axioms balancedHermite_affine
end Blueprint.CAP
