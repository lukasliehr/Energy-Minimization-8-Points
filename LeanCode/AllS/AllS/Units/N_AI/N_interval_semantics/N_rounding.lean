import Blueprint.CAPContracts
import Blueprint.Target

namespace Blueprint.CAP
def IntervalRoundingStatement : Prop :=
  ∀ (n zl zu : ℤ) (d b : ℕ), 0<d → zl*(d:ℤ) ≤ n*2^b → n*2^b ≤ zu*(d:ℤ) →
    (zl:ℝ)/2^b ≤ (n:ℝ)/d ∧ (n:ℝ)/d ≤ (zu:ℝ)/2^b
theorem interval_semantics_rounding : IntervalRoundingStatement := by
  intro n zl zu d b hd hl hu
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hp : (0:ℝ)<2^b := pow_pos (by norm_num) b
  have hlR : (zl:ℝ)*(d:ℝ)≤(n:ℝ)*2^b := by exact_mod_cast hl
  have huR : (n:ℝ)*2^b≤(zu:ℝ)*(d:ℝ) := by exact_mod_cast hu
  exact ⟨(div_le_div_iff₀ hp hdR).2 hlR, (div_le_div_iff₀ hdR hp).2 huR⟩

theorem floorCeil_cross_bounds (n : ℤ) (d b : ℕ) (hd : 0<d) :
    ((n*2^b)/(d:ℤ))*(d:ℤ) ≤ n*2^b ∧
    n*2^b ≤ -((-n*2^b)/(d:ℤ))*(d:ℤ) := by
  have hdI : (0:ℤ)<d := by exact_mod_cast hd
  constructor
  · exact Int.ediv_mul_le _ (ne_of_gt hdI)
  · have h := Int.ediv_mul_le (-n*2^b) (ne_of_gt hdI)
    nlinarith

#check interval_semantics_rounding
#print interval_semantics_rounding
#print axioms interval_semantics_rounding
#print axioms floorCeil_cross_bounds
end Blueprint.CAP
