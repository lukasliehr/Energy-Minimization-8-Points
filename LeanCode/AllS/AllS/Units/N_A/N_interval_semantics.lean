import AllS.Units.N_AI.N_interval_semantics.N_affine
import AllS.Units.N_AI.N_interval_semantics.N_product
import AllS.Units.N_AI.N_interval_semantics.N_inverse_sqrt
import AllS.Units.N_AI.N_interval_semantics.N_hulls
import AllS.Units.N_AI.N_interval_semantics.N_rounding

namespace Blueprint.CAP
def IntervalQuotientStatement : Prop :=
  ∀ {I J InvJ K : Box} {x y : ℝ}, I.Contains x → J.Contains y →
    Box.InvGate J InvJ → Box.MulGate I InvJ K → K.Contains (x/y) ∧ y≠0
def IntervalOperationsStatement : Prop :=
  IntervalAffineStatement ∧ IntervalProductStatement ∧ IntervalInverseSqrtStatement ∧
    IntervalHullsStatement ∧ IntervalRoundingStatement ∧ IntervalQuotientStatement
theorem interval_quotient_sound : IntervalQuotientStatement := by
  intro I J InvJ K x y hx hy hi hm
  have hinv := Box.contains_inverse hy hi
  have hprod := Box.contains_mul hx hinv.1 hm
  exact ⟨by simpa only [div_eq_mul_inv, one_mul] using hprod, hinv.2⟩

theorem intervalOperations_sound : IntervalOperationsStatement :=
  ⟨interval_semantics_affine, interval_semantics_product,
    interval_semantics_inverse_sqrt, interval_semantics_hulls,
    interval_semantics_rounding, interval_quotient_sound⟩
#check intervalOperations_sound
#print IntervalOperationsStatement
#print axioms intervalOperations_sound
end Blueprint.CAP
