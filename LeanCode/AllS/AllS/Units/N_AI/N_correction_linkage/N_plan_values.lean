import Blueprint.CAPContracts

noncomputable section
namespace Blueprint.CAP

def CorrectionPlanValuesStatement : Prop :=
  ∀ {n : ℕ} (P : LinearPlan n) (a : ℝ) (v : Fin n→ℝ), P.DefinedAt a →
    ∃! values, P.Values a v values

def LinearPlan.evalValues {n : ℕ} (P : LinearPlan n) (a : ℝ) (v : Fin n→ℝ)
    (j : Fin P.length) : ℝ :=
  match P.step j with
  | .input i => v i
  | .zero => 0
  | .add i k => P.evalValues a v (earlier j i)+P.evalValues a v (earlier j k)
  | .scale c i => c.eval a*P.evalValues a v (earlier j i)
termination_by j.val
decreasing_by
  · exact i.isLt
  · exact k.isLt
  · exact i.isLt

theorem LinearPlan.evalValues_valid {n : ℕ} (P : LinearPlan n) (a : ℝ) (v : Fin n→ℝ) :
    P.Values a v (P.evalValues a v) := by
  intro j
  exact LinearPlan.evalValues.eq_1 P a v j

theorem LinearPlan.values_unique {n : ℕ} (P : LinearPlan n) (a : ℝ) (v : Fin n→ℝ)
    (values : Fin P.length→ℝ) (hvalues : P.Values a v values) :
    values=P.evalValues a v := by
  funext j
  have hh : ∀ k : ℕ, ∀ j : Fin P.length, j.val=k → values j=P.evalValues a v j := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro j hj
      rw [hvalues j, LinearPlan.evalValues]
      cases hs : P.step j with
      | input i => rfl
      | zero => rfl
      | add i l =>
        dsimp only
        rw [ih i.val (by simpa only [←hj] using i.isLt) (earlier j i) rfl,
          ih l.val (by simpa only [←hj] using l.isLt) (earlier j l) rfl]
      | scale c i =>
        dsimp only
        rw [ih i.val (by simpa only [←hj] using i.isLt) (earlier j i) rfl]
  exact hh j.val j rfl

theorem correction_linkage_plan_values : CorrectionPlanValuesStatement := by
  intro n P a v _ha
  exact ⟨P.evalValues a v, P.evalValues_valid a v, fun values hv=>P.values_unique a v values hv⟩

#check correction_linkage_plan_values
#print CorrectionPlanValuesStatement
#print axioms correction_linkage_plan_values
end Blueprint.CAP
