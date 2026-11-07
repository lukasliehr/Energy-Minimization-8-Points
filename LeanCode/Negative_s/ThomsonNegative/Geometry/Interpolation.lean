import ThomsonNegative.Geometry.Newton

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Geometry

/-- Four contacts, each repeated twice, with total multiplicity eight. -/
def doubleNode (z : Fin 4 → ℝ) (n : ℕ) : ℝ := z ⟨(n/2)%4,Nat.mod_lt _ (by decide)⟩

lemma doubleNode_multiplicity (z : Fin 4 → ℝ) (hz : Function.Injective z) (i : Fin 4) :
    priorMultiplicity (doubleNode z) 8 (z i)=2 := by
  classical
  simp only [priorMultiplicity,doubleNode,hz.eq_iff]
  fin_cases i <;> decide

/-- A concrete degree-seven interpolation polynomial, not an existential
interpolation assumption. The finite Newton recursion uses only the eight jets. -/
def hermiteH7 (q : ℝ) (z : Fin 4 → ℝ) : Polynomial ℝ :=
  newtonHermite (doubleNode z) (Analytic.auxiliaryTJet q) 8

lemma hermiteH7_degree (q : ℝ) (z : Fin 4 → ℝ) : (hermiteH7 q z).degree < 8 :=
  (newton_hermite_stage_invariant (doubleNode z) (Analytic.auxiliaryTJet q) 8).1

lemma hermiteH7_jets (q : ℝ) (z : Fin 4 → ℝ) (hz : Function.Injective z)
    (i : Fin 4) (k : ℕ) (hk : k < 2) :
    Analytic.polynomialJet (hermiteH7 q z) k (z i)=Analytic.auxiliaryTJet q k (z i) := by
  apply (newton_hermite_stage_invariant (doubleNode z) (Analytic.auxiliaryTJet q) 8).2
  rwa [doubleNode_multiplicity z hz i]

lemma hermiteH7_value (q : ℝ) (z : Fin 4 → ℝ) (hz : Function.Injective z) (i : Fin 4) :
    (hermiteH7 q z).eval (z i)=Analytic.auxiliaryT q (z i) := by
  simpa [Analytic.polynomialJet,Analytic.auxiliaryTJet,Analytic.auxiliaryJet,Analytic.auxiliaryT]
    using hermiteH7_jets q z hz i 0 (by norm_num)

lemma hermiteH7_slope (q : ℝ) (z : Fin 4 → ℝ) (hz : Function.Injective z) (i : Fin 4) :
    (hermiteH7 q z).derivative.eval (z i)=auxSlope q ((1+z i)/2)/2 := by
  simpa [Analytic.polynomialJet,Analytic.auxiliaryTJet,Analytic.auxiliaryJet]
    using hermiteH7_jets q z hz i 1 (by norm_num)

/-- Complete H7 scalar soundness: degree, values and slopes are now discharged
by the concrete constructor. Only the geometric node domain remains. -/
theorem hermiteH7_minorant (q : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1)
    (z : Fin 4 → ℝ) (hz : Function.Injective z)
    (hzm : ∀ i, z i ∈ Set.Ico (-1:ℝ) 1) (t : ℝ) (ht : t ∈ Set.Ico (-1:ℝ) 1) :
    (hermiteH7 q z).eval t ≤ Analytic.auxiliaryT q t ∧
      (∏ i, (t-z i)^2)/14336 ≤ Analytic.auxiliaryT q t-(hermiteH7 q z).eval t ∧
      ((hermiteH7 q z).eval t=Analytic.auxiliaryT q t ↔ ∃ i, t=z i) :=
  Analytic.hermiteSeven_minorant q hq z hz hzm _ (hermiteH7_degree q z)
    (hermiteH7_value q z hz) (hermiteH7_slope q z hz) t ht

#print axioms hermiteH7_jets
#print axioms hermiteH7_minorant
end ThomsonNegative.Geometry
