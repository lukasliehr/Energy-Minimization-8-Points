import AllS.Units.N_AI.N_correction_linkage.N_plan_values

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def LinearPlan.Coefficients {n : ℕ} (P : LinearPlan n)
    (r : Fin P.length→Fin n→RatFun) : Prop :=
  ∀ j i, r j i=match P.step j with
    | .input k => if i=k then RatFun.one else RatFun.zero
    | .zero => RatFun.zero
    | .add k l => (r (earlier j k) i).add (r (earlier j l) i)
    | .scale c k => c.mul (r (earlier j k) i)

def CorrectionCoefficientSemanticsStatement : Prop :=
  ∀ {n : ℕ} (P : LinearPlan n) (r : Fin P.length→Fin n→RatFun) (a : ℝ),
    P.Coefficients r → P.DefinedAt a → (∀ j i, (r j i).DefinedAt a) →
    ∀ (v : Fin n→ℝ) (values : Fin P.length→ℝ), P.Values a v values →
      ∀ j, values j=∑ i, (r j i).eval a*v i

@[simp] theorem RatFun.eval_zero (a : ℝ) : RatFun.zero.eval a=0 := by
  simp [RatFun.zero, RatFun.eval, evalQPoly]

@[simp] theorem RatFun.eval_one (a : ℝ) : RatFun.one.eval a=1 := by
  simp [RatFun.one, RatFun.eval, evalQPoly]

theorem RatFun.eval_add (f g : RatFun) (a : ℝ) (hf : f.DefinedAt a) (hg : g.DefinedAt a) :
    (f.add g).eval a=f.eval a+g.eval a := by
  unfold RatFun.DefinedAt evalQPoly at hf hg
  simp only [RatFun.eval, RatFun.add, evalQPoly, Polynomial.eval₂_add, Polynomial.eval₂_mul]
  field_simp
  <;> ring

theorem RatFun.eval_mul (f g : RatFun) (a : ℝ) (hf : f.DefinedAt a) (hg : g.DefinedAt a) :
    (f.mul g).eval a=f.eval a*g.eval a := by
  unfold RatFun.DefinedAt evalQPoly at hf hg
  simp only [RatFun.eval, RatFun.mul, evalQPoly, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_ofNat]
  field_simp
  ring_nf
  simp [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]

theorem correction_linkage_coefficient_semantics : CorrectionCoefficientSemanticsStatement := by
  classical
  intro n P r a hr hP hrd v values hv
  have hs : P.Values a v (fun j=>∑ i, (r j i).eval a*v i) := by
    intro j
    have hj : ∀ i, r j i=match P.step j with
        | .input k => if i=k then RatFun.one else RatFun.zero
        | .zero => RatFun.zero
        | .add k l => (r (earlier j k) i).add (r (earlier j l) i)
        | .scale c k => c.mul (r (earlier j k) i) := hr j
    cases hstep : P.step j with
    | input k =>
      simp only [hstep] at hj ⊢
      rw [Finset.sum_eq_single k]
      · rw [hj k]
        simp
      · intro i _ hik
        rw [hj i, if_neg hik]
        simp
      · simp
    | zero =>
      simp only [hstep] at hj ⊢
      simp [hj]
    | add k l =>
      simp only [hstep] at hj ⊢
      simp only [hj, RatFun.eval_add _ _ a (hrd (earlier j k) _) (hrd (earlier j l) _),
        add_mul, Finset.sum_add_distrib]
    | scale c k =>
      simp only [hstep] at hj ⊢
      have hc : c.DefinedAt a := by simpa only [LinearPlan.DefinedAt, hstep] using hP j
      simp only [hj, RatFun.eval_mul _ _ a hc (hrd (earlier j k) _),
        mul_assoc, Finset.mul_sum]
  have he := (P.values_unique a v values hv).trans (P.values_unique a v _ hs).symm
  exact congrFun he

#check correction_linkage_coefficient_semantics
#print CorrectionCoefficientSemanticsStatement
#print axioms correction_linkage_coefficient_semantics
end Blueprint.CAP
