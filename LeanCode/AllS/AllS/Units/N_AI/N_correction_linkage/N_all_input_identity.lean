import AllS.Units.N_AI.N_correction_linkage.N_coefficient_semantics

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def RatFun.ClearedEq (f g : RatFun) : Prop :=
  f.rational*g.denominator=g.rational*f.denominator ∧
    f.irrational*g.denominator=g.irrational*f.denominator

def CorrectionAllInputIdentityStatement : Prop :=
  ∀ {n : ℕ} (P : LinearPlan n) (r : Fin P.length→Fin n→RatFun)
    (D : Matrix (Fin n) (Fin n) RatFun) (a : ℝ),
    P.Coefficients r → (∀ j i, (r j i).DefinedAt a) → (∀ j i, (D j i).DefinedAt a) →
    (∀ j i, (r (P.output j) i).ClearedEq (D j i)) →
    ∀ (v out : Fin n→ℝ), P.Outputs a v out →
      ∀ j, out j=∑ i, (D j i).eval a*v i

theorem RatFun.ClearedEq.eval_eq {f g : RatFun} (h : f.ClearedEq g)
    (a : ℝ) (hf : f.DefinedAt a) (hg : g.DefinedAt a) : f.eval a=g.eval a := by
  have hp := congrArg (fun p=>evalQPoly p a) h.1
  have hq := congrArg (fun p=>evalQPoly p a) h.2
  simp only [evalQPoly, Polynomial.eval₂_mul] at hp hq
  change evalQPoly f.rational a*evalQPoly g.denominator a=
    evalQPoly g.rational a*evalQPoly f.denominator a at hp
  change evalQPoly f.irrational a*evalQPoly g.denominator a=
    evalQPoly g.irrational a*evalQPoly f.denominator a at hq
  unfold RatFun.eval
  apply (div_eq_div_iff hf hg).mpr
  calc
    _ = evalQPoly f.rational a*evalQPoly g.denominator a+
        Real.sqrt 2*(evalQPoly f.irrational a*evalQPoly g.denominator a) := by ring
    _ = evalQPoly g.rational a*evalQPoly f.denominator a+
        Real.sqrt 2*(evalQPoly g.irrational a*evalQPoly f.denominator a) := by rw [hp,hq]
    _ = _ := by ring

theorem correction_linkage_all_input_identity : CorrectionAllInputIdentityStatement := by
  intro n P r D a hr hrd hDd hEq v out ho j
  obtain ⟨hP,values,hv,hout⟩ := ho
  rw [hout j, correction_linkage_coefficient_semantics P r a hr hP hrd v values hv]
  apply Finset.sum_congr rfl
  intro i _
  rw [(hEq j i).eval_eq a (hrd (P.output j) i) (hDd j i)]

#check correction_linkage_all_input_identity
#print CorrectionAllInputIdentityStatement
#print axioms correction_linkage_all_input_identity
end Blueprint.CAP
