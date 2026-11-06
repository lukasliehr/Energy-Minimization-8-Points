import Blueprint.CAPContracts
import AllS.Units.N_AI.N_interval_semantics.N_inverse_sqrt
import Blueprint.Target

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP
def TM.constantBox (n : ℕ) (I : Box) : TM n :=
  ⟨fun k => if k=0 then I else Box.point 0, 0⟩
def ScalarConstantReciprocalStatement : Prop :=
  ∀ {n : ℕ} (M : TM n) (f : ℝ→ℝ) (K : Box), M.Valid f → M.error=0 →
    (∀ k : Fin (n+1), k≠0 → M.coeff k=Box.point 0) →
    Box.InvGate (M.coeff 0) K →
    (TM.constantBox n K).Valid (fun x=>1/f x)
theorem scalarEval_single_zero {n : ℕ} (a x : ℝ) :
    scalarEval (fun k : Fin (n+1) => if k=0 then a else 0) x = a := by
  classical
  simp [scalarEval, ite_mul]

theorem scalar_models_constant_reciprocal : ScalarConstantReciprocalStatement := by
  intro n M f K hm he hc hi
  classical
  rcases hm with ⟨hem,a,ha,hr⟩
  have ha0 (k : Fin (n+1)) (hk : k≠0) : a k=0 := by
    have hp : (Box.point 0).Contains (a k) := by simpa only [hc k hk] using ha k
    simpa using (Box.eq_of_contains_point (q:=0) hp)
  have havec : a = (fun k : Fin (n+1) => if k=0 then a 0 else 0) := by
    funext k
    by_cases hk : k=0
    · simp [hk]
    · simp [hk, ha0 k hk]
  have hf (x : ℝ) (hx : x∈cellDomain) : f x=a 0 := by
    have h := hr x hx
    rw [he, Rat.cast_zero, havec, scalarEval_single_zero] at h
    exact sub_eq_zero.mp (abs_nonpos_iff.mp h)
  have hinv := Box.contains_inverse (ha 0) hi
  refine ⟨le_rfl, (fun k : Fin (n+1) => if k=0 then 1/a 0 else 0), ?_, ?_⟩
  · intro k
    by_cases hk : k=0
    · subst k
      simpa [TM.constantBox] using hinv.1
    · simp [TM.constantBox, hk, Box.Contains, Box.point]
  · intro x hx
    simp [scalarEval_single_zero, hf x hx, TM.constantBox]
#check scalar_models_constant_reciprocal
#print ScalarConstantReciprocalStatement
#print axioms scalar_models_constant_reciprocal
end Blueprint.CAP
