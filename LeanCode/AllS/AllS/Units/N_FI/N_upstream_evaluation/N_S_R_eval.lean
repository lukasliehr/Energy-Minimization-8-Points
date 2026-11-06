import AllS.Units.N_FI.N_upstream_evaluation.N_Q_eval

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

def KernelSREvaluationContract : Prop := ∀ k i j : ℕ, ∀ u v t : ℝ,
  MvPolynomial.eval ![u,v,t] (kernelSPoly k i j) = GenericMoments.Sfun k i j u v t ∧
  MvPolynomial.eval ![u,v,t] (kernelRPoly k i j) = GenericMoments.Rfun k i j u v t
def coordinatePermEnum : Fin 6 → Equiv.Perm (Fin 3) :=
  ![Equiv.refl _, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
    (Equiv.swap 0 1).trans (Equiv.swap 1 2), (Equiv.swap 1 2).trans (Equiv.swap 0 1)]

theorem coordinatePermEnum_bijective : Function.Bijective coordinatePermEnum := by decide

def coordinatePermEquiv : Fin 6 ≃ Equiv.Perm (Fin 3) :=
  Equiv.ofBijective coordinatePermEnum coordinatePermEnum_bijective

theorem coordinatePermEnum_values (x : Fin 3 → ℝ) : ∀ i : Fin 6,
    x ∘ coordinatePermEnum i =
      ![![x 0,x 1,x 2], ![x 1,x 0,x 2], ![x 2,x 1,x 0], ![x 0,x 2,x 1],
        ![x 2,x 0,x 1], ![x 1,x 2,x 0]] i := by
  intro i
  funext j
  fin_cases i <;> fin_cases j <;> simp [coordinatePermEnum,Function.comp_def,Equiv.swap_apply_def]

theorem coordinatePerm_sum (f : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) :
    (∑ σ : Equiv.Perm (Fin 3), f (x ∘ σ)) =
      f ![x 0,x 1,x 2]+f ![x 1,x 0,x 2]+f ![x 2,x 1,x 0]+
      f ![x 0,x 2,x 1]+f ![x 2,x 0,x 1]+f ![x 1,x 2,x 0] := by
  rw [← Equiv.sum_comp coordinatePermEquiv (fun σ => f (x ∘ σ))]
  change (∑ i : Fin 6, f (x ∘ coordinatePermEnum i)) = _
  simp_rw [coordinatePermEnum_values]
  simp [Fin.sum_univ_succ, add_assoc]

theorem eval_reynolds (p : Poly3) (u v t : ℝ) :
    MvPolynomial.eval ![u,v,t] (reynolds p) =
      GenericMoments.symEval (fun x y z => MvPolynomial.eval ![x,y,z] p) u v t := by
  simp only [reynolds,LinearMap.smul_apply,LinearMap.sum_apply,AlgHom.toLinearMap_apply,
    MvPolynomial.smul_eval,map_sum,MvPolynomial.eval_rename,smul_eq_mul]
  rw [coordinatePerm_sum (fun x => MvPolynomial.eval x p) ![u,v,t]]
  simp [GenericMoments.symEval]
  ring

theorem kernelSPoly_eval (k i j : ℕ) (u v t : ℝ) :
    MvPolynomial.eval ![u,v,t] (kernelSPoly k i j) = GenericMoments.Sfun k i j u v t := by
  rw [kernelSPoly,eval_reynolds]
  simp [GenericMoments.Sfun, GenericMoments.symEval, upstream_evaluation_Q_eval]

theorem eval_aeval_poly (x : Fin 3 → ℝ) (g : Fin 3 → Poly3) (p : Poly3) :
    MvPolynomial.eval x (MvPolynomial.aeval g p) =
      MvPolynomial.eval (fun i => MvPolynomial.eval x (g i)) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p i hp => simp only [map_mul,MvPolynomial.aeval_X,MvPolynomial.eval_X,hp]

theorem repeatSubst_eval (x : Fin 3) (p : Poly3) (u v t : ℝ) :
    MvPolynomial.eval ![u,v,t] (repeatSubst x p) =
      MvPolynomial.eval ![![u,v,t] x,![u,v,t] x,1] p := by
  rw [repeatSubst,eval_aeval_poly]
  apply congrArg (fun z : Fin 3 → ℝ => MvPolynomial.eval z p)
  funext i
  fin_cases i <;> simp

theorem kernelRPoly_eval (k i j : ℕ) (u v t : ℝ) :
    MvPolynomial.eval ![u,v,t] (kernelRPoly k i j) = GenericMoments.Rfun k i j u v t := by
  simp [kernelRPoly,GenericMoments.Rfun,repeatSubst_eval,kernelSPoly_eval]
  split_ifs <;> norm_num

theorem upstream_evaluation_S_R_eval : KernelSREvaluationContract := by
  intro k i j u v t
  exact ⟨kernelSPoly_eval k i j u v t,kernelRPoly_eval k i j u v t⟩

#check upstream_evaluation_S_R_eval
#print axioms upstream_evaluation_S_R_eval
#check KernelSREvaluationContract
#print axioms KernelSREvaluationContract
end Blueprint.Thomson.Finite
