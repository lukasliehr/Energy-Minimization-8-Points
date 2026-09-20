import Coulomb8.CoefficientBasis
import Coulomb8.ContactPolynomial
import Coulomb8.Target
import Mathlib.Data.List.OfFn

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8
open scoped BigOperators

noncomputable def coefficientValue (f : Fin 102 → ℝ) (i : ℕ) : ℝ :=
  if h : i<102 then f ⟨i,h⟩ else 0

noncomputable def expansionOn (ts : List (Exponent × ℕ)) (f : Fin 102 → ℝ) (u v t : ℝ) : ℝ :=
  (ts.map fun m => coefficientValue f m.2*m.1.eval u v t).sum

noncomputable def realExpansion (f : Fin 102 → ℝ) (u v t : ℝ) : ℝ :=
  expansionOn canonicalTerms f u v t

theorem expand_filterMap_eval (ts : List (Exponent × ℕ)) (cs : List K) (u v t : ℝ) :
    Poly.eval (ts.filterMap (fun (e,i) => let c := cs.getD i K.zero
      if c=K.zero then none else some (e,c))) u v t=
    (ts.map fun (e,i) => K.eval (cs.getD i K.zero)*e.eval u v t).sum := by
  induction ts with
  | nil => simp
  | cons m ts ih =>
    rcases m with ⟨e,i⟩
    by_cases hc : cs.getD i K.zero=K.zero
    · simp only [List.filterMap_cons,List.map_cons,List.sum_cons,hc,ite_true,
        K.eval_zero,zero_mul,zero_add,ih]
    · simp only [List.filterMap_cons,List.map_cons,List.sum_cons,if_neg hc,Poly.eval_cons,ih]

theorem eval_getD_ofFn (f : Fin 102 → K) (i : ℕ) :
    K.eval ((List.ofFn f).getD i K.zero)=coefficientValue (fun r => K.eval (f r)) i := by
  rw [List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  by_cases h : i<102 <;> simp only [coefficientValue,h,dite_true,dite_false,Option.getD_some,Option.getD_none,K.eval_zero]

theorem expandColumn_eval (f : Fin 102 → K) (u v t : ℝ) :
    (expandColumn (List.ofFn f)).eval u v t=realExpansion (fun r => K.eval (f r)) u v t := by
  rw [expandColumn,expand_filterMap_eval]
  simp only [realExpansion,expansionOn,eval_getD_ofFn]

theorem coefficientValue_sum {κ : Type*} [Fintype κ] (A : Fin 102 → κ → ℝ) (w : κ → ℝ) (i : ℕ) :
    coefficientValue (fun r => ∑ c, A r c*w c) i=
      ∑ c, coefficientValue (fun r => A r c) i*w c := by
  by_cases h : i<102 <;> simp [coefficientValue,h]

theorem expansionOn_sum {κ : Type*} [Fintype κ] (ts : List (Exponent × ℕ))
    (A : Fin 102 → κ → ℝ) (w : κ → ℝ) (u v t : ℝ) :
    expansionOn ts (fun r => ∑ c, A r c*w c) u v t=
      ∑ c, w c*expansionOn ts (fun r => A r c) u v t := by
  induction ts with
  | nil => simp [expansionOn]
  | cons m ts ih =>
    change coefficientValue (fun r => ∑ c, A r c*w c) m.2*m.1.eval u v t+
      expansionOn ts (fun r => ∑ c, A r c*w c) u v t=
      ∑ c, w c*(coefficientValue (fun r => A r c) m.2*m.1.eval u v t+
        expansionOn ts (fun r => A r c) u v t)
    rw [coefficientValue_sum,ih,Finset.sum_mul]
    simp only [mul_add,Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro c hc
    ring

theorem expansion_sum {κ : Type*} [Fintype κ] (A : Fin 102 → κ → ℝ) (w : κ → ℝ) (u v t : ℝ) :
    realExpansion (fun r => ∑ c, A r c*w c) u v t=
      ∑ c, w c*realExpansion (fun r => A r c) u v t :=
  expansionOn_sum canonicalTerms A w u v t

theorem target_expansion (u v t : ℝ) :
    realExpansion target u v t=(H u+H v+H t)/3-G a/28 := by
  simp only [H,eval_degree_twelve Hpoly Hpoly_degree,Fin.sum_univ_succ]
  norm_num [realExpansion,expansionOn,canonicalTerms,coefficientValue,target,Exponent.eval]
  ring

end Coulomb8

#print axioms Coulomb8.expandColumn_eval
#print axioms Coulomb8.target_expansion
