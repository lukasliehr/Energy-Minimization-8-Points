import Coulomb8.FiniteLinear
import Thomson8.Positivity

namespace Coulomb8.Dyadic
open scoped BigOperators

theorem realDot_append (cs ds : List ℤ) (xs ys : List ℝ) (h : cs.length=xs.length) :
    realDot (cs++ds) (xs++ys)=realDot cs xs+realDot ds ys := by
  induction cs generalizing xs with
  | nil => cases xs <;> simp_all [realDot]
  | cons c cs ih =>
    cases xs with
    | nil => simp at h
    | cons x xs =>
      simp only [List.length_cons,Nat.add_right_cancel_iff] at h
      simp only [List.cons_append,realDot,ih xs h]
      ring

theorem realDot_flatten_ofFn {m n : ℕ} (cs : Fin m → Fin n → ℤ) (x : Fin m → Fin n → ℝ) :
    realDot (List.ofFn (fun i => List.ofFn (cs i))).flatten
      (List.ofFn (fun i => List.ofFn (x i))).flatten=∑ i, ∑ j, (cs i j : ℝ)*x i j := by
  induction m with
  | zero => simp [realDot]
  | succ m ih =>
    rw [List.ofFn_succ,List.ofFn_succ,List.flatten_cons,List.flatten_cons,
      realDot_append _ _ _ _ (by simp),realDot_ofFn,ih,Fin.sum_univ_succ]

theorem forall₂_append {α β : Type*} {R : α → β → Prop} {as bs : List α} {xs ys : List β}
    (h : List.Forall₂ R as xs) (g : List.Forall₂ R bs ys) : List.Forall₂ R (as++bs) (xs++ys) := by
  induction h with
  | nil => exact g
  | cons hr ht ih => exact List.Forall₂.cons hr ih

theorem forall₂_flatten_ofFn {m n : ℕ} (b : Fin m → Fin n → Dyadic) (x : Fin m → Fin n → ℝ)
    (h : ∀ i j, (b i j).Contains (x i j)) :
    List.Forall₂ Contains (List.ofFn (fun i => List.ofFn (b i))).flatten
      (List.ofFn (fun i => List.ofFn (x i))).flatten := by
  induction m with
  | zero => exact List.Forall₂.nil
  | succ m ih =>
    rw [List.ofFn_succ,List.ofFn_succ,List.flatten_cons,List.flatten_cons]
    exact forall₂_append (forall₂_ofFn _ _ _ (h 0)) (ih _ _ (fun i j => h i.succ j))

noncomputable def scaledMatrix {n : ℕ} (P : Matrix (Fin n) (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℝ :=
  fun k l => (P k l : ℝ)/(2^40 : ℝ)

theorem congruence_entry_bound {n : ℕ} (P : Matrix (Fin n) (Fin n) ℤ)
    (W : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → Fin n → Dyadic)
    (hb : ∀ k l, (b k l).Contains (W k l)) (i j : Fin n)
    (hE : errorNumerator
      (List.ofFn (fun k => List.ofFn (fun l => P i k*P j l))).flatten
      (List.ofFn (fun k => List.ofFn (b k))).flatten (identityBox i j) (2^80) ≤ 2^203) :
    |(scaledMatrix P*W*(scaledMatrix P).transpose) i j-(if i=j then 1 else 0)| ≤ (1/32 : ℝ) := by
  have he := linear_error_bound
    (List.ofFn (fun k => List.ofFn (fun l => P i k*P j l))).flatten
    (d:=2^80) (E:=2^203) (by norm_num)
    (forall₂_flatten_ofFn b W hb) (identityBox_contains i j) hE
  rw [realDot_flatten_ofFn (fun k l => P i k*P j l) (fun k l => W k l)] at he
  have hm : (scaledMatrix P*W*(scaledMatrix P).transpose) i j=
      (∑ k, ∑ l, ((P i k*P j l : ℤ) : ℝ)*W k l)/(2^80 : ℝ) := by
    simp only [scaledMatrix,Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul,Finset.sum_div,Int.cast_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    ring
  rw [hm,abs_sub_comm]
  norm_num [scale,Matrix.one_apply] at he ⊢
  exact he

end Coulomb8.Dyadic

#print axioms Coulomb8.Dyadic.congruence_entry_bound
