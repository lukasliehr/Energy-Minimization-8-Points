import Coulomb8.DyadicLinear

namespace Coulomb8.Dyadic
open scoped BigOperators

theorem ofFn_getD_of_length {α : Type*} (d : α) (xs : List α)
    {n : ℕ} (h : xs.length=n) :
    List.ofFn (fun i : Fin n => xs.getD i.val d)=xs := by
  subst n
  exact ofFn_getD d xs

theorem realDot_div_ofFn {n : ℕ} (cs : Fin n → ℤ) (x : Fin n → ℝ) (d : ℝ) :
    realDot (List.ofFn cs) (List.ofFn x)/d=∑ j, (cs j : ℝ)/d*x j := by
  rw [realDot_ofFn,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  ring

def identityBox {n : ℕ} (i j : Fin n) : Dyadic :=
  if i=j then ⟨scale,scale⟩ else ⟨0,0⟩

theorem identityBox_contains {n : ℕ} (i j : Fin n) :
    (identityBox i j).Contains ((1 : Matrix (Fin n) (Fin n) ℝ) i j) := by
  by_cases h : i=j <;> simp [identityBox,h,Contains,Matrix.one_apply]

theorem inverse_entry_bound {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (cs : Fin n → ℤ) (bs : List Dyadic) (i j : Fin n)
    (hb : List.Forall₂ Contains bs (List.ofFn (fun k => M k j)))
    (hE : errorNumerator (List.ofFn cs) bs (identityBox i j) (2^40) ≤ 2^160) :
    |((1 : Matrix (Fin n) (Fin n) ℝ) i j)-∑ k, (cs k : ℝ)/(2^40 : ℝ)*M k j| ≤
      (1/256 : ℝ) := by
  have h := linear_error_bound (List.ofFn cs) (d:=2^40) (E:=2^160)
    (by norm_num) hb (identityBox_contains i j) hE
  rw [realDot_div_ofFn] at h
  norm_num [scale] at h ⊢
  exact h

end Coulomb8.Dyadic

#print axioms Coulomb8.Dyadic.inverse_entry_bound
