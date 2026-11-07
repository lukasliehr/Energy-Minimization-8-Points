import Blueprint.Tail

noncomputable section
open Real
open scoped BigOperators
namespace Blueprint.Thomson.Tail.Implementation

def weightedMean {n : ℕ} (w x : Fin n → ℝ) : ℝ := ∑ i, w i*x i
def weightedSquare {n : ℕ} (w x : Fin n → ℝ) : ℝ := ∑ i, w i*(x i)^2
def weightedExp {n : ℕ} (w x : Fin n → ℝ) : ℝ := ∑ i, w i*exp (x i)
def weightedFeasible {n : ℕ} (w : Fin n → ℝ) (v : ℝ) : Set (Fin n → ℝ) :=
  {x | weightedMean w x=0 ∧ weightedSquare w x=v^2}

theorem weightedMean_continuous {n : ℕ} (w : Fin n → ℝ) : Continuous (weightedMean w) := by
  unfold weightedMean
  fun_prop

theorem weightedSquare_continuous {n : ℕ} (w : Fin n → ℝ) : Continuous (weightedSquare w) := by
  unfold weightedSquare
  fun_prop

theorem weightedExp_continuous {n : ℕ} (w : Fin n → ℝ) : Continuous (weightedExp w) := by
  unfold weightedExp
  fun_prop

theorem weightedSquare_nonneg {n : ℕ} (w x : Fin n → ℝ) (hw : ∀ i, 0 < w i) :
    0 ≤ weightedSquare w x := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i).le (sq_nonneg _))

theorem weightedMean_smul {n : ℕ} (w x : Fin n → ℝ) (c : ℝ) :
    weightedMean w (fun i => c*x i)=c*weightedMean w x := by
  simp only [weightedMean,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _; ring

theorem weightedSquare_smul {n : ℕ} (w x : Fin n → ℝ) (c : ℝ) :
    weightedSquare w (fun i => c*x i)=c^2*weightedSquare w x := by
  simp only [weightedSquare,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _; ring

theorem weightedFeasible_nonempty {n : ℕ} (hn : 2 ≤ n) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (v : ℝ) (hv : 0 < v) : (weightedFeasible w v).Nonempty := by
  let i0 : Fin n := ⟨0,by omega⟩
  let i1 : Fin n := ⟨1,by omega⟩
  have hij : i0 ≠ i1 := by simp [i0,i1]
  let u : Fin n → ℝ := fun i => if i=i0 then 1/w i0 else if i=i1 then -(1/w i1) else 0
  have hsum (f : Fin n → ℝ) (hf : ∀ i, i ≠ i0 → i ≠ i1 → f i=0) :
      (∑ i, f i)=f i0+f i1 := by
    calc
      _ = ∑ i ∈ ({i0,i1} : Finset (Fin n)), f i := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _ hi
        simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hi
        exact hf i hi.1 hi.2
      _ = _ := Finset.sum_pair hij
  have hw0 := hw i0
  have hw1 := hw i1
  have hmean : weightedMean w u=0 := by
    unfold weightedMean
    rw [hsum (fun i => w i*u i) (by intro i hi hj; simp [u,hi,hj])]
    simp [u,hij,Ne.symm hij,hw0.ne',hw1.ne']
  have hvar : weightedSquare w u=1/w i0+1/w i1 := by
    unfold weightedSquare
    rw [hsum (fun i => w i*(u i)^2) (by intro i hi hj; simp [u,hi,hj])]
    simp [u,Ne.symm hij]
    field_simp
    <;> ring
  have hvarpos : 0 < weightedSquare w u := by rw [hvar]; positivity
  have hroot : 0 < √(weightedSquare w u) := Real.sqrt_pos.mpr hvarpos
  refine ⟨fun i => (v/√(weightedSquare w u))*u i,?_,?_⟩
  · rw [weightedMean_smul,hmean,mul_zero]
  · rw [weightedSquare_smul,div_pow,Real.sq_sqrt hvarpos.le]
    field_simp

theorem weightedFeasible_isCompact {n : ℕ} (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (v : ℝ) (hv : 0 < v) : IsCompact (weightedFeasible w v) := by
  have hclosed : IsClosed (weightedFeasible w v) :=
    (isClosed_eq (weightedMean_continuous w) continuous_const).inter
      (isClosed_eq (weightedSquare_continuous w) continuous_const)
  have hbox := isCompact_univ_pi (fun i : Fin n => isCompact_Icc (a := -(v/√(w i))) (b := v/√(w i)))
  apply hbox.of_isClosed_subset hclosed
  intro x hx
  simp only [Set.mem_pi,Set.mem_univ,true_implies,Set.mem_Icc]
  intro i
  have ht : w i*(x i)^2 ≤ v^2 := by
    have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
      mul_nonneg (hw j).le (sq_nonneg (x j))) (Finset.mem_univ i)
    exact h.trans_eq hx.2
  have hs := Real.sq_sqrt (hw i).le
  have hs0 := Real.sqrt_pos.mpr (hw i)
  have hb : |x i| ≤ v/√(w i) := by
    apply (le_div_iff₀ hs0).mpr
    have ha := abs_nonneg (x i)
    have hae := sq_abs (x i)
    have hmul : (|x i| *√(w i))^2 ≤ v^2 := by
      calc
        _ = w i*(x i)^2 := by rw [mul_pow,hs,hae]; ring
        _ ≤ _ := ht
    nlinarith [mul_nonneg ha hs0.le]
  exact abs_le.mp hb

theorem weighted_two_value_constraint_compact {n : ℕ} (hn : 2 ≤ n) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (v : ℝ) (hv : 0 < v) :
    (weightedFeasible w v).Nonempty ∧ IsCompact (weightedFeasible w v) :=
  ⟨weightedFeasible_nonempty hn w hw v hv,weightedFeasible_isCompact w hw v hv⟩

#check weighted_two_value_constraint_compact
#print axioms weighted_two_value_constraint_compact
end Blueprint.Thomson.Tail.Implementation
