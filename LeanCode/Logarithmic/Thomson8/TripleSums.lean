import Thomson8.Statement

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Thomson8

abbrev Index := Fin 8

noncomputable def tripleSum (f : Index → Index → Index → ℝ) : ℝ := ∑ i, ∑ j, ∑ k, f i j k
noncomputable def distinctSum (f : Index → Index → Index → ℝ) : ℝ :=
  ∑ i, ∑ j, ∑ k, if i≠j ∧ j≠k ∧ k≠i then f i j k else 0
noncomputable def offSum (f : Index → Index → ℝ) : ℝ := ∑ i, ∑ j, if i≠j then f i j else 0

theorem tripleSum_swap12 (f : Index → Index → Index → ℝ) :
    tripleSum (fun i j k => f j i k) = tripleSum f := by
  unfold tripleSum
  rw [Finset.sum_comm]

theorem tripleSum_swap23 (f : Index → Index → Index → ℝ) :
    tripleSum (fun i j k => f i k j) = tripleSum f := by
  unfold tripleSum
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

theorem distinctSum_swap12 (f : Index → Index → Index → ℝ) :
    distinctSum (fun i j k => f j i k) = distinctSum f := by
  unfold distinctSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  simp only [ne_comm,and_comm,and_left_comm,and_assoc]

theorem distinctSum_swap23 (f : Index → Index → Index → ℝ) :
    distinctSum (fun i j k => f i k j) = distinctSum f := by
  unfold distinctSum
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  simp only [ne_comm,and_comm,and_left_comm,and_assoc]

theorem distinctSum_pair (f : Index → Index → ℝ) :
    distinctSum (fun i j _ => f i j) = 6*offSum f := by
  have h (i j : Index) :
      (∑ k : Index, if i≠j ∧ j≠k ∧ k≠i then f i j else 0) =
        6*(if i≠j then f i j else 0) := by
    fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_succ] <;> ring
  simp only [distinctSum,h,offSum,Finset.mul_sum]

theorem distinctSum_const (c : ℝ) : distinctSum (fun _ _ _ => c) = 336*c := by
  rw [distinctSum_pair]
  simp [offSum,Fin.sum_univ_succ]
  ring

theorem tripleSum_decomposition (f : Index → Index → Index → ℝ) :
    tripleSum f = distinctSum f +
      offSum (fun i j => f i i j+f i j i+f j i i) + ∑ i, f i i i := by
  simp only [tripleSum,distinctSum,offSum,Fin.sum_univ_succ]
  norm_num [Fin.succ]
  ring

#print axioms tripleSum_decomposition

end Thomson8
