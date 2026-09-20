import Thomson8.TripleSums

namespace Thomson8

theorem distinctSum_add (f g : Index → Index → Index → ℝ) :
    distinctSum (fun i j k => f i j k+g i j k)=distinctSum f+distinctSum g := by
  simp only [distinctSum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> ring

theorem distinctSum_mul (c : ℝ) (f : Index → Index → Index → ℝ) :
    distinctSum (fun i j k => c*f i j k)=c*distinctSum f := by
  simp [distinctSum,Finset.mul_sum,mul_ite]

theorem offSum_add (f g : Index → Index → ℝ) :
    offSum (fun i j => f i j+g i j)=offSum f+offSum g := by
  simp only [offSum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

theorem offSum_mul (c : ℝ) (f : Index → Index → ℝ) :
    offSum (fun i j => c*f i j)=c*offSum f := by
  simp [offSum,Finset.mul_sum,mul_ite]

theorem distinctSum_pair13 (f : Index → Index → ℝ) :
    distinctSum (fun i _ k => f i k)=6*offSum f :=
  (distinctSum_swap23 (fun i j _ => f i j)).trans (distinctSum_pair f)

theorem distinctSum_pair23 (f : Index → Index → ℝ) :
    distinctSum (fun _ j k => f j k)=6*offSum f :=
  (distinctSum_swap12 (fun i _ k => f i k)).trans (distinctSum_pair13 f)

end Thomson8
