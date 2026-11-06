import AllS.Units.N_GI.N_signed_mean.N_cubic_tensor

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

def tensorSymSix {ι : Type*} (T : OrderedTensor ι) : OrderedTensor ι := fun i j k=>
  (T i j k+T i k j+T j i k+T j k i+T k i j+T k j i)/6

theorem tensorCubic_swap12 {ι : Type*} [Fintype ι] (T : OrderedTensor ι) (x : ι → ℝ) :
    tensorCubic (fun i j k=>T j i k) x=tensorCubic T x := by
  unfold tensorCubic
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem tensorCubic_swap23 {ι : Type*} [Fintype ι] (T : OrderedTensor ι) (x : ι → ℝ) :
    tensorCubic (fun i j k=>T i k j) x=tensorCubic T x := by
  unfold tensorCubic
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem tensorCubic_symSix {ι : Type*} [Fintype ι] (T : OrderedTensor ι) (x : ι → ℝ) :
    tensorCubic (tensorSymSix T) x=tensorCubic T x := by
  have h123 := tensorCubic_swap23 T x
  have h213 := tensorCubic_swap12 T x
  have h231 : tensorCubic (fun i j k=>T j k i) x=tensorCubic T x :=
    (tensorCubic_swap12 (fun i j k=>T i k j) x).trans h123
  have h312 : tensorCubic (fun i j k=>T k i j) x=tensorCubic T x :=
    (tensorCubic_swap23 (fun i j k=>T j i k) x).trans h213
  have h321 : tensorCubic (fun i j k=>T k j i) x=tensorCubic T x :=
    (tensorCubic_swap12 (fun i j k=>T k i j) x).trans h312
  unfold tensorCubic at h123 h213 h231 h312 h321 ⊢
  unfold tensorSymSix
  simp only [add_div,add_mul,Finset.sum_add_distrib,div_mul_eq_mul_div,← Finset.sum_div]
  rw [h123,h213,h231,h312,h321]
  ring

#print axioms tensorCubic_symSix
end Blueprint.Thomson.Tail.Implementation
