import AllS.Units.N_GI.N_cubic_absorption.N_tensor_norm
import Mathlib.Analysis.InnerProductSpace.Spectrum

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

abbrev OrderedTensor (ι : Type*) := ι → ι → ι → ℝ

def diagonalPairU {ι : Type*} (eig : ι → ℝ) (T : OrderedTensor ι) : OrderedTensor ι :=
  fun i j k => ((eig i+eig j)⁻¹+(eig i+eig k)⁻¹)*T i j k

def tensorCubic {ι : Type*} [Fintype ι] (T : OrderedTensor ι) (q : ι → ℝ) : ℝ :=
  ∑i,∑j,∑k,T i j k*q i*q j*q k

def pairFirstContraction {ι : Type*} [Fintype ι] (eig : ι → ℝ)
    (T : OrderedTensor ι) (q : ι → ℝ) : ℝ :=
  ∑i,∑j,∑k,eig i*(eig i+eig j)⁻¹*T i j k*q i*q j*q k

theorem pairFirstContraction_swap {ι : Type*} [Fintype ι] (eig : ι → ℝ)
    (T : OrderedTensor ι) (hT : ∀ i j k,T i j k=T j i k) (q : ι → ℝ) :
    pairFirstContraction eig T q=
      ∑i,∑j,∑k,eig j*(eig i+eig j)⁻¹*T i j k*q i*q j*q k := by
  unfold pairFirstContraction
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [hT j i k]
  ring

theorem pairFirstContraction_twice {ι : Type*} [Fintype ι]
    (eig : ι → ℝ) (heig : ∀ i, 0 < eig i) (T : OrderedTensor ι)
    (hT : ∀ i j k,T i j k=T j i k) (q : ι → ℝ) :
    2*pairFirstContraction eig T q=tensorCubic T q := by
  calc
    _ = pairFirstContraction eig T q+pairFirstContraction eig T q := by ring
    _ = _ := by
      conv_lhs => rhs; rw [pairFirstContraction_swap eig T hT q]
      unfold pairFirstContraction tensorCubic
      simp only [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      have hn : eig i+eig j ≠ 0 := ne_of_gt (add_pos (heig i) (heig j))
      field_simp

theorem diagonalPairU_contraction {ι : Type*} [Fintype ι]
    (eig : ι → ℝ) (heig : ∀ i, 0 < eig i) (T : OrderedTensor ι)
    (h12 : ∀ i j k,T i j k=T j i k) (h23 : ∀ i j k,T i j k=T i k j)
    (q : ι → ℝ) :
    (∑i,∑j,∑k,eig i*diagonalPairU eig T i j k*q i*q j*q k)=tensorCubic T q := by
  have hswap : (∑i,∑j,∑k,eig i*(eig i+eig k)⁻¹*T i j k*q i*q j*q k)=pairFirstContraction eig T q := by
    unfold pairFirstContraction
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [h23 i k j]
    ring
  calc
    _ = pairFirstContraction eig T q+(∑i,∑j,∑k,eig i*(eig i+eig k)⁻¹*T i j k*q i*q j*q k) := by
      unfold pairFirstContraction diagonalPairU
      simp only [mul_add,add_mul,Finset.sum_add_distrib,mul_assoc]
    _ = 2*pairFirstContraction eig T q := by rw [hswap]; ring
    _ = _ := pairFirstContraction_twice eig heig T h12 q

#print axioms diagonalPairU_contraction
end Blueprint.Thomson.Tail.Implementation
