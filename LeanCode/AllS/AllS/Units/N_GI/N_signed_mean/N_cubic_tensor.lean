import AllS.Units.N_GI.N_signed_mean.N_quartic_error
import AllS.Units.N_GI.N_cubic_absorption.N_diagonal_pair

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

def meanOrderedCubic (q v z : TangentCoordinates) : ℝ :=
  -stressB q (fun i=>inner ℝ (tangentVector v i) (tangentVector z i))

theorem meanOrderedCubic_diagonal (q : TangentCoordinates) : meanOrderedCubic q q q=stressCubic q := by
  simp [meanOrderedCubic,stressCubic,real_inner_self_eq_norm_sq]

theorem meanOrderedCubic_swap (q v z : TangentCoordinates) : meanOrderedCubic q v z=meanOrderedCubic q z v := by
  unfold meanOrderedCubic
  simp only [real_inner_comm (tangentVector v _) (tangentVector z _)]

theorem meanOrderedCubic_sum_first {ι : Type*} (s : Finset ι) (q : ι → TangentCoordinates) (v z : TangentCoordinates) :
    meanOrderedCubic (∑i∈s,q i) v z=∑i∈s,meanOrderedCubic (q i) v z := by
  simp only [meanOrderedCubic,stressB_sum_left,Finset.sum_neg_distrib]

theorem meanOrderedCubic_smul_first (c : ℝ) (q v z : TangentCoordinates) :
    meanOrderedCubic (c • q) v z=c*meanOrderedCubic q v z := by
  simp [meanOrderedCubic,stressB_smul_left]

theorem meanOrderedCubic_sum_second {ι : Type*} (s : Finset ι) (v : ι → TangentCoordinates) (q z : TangentCoordinates) :
    meanOrderedCubic q (∑i∈s,v i) z=∑i∈s,meanOrderedCubic q (v i) z := by
  simp only [meanOrderedCubic,tangentVector_sum,sum_inner,stressB_sum_right,Finset.sum_neg_distrib]

theorem meanOrderedCubic_smul_second (c : ℝ) (q v z : TangentCoordinates) :
    meanOrderedCubic q (c • v) z=c*meanOrderedCubic q v z := by
  simp only [meanOrderedCubic,tangentVector_smul,real_inner_smul_left,stressB_smul_right]
  ring

theorem meanOrderedCubic_sum_third {ι : Type*} (s : Finset ι) (z : ι → TangentCoordinates) (q v : TangentCoordinates) :
    meanOrderedCubic q v (∑i∈s,z i)=∑i∈s,meanOrderedCubic q v (z i) := by
  rw [meanOrderedCubic_swap,meanOrderedCubic_sum_second]
  simp only [meanOrderedCubic_swap q v]

theorem meanOrderedCubic_smul_third (c : ℝ) (q v z : TangentCoordinates) :
    meanOrderedCubic q v (c • z)=c*meanOrderedCubic q v z := by
  rw [meanOrderedCubic_swap,meanOrderedCubic_smul_second,meanOrderedCubic_swap q z v]

section Coordinates
variable {ι : Type*} [Fintype ι]

def meanPhysicalTensor (b : ι → TangentCoordinates) : OrderedTensor ι := fun i j k=>
  (meanOrderedCubic (b i) (b j) (b k)+meanOrderedCubic (b j) (b i) (b k)+
    meanOrderedCubic (b k) (b i) (b j))/3

theorem meanPhysicalTensor_swap12 (b : ι → TangentCoordinates) (i j k : ι) :
    meanPhysicalTensor b i j k=meanPhysicalTensor b j i k := by
  unfold meanPhysicalTensor
  rw [meanOrderedCubic_swap (b k) (b i) (b j)]
  ring

theorem meanPhysicalTensor_swap23 (b : ι → TangentCoordinates) (i j k : ι) :
    meanPhysicalTensor b i j k=meanPhysicalTensor b i k j := by
  unfold meanPhysicalTensor
  rw [meanOrderedCubic_swap (b i) (b j) (b k)]
  ring

theorem meanOrderedCubic_coordinates (b : ι → TangentCoordinates) (x : ι → ℝ) :
    stressCubic (∑i,x i • b i)=∑i,∑j,∑k,meanOrderedCubic (b i) (b j) (b k)*x i*x j*x k := by
  rw [← meanOrderedCubic_diagonal,meanOrderedCubic_sum_first]
  apply Finset.sum_congr rfl
  intro i _
  rw [meanOrderedCubic_smul_first,meanOrderedCubic_sum_second,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [meanOrderedCubic_smul_second,meanOrderedCubic_sum_third,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [meanOrderedCubic_smul_third]
  ring
theorem meanPhysicalTensor_coordinates (b : ι → TangentCoordinates) (x : ι → ℝ) :
    tensorCubic (meanPhysicalTensor b) x=stressCubic (∑i,x i • b i) := by
  rw [meanOrderedCubic_coordinates]
  have h12 : (∑i,∑j,∑k,meanOrderedCubic (b j) (b i) (b k)*x i*x j*x k)=
      ∑i,∑j,∑k,meanOrderedCubic (b i) (b j) (b k)*x i*x j*x k := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have h13 : (∑i,∑j,∑k,meanOrderedCubic (b k) (b i) (b j)*x i*x j*x k)=
      ∑i,∑j,∑k,meanOrderedCubic (b i) (b j) (b k)*x i*x j*x k := by
    have hi (i : ι) : (∑j,∑k,meanOrderedCubic (b k) (b i) (b j)*x i*x j*x k)=
        ∑k,∑j,meanOrderedCubic (b k) (b i) (b j)*x i*x j*x k := Finset.sum_comm
    simp_rw [hi]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  unfold tensorCubic meanPhysicalTensor
  simp only [add_div,add_mul,Finset.sum_add_distrib,div_mul_eq_mul_div,← Finset.sum_div]
  rw [h12,h13]
  ring

theorem meanPhysicalTensor_contraction (b : OrthonormalBasis ι ℝ TangentCoordinates) (q : TangentCoordinates) :
    tensorCubic (meanPhysicalTensor b) (b.repr q)=stressCubic q := by
  rw [meanPhysicalTensor_coordinates]
  have he : (∑i,b.repr q i • b i)=q := by
    simpa only [OrthonormalBasis.repr_apply_apply] using b.sum_repr' q
  rw [he]
end Coordinates

#print axioms meanPhysicalTensor_swap12
#print axioms meanOrderedCubic_coordinates
#print axioms meanPhysicalTensor_contraction
end Blueprint.Thomson.Tail.Implementation
