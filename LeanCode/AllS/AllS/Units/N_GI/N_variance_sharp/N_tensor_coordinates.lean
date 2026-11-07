import AllS.Units.N_GI.N_variance_sharp.N_physical_tensor_bridge
import AllS.Units.N_GI.N_contact_spectrum.N_contact_rows

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem varianceTrilinear_add_first (q q' v z : TangentCoordinates) :
    varianceTrilinear (q+q') v z =
      varianceTrilinear q v z + varianceTrilinear q' v z := by
  unfold varianceTrilinear
  rw [←mul_add,←Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  simp only [contactLinearArray,contactLinear_add,inner_add_left]
  ring

theorem varianceTrilinear_smul_first (c : ℝ) (q v z : TangentCoordinates) :
    varianceTrilinear (c • q) v z = c*varianceTrilinear q v z := by
  unfold varianceTrilinear
  rw [mul_left_comm c]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  simp only [contactLinearArray,contactLinear_smul_spectrum,real_inner_smul_left]
  ring

def varianceTrilinearLinear (v z : TangentCoordinates) : TangentCoordinates →ₗ[ℝ] ℝ where
  toFun q := varianceTrilinear q v z
  map_add' q q' := varianceTrilinear_add_first q q' v z
  map_smul' c q := varianceTrilinear_smul_first c q v z

theorem varianceTrilinear_sum_first {ι : Type*} (s : Finset ι)
    (q : ι → TangentCoordinates) (v z : TangentCoordinates) :
    varianceTrilinear (∑ i∈s,q i) v z = ∑ i∈s,varianceTrilinear (q i) v z :=
  map_sum (varianceTrilinearLinear v z) q s

theorem varianceTrilinear_synthesis {ι : Type*} [Fintype ι]
    (b : ι → TangentCoordinates) (c : ι → ℝ) :
    varianceCubic (∑ i,c i • b i) =
      ∑ i,∑ j,∑ k,c i*c j*c k*varianceTrilinear (b i) (b j) (b k) := by
  rw [←varianceTrilinear_diagonal,varianceTrilinear_sum_first]
  apply Finset.sum_congr rfl
  intro i _
  rw [varianceTrilinear_smul_first,varianceTrilinear_swap12,
    varianceTrilinear_sum_first,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [varianceTrilinear_smul_first,varianceTrilinear_swap23,
    varianceTrilinear_swap12,varianceTrilinear_sum_first,
    Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [varianceTrilinear_smul_first,
    varianceTrilinear_swap12 (b k) (b j) (b i),
    varianceTrilinear_swap23 (b j) (b k) (b i),
    varianceTrilinear_swap12 (b j) (b i) (b k)]
  ring

#print axioms varianceTrilinear_synthesis
end Blueprint.Thomson.Tail.Implementation
