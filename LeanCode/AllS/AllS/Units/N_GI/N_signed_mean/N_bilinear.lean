import AllS.Units.N_GI.N_signed_mean.N_spectral_data
import AllS.Units.N_GI.N_boundary_basis.N_synthesis

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem stressH_symm (q v : TangentCoordinates) : stressH q v=stressH v q := by
  unfold stressH
  apply Finset.sum_congr rfl
  intro e _
  rw [real_inner_comm (tangentVector q e.1) (tangentVector v e.1),
    real_inner_comm (tangentVector q (contactNext e)) (tangentVector v (contactNext e)),
    real_inner_comm (tangentVector q e.1) (tangentVector v (contactNext e)),
    real_inner_comm (tangentVector q (contactNext e)) (tangentVector v e.1)]
  ring

theorem stressH_sum_left {ι : Type*} (s : Finset ι) (q : ι → TangentCoordinates) (v : TangentCoordinates) :
    stressH (∑i∈s,q i) v=∑i∈s,stressH (q i) v := by
  unfold stressH
  simp_rw [tangentVector_sum,sum_inner]
  simp only [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  exact Finset.sum_comm

theorem stressH_smul_left (c : ℝ) (q v : TangentCoordinates) : stressH (c • q) v=c*stressH q v := by
  unfold stressH
  simp_rw [tangentVector_smul,real_inner_smul_left]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem stressB_sum_left {ι : Type*} (s : Finset ι) (q : ι → TangentCoordinates) (b : Fin 8 → ℝ) :
    stressB (∑i∈s,q i) b=∑i∈s,stressB (q i) b := by
  unfold stressB
  simp_rw [tangentVector_sum,sum_inner]
  simp only [Finset.mul_sum,← Finset.sum_sub_distrib]
  exact Finset.sum_comm

theorem stressB_smul_left (c : ℝ) (q : TangentCoordinates) (b : Fin 8 → ℝ) :
    stressB (c • q) b=c*stressB q b := by
  unfold stressB
  simp_rw [tangentVector_smul,real_inner_smul_left]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem stressB_sum_right {ι : Type*} (s : Finset ι) (q : TangentCoordinates) (b : ι → Fin 8 → ℝ) :
    stressB q (fun j=>∑i∈s,b i j)=∑i∈s,stressB q (b i) := by
  unfold stressB
  simp only [Finset.sum_mul,Finset.mul_sum,← Finset.sum_neg_distrib,← Finset.sum_sub_distrib]
  exact Finset.sum_comm

theorem stressB_smul_right (c : ℝ) (q : TangentCoordinates) (b : Fin 8 → ℝ) :
    stressB q (fun i=>c*b i)=c*stressB q b := by
  unfold stressB
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem stressD_symm (b c : Fin 8 → ℝ) : stressD b c=stressD c b := by
  unfold stressD
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem stressD_sum_left {ι : Type*} (s : Finset ι) (b : ι → Fin 8 → ℝ) (c : Fin 8 → ℝ) :
    stressD (fun j=>∑i∈s,b i j) c=∑i∈s,stressD (b i) c := by
  unfold stressD
  simp only [← Finset.sum_sub_distrib,Finset.mul_sum,Finset.sum_mul]
  exact Finset.sum_comm

theorem stressD_smul_left (r : ℝ) (b c : Fin 8 → ℝ) :
    stressD (fun i=>r*b i) c=r*stressD b c := by
  unfold stressD
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

#print axioms stressH_sum_left
#print axioms stressB_sum_right
#print axioms stressD_sum_left
end Blueprint.Thomson.Tail.Implementation
