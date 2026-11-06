import AllS.Units.N_GI.N_signed_mean.N_bilinear

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def meanTangentSynthesis (x : Fin 8 × Fin 2 → ℝ) : TangentCoordinates := ∑j,x j • meanTangentRaw j

def meanScalarSynthesis (x : Fin 8 → ℝ) (i : Fin 8) : ℝ := ∑j,x j*meanScalarRaw j i

theorem meanTangentSynthesis_surjective (q : TangentCoordinates) :
    ∃ x,meanTangentSynthesis x=q := by
  refine ⟨fun j=>inner ℝ (meanTangentNormalized j) q*(√(meanScalarWeight j.1))⁻¹,?_⟩
  have he := meanTangentBasis.sum_repr' q
  simp only [meanTangentBasis_apply] at he
  refine Eq.trans (b := ∑j,inner ℝ (meanTangentNormalized j) q • meanTangentNormalized j) ?_ he
  unfold meanTangentSynthesis
  apply Finset.sum_congr rfl
  intro j _
  simp only [meanTangentNormalized,mul_smul]

theorem meanScalarSynthesis_surjective (b : Fin 8 → ℝ) : ∃x,meanScalarSynthesis x=b := by
  let z : EuclideanSpace ℝ (Fin 8) := WithLp.toLp 2 b
  refine ⟨fun j=>inner ℝ (meanScalarNormalized j) z*(√(meanScalarWeight j))⁻¹,?_⟩
  have he := meanScalarBasis.sum_repr' z
  simp only [meanScalarBasis_apply,meanScalarNormalized] at he
  funext i
  have hi := congrArg (fun v : EuclideanSpace ℝ (Fin 8)=>v i) he
  simpa [meanScalarSynthesis,meanScalarNormalized,meanScalarVector,PiLp.smul_apply,
    WithLp.ofLp_sum,Finset.sum_apply,smul_eq_mul,mul_assoc,z] using hi

theorem meanTangentSynthesis_norm_sq (x : Fin 8 × Fin 2 → ℝ) :
    ‖meanTangentSynthesis x‖^2=∑j,meanScalarWeight j.1*(x j)^2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [meanTangentSynthesis,sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,
    meanTangentRaw_gram]
  simp [pow_two,mul_assoc,mul_comm,mul_left_comm]

theorem meanScalarSynthesis_norm_sq (x : Fin 8 → ℝ) :
    ‖(WithLp.toLp 2 (meanScalarSynthesis x) : EuclideanSpace ℝ (Fin 8))‖^2=
      ∑j,meanScalarWeight j*(x j)^2 := by
  have he : (WithLp.toLp 2 (meanScalarSynthesis x) : EuclideanSpace ℝ (Fin 8))=
      ∑j,x j • meanScalarVector j := by
    ext i
    simp [meanScalarSynthesis,meanScalarVector,PiLp.smul_apply,WithLp.ofLp_sum,Finset.sum_apply]
  rw [he,← real_inner_self_eq_norm_sq]
  simp only [sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,meanScalarVector_gram]
  simp [pow_two,mul_assoc,mul_comm,mul_left_comm]

theorem stressH_synthesis (x y : Fin 8 × Fin 2 → ℝ) :
    stressH (meanTangentSynthesis x) (meanTangentSynthesis y)=
      ∑j,∑k,x j*y k*stressH (meanTangentRaw j) (meanTangentRaw k) := by
  unfold meanTangentSynthesis
  rw [stressH_sum_left]
  apply Finset.sum_congr rfl
  intro j _
  rw [stressH_smul_left,stressH_symm,stressH_sum_left,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [stressH_smul_left,stressH_symm]
  ring

theorem stressB_synthesis (x : Fin 8 × Fin 2 → ℝ) (y : Fin 8 → ℝ) :
    stressB (meanTangentSynthesis x) (meanScalarSynthesis y)=
      ∑j,∑k,x j*y k*stressB (meanTangentRaw j) (meanScalarRaw k) := by
  unfold meanTangentSynthesis meanScalarSynthesis
  rw [stressB_sum_left]
  apply Finset.sum_congr rfl
  intro j _
  rw [stressB_smul_left,stressB_sum_right,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [stressB_smul_right]
  ring

theorem stressD_synthesis (x y : Fin 8 → ℝ) :
    stressD (meanScalarSynthesis x) (meanScalarSynthesis y)=
      ∑j,∑k,x j*y k*stressD (meanScalarRaw j) (meanScalarRaw k) := by
  unfold meanScalarSynthesis
  rw [stressD_sum_left]
  apply Finset.sum_congr rfl
  intro j _
  rw [stressD_smul_left,stressD_symm,stressD_sum_left,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [stressD_smul_left,stressD_symm]
  ring

#print axioms meanTangentSynthesis_surjective
#print axioms stressB_synthesis
end Blueprint.Thomson.Tail.Implementation
