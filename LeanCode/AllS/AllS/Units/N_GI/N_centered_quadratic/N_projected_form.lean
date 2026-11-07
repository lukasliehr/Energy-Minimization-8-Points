import AllS.Units.N_GI.N_centered_quadratic.N_contact_operator
import AllS.Units.N_GI.N_signed_mean.N_gram_exact

set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def centeredContactGram (q v : TangentCoordinates) : ℝ :=
  (∑e : ContactIndex,contactWeight e*(inner ℝ (contactM e q) (contactM e v)-
    ∑j : Fin 3,inner ℝ (normalizedRotation j) (contactM e q)*inner ℝ (normalizedRotation j) (contactM e v)))-
  (∑j : Fin 8 × Fin 2,stressH q (meanTangentRaw j)*stressH v (meanTangentRaw j)/meanScalarWeight j.1)/contactTotalWeight

def centeredContactRawGram (q v : TangentCoordinates) : ℝ :=
  (∑e : ContactIndex,contactWeight e*((∑k : Fin 4,contactMComponents e q k*contactMComponents e v k)-
    ∑j : Fin 3,contactMBilinear e (boundaryRotation j) q*contactMBilinear e (boundaryRotation j) v /
      boundaryWeight (boundaryRotationIndex j)))-
  (∑j : Fin 8 × Fin 2,stressH q (meanTangentRaw j)*stressH v (meanTangentRaw j)/meanScalarWeight j.1)/contactTotalWeight

theorem centeredContactGram_raw (q v : TangentCoordinates) : centeredContactGram q v=centeredContactRawGram q v := by
  unfold centeredContactGram centeredContactRawGram
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  rw [contactM_pair_inner]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  rw [normalizedRotation,boundaryNormalized,real_inner_smul_left,real_inner_smul_left]
  change (√(boundaryWeight (boundaryRotationIndex j)))⁻¹*inner ℝ (boundaryRotation j) (contactM e q)*
    ((√(boundaryWeight (boundaryRotationIndex j)))⁻¹*inner ℝ (boundaryRotation j) (contactM e v))=_
  rw [contactM_inner,contactM_inner]
  have hn := ne_of_gt (Real.sqrt_pos.mpr (boundaryWeight_pos (boundaryRotationIndex j)))
  have hs := Real.sq_sqrt (boundaryWeight_pos (boundaryRotationIndex j)).le
  ring_nf
  rw [inv_pow,hs]
  ring

theorem meanTangent_parseval (q v : TangentCoordinates) :
    inner ℝ q v=∑j : Fin 8 × Fin 2,inner ℝ q (meanTangentRaw j)*inner ℝ v (meanTangentRaw j)/meanScalarWeight j.1 := by
  rw [← meanTangentBasis.repr.inner_map_map q v,PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.inner_apply,OrthonormalBasis.repr_apply_apply,OrthonormalBasis.repr_apply_apply,
    meanTangentBasis_apply,meanTangentNormalized,real_inner_smul_left,real_inner_smul_left]
  rw [real_inner_comm (meanTangentRaw j) q,real_inner_comm (meanTangentRaw j) v]
  have hn := ne_of_gt (Real.sqrt_pos.mpr (meanScalarWeight_pos j.1))
  have hs := Real.sq_sqrt (meanScalarWeight_pos j.1).le
  ring_nf
  rw [inv_pow,hs]
  ring

theorem stressMap_inner_symm (q v : TangentCoordinates) : inner ℝ (stressMap q) v=stressH q v := by
  rw [real_inner_comm,stressMap_inner,stressH_symm]

theorem stressMap_norm_sq (q : TangentCoordinates) :
    ‖stressMap q‖^2=∑j : Fin 8 × Fin 2,(stressH q (meanTangentRaw j))^2/meanScalarWeight j.1 := by
  rw [← real_inner_self_eq_norm_sq,meanTangent_parseval]
  simp_rw [stressMap_inner_symm,pow_two]

theorem centeredContactGram_self (q : TangentCoordinates) : centeredContactGram q q=
    (∑e : ContactIndex,contactWeight e*‖sliceProjection (contactM e q)‖^2)-‖stressMap q‖^2/contactTotalWeight := by
  simp only [centeredContactGram,sliceProjection_norm_sq,stressMap_norm_sq]
  simp only [real_inner_self_eq_norm_sq,pow_two]

#print axioms centeredContactGram_raw
#print axioms centeredContactGram_self
end Blueprint.Thomson.Tail.Implementation
