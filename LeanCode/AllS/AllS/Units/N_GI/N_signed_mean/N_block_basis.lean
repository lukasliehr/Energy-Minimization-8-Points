import AllS.Units.N_GI.N_signed_mean.N_radical_data
import AllS.Units.N_GI.N_signed_mean.N_cubic_tensor
import AllS.Units.N_GI.N_signed_mean.N_absorption_operator

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def meanBlockIndex (j : Fin 8 × Fin 2) : Fin 8 × Fin 2 :=
  (if j.2=0 then j.1 else meanPartner j.1,j.2)

def meanBlockEquiv : (Fin 8 × Fin 2) ≃ (Fin 8 × Fin 2) where
  toFun := meanBlockIndex
  invFun := meanBlockIndex
  left_inv := by
    rintro ⟨j,b⟩
    fin_cases j <;> fin_cases b <;> decide
  right_inv := by
    rintro ⟨j,b⟩
    fin_cases j <;> fin_cases b <;> decide

def meanBlockBasis : OrthonormalBasis (Fin 8 × Fin 2) ℝ TangentCoordinates :=
  meanTangentBasis.reindex meanBlockEquiv

theorem meanBlockBasis_apply (j : Fin 8 × Fin 2) : meanBlockBasis j=meanTangentNormalized (meanBlockIndex j) := by
  rw [meanBlockBasis,OrthonormalBasis.reindex_apply,meanTangentBasis_apply]
  rfl

def meanNormalization (j : Fin 8) : ℝ := if j=0 ∨ j=7 then √2/4 else 1/2

theorem meanNormalization_eq (j : Fin 8) : (√(meanScalarWeight j))⁻¹=meanNormalization j := by
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hp : 0<√(2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have h8 : √(8:ℝ)=2*√2 := by
    rw [show (8:ℝ)=4*2 by norm_num,Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]
    norm_num
  unfold meanScalarWeight meanNormalization
  split_ifs
  · rw [h8]
    field_simp
    nlinarith
  · norm_num

theorem stressH_normalized (j k : Fin 8 × Fin 2) :
    stressH (meanTangentNormalized j) (meanTangentNormalized k)=
      meanNormalization j.1*meanNormalization k.1*meanHEntry j k := by
  unfold meanTangentNormalized
  rw [stressH_smul_left,stressH_symm,stressH_smul_left,stressH_symm,meanH_raw,
    meanNormalization_eq,meanNormalization_eq]
  ring

theorem meanAbsorptionOperator_block_entries (j k : Fin 8 × Fin 2) :
    inner ℝ (meanBlockBasis j) (meanAbsorptionOperator (meanBlockBasis k))=
      if j.1=k.1 then meanRadicalEval (meanBlockAData j.1 j.2 k.2) else 0 := by
  rw [meanAbsorptionOperator_inner]
  have hg := (orthonormal_iff_ite.mp meanBlockBasis.orthonormal) j k
  rw [hg,meanBlockBasis_apply,meanBlockBasis_apply,stressH_normalized]
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hs3 : (√(2:ℝ))^3=2*√2 := by rw [pow_succ,hs]
  rcases j with ⟨j,b⟩
  rcases k with ⟨k,c⟩
  fin_cases j <;> fin_cases k <;> fin_cases b <;> fin_cases c <;>
    norm_num [meanBlockIndex,meanNormalization,meanHEntry,meanScalarWeight,meanPartner,meanSinSign,
      meanPhiEigen,meanMeridianEigen,meanBetaFactor,meanBlockAData,meanRadicalEval,
      Fin.instOfNat,Fin.ofNat,Fin.succ,Fin.ext_iff] <;>
    ring_nf <;> simp [hs,hs3] <;> ring

#print axioms meanAbsorptionOperator_block_entries
end Blueprint.Thomson.Tail.Implementation
