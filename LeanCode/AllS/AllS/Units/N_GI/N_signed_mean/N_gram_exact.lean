import AllS.Units.N_GI.N_signed_mean.N_hgram_row_0_0
import AllS.Units.N_GI.N_signed_mean.N_hgram_row_0_1
import AllS.Units.N_GI.N_signed_mean.N_hgram_row_1_0
import AllS.Units.N_GI.N_signed_mean.N_hgram_row_1_1
import AllS.Units.N_GI.N_signed_mean.N_hgram_row_2_0
import AllS.Units.N_GI.N_signed_mean.N_hgram_row_2_1
import AllS.Units.N_GI.N_signed_mean.N_hgram_row_3_0
import AllS.Units.N_GI.N_signed_mean.N_hgram_row_3_1
import AllS.Units.N_GI.N_signed_mean.N_hgram_row_4_0
import AllS.Units.N_GI.N_signed_mean.N_hgram_row_4_1
import AllS.Units.N_GI.N_signed_mean.N_hgram_row_5_0
import AllS.Units.N_GI.N_signed_mean.N_hgram_row_5_1
import AllS.Units.N_GI.N_signed_mean.N_hgram_row_6_0
import AllS.Units.N_GI.N_signed_mean.N_hgram_row_6_1
import AllS.Units.N_GI.N_signed_mean.N_hgram_row_7_0
import AllS.Units.N_GI.N_signed_mean.N_hgram_row_7_1
import AllS.Units.N_GI.N_signed_mean.N_bgram_row_0_0
import AllS.Units.N_GI.N_signed_mean.N_bgram_row_0_1
import AllS.Units.N_GI.N_signed_mean.N_bgram_row_1_0
import AllS.Units.N_GI.N_signed_mean.N_bgram_row_1_1
import AllS.Units.N_GI.N_signed_mean.N_bgram_row_2_0
import AllS.Units.N_GI.N_signed_mean.N_bgram_row_2_1
import AllS.Units.N_GI.N_signed_mean.N_bgram_row_3_0
import AllS.Units.N_GI.N_signed_mean.N_bgram_row_3_1
import AllS.Units.N_GI.N_signed_mean.N_bgram_row_4_0
import AllS.Units.N_GI.N_signed_mean.N_bgram_row_4_1
import AllS.Units.N_GI.N_signed_mean.N_bgram_row_5_0
import AllS.Units.N_GI.N_signed_mean.N_bgram_row_5_1
import AllS.Units.N_GI.N_signed_mean.N_bgram_row_6_0
import AllS.Units.N_GI.N_signed_mean.N_bgram_row_6_1
import AllS.Units.N_GI.N_signed_mean.N_bgram_row_7_0
import AllS.Units.N_GI.N_signed_mean.N_bgram_row_7_1
import AllS.Units.N_GI.N_signed_mean.N_dgram
import AllS.Units.N_GI.N_signed_mean.N_synthesis

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem meanH_raw (j : Fin 8 × Fin 2) (k : Fin 8 × Fin 2) :
    stressH (meanTangentRaw j) (meanTangentRaw k)=meanHEntry j k := by
  rcases j with ⟨j,b⟩
  fin_cases j <;> fin_cases b
  · exact meanH_raw_row_0_0 k
  · exact meanH_raw_row_0_1 k
  · exact meanH_raw_row_1_0 k
  · exact meanH_raw_row_1_1 k
  · exact meanH_raw_row_2_0 k
  · exact meanH_raw_row_2_1 k
  · exact meanH_raw_row_3_0 k
  · exact meanH_raw_row_3_1 k
  · exact meanH_raw_row_4_0 k
  · exact meanH_raw_row_4_1 k
  · exact meanH_raw_row_5_0 k
  · exact meanH_raw_row_5_1 k
  · exact meanH_raw_row_6_0 k
  · exact meanH_raw_row_6_1 k
  · exact meanH_raw_row_7_0 k
  · exact meanH_raw_row_7_1 k

theorem meanB_raw (j : Fin 8 × Fin 2) (k : Fin 8) :
    stressB (meanTangentRaw j) (meanScalarRaw k)=meanBEntry j k := by
  rcases j with ⟨j,b⟩
  fin_cases j <;> fin_cases b
  · exact meanB_raw_row_0_0 k
  · exact meanB_raw_row_0_1 k
  · exact meanB_raw_row_1_0 k
  · exact meanB_raw_row_1_1 k
  · exact meanB_raw_row_2_0 k
  · exact meanB_raw_row_2_1 k
  · exact meanB_raw_row_3_0 k
  · exact meanB_raw_row_3_1 k
  · exact meanB_raw_row_4_0 k
  · exact meanB_raw_row_4_1 k
  · exact meanB_raw_row_5_0 k
  · exact meanB_raw_row_5_1 k
  · exact meanB_raw_row_6_0 k
  · exact meanB_raw_row_6_1 k
  · exact meanB_raw_row_7_0 k
  · exact meanB_raw_row_7_1 k

def meanHValue (x : Fin 8 × Fin 2 → ℝ) : ℝ :=
  ∑j,meanScalarWeight j*(meanPhiEigen j*(x (j,0))^2+
    2*packingZHeight*meanBetaFactor j*meanSinSign j*x (j,0)*x (meanPartner j,1)+
    meanMeridianEigen j*(x (meanPartner j,1))^2)

def meanBOutput (x : Fin 8 × Fin 2 → ℝ) (j : Fin 8) : ℝ :=
  packingRadius*(meanBetaFactor j*meanSinSign j*x (meanPartner j,0)+
    packingZHeight*meanRadialFactor j*x (j,1))

theorem meanH_synthesis_value (x : Fin 8 × Fin 2 → ℝ) :
    stressH (meanTangentSynthesis x) (meanTangentSynthesis x)=meanHValue x := by
  rw [stressH_synthesis]
  simp_rw [meanH_raw]
  norm_num [Fintype.sum_prod_type,Fin.sum_univ_succ,Fin.succ,Fin.instOfNat,Fin.ofNat,meanHValue,meanHEntry,meanScalarWeight,
    meanPhiEigen,meanMeridianEigen,meanBetaFactor,meanSinSign,meanPartner]
  simp [Fin.ext_iff]
  <;> ring

theorem meanB_synthesis_value (x : Fin 8 × Fin 2 → ℝ) (y : Fin 8 → ℝ) :
    stressB (meanTangentSynthesis x) (meanScalarSynthesis y)=
      ∑j,meanScalarWeight j*meanBOutput x j*y j := by
  rw [stressB_synthesis]
  simp_rw [meanB_raw]
  norm_num [Fintype.sum_prod_type,Fin.sum_univ_succ,Fin.succ,Fin.instOfNat,Fin.ofNat,meanBOutput,meanBEntry,meanScalarWeight,
    meanRadialFactor,meanBetaFactor,meanSinSign,meanPartner]
  simp [Fin.ext_iff]
  <;> ring

theorem meanD_synthesis_value (y : Fin 8 → ℝ) :
    stressD (meanScalarSynthesis y) (meanScalarSynthesis y)=∑j,meanScalarWeight j*meanDEigen j*(y j)^2 := by
  rw [stressD_synthesis]
  simp_rw [meanD_raw]
  simp [meanDEntry,pow_two,mul_assoc,mul_comm,mul_left_comm]

#print axioms meanH_synthesis_value
#print axioms meanB_synthesis_value
#print axioms meanD_synthesis_value
end Blueprint.Thomson.Tail.Implementation
