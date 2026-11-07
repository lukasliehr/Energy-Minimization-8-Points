import AllS.Units.N_GI.N_centered_quadratic.N_bilinear
import AllS.Units.N_GI.N_centered_quadratic.N_spectral_inequalities
import AllS.Units.N_GI.N_signed_mean.N_physical_bounds

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

def centeredQValue (x : Fin 8 × Fin 2 → ℝ) : ℝ :=
  ∑j,meanScalarWeight j*(centeredPhiEigen j*(x (j,0))^2+
    2*packingZHeight*centeredBetaFactor j*meanSinSign j*x (j,0)*x (meanPartner j,1)+
    centeredMeridianEigen j*(x (meanPartner j,1))^2)

theorem centeredQ_synthesis_value_of_entries
    (hentries : ∀ j k : Fin 8 × Fin 2,
      centeredContactGram (meanTangentRaw j) (meanTangentRaw k)=centeredQEntry j k) (x : Fin 8 × Fin 2 → ℝ) :
    centeredContactGram (meanTangentSynthesis x) (meanTangentSynthesis x)=centeredQValue x := by
  rw [centeredContactGram_synthesis]
  simp_rw [hentries]
  norm_num [Fintype.sum_prod_type,Fin.sum_univ_succ,Fin.succ,Fin.instOfNat,Fin.ofNat,centeredQValue,centeredQEntry,meanScalarWeight,
    centeredPhiEigen,centeredMeridianEigen,centeredBetaFactor,meanSinSign,meanPartner]
  simp [Fin.ext_iff]
  <;> ring

theorem centeredContactGram_bound_of_entries
    (hentries : ∀ j k : Fin 8 × Fin 2,
      centeredContactGram (meanTangentRaw j) (meanTangentRaw k)=centeredQEntry j k) (q : TangentCoordinates) : centeredContactGram q q ≤ 4*‖q‖^2 := by
  obtain ⟨x,rfl⟩ := meanTangentSynthesis_surjective q
  rw [centeredQ_synthesis_value_of_entries hentries]
  unfold centeredQValue
  calc
    _ ≤ ∑j,meanScalarWeight j*(4*((x (j,0))^2+(x (meanPartner j,1))^2)) := by
      exact Finset.sum_le_sum (fun j _=>mul_le_mul_of_nonneg_left
        (centeredQ_block_bound j _ _) (meanScalarWeight_pos j).le)
    _ = _ := by
      simp only [mul_add,Finset.sum_add_distrib]
      simp_rw [mul_left_comm (meanScalarWeight _) (4:ℝ)]
      rw [← Finset.mul_sum,← Finset.mul_sum,meanPartner_norm_sum,meanTangentSynthesis_norm_split]
      ring

#print axioms centeredContactGram_bound_of_entries
end Blueprint.Thomson.Tail.Implementation
