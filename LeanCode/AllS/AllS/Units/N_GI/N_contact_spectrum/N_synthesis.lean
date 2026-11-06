import AllS.Units.N_GI.N_contact_spectrum.N_gram_data

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

def contactRawSynthesis (x : Fin 13 → ℝ) : TangentCoordinates := ∑ j, x j • contactRawVector j

theorem contactRawSynthesis_surjective (q : TangentCoordinates) (hq : q∈rotationSlice) :
    ∃ x : Fin 13 → ℝ, contactRawSynthesis x=q := by
  refine ⟨fun j=>inner ℝ (boundaryFourier j) q*(Real.sqrt (boundaryWeight (boundaryBasisIndex j)))⁻¹,?_⟩
  have he := boundarySlice_expand q hq
  apply Eq.trans (b := ∑ j : Fin 13, inner ℝ (boundaryFourier j) q • boundaryFourier j) _ he
  change (∑ j : Fin 13, (inner ℝ (boundaryFourier j) q*(Real.sqrt (boundaryWeight (boundaryBasisIndex j)))⁻¹) • contactRawVector j)=_
  apply Finset.sum_congr rfl
  intro j _
  simp only [boundaryFourier,boundaryNormalized,contactRawVector,mul_smul]

theorem contactRawVector_gram (j k : Fin 13) :
    inner ℝ (contactRawVector j) (contactRawVector k)=
      if j=k then boundaryWeight (boundaryBasisIndex j) else 0 := by
  simp [contactRawVector,boundaryRaw_gram,boundaryBasisIndex_injective.eq_iff]

theorem contactRawSynthesis_norm_sq (x : Fin 13 → ℝ) :
    ‖contactRawSynthesis x‖^2=∑ j, boundaryWeight (boundaryBasisIndex j)*(x j)^2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [contactRawSynthesis,sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,
    contactRawVector_gram]
  simp [pow_two,mul_assoc,mul_comm,mul_left_comm]

theorem contactLinear_synthesis (x : Fin 13 → ℝ) (e : ContactIndex) :
    contactLinear (contactRawSynthesis x) e.1 (contactNext e)=
      ∑ j, x j*contactLinear (contactRawVector j) e.1 (contactNext e) := by
  change contactLinearMap e (∑j,x j • contactRawVector j)=_
  simp [map_sum,contactLinearMap]

theorem contactGram_synthesis (w : ℝ) (x y : Fin 13 → ℝ) :
    contactGram w (contactRawSynthesis x) (contactRawSynthesis y)=
      ∑ j, ∑ k, x j*y k*contactGram w (contactRawVector j) (contactRawVector k) := by
  unfold contactGram
  simp_rw [contactLinear_synthesis]
  simp only [Finset.mul_sum,Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro e _
  ring

#print axioms contactGram_synthesis
end Blueprint.Thomson.Tail.Implementation
