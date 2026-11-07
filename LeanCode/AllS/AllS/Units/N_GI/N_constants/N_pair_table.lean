import Blueprint.TailContactData
import AllS.Units.N_GI.N_constants.N_algebra
import AllS.Units.N_GI.N_nearest_chart.N_frame
import AllS.Units.N_GI.N_upstream_bridge.N_coordinates
import AllS.Units.N_GI.N_setup.N_pairs

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem packingReference_configuration : IsConfiguration packingReference := by
  have hX := Blueprint.antiprism_is_configuration packingHeight packingHeight_mem_Ioo
  exact ⟨fun i => hX.1 (cyclicIndex i),hX.2.comp cyclicIndex_bijective.1⟩

theorem packingReference_inner_formula (i j : Fin 8) :
    inner ℝ (packingReference i) (packingReference j)=
      (1-packingHeight)*(angularCos i*angularCos j+angularSin i*angularSin j)+
      packingHeight*layerSign i*layerSign j := by
  obtain ⟨_,_,hH,hR⟩ := packing_parameters
  rw [packingReference_formula,packingReference_formula,PiLp.inner_apply]
  simp [Fin.sum_univ_succ]
  linear_combination (angularCos i*angularCos j+angularSin i*angularSin j)*hR+
    (layerSign i*layerSign j)*hH

theorem packingReference_inner_cyclic (i j : Fin 8) :
    inner ℝ (packingReference i) (packingReference j)=
      if i=j then 1 else if IsCyclicContact i j then packingHeight
      else if j=i+4 then 2*packingHeight-1 else -3*packingHeight := by
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hp : 0 < √(2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have ha : (1-packingHeight)/√2=2*packingHeight := by
    apply (div_eq_iff hp.ne').mpr
    dsimp [packingHeight]
    nlinarith
  have hi : (√(2:ℝ))⁻¹ = √2/2 := by
    apply (inv_eq_iff_eq_inv).mpr
    field_simp
    nlinarith [hs]
  have hs3 : (√(2:ℝ))^3 = 2*√2 := by rw [pow_succ,hs]
  rw [packingReference_inner_formula]
  fin_cases i <;> fin_cases j <;>
    norm_num [IsCyclicContact,Fin.ext_iff,Fin.val_add,angularCos,angularSin,layerSign,div_eq_mul_inv,hi,packingHeight] <;>
    ring_nf <;> simp [hs,hs3] <;> ring

theorem cyclicContactPairs_card : cyclicContactPairs.card=16 := by decide

theorem cyclicContactPairs_subset : cyclicContactPairs ⊆ unorderedPairs := by decide

theorem cyclicContactPairs_mem (i j : Fin 8) :
    (i,j) ∈ cyclicContactPairs ↔ i < j ∧ IsCyclicContact i j := by
  revert i j
  decide

theorem contactNext_contact (e : ContactIndex) : IsCyclicContact e.1 (contactNext e) := by
  rcases e with ⟨i,k⟩
  fin_cases k <;> simp [IsCyclicContact,contactNext]

theorem contactNext_ne (e : ContactIndex) : e.1 ≠ contactNext e := by
  revert e
  decide

theorem constants_pair_table : IsConfiguration packingReference ∧
    cyclicContactPairs.card=16 ∧ (unorderedPairs \ cyclicContactPairs).card=12 ∧
    (∀ e : ContactIndex, inner ℝ (packingReference e.1) (packingReference (contactNext e))=packingHeight ∧
      squaredDistance packingReference e.1 (contactNext e)=tau) ∧
    (∀ ij ∈ unorderedPairs \ cyclicContactPairs, 2*tau ≤ squaredDistance packingReference ij.1 ij.2) := by
  refine ⟨packingReference_configuration,cyclicContactPairs_card,by decide,?_,?_⟩
  · intro e
    have hi : inner ℝ (packingReference e.1) (packingReference (contactNext e))=packingHeight := by
      rw [packingReference_inner_cyclic,if_neg (contactNext_ne e),if_pos (contactNext_contact e)]
    refine ⟨hi,?_⟩
    rw [squaredDistance,norm_sub_sq_real,packingReference_configuration.1,packingReference_configuration.1,hi]
    dsimp [tau]; ring
  · rintro ⟨i,j⟩ hij
    obtain ⟨hij,hnot⟩ := Finset.mem_sdiff.mp hij
    have hlt := (mem_unorderedPairs i j).mp hij
    have hnc : ¬ IsCyclicContact i j := by
      intro h
      exact hnot ((cyclicContactPairs_mem i j).mpr ⟨hlt,h⟩)
    rw [squaredDistance,norm_sub_sq_real,packingReference_configuration.1,packingReference_configuration.1,
      packingReference_inner_cyclic,if_neg hlt.ne,if_neg hnc]
    split_ifs
    · dsimp [tau]; ring_nf; rfl
    · have ha : 1/5 < packingHeight := by
        have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
        have hp := Real.sqrt_nonneg (2:ℝ)
        dsimp [packingHeight]
        nlinarith
      dsimp [tau]
      linarith

#check constants_pair_table
#print axioms constants_pair_table
end Blueprint.Thomson.Tail.Implementation
