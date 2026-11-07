import ThomsonNegative.Structure.DenominatorSupport

import ThomsonNegative.Structure.Packed.ChainSound

import ThomsonNegative.Structure.Factored.DenominatorLeaves



noncomputable section

namespace ThomsonNegative.Structure.Factored

open ThomsonNegative.Structure.Exact ThomsonNegative.Structure.Packed



def primitiveCoefficients : Fin 14 → List ℤ := ![[-1,1], [-1,3], [-1,5], [0,1], [-1,-6,23], [-1,2,7], [1,-10,17], [1,6,1], [3,-30,35], [-3,21,-45,35], [-1,9,-35,35], [-1,0,78,-408,587], [1,-84,1794,-19684,141983,-783016,3545180,-12904040,35253007,-67080708,81406786,-54042548,13170609], [-1,18,-91,-532,6009,-17310,16003]]

def primitiveModel : Fin 14 → ℝ → ℝ := ![ThomsonNegative.Reduction.denominatorFactor0, ThomsonNegative.Reduction.denominatorFactor1, ThomsonNegative.Reduction.denominatorFactor2, ThomsonNegative.Reduction.denominatorFactor3, ThomsonNegative.Reduction.denominatorFactor4, ThomsonNegative.Reduction.denominatorFactor5, ThomsonNegative.Reduction.denominatorFactor6, ThomsonNegative.Reduction.denominatorFactor7, ThomsonNegative.Reduction.denominatorFactor8, ThomsonNegative.Reduction.denominatorFactor9, ThomsonNegative.Reduction.denominatorFactor10, ThomsonNegative.Reduction.denominatorFactor11, ThomsonNegative.Reduction.denominatorFactor12, ThomsonNegative.Structure.lowExtraFactor]

theorem primitive_decode : ∀ i : Fin 14, recCoeffs (DenData.factorWord i.val)=primitiveCoefficients i := by decide +kernel

theorem primitive_eval (i : Fin 14) (a : ℝ) : evalZ (recCoeffs (DenData.factorWord i.val)) a=primitiveModel i a := by
  rw [primitive_decode]
  fin_cases i <;> simp [primitiveCoefficients, primitiveModel, evalZ, horner, ThomsonNegative.Reduction.denominatorFactor0, ThomsonNegative.Reduction.denominatorFactor1, ThomsonNegative.Reduction.denominatorFactor2, ThomsonNegative.Reduction.denominatorFactor3, ThomsonNegative.Reduction.denominatorFactor4, ThomsonNegative.Reduction.denominatorFactor5, ThomsonNegative.Reduction.denominatorFactor6, ThomsonNegative.Reduction.denominatorFactor7, ThomsonNegative.Reduction.denominatorFactor8, ThomsonNegative.Reduction.denominatorFactor9, ThomsonNegative.Reduction.denominatorFactor10, ThomsonNegative.Reduction.denominatorFactor11, ThomsonNegative.Reduction.denominatorFactor12, ThomsonNegative.Structure.lowExtraFactor] <;> ring

theorem primitive_nonzero (i : Fin 14) (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) : evalZ (recCoeffs (DenData.factorWord i.val)) a≠0 := by
  rw [primitive_eval]
  fin_cases i

  · exact ThomsonNegative.Reduction.denominatorFactor_ne_zero a ha hb 0

  · exact ThomsonNegative.Reduction.denominatorFactor_ne_zero a ha hb 1

  · exact ThomsonNegative.Reduction.denominatorFactor_ne_zero a ha hb 2

  · exact ThomsonNegative.Reduction.denominatorFactor_ne_zero a ha hb 3

  · exact ThomsonNegative.Reduction.denominatorFactor_ne_zero a ha hb 4

  · exact ThomsonNegative.Reduction.denominatorFactor_ne_zero a ha hb 5

  · exact ThomsonNegative.Reduction.denominatorFactor_ne_zero a ha hb 6

  · exact ThomsonNegative.Reduction.denominatorFactor_ne_zero a ha hb 7

  · exact ThomsonNegative.Reduction.denominatorFactor_ne_zero a ha hb 8

  · exact ThomsonNegative.Reduction.denominatorFactor_ne_zero a ha hb 9

  · exact ThomsonNegative.Reduction.denominatorFactor_ne_zero a ha hb 10

  · exact ThomsonNegative.Reduction.denominatorFactor_ne_zero a ha hb 11

  · exact ThomsonNegative.Reduction.denominatorFactor_ne_zero a ha hb 12

  · exact ne_of_gt (ThomsonNegative.Structure.lowExtraFactor_pos a ha hb)

theorem all_chains_accepted (i : Fin 7) : (DenData.chain i.val).check=true := by
  fin_cases i

  · exact DenData.chain_0_accepted

  · exact DenData.chain_1_accepted

  · exact DenData.chain_2_accepted

  · exact DenData.chain_3_accepted

  · exact DenData.chain_4_accepted

  · exact DenData.chain_5_accepted

  · exact DenData.chain_6_accepted

theorem chain_base : ∀ i : Fin 7, recCoeffs ((DenData.chain i.val).node 0)=[Int.ofNat (DenData.unit i.val)] := by decide +kernel

theorem chain_unit_pos : ∀ i : Fin 7, 0<DenData.unit i.val := by decide +kernel

theorem chain_factor : ∀ (i : Fin 7) (k : Nat), (DenData.chain i.val).factor k=DenData.factorWord (DenData.factorIndex i.val k) := by
  intro i k
  fin_cases i <;> rfl

theorem chain_factor_bound : ∀ (i : Fin 7) (k : Fin (DenData.chain i.val).length), DenData.factorIndex i.val k.val<14 := by decide +kernel

theorem chain_last : ∀ i : Fin 7, (DenData.chain i.val).node (DenData.chain i.val).length=DenData.denominatorWord i.val := by decide +kernel

theorem denominator_nonzero (i : Fin 7) (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) :
    evalZ (recCoeffs (DenData.denominatorWord i.val)) a≠0 := by
  rw [← chain_last i]
  apply ProductChain.nonzero _ (all_chains_accepted i) a
  · rw [chain_base]
    have hp : (0:ℝ)<(DenData.unit i.val:ℝ) := by exact_mod_cast chain_unit_pos i
    simpa [evalZ,horner] using ne_of_gt hp
  · intro k hk
    rw [chain_factor]
    exact primitive_nonzero ⟨DenData.factorIndex i.val k,chain_factor_bound i ⟨k,hk⟩⟩ a ha hb


theorem P_regular (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) : Data.P.RegularAt a := by
  exact denominator_nonzero 0 a ha hb


theorem S_regular (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) : Data.S.RegularAt a := by
  exact denominator_nonzero 1 a ha hb


theorem J_regular (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) : Data.J.RegularAt a := by
  exact denominator_nonzero 2 a ha hb


theorem M_regular (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) : Data.M.RegularAt a := by
  exact denominator_nonzero 3 a ha hb


theorem MI_regular (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) : Data.MI.RegularAt a := by
  exact denominator_nonzero 4 a ha hb


theorem SI_regular (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) : Data.SI.RegularAt a := by
  exact denominator_nonzero 5 a ha hb


theorem CI_regular (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) : Data.CI.RegularAt a := by
  exact denominator_nonzero 6 a ha hb


theorem SM_regular (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) : Data.SM.RegularAt a := S_regular a ha hb

theorem JC_regular (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) : Data.JC.RegularAt a := J_regular a ha hb

end ThomsonNegative.Structure.Factored
