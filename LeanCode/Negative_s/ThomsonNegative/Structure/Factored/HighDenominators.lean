import ThomsonNegative.Structure.Factored.Denominators

import ThomsonNegative.Structure.Factored.HighDenominatorLeaves

noncomputable section

namespace ThomsonNegative.Structure.Factored

open ThomsonNegative.Structure.Exact ThomsonNegative.Structure.Packed

namespace HighRegular

theorem all_chains_accepted (i : Fin 7) : (HighDenData.chain i.val).check=true := by
  fin_cases i
  · exact HighDenData.chain_0_accepted
  · exact HighDenData.chain_1_accepted
  · exact HighDenData.chain_2_accepted
  · exact HighDenData.chain_3_accepted
  · exact HighDenData.chain_4_accepted
  · exact HighDenData.chain_5_accepted
  · exact HighDenData.chain_6_accepted

theorem chain_base : ∀ i : Fin 7, recCoeffs ((HighDenData.chain i.val).node 0)=[Int.ofNat (HighDenData.unit i.val)] := by decide +kernel

theorem chain_unit_pos : ∀ i : Fin 7, 0<HighDenData.unit i.val := by decide +kernel

theorem chain_factor : ∀ (i : Fin 7) (k : Nat), (HighDenData.chain i.val).factor k=DenData.factorWord (HighDenData.factorIndex i.val k) := by
  intro i k
  fin_cases i <;> rfl

theorem chain_factor_bound : ∀ (i : Fin 7) (k : Fin (HighDenData.chain i.val).length), HighDenData.factorIndex i.val k.val<14 := by decide +kernel

theorem chain_last : ∀ i : Fin 7, (HighDenData.chain i.val).node (HighDenData.chain i.val).length=HighDenData.denominatorWord i.val := by decide +kernel

theorem denominator_nonzero (i : Fin 7) (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) :
    evalZ (recCoeffs (HighDenData.denominatorWord i.val)) a≠0 := by
  rw [← chain_last i]
  apply ProductChain.nonzero _ (all_chains_accepted i) a
  · rw [chain_base]
    have hp : (0:ℝ)<(HighDenData.unit i.val:ℝ) := by exact_mod_cast chain_unit_pos i
    simpa [evalZ,horner] using ne_of_gt hp
  · intro k hk
    rw [chain_factor]
    exact primitive_nonzero ⟨HighDenData.factorIndex i.val k,chain_factor_bound i ⟨k,hk⟩⟩ a ha hb
end HighRegular

theorem A_regular (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) : HighData.A.RegularAt a := HighRegular.denominator_nonzero 0 a ha hb

theorem K3_regular (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) : HighData.K3.RegularAt a := HighRegular.denominator_nonzero 1 a ha hb

theorem K14_regular (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) : HighData.K14.RegularAt a := HighRegular.denominator_nonzero 2 a ha hb

theorem K15_regular (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) : HighData.K15.RegularAt a := HighRegular.denominator_nonzero 3 a ha hb

theorem K36_regular (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) : HighData.K36.RegularAt a := HighRegular.denominator_nonzero 4 a ha hb

theorem H3_regular (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) : HighData.H3.RegularAt a := HighRegular.denominator_nonzero 5 a ha hb

theorem H14_regular (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) : HighData.H14.RegularAt a := HighRegular.denominator_nonzero 6 a ha hb

theorem LP_regular (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) : HighData.LP.RegularAt a := P_regular a ha hb

theorem LS_regular (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) : HighData.LS.RegularAt a := S_regular a ha hb

end ThomsonNegative.Structure.Factored
