import ThomsonNegative.Structure.Concrete.BasisDen.DenLeaves

import ThomsonNegative.Structure.Factored.Denominators

noncomputable section

namespace ThomsonNegative.Structure.Concrete.BasisDen

open ThomsonNegative.Structure.Exact ThomsonNegative.Structure.Packed

theorem chain_accepted (i : Fin 8) : (DenData.chain i.val).check=true := by
  fin_cases i
  · exact DenData.check0
  · exact DenData.check1
  · exact DenData.check2
  · exact DenData.check3
  · exact DenData.check4
  · exact DenData.check5
  · exact DenData.check6
  · exact DenData.check7

theorem chain_base : ∀i : Fin 8,recCoeffs ((DenData.chain i.val).node 0)=[Int.ofNat (DenData.unit i.val)] := by decide +kernel

theorem chain_unit_pos : ∀i : Fin 8,0<DenData.unit i.val := by decide +kernel

theorem chain_factor : ∀(i : Fin 8)(k : Nat),(DenData.chain i.val).factor k=ThomsonNegative.Structure.Factored.DenData.factorWord (DenData.factorIndex i.val k) := by
  intro i k
  fin_cases i <;> rfl

theorem factor_bound : ∀(i : Fin 8)(k : Fin (DenData.chain i.val).length),DenData.factorIndex i.val k.val<14 := by decide +kernel

theorem chain_last : ∀i : Fin 8,(DenData.chain i.val).node (DenData.chain i.val).length=DenData.word i.val := by decide +kernel

theorem denominator_nonzero (i : Fin 8) (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) :
    evalZ (recCoeffs (DenData.word i.val)) a≠0 := by
  rw [← chain_last i]
  apply ProductChain.nonzero _ (chain_accepted i) a
  · rw [chain_base]
    have hp : (0:ℝ)<(DenData.unit i.val:ℝ) := by exact_mod_cast chain_unit_pos i
    simpa [evalZ,horner] using ne_of_gt hp
  · intro k hk
    rw [chain_factor]
    exact ThomsonNegative.Structure.Factored.primitive_nonzero
      ⟨DenData.factorIndex i.val k,factor_bound i ⟨k,hk⟩⟩ a ha hb
end ThomsonNegative.Structure.Concrete.BasisDen
