import ThomsonCompact.CoeffMap.ECheck.B00
import ThomsonCompact.CoeffMap.ECheck.B01
import ThomsonCompact.CoeffMap.ECheck.B02
import ThomsonCompact.CoeffMap.ECheck.B03
import ThomsonCompact.CoeffMap.ECheck.B04
import ThomsonCompact.CoeffMap.ECheck.B05
import ThomsonCompact.CoeffMap.ECheck.B06
import ThomsonCompact.CoeffMap.ECheck.B07
import ThomsonCompact.CoeffMap.ECheck.B08
import ThomsonCompact.CoeffMap.ECheck.B09
import ThomsonCompact.CoeffMap.ECheck.B10
import ThomsonCompact.CoeffMap.ECheck.B11
import ThomsonCompact.CoeffMap.ECheck.B12
import ThomsonCompact.CoeffMap.ECheck.B13

/-!
# One-time check of the D12 sparse coefficient tables (F2b b): assembly

`eList_eq`: the packed list `D12E.eList b r` is `symEntries` of the integer raw-tensor coefficients
`zG (blockEquiv b) (tagN r)` of the proven `RawMomentTensors.D12_F*` / `RawScalarTensors.D12_*` sources, and
`eDen`/`eSize` are the block denominators/raw dimensions. The checks are one leaf module per block
(`ECheck.B00` … `ECheck.B13`, definitions in `ECheck.Def`); none of them imports `Interface`.
-/

namespace ThomsonCompact.CoeffMap.D12

open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite

theorem checkE_all : ∀ bi : Fin 14, checkE bi = true := by
  intro bi
  fin_cases bi
  exacts [checkE_0, checkE_1, checkE_2, checkE_3, checkE_4, checkE_5, checkE_6, checkE_7, checkE_8,
    checkE_9, checkE_10, checkE_11, checkE_12, checkE_13]

theorem eSize_eq (bi : Fin 14) : D12E.eSize bi = rawDim (blockEquiv bi) := by
  have h := checkE_all bi
  simp only [checkE, Bool.and_eq_true, Nat.beq_eq] at h
  exact h.1.1

theorem eDen_eq (bi : Fin 14) : D12E.eDen bi = blockDen (blockEquiv bi) := by
  have h := checkE_all bi
  simp only [checkE, Bool.and_eq_true, Nat.beq_eq] at h
  exact h.1.2

/-- **The packed tables are the symmetric sparse lists of the proven raw tensors.** -/
theorem eList_eq (bi : Fin 14) (r : Nat) (hr : r < 100) :
    D12E.eList bi r = symEntries (zG (blockEquiv bi) (tagN r)) (rawDim (blockEquiv bi)) := by
  have h := checkE_all bi
  simp only [checkE, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  rw [← eSize_eq bi]
  exact h.2 r hr

#print axioms eList_eq

end ThomsonCompact.CoeffMap.D12
