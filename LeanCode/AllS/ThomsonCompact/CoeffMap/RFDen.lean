import ThomsonCompact.CoeffMap.RFD12

/-!
# Shared denominators of the D12 RF records (Init only)

`denIdx k`, `denPoly d`, `denScale d`; `denTableOk` (Bool checker, proved in `ColumnSupport`).
-/

namespace ThomsonCompact.CoeffMap.D12RF

/-- Shared-denominator index of record `k`. -/
noncomputable def denIdx (k : Nat) : Nat := (numOfSlots (tableSlots recChunk 26 18 34 k)).2.2

/-- Denominator polynomial `d` (integer coefficients) and its scale. -/
noncomputable def denPoly (d : Nat) : List Int := (denOfSlots (tableSlots denChunk 26 12 50 d)).1
noncomputable def denScale (d : Nat) : Nat := (denOfSlots (tableSlots denChunk 26 12 50 d)).2

/-- Bool checker: records `0 … n-1` point to one of the `nDen` denominators, with nonzero scale. -/
noncomputable def denTableOk : Nat → Bool
  | 0 => true
  | k + 1 => denTableOk k && Nat.blt (denIdx k) nDen && Nat.blt 0 (denScale (denIdx k))

end ThomsonCompact.CoeffMap.D12RF
