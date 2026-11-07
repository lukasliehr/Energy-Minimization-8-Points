import ThomsonCompact.Floor.B.SoundBridgeOld
import ThomsonCompact.Floor.B.TabSpec
import AllS.Units.N_AI.N_fixed_tables.D12.OperatorDefinitions

/-!
# The old D12 inverse table in the form of the F3b row theorems (F3c)

* `Hd12 j m a`, `dl12 j a`: numerator entries and row denominators of `FixedTables.D12.inverseMatrix`
  (`inverseMatrix_eq`; `dl12_ne` on physical heights);
* `tab12`: the D12 table as a `TabSpec` (anchor `a0 = 19/2^6`, `σ = 2^-4`); `RowFacts j r = RowFactsT tab12 j r`
  (`RowSem` at the anchor, `u_D = 1/2`, entries off `r.msL` vanish, the old output coordinate);
* `rowFacts_of`: `RowFacts` from the bridge leaf (`rowBridgeOk`, old entries), the denominator leaf (`denOk`) and
  the old denominator/scale/coordinate literals.
-/

namespace ThomsonCompact.Floor.B
open Blueprint.CAP ThomsonCompact.Packed

/-- numerator entry `(j, m)` of the old D12 inverse table -/
noncomputable def Hd12 (j m : ℕ) (a : ℝ) : ℝ :=
  if h : j < 100 ∧ m < 100 then evalIntegerList (FixedTables.D12.H ⟨j, h.1⟩ ⟨m, h.2⟩) a else 0

/-- row denominator `λ_j d_j(a)` of the old D12 inverse table -/
noncomputable def dl12 (j : ℕ) (a : ℝ) : ℝ :=
  if h : j < 100 then (FixedTables.D12.tableScales ⟨j, h⟩ : ℝ) *
    evalRationalList (FixedTables.D12.tableDenominators ⟨j, h⟩) a else 1

theorem inverseMatrix_eq (a : ℝ) (j m : Fin 100) :
    FixedTables.D12.inverseMatrix a j m = Hd12 j m a / dl12 j a := by
  simp only [FixedTables.D12.inverseMatrix, Hd12, dl12, dif_pos (And.intro j.isLt m.isLt), dif_pos j.isLt]

theorem dl12_ne (a : ℝ) (ha : Blueprint.Thomson.Finite.physical a) (j : ℕ) (hj : j < 100) : dl12 j a ≠ 0 := by
  simp only [dl12, dif_pos hj]
  exact FixedTables.D12.inverseMatrix_denominator_nonzero a ha ⟨j, hj⟩

/-- the D12 anchor `a0 = 19/2^6` -/
noncomputable def a0D12 : ℝ := ((19 : ℕ) : ℝ) / 2 ^ 6

/-- the D12 scale `σ = 2^-4` -/
noncomputable def σD12 : ℝ := 1 / 2 ^ 4

/-- the D12 table in the form of the F3b row theorems (anchor `19/2^6`, `σ = 2^-4`) -/
noncomputable def tab12 : TabSpec 100 where
  inv := FixedTables.D12.inverseMatrix
  coords := FixedTables.D12.outputCoordinates
  Hd := Hd12
  dl := dl12
  inv_eq := inverseMatrix_eq
  p := 19
  q := 6
  g := 4

/-- what the one-time D12 leaves give for row `j` -/
abbrev RowFacts (j : ℕ) (r : RowT) : Prop := RowFactsT tab12 j r

/-- **`RowFacts` of a row** from its bridge leaf, its denominator leaf and the old literals. -/
theorem rowFacts_of (j : ℕ) (hj : j < 100) (r : RowT) (hrow : Fin 100 → List ℤ) (W Wd lam dq : ℕ) (dz : List ℤ)
    (hW : 2 ≤ W) (hWd : 2 ≤ Wd)
    (hb : rowBridgeOk 100 19 6 4 W 1 r (fun m => if h : m < 100 then hrow ⟨m, h⟩ else []) = true)
    (hd : denOk 19 6 4 Wd r lam dq dz = true)
    (hH : ∀ m : Fin 100, FixedTables.D12.H ⟨j, hj⟩ m = hrow m)
    (hden : FixedTables.D12.tableDenominators ⟨j, hj⟩ = dz.map (fun z : ℤ => (z : ℚ) / (dq : ℚ)))
    (hlam : FixedTables.D12.tableScales ⟨j, hj⟩ = (lam : ℤ)) {name : String}
    (hout : FixedTables.D12.outputCoordinates ⟨j, hj⟩ = (name, r.u, r.v)) :
    RowFacts j r := by
  refine rowFactsT_of tab12 (by decide) j hj r _ W Wd lam dq dz hW hWd hb hd ?_ ?_ ?_
  · intro m hm a
    show Hd12 j m a = _
    simp only [Hd12, dif_pos (And.intro hj hm), hH, evalIntegerList_eq_evalZ, dif_pos hm]
  · intro a
    show dl12 j a = _
    simp only [dl12, dif_pos hj, hden, hlam, evalRationalList_div']
    push_cast
    ring
  · show (FixedTables.D12.outputCoordinates ⟨j, hj⟩).2 = _
    rw [hout]

end ThomsonCompact.Floor.B
