import ThomsonCompact.Floor.B.SoundBridgeOld
import ThomsonCompact.Floor.B.TabSpec
import AllS.Units.N_AI.N_fixed_tables.D18.OperatorDefinitions

/-!
# The old D18 inverse table in the form of the F3b row theorems (F3d)

* `Hd18 j m a`, `dl18 j a`: numerator entries and row denominators of `FixedTables.D18.inverseMatrix`
  (`inverseMatrix_eq`; `dl18_ne` on physical heights);
* `tab18`: the D18 table as a `TabSpec` (anchor `a0 = 1083/2^12`, `σ = 2^-10`); `RowFacts j r = RowFactsT tab18 j r`
  (`RowSem` at the anchor, `u_D = 1/2`, entries off `r.msL` vanish, the old output coordinate);
* `rowFacts_of`: `RowFacts` from the bridge leaf (`rowBridgeOk`, old entries), the denominator leaf (`denOk`) and
  the old denominator/scale/coordinate literals.
-/

namespace ThomsonCompact.Floor.B
open Blueprint.CAP ThomsonCompact.Packed

/-- numerator entry `(j, m)` of the old D18 inverse table -/
noncomputable def Hd18 (j m : ℕ) (a : ℝ) : ℝ :=
  if h : j < 272 ∧ m < 272 then evalIntegerList (FixedTables.D18.H ⟨j, h.1⟩ ⟨m, h.2⟩) a else 0

/-- row denominator `λ_j d_j(a)` of the old D18 inverse table -/
noncomputable def dl18 (j : ℕ) (a : ℝ) : ℝ :=
  if h : j < 272 then (FixedTables.D18.tableScales ⟨j, h⟩ : ℝ) *
    evalRationalList (FixedTables.D18.tableDenominators ⟨j, h⟩) a else 1

theorem inverseMatrix_eq18 (a : ℝ) (j m : Fin 272) :
    FixedTables.D18.inverseMatrix a j m = Hd18 j m a / dl18 j a := by
  simp only [FixedTables.D18.inverseMatrix, Hd18, dl18, dif_pos (And.intro j.isLt m.isLt), dif_pos j.isLt]

theorem dl18_ne (a : ℝ) (ha : Blueprint.Thomson.Finite.physical a) (j : ℕ) (hj : j < 272) : dl18 j a ≠ 0 := by
  simp only [dl18, dif_pos hj]
  exact FixedTables.D18.inverseMatrix_denominator_nonzero a ha ⟨j, hj⟩

/-- the D18 table in the form of the F3b row theorems (anchor `1083/2^12`, `σ = 2^-10`) -/
noncomputable def tab18 : TabSpec 272 where
  inv := FixedTables.D18.inverseMatrix
  coords := FixedTables.D18.outputCoordinates
  Hd := Hd18
  dl := dl18
  inv_eq := inverseMatrix_eq18
  p := 1083
  q := 12
  g := 10

/-- what the one-time D18 leaves give for row `j` -/
abbrev RowFacts18 (j : ℕ) (r : RowT) : Prop := RowFactsT tab18 j r

/-- **`RowFacts` of a row** from its bridge leaf, its denominator leaf and the old literals. -/
theorem rowFacts18_of (j : ℕ) (hj : j < 272) (r : RowT) (hrow : Fin 272 → List ℤ) (W Wd lam dq : ℕ) (dz : List ℤ)
    (hW : 2 ≤ W) (hWd : 2 ≤ Wd)
    (hb : rowBridgeOk 272 1083 12 10 W 1 r (fun m => if h : m < 272 then hrow ⟨m, h⟩ else []) = true)
    (hd : denOk 1083 12 10 Wd r lam dq dz = true)
    (hH : ∀ m : Fin 272, FixedTables.D18.H ⟨j, hj⟩ m = hrow m)
    (hden : FixedTables.D18.tableDenominators ⟨j, hj⟩ = dz.map (fun z : ℤ => (z : ℚ) / (dq : ℚ)))
    (hlam : FixedTables.D18.tableScales ⟨j, hj⟩ = (lam : ℤ)) {name : String}
    (hout : FixedTables.D18.outputCoordinates ⟨j, hj⟩ = (name, r.u, r.v)) :
    RowFacts18 j r := by
  refine rowFactsT_of tab18 (by decide) j hj r _ W Wd lam dq dz hW hWd hb hd ?_ ?_ ?_
  · intro m hm a
    show Hd18 j m a = _
    simp only [Hd18, dif_pos (And.intro hj hm), hH, evalIntegerList_eq_evalZ, dif_pos hm]
  · intro a
    show dl18 j a = _
    simp only [dl18, dif_pos hj, hden, hlam, evalRationalList_div']
    push_cast
    ring
  · show (FixedTables.D18.outputCoordinates ⟨j, hj⟩).2 = _
    rw [hout]

end ThomsonCompact.Floor.B
