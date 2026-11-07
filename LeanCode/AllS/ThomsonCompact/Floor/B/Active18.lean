import ThomsonCompact.Interface.D18
import ThomsonCompact.Floor.B.ActiveQ
import ThomsonCompact.Floor.B.TableD18

/-!
# One corrected block of a D18 cell: `Active18'` from the F3b leaves (F3d; column-split block leaves: F3f)

The D18 instance of the degree-generic builder `BlockLeaves.activeT` (`Floor/B/ActiveG.lean`) for the table
`tab18` (`Floor/B/TableD18.lean`).
-/

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Packed
open ThomsonCompact.Floor (mask slot checkTheta checkTotal zReal)
open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite
open scoped BigOperators

/-- **`Active18'` of a corrected block** from its leaves and the cell facts. -/
noncomputable def BlockLeaves.active18 {s : ℝ → ℝ} {cb : CellB} {row : ℕ → RowT} {j0 nr n : ℕ}
    (BL : BlockLeaves cb row j0 nr n) (hC : CellFactsT tab18 s cb row)
    {cell : Literals.Cell} {X : Literals.Block} {name : String}
    {H : Fin cb.nT → QModel cb.N} {q : Fin 272 → Fin cb.nT → ℚ}
    {center : Fin 272 → Fin (cb.N + 1) → ℚ} {err : Fin 272 → ℚ}
    (hcen : ∀ r : Fin 272, ∀ k : Fin (cb.N + 1),
      center r k = (sv (smDec (slot cb.wc (cb.cm r) k)) : ℚ) / 2 ^ BL.Sc)
    (hq : ∀ r : Fin 272, ∀ j : Fin cb.nT, q r j = ((if cb.dirT r = j then sv (cb.dirQ r) else 0 : ℤ) : ℚ) / 3)
    (hH : ∀ j : Fin cb.nT, (H j).error ≤ (cb.herr j : ℚ) / 2 ^ 256)
    (herr : ∀ r : Fin 272, err r ≤ (cb.Er r : ℚ) / 2 ^ 256)
    (hX : X.order = n) (hnr : j0 + nr ≤ 272)
    (hname : ∀ k : Fin 272, (Blueprint.CAP.FixedTables.D18.outputCoordinates k).1 = name ↔ (j0 ≤ k.val ∧ k.val < j0 + nr))
    (mb claim E : ℕ) (ex kl : List ℤ) (hex : X.diagonalExponents = ex) (hkl : X.strictLower = kl)
    (hθ : checkTheta n BL.wz cell.metricBits mb BL.zrows ex kl claim = true)
    (hE : cell.floorExponent = -(E : ℤ))
    (hgap : checkTotal ((List.range 1).map fun _ => BL.Gc) BL.Geta (BL.Gc + BL.Geta) claim (32 + mb) E = true) :
    ThomsonCompact.Interface.D18.Active18' s cell X name H q center err :=
  let A := BL.activeT hC (fun a ha j hj => dl18_ne a ha j hj) hcen hq hH herr hX hnr hname mb claim E ex kl hex hkl hθ hE hgap
  ⟨A.Z, A.θ, A.γ, A.short_metric, A.gap, A.γc, A.η, A.total, A.centerBound, A.error⟩

/-- **`Active18'` of a corrected block** from its leaves (plain or column-split block leaves) and the cell facts. -/
noncomputable def BlockLeavesQ.active18 {s : ℝ → ℝ} {cb : CellB} {row : ℕ → RowT} {j0 nr n : ℕ}
    (BL : BlockLeavesQ cb row j0 nr n) (hC : CellFactsT tab18 s cb row)
    {cell : Literals.Cell} {X : Literals.Block} {name : String}
    {H : Fin cb.nT → QModel cb.N} {q : Fin 272 → Fin cb.nT → ℚ}
    {center : Fin 272 → Fin (cb.N + 1) → ℚ} {err : Fin 272 → ℚ}
    (hcen : ∀ r : Fin 272, ∀ k : Fin (cb.N + 1),
      center r k = (sv (smDec (slot cb.wc (cb.cm r) k)) : ℚ) / 2 ^ BL.Sc)
    (hq : ∀ r : Fin 272, ∀ j : Fin cb.nT, q r j = ((if cb.dirT r = j then sv (cb.dirQ r) else 0 : ℤ) : ℚ) / 3)
    (hH : ∀ j : Fin cb.nT, (H j).error ≤ (cb.herr j : ℚ) / 2 ^ 256)
    (herr : ∀ r : Fin 272, err r ≤ (cb.Er r : ℚ) / 2 ^ 256)
    (hX : X.order = n) (hnr : j0 + nr ≤ 272)
    (hname : ∀ k : Fin 272, (Blueprint.CAP.FixedTables.D18.outputCoordinates k).1 = name ↔ (j0 ≤ k.val ∧ k.val < j0 + nr))
    (mb claim E : ℕ) (ex kl : List ℤ) (hex : X.diagonalExponents = ex) (hkl : X.strictLower = kl)
    (hθ : checkTheta n BL.wz cell.metricBits mb BL.zrows ex kl claim = true)
    (hE : cell.floorExponent = -(E : ℤ))
    (hgap : checkTotal ((List.range 1).map fun _ => BL.Gc) BL.Geta (BL.Gc + BL.Geta) claim (32 + mb) E = true) :
    ThomsonCompact.Interface.D18.Active18' s cell X name H q center err :=
  let A := BL.activeT hC (fun a ha j hj => dl18_ne a ha j hj) hcen hq hH herr hX hnr hname mb claim E ex kl hex hkl hθ hE hgap
  ⟨A.Z, A.θ, A.γ, A.short_metric, A.gap, A.γc, A.η, A.total, A.centerBound, A.error⟩

end ThomsonCompact.Floor.B
