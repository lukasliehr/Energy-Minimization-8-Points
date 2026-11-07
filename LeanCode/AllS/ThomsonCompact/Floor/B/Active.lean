import ThomsonCompact.Interface.D12
import ThomsonCompact.Floor.B.ActiveG
import ThomsonCompact.Floor.B.TableD12

/-!
# One corrected block of a D12 cell: `Active12'` from the F3b leaves (F3c)

The D12 instance of the degree-generic builder `BlockLeaves.activeT` (`Floor/B/ActiveG.lean`) for the old table
`tab12`: `CellFacts = CellFactsT tab12`, `box_of_height` (D12 anchor) and `BlockLeaves.active : Active12' …`.
-/

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Packed
open ThomsonCompact.Floor (mask slot checkTheta checkTotal zReal)
open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite
open scoped BigOperators

/-! ## The height box -/

theorem box_of_height {N B W : ℕ} (hg : Good N 256 B W) {A : TM} {s : ℝ → ℝ}
    (hA : Encl (mkCtx N 256 B W) A (fun x => aS (s x))) (cb : CellB) (acN rg : ℕ)
    (hok : heightOk (mkCtx N 256 B W) A acN rg = true)
    (hneg : cb.ucNeg = false) (hac : 16 * acN = 19 * 2 ^ 254 + cb.ucN) (hrg : cb.rN = 16 * rg) (hr : 0 < cb.rN) :
    ∀ x ∈ cellDomain, ∃ t ∈ Set.Icc (-1 : ℝ) 1, aS (s x) = a0D12 + σD12 * cb.uf t := by
  intro x hx
  have h1 := heightOk_sound hg hA acN rg hok x hx
  apply box_param cb a0D12 σD12 (aS (s x)) (by unfold σD12; positivity) hr
  rw [hneg]
  simp only [Bool.false_eq_true, if_false]
  have hac' : (cb.ucN : ℝ) = 16 * acN - 19 * 2 ^ 254 := by
    have := congrArg (Nat.cast (R := ℝ)) hac
    push_cast at this
    linarith
  have hrg' : (cb.rN : ℝ) = 16 * rg := by exact_mod_cast hrg
  unfold a0D12 σD12
  rw [hac', hrg']
  have e1 : ((19 : ℕ) : ℝ) / 2 ^ 6 + 1 / 2 ^ 4 * ((16 * (acN : ℝ) - 19 * 2 ^ 254) / 2 ^ 256) =
      (acN : ℝ) / 2 ^ 256 := by
    push_cast
    ring
  have e2 : (1 : ℝ) / 2 ^ 4 * (16 * (rg : ℝ) / 2 ^ 256) = (rg : ℝ) / 2 ^ 256 := by ring
  rw [e1, e2]
  exact h1

/-! ## `Active12'` of one block -/

/-- the per-cell facts shared by the corrected blocks of a D12 cell -/
abbrev CellFacts (s : ℝ → ℝ) (cb : CellB) (row : ℕ → RowT) : Prop := CellFactsT tab12 s cb row

/-- **`Active12'` of a corrected block** from its leaves and the cell facts. -/
noncomputable def BlockLeaves.active {s : ℝ → ℝ} {cb : CellB} {row : ℕ → RowT} {j0 nr n : ℕ}
    (BL : BlockLeaves cb row j0 nr n) (hC : CellFacts s cb row)
    {cell : Literals.Cell} {X : Literals.Block} {name : String}
    {H : Fin cb.nT → QModel cb.N} {q : Fin 100 → Fin cb.nT → ℚ}
    {center : Fin 100 → Fin (cb.N + 1) → ℚ} {err : Fin 100 → ℚ}
    (hcen : ∀ r : Fin 100, ∀ k : Fin (cb.N + 1),
      center r k = (sv (smDec (slot cb.wc (cb.cm r) k)) : ℚ) / 2 ^ BL.Sc)
    (hq : ∀ r : Fin 100, ∀ j : Fin cb.nT, q r j = ((if cb.dirT r = j then sv (cb.dirQ r) else 0 : ℤ) : ℚ) / 3)
    (hH : ∀ j : Fin cb.nT, (H j).error ≤ (cb.herr j : ℚ) / 2 ^ 256)
    (herr : ∀ r : Fin 100, err r ≤ (cb.Er r : ℚ) / 2 ^ 256)
    (hX : X.order = n) (hnr : j0 + nr ≤ 100)
    (hname : ∀ k : Fin 100, (FixedTables.D12.outputCoordinates k).1 = name ↔ (j0 ≤ k.val ∧ k.val < j0 + nr))
    (mb claim E : ℕ) (ex kl : List ℤ) (hex : X.diagonalExponents = ex) (hkl : X.strictLower = kl)
    (hθ : checkTheta n BL.wz cell.metricBits mb BL.zrows ex kl claim = true)
    (hE : cell.floorExponent = -(E : ℤ))
    (hgap : checkTotal ((List.range 1).map fun _ => BL.Gc) BL.Geta (BL.Gc + BL.Geta) claim (32 + mb) E = true) :
    ThomsonCompact.Interface.D12.Active12' s cell X name H q center err :=
  let A := BL.activeT hC (fun a ha j hj => dl12_ne a ha j hj) hcen hq hH herr hX hnr hname mb claim E ex kl hex hkl
    hθ hE hgap
  ⟨A.Z, A.θ, A.γ, A.short_metric, A.gap, A.γc, A.η, A.total, A.centerBound, A.error⟩

end ThomsonCompact.Floor.B
