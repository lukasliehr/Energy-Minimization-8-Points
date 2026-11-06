import ThomsonCompact.Floor.B.Active14
import ThomsonCompact.Floor.B.ActiveXG

/-!
# Two-piece corrected blocks of a D14 cell (F3g)

`BlockLeavesQ.active14X`: `Active14'` of a block from its two x-halves (`BlockLeavesQ.activeTX` for `tab14`, as
`ActiveX12.active12X` for D12); `box_of_piece14`: the box of a half from its height leaf (`pieceHeight`) at the D14
anchor `35/2^7`, `σ = 2^-6` (generic helpers `half_memX`, `hcen_of_reexps`: `ActiveXG.lean`).
-/

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Packed
open ThomsonCompact.Floor (mask slot checkTheta checkTotal zReal)
open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite
open scoped BigOperators

/-- the box of a half from its height leaf (`pieceHeight` of the cell's height TM), D14 anchor -/
theorem box_of_piece14 {N B W : ℕ} (hg : Good N 256 B W) {A : TM} {s : ℝ → ℝ}
    (hA : Encl (mkCtx N 256 B W) A (fun x => aS (s x))) (neg : Bool) (hN : 1 ≤ N) (cb : CellB) (acN rg : ℕ)
    (hok : ((halfU (mkCtx N 256 B W) neg).ok && ((pieceHeight (mkCtx N 256 B W) A neg).ok &&
      heightOk (mkCtx N 256 B W) (pieceHeight (mkCtx N 256 B W) A neg) acN rg)) = true)
    (hac : (2 : ℤ) ^ 6 * acN = ((35 : ℕ) : ℤ) * 2 ^ (256 - 7 + 6) +
      (if cb.ucNeg then -(cb.ucN : ℤ) else cb.ucN))
    (hrg : cb.rN = 2 ^ 6 * rg) (hr : 0 < cb.rN) :
    ∀ y ∈ cellDomain, ∃ t ∈ Set.Icc (-1 : ℝ) 1, aS (s ((y + sgnH neg) / 2)) = tab14.a0 + tab14.σ * cb.uf t := by
  simp only [Bool.and_eq_true] at hok
  obtain ⟨hU, hP, hH⟩ := hok
  have hA' := pieceHeight_sound hg hA neg hN (by norm_num) hU hP
  intro y hy
  obtain ⟨t, ht, h⟩ := box_of_heightG hg hA' cb acN rg hH 35 7 6 (by norm_num) hac hrg hr y hy
  exact ⟨t, ht, h⟩

/-- **`Active14'` of a corrected block from its two x-halves.** -/
noncomputable def BlockLeavesQ.active14X {s : ℝ → ℝ} {cbL cbR : CellB} {row : ℕ → RowT} {j0 nr n : ℕ}
    (BL : BlockLeavesQ cbL row j0 nr n) (BR : BlockLeavesQ cbR row j0 nr n)
    (hCL : CellFactsT tab14 (fun y => s ((y + sgnH true) / 2)) cbL row)
    (hCR : CellFactsT tab14 (fun y => s ((y + sgnH false) / 2)) cbR row)
    {cell : Literals.Cell} {X : Literals.Block} {name : String}
    {N t : ℕ} {H : Fin t → QModel N} {q : Fin 145 → Fin t → ℚ}
    {center : Fin 145 → Fin (N + 1) → ℚ} {err : Fin 145 → ℚ}
    (hcenL : ∀ r : Fin 145, ∀ y : ℝ, scalarEval (fun k => (center r k : ℝ)) ((y + sgnH true) / 2) =
      scalarEval (fun k => (pieceCenter cbL BL.Sc r k : ℝ)) y)
    (hcenR : ∀ r : Fin 145, ∀ y : ℝ, scalarEval (fun k => (center r k : ℝ)) ((y + sgnH false) / 2) =
      scalarEval (fun k => (pieceCenter cbR BR.Sc r k : ℝ)) y)
    (htL : cbL.nT = t) (htR : cbR.nT = t)
    (hqL : ∀ r : Fin 145, ∀ j : Fin t, q r j = ((if cbL.dirT r = j then sv (cbL.dirQ r) else 0 : ℤ) : ℚ) / 3)
    (hqR : ∀ r : Fin 145, ∀ j : Fin t, q r j = ((if cbR.dirT r = j then sv (cbR.dirQ r) else 0 : ℤ) : ℚ) / 3)
    (hHL : ∀ j : Fin t, (H j).error ≤ (cbL.herr j : ℚ) / 2 ^ 256)
    (hHR : ∀ j : Fin t, (H j).error ≤ (cbR.herr j : ℚ) / 2 ^ 256)
    (herrL : ∀ r : Fin 145, err r ≤ (cbL.Er r : ℚ) / 2 ^ 256)
    (herrR : ∀ r : Fin 145, err r ≤ (cbR.Er r : ℚ) / 2 ^ 256)
    (hX : X.order = n) (hnr : j0 + nr ≤ 145)
    (hname : ∀ k : Fin 145, (ThomsonCompact.FixedD14.outputCoordinates k).1 = name ↔ (j0 ≤ k.val ∧ k.val < j0 + nr))
    (hwz : BR.wz = BL.wz) (hzr : BR.zrows = BL.zrows)
    (mb claim E : ℕ) (ex kl : List ℤ) (hex : X.diagonalExponents = ex) (hkl : X.strictLower = kl)
    (hθ : checkTheta n BL.wz cell.metricBits mb BL.zrows ex kl claim = true)
    (hE : cell.floorExponent = -(E : ℤ))
    (hgap : checkTotal ((List.range 1).map fun _ => Nat.max BL.Gc BR.Gc) (Nat.max BL.Geta BR.Geta)
      (Nat.max BL.Gc BR.Gc + Nat.max BL.Geta BR.Geta) claim (32 + mb) E = true) :
    ThomsonCompact.Interface.D14.Active14' s cell X name H q center err :=
  let A := BL.activeTX BR hCL hCR dl14_ne hcenL hcenR htL htR hqL hqR hHL hHR herrL herrR hX hnr hname hwz hzr mb
    claim E ex kl hex hkl hθ hE hgap
  ⟨A.Z, A.θ, A.γ, A.short_metric, A.gap, A.γc, A.η, A.total, A.centerBound, A.error⟩

end ThomsonCompact.Floor.B
