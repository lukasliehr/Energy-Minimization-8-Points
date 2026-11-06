import ThomsonCompact.Floor.B.Active
import ThomsonCompact.Floor.B.ActiveX

/-!
# Two-piece corrected blocks of a D12 cell (F3f)

`BlockLeavesQ.active12X`: `Active12'` of a block from its two x-halves (`BlockLeavesQ.activeTX` for `tab12`);
`hcen_of_reexp`: the centre hypothesis of a half from its re-expansion leaf; `half_mem`: the halves map
`[-1,1]` into `[-1,1]`.
-/

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Packed
open ThomsonCompact.Floor (mask slot checkTheta checkTotal zReal)
open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite
open scoped BigOperators

theorem half_mem (neg : Bool) {y : ℝ} (hy : y ∈ cellDomain) : (y + sgnH neg) / 2 ∈ cellDomain := by
  obtain ⟨h1, h2⟩ := hy
  unfold sgnH; cases neg <;> simp <;> constructor <;> linarith

/-- the centre hypothesis of a half (all `nI` coordinates in one re-expansion leaf) -/
theorem hcen_of_reexp {N wc wcP : ℕ} {neg : Bool} {cm cmP : ℕ → ℕ} {nI : ℕ}
    (h : reexpOk N wc wcP neg cm cmP 0 nI = true) (Sc : ℕ) (r : Fin nI) (y : ℝ) :
    scalarEval (fun k : Fin (N + 1) => (((sv (smDec (slot wc (cm r) k)) : ℚ) / 2 ^ Sc : ℚ) : ℝ))
        ((y + sgnH neg) / 2) =
      scalarEval (fun k : Fin (N + 1) => (((sv (smDec (slot wcP (cmP r) k)) : ℚ) / 2 ^ (Sc + N) : ℚ) : ℝ)) y := by
  have := reexpOk_sound h Sc r.val r.isLt y
  simp only [Nat.zero_add] at this
  push_cast
  exact this

/-- the box of a half from its height leaf (`pieceHeight` of the cell's height TM) -/
theorem box_of_piece12 {N B W : ℕ} (hg : Good N 256 B W) {A : TM} {s : ℝ → ℝ}
    (hA : Encl (mkCtx N 256 B W) A (fun x => aS (s x))) (neg : Bool) (hN : 1 ≤ N) (cb : CellB) (acN rg : ℕ)
    (hok : ((halfU (mkCtx N 256 B W) neg).ok && ((pieceHeight (mkCtx N 256 B W) A neg).ok &&
      heightOk (mkCtx N 256 B W) (pieceHeight (mkCtx N 256 B W) A neg) acN rg)) = true)
    (hac : (2 : ℤ) ^ 4 * acN = ((19 : ℕ) : ℤ) * 2 ^ (256 - 6 + 4) +
      (if cb.ucNeg then -(cb.ucN : ℤ) else cb.ucN))
    (hrg : cb.rN = 2 ^ 4 * rg) (hr : 0 < cb.rN) :
    ∀ y ∈ cellDomain, ∃ t ∈ Set.Icc (-1 : ℝ) 1, aS (s ((y + sgnH neg) / 2)) = a0D12 + σD12 * cb.uf t := by
  simp only [Bool.and_eq_true] at hok
  obtain ⟨hU, hP, hH⟩ := hok
  have hA' := pieceHeight_sound hg hA neg hN (by norm_num) hU hP
  exact box_of_heightG hg hA' cb acN rg hH 19 6 4 (by norm_num) hac hrg hr

/-- **`Active12'` of a corrected block from its two x-halves.** -/
noncomputable def BlockLeavesQ.active12X {s : ℝ → ℝ} {cbL cbR : CellB} {row : ℕ → RowT} {j0 nr n : ℕ}
    (BL : BlockLeavesQ cbL row j0 nr n) (BR : BlockLeavesQ cbR row j0 nr n)
    (hCL : CellFacts (fun y => s ((y + sgnH true) / 2)) cbL row)
    (hCR : CellFacts (fun y => s ((y + sgnH false) / 2)) cbR row)
    {cell : Literals.Cell} {X : Literals.Block} {name : String}
    {N t : ℕ} {H : Fin t → QModel N} {q : Fin 100 → Fin t → ℚ}
    {center : Fin 100 → Fin (N + 1) → ℚ} {err : Fin 100 → ℚ}
    (hcenL : ∀ r : Fin 100, ∀ y : ℝ, scalarEval (fun k => (center r k : ℝ)) ((y + sgnH true) / 2) =
      scalarEval (fun k => (pieceCenter cbL BL.Sc r k : ℝ)) y)
    (hcenR : ∀ r : Fin 100, ∀ y : ℝ, scalarEval (fun k => (center r k : ℝ)) ((y + sgnH false) / 2) =
      scalarEval (fun k => (pieceCenter cbR BR.Sc r k : ℝ)) y)
    (htL : cbL.nT = t) (htR : cbR.nT = t)
    (hqL : ∀ r : Fin 100, ∀ j : Fin t, q r j = ((if cbL.dirT r = j then sv (cbL.dirQ r) else 0 : ℤ) : ℚ) / 3)
    (hqR : ∀ r : Fin 100, ∀ j : Fin t, q r j = ((if cbR.dirT r = j then sv (cbR.dirQ r) else 0 : ℤ) : ℚ) / 3)
    (hHL : ∀ j : Fin t, (H j).error ≤ (cbL.herr j : ℚ) / 2 ^ 256)
    (hHR : ∀ j : Fin t, (H j).error ≤ (cbR.herr j : ℚ) / 2 ^ 256)
    (herrL : ∀ r : Fin 100, err r ≤ (cbL.Er r : ℚ) / 2 ^ 256)
    (herrR : ∀ r : Fin 100, err r ≤ (cbR.Er r : ℚ) / 2 ^ 256)
    (hX : X.order = n) (hnr : j0 + nr ≤ 100)
    (hname : ∀ k : Fin 100, (FixedTables.D12.outputCoordinates k).1 = name ↔ (j0 ≤ k.val ∧ k.val < j0 + nr))
    (hwz : BR.wz = BL.wz) (hzr : BR.zrows = BL.zrows)
    (mb claim E : ℕ) (ex kl : List ℤ) (hex : X.diagonalExponents = ex) (hkl : X.strictLower = kl)
    (hθ : checkTheta n BL.wz cell.metricBits mb BL.zrows ex kl claim = true)
    (hE : cell.floorExponent = -(E : ℤ))
    (hgap : checkTotal ((List.range 1).map fun _ => Nat.max BL.Gc BR.Gc) (Nat.max BL.Geta BR.Geta)
      (Nat.max BL.Gc BR.Gc + Nat.max BL.Geta BR.Geta) claim (32 + mb) E = true) :
    ThomsonCompact.Interface.D12.Active12' s cell X name H q center err :=
  let A := BL.activeTX BR hCL hCR (fun a ha j hj => dl12_ne a ha j hj) hcenL hcenR htL htR hqL hqR hHL hHR herrL
    herrR hX hnr hname hwz hzr mb claim E ex kl hex hkl hθ hE hgap
  ⟨A.Z, A.θ, A.γ, A.short_metric, A.gap, A.γc, A.η, A.total, A.centerBound, A.error⟩

end ThomsonCompact.Floor.B
