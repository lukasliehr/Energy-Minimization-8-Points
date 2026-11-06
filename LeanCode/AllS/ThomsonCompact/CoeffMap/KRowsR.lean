import ThomsonCompact.CoeffMap.BProg

/-!
# Precise column-matrix rows (Init only; F2d)

The RF records and the moment pivot ratios are quotients `p(A)/q(A)` whose denominators are small on some cells
(`|q| ≈ 2^-19` for M1_even): `p(A) · (1/q)(A)` (the `recTMz`/`rhoTM` rows) carries the Taylor tail and the magnitude
bound of `1/q` (`2^19`) into every product, giving piece errors up to `2^-27`. Here every entry is computed by F1's
residual-lemma division `divR` (quotient refreshed, error `‖p - q Q‖ · ‖1/q‖`, no truncation of `1/q`) with the
shared inverse as the enclosure of `1/q`, and refreshed (exact magnitudes) before it enters the contraction. Piece
errors drop to `≤ 2^-59` on cell 4 (sums `≤ 2^-57.6`). Soundness: `CoeffMap.KRowsRSound`.
-/

namespace ThomsonCompact.CoeffMap

open ThomsonCompact.Packed

/-- Shared inverse of denominator `d` at `A` (table entry for `d < nDen`). -/
noncomputable def denInvAt (c : Ctx) (A : TM) (d : Nat) : TM :=
  cond (Nat.blt d D12RF.nDen) (listAt zeroTM (denInvTab c A) d) (invN c 8 0 (hornerQ c A (denQ d)))

/-- Record `k` at `A`: `refresh (divR num den (1/den))`. -/
noncomputable def recTMr (c : Ctx) (A : TM) (k : Nat) : TM :=
  refresh c (divR c (hornerQ c A (numQN k)) (hornerQ c A (denQ (D12RF.denIdx k))) (denInvAt c A (D12RF.denIdx k)))

/-- `scalarRowz` with the precise records. -/
noncomputable def scalarRowr (c : Ctx) (A : TM) (bi d u : Nat) : List (Nat × Option TM) :=
  ((List.range d).filter fun i => !(Nat.beq (D12RF.colRec bi i u) 1)).map fun i =>
    (i, if Nat.beq (D12RF.colRec bi i u) 0 then none else some (recTMr c A (D12RF.colRec bi i u)))

/-- `-momentP k (succAbove p i) / momentP k p` at the height TM by the residual lemma. -/
noncomputable def rhoTMr (c : Ctx) (A : TM) (k p i : Nat) : TM :=
  refresh c (neg c (divR c (hornerQ c A (momQ k (sA p i))) (hornerQ c A (momQ k p))
    (invN c 8 0 (hornerQ c A (momQ k p)))))

/-- `momentRow` with the precise pivot ratios. -/
noncomputable def momentRowr (c : Ctx) (A : TM) (k p d r : Nat) : List (Nat × Option TM) :=
  if r = p then (List.range d).map fun i => (i, some (rhoTMr c A k p i))
  else [(if r < p then r else r - 1, none)]

/-- Rows of block `bi` with the precise entries. -/
noncomputable def blockRowr (c : Ctx) (A : TM) (bi : Nat) : Nat → List (Nat × Option TM) :=
  if bi < 6 then momentRowr c A bi (pivN bi) (6 - bi) else scalarRowr c A (bi - 6) (sDimN (bi - 6))

/-- Piece `g` of block `bi` at coordinate `r` with the precise rows (`blockTMg` otherwise). -/
noncomputable def blockTMgr (c : Ctx) (A : TM) (WT : Nat → Nat → TM) (bi g r : Nat) : TM :=
  gTMz c WT (blockRowr c A bi) (gDimN bi) (D12E.eSize bi) (listAt [] (eTabG (Nat.add (Nat.mul 8 bi) g)) r)
    (D12E.eDen bi)

end ThomsonCompact.CoeffMap
