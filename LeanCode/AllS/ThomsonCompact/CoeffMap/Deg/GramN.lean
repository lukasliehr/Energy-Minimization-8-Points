import ThomsonCompact.CoeffMap.GramPack
import ThomsonCompact.CoeffMap.Deg.Flat

/-!
# Packed W0 entries with narrow Kronecker columns (Init only; F2e)

`CoeffMap.GramPack` packs a whole Gram column at the TM width (`W (N_W + 1)` bits per row), so a block of order `n`
costs `~n³ (N_W+1)² W / 2` bits of kernel terms (1.5 GB for M1_even of cell 23). Here the factor and metric Gram
columns are packed at a narrow width `wn ≈ 2 w_f + 10` (one dot product per row slot):

* `dColB ent wn n q = D_q + 2^(wn-1) · ones` mod `2^(wn n)` with `D_q = Σ_{l ≤ q} x(q, l) C_l` (`CoeffMap.dPack` at
  width `wn`): slot `p` is `dot(p, q) + 2^(wn-1)` (`sgnSlot` decodes `(dot < 0, |dot|)`);
* entry `(p, q)`: `Σ_u dot_u(p, q) · (U⁺_u - U⁻_u) + dotM(p, q) · 2^(S - Lm)` accumulated as `(pos, neg)`
  (`U±_u = uPair`, the Bernstein weights at the TM scale), the window `winN = pos + 2^(W-1) ones - neg` (the biased
  `N_W + 1` slots `czI k p + 2^(W-1)` of `CoeffMap.GramPack`), and `entryN` = `CoeffMap.entryTM` on that window.

`w0OkN`: the D12 block check `w0Ok` (on the flattened data) and the narrow slot bounds. Soundness:
`CoeffMap.Deg.GramNSound` (`WTn_sound`). Bit-exact mirror: `CoeffMap/Deg/gen/mirror.py`.
-/

namespace ThomsonCompact.CoeffMap.Deg

open ThomsonCompact.Packed ThomsonCompact.CoeffMap

/-- Narrow slot width of block `bi`: `2 max(w_f, mxK + 1) + 10`. -/
noncomputable def wnOf (d : CellData) (bi : Nat) : Nat :=
  Nat.add (Nat.mul 2 (Nat.max (d.layout bi).2.1 (Nat.add (mxK d bi) 1))) 10

/-- Biased narrow Gram column `q`: `D_q + 2^(wn-1) · ones` modulo `2^(wn n)`. -/
noncomputable def dColB (ent : Nat → Nat → Bool × Nat) (wn n q : Nat) : Nat :=
  Nat.land (Nat.add (dPack ent wn (Nat.pow 2 (Nat.mul wn n)) n q) (Nat.mul (Nat.shiftLeft 1 (Nat.sub wn 1)) (ones wn n)))
    (Nat.sub (Nat.pow 2 (Nat.mul wn n)) 1)

/-- `(x < 2^(wn-1), |x - 2^(wn-1)|)` of slot `p` of a biased narrow column. -/
def sgnSlot (wn x p : Nat) : Bool × Nat :=
  (fun y => (Nat.blt y (Nat.shiftLeft 1 (Nat.sub wn 1)),
    Nat.add (Nat.sub y (Nat.shiftLeft 1 (Nat.sub wn 1))) (Nat.sub (Nat.shiftLeft 1 (Nat.sub wn 1)) y))) (slotAt wn x p)

/-- Accumulate `±m · (U⁺ - U⁻)` into `(pos, neg)`. -/
def accPM (s : Bool) (m Up Un : Nat) (a : Nat × Nat) : Nat × Nat :=
  cond s (Nat.add a.1 (Nat.mul m Un), Nat.add a.2 (Nat.mul m Up)) (Nat.add a.1 (Nat.mul m Up), Nat.add a.2 (Nat.mul m Un))

/-- The `(pos, neg)` accumulators of entry `(p, q)` of block `bi`. -/
noncomputable def accN (d : CellData) (c : Ctx) (bi p q : Nat) : Nat × Nat :=
  Nat.rec (motive := fun _ => Nat × Nat)
    ((fun sm => cond sm.1 (0, Nat.shiftLeft sm.2 (Nat.sub c.S (scaleM d bi)))
        (Nat.shiftLeft sm.2 (Nat.sub c.S (scaleM d bi)), 0))
      (sgnSlot (wnOf d bi) (dColB (metEnt d bi) (wnOf d bi) (d.order bi) q) p))
    (fun u ih => (fun sm U => accPM sm.1 sm.2 U.1 U.2 ih)
      (sgnSlot (wnOf d bi) (dColB (facEnt d bi u) (wnOf d bi) (d.order bi) q) p)
      (uPair c.W d.nw u (Nat.sub c.S (Nat.add (Nat.mul 2 d.fb) d.nw)))) (Nat.add d.nw 1)

/-- The biased window (`N_W + 1` slots of width `W`) of entry `(p, q)`. -/
noncomputable def winN (d : CellData) (c : Ctx) (bi p q : Nat) : Nat :=
  (fun a => Nat.sub (Nat.add a.1 (Nat.mul c.hW (ones c.W (Nat.add d.nw 1)))) a.2) (accN d c bi p q)

/-- The entry TM from a biased window (as `CoeffMap.entryTM`). -/
noncomputable def entryN (c : Ctx) (M Wv : Nat) (ok0 : Bool) : TM :=
  (fun v => (fun a => (⟨v, a, ssum c a, 0, Nat.blt (ssum c a) c.twoB && ok0⟩ : TM)) (pabs c ⟨v, 0, 0, 0, true⟩))
    (Nat.land (Nat.add Wv (Nat.sub c.twoK (Nat.mul c.hW (ones c.W M)))) c.maskK)

/-- Block check: the D12 `w0Ok` and the narrow slot bounds (`|dot| < 2^(wn-1)` for factor and metric rows). -/
noncomputable def w0OkN (d : CellData) (c : Ctx) (bi : Nat) : Bool :=
  w0Ok d c bi && Nat.ble (d.layout bi).2.1 (wnOf d bi) && Nat.blt (mxK d bi) (wnOf d bi) &&
    Nat.blt (Nat.mul (d.order bi) (Nat.pow 4 (Nat.sub (d.layout bi).2.1 1))) (Nat.shiftLeft 1 (Nat.sub (wnOf d bi) 1)) &&
    Nat.blt (Nat.mul (d.order bi) (Nat.pow 4 (mxK d bi))) (Nat.shiftLeft 1 (Nat.sub (wnOf d bi) 1))

/-- Column `q` of entry TMs `[(0,q), …, (q,q)]`. -/
noncomputable def wColN (d : CellData) (c : Ctx) (bi q : Nat) : List TM :=
  (fun ok0 => mkList (fun p => entryN c (Nat.add d.nw 1) (winN d c bi p q) ok0) (Nat.add q 1)) (w0OkN d c bi)

/-- All entry TMs of block `bi`, column by column (each evaluated once by the kernel). -/
noncomputable def wTabN (d : CellData) (c : Ctx) (bi : Nat) : List (List TM) :=
  mkList (fun q => wColN d c bi q) (d.order bi)

/-- Packed W0 TMs of block `bi` on `ℕ` indices (symmetric; zero outside the block). -/
noncomputable def WTn (d : CellData) (c : Ctx) (bi i j : Nat) : TM :=
  cond (Nat.ble i j) (listAt zeroTM (listAt [] (wTabN d c bi) j) i) (listAt zeroTM (listAt [] (wTabN d c bi) i) j)

end ThomsonCompact.CoeffMap.Deg
