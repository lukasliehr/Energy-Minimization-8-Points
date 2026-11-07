import ThomsonCompact.CoeffMap.Deg.GramN

/-!
# Row-oriented narrow W0 entries (Init only; F2g)

Variant of `CoeffMap.Deg.GramN` for the large D16/D18 blocks, where every leaf that touches the W0 entries pays for them:

* factor entries are read row by row (`facRowR`: one shift of the flattened field per row, then slots of the short row;
  `GramN` shifts the whole field once per entry, which costs memory for fields of 100+ kbit);
* entry `(i, j)` is read from the narrow column `i` at slot `j` (`WTr`, row-oriented): a leaf that needs the rows `i ∈ I`
  of `W` computes only the columns `i ∈ I` (and the factor columns `l ≤ max I`);
* the accumulation uses the **biased** slots directly (`accR`: `pos += y_u U⁺_u`, `neg += y_u U⁻_u`, `y_u = dot_u +
  2^(wn-1)`), and the bias is removed once by per-block constants (`winR`); no sign decode per slot.

The window `winR d c bi j i` is the window of the D12 packed column (`CoeffMap.Deg.GramRSound.winR_window`), so the entry
TM is the D12 `entryTM` and `CoeffMap.entryTM_sound` applies (`WTr_sound`).
-/

namespace ThomsonCompact.CoeffMap.Deg

open ThomsonCompact.Packed ThomsonCompact.CoeffMap

/-- Row `p` of factor `u` of block `bi`: the slots `tri p … tri p + p` of the (single-numeral) field. -/
def facRowR (d : CellData) (bi u p : Nat) : Nat :=
  Nat.land (Nat.shiftRight (d.fac bi u 0) (Nat.mul (d.layout bi).2.1 (tri p)))
    (Nat.sub (Nat.shiftLeft 1 (Nat.mul (d.layout bi).2.1 (Nat.add p 1))) 1)

/-- Entry `(p, l)` (`l ≤ p`) of factor `u` of block `bi`, read from its row. -/
def facEntR (d : CellData) (bi u p l : Nat) : Bool × Nat :=
  smSlot (slotAt (d.layout bi).2.1 (facRowR d bi u p) l)

/-- `(Σ_u U⁺_u, Σ_u U⁻_u)` over the Bernstein factors `u < k`. -/
noncomputable def uSum (c : Ctx) (d : CellData) (k : Nat) : Nat × Nat :=
  Nat.rec (motive := fun _ => Nat × Nat) (0, 0)
    (fun u ih => (fun U => (Nat.add ih.1 U.1, Nat.add ih.2 U.2))
      (uPair c.W d.nw u (Nat.sub c.S (Nat.add (Nat.mul 2 d.fb) d.nw)))) k

/-- The biased `(pos, neg)` accumulators of entry `(p, q)` of block `bi` (column `q`, slot `p`). -/
noncomputable def accR (d : CellData) (c : Ctx) (bi p q : Nat) : Nat × Nat :=
  Nat.rec (motive := fun _ => Nat × Nat)
    (Nat.shiftLeft (slotAt (wnOf d bi) (dColB (metEnt d bi) (wnOf d bi) (d.order bi) q) p) (Nat.sub c.S (scaleM d bi)), 0)
    (fun u ih => (fun y U => (Nat.add ih.1 (Nat.mul y U.1), Nat.add ih.2 (Nat.mul y U.2)))
      (slotAt (wnOf d bi) (dColB (facEntR d bi u) (wnOf d bi) (d.order bi) q) p)
      (uPair c.W d.nw u (Nat.sub c.S (Nat.add (Nat.mul 2 d.fb) d.nw)))) (Nat.add d.nw 1)

/-- The biased window of entry `(p, q)`: `pos + 2^(W-1) ones + β Σ U⁻ - (neg + β (Σ U⁺ + 2^(S-Lm)))`, `β = 2^(wn-1)`. -/
noncomputable def winR (d : CellData) (c : Ctx) (bi p q : Nat) : Nat :=
  (fun a us bt => Nat.sub (Nat.add (Nat.add a.1 (Nat.mul c.hW (ones c.W (Nat.add d.nw 1)))) (Nat.mul bt us.2))
      (Nat.add a.2 (Nat.mul bt (Nat.add us.1 (Nat.shiftLeft 1 (Nat.sub c.S (scaleM d bi)))))))
    (accR d c bi p q) (uSum c d (Nat.add d.nw 1)) (Nat.shiftLeft 1 (Nat.sub (wnOf d bi) 1))

/-- Row `i` of entry TMs `[(i,0), …, (i,n-1)]` (column `i`, every slot). -/
noncomputable def wRowR (d : CellData) (c : Ctx) (bi i : Nat) : List TM :=
  (fun ok0 => mkList (fun j => entryN c (Nat.add d.nw 1) (winR d c bi j i) ok0) (d.order bi)) (w0OkN d c bi)

/-- All rows of entry TMs of block `bi` (each evaluated once, on demand). -/
noncomputable def wTabR (d : CellData) (c : Ctx) (bi : Nat) : List (List TM) :=
  mkList (fun i => wRowR d c bi i) (d.order bi)

/-- Row-oriented W0 TMs of block `bi` on `ℕ` indices (zero outside the block). -/
noncomputable def WTr (d : CellData) (c : Ctx) (bi i j : Nat) : TM :=
  listAt zeroTM (listAt [] (wTabR d c bi) i) j

/-- The transposed lookup (`WTt i j = WTr j i`: column `j`). -/
noncomputable def WTt (d : CellData) (c : Ctx) (bi i j : Nat) : TM := WTr d c bi j i

end ThomsonCompact.CoeffMap.Deg
