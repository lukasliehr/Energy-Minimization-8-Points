import ThomsonCompact.CoeffMap.BProg

/-!
# Leaf checker with coordinate ranges (Init only; F2d)

`blockOkgr c A WT bi g0 g1 r0 r1`: the pieces `g0 ≤ g < g1` of block `bi` at the coordinates `r0 ≤ r < r1` are `ok`.
Splitting a block's pieces by coordinate ranges bounds the work, hence the kernel memory, of one leaf; any cover of
`[0,8) × [0,100)` by such ranges gives every piece (`blockOkgr_spec` in `CoeffMap.W0Part`). Kept out of `BProg` so
that the one-time table checks importing `BProg` stay valid.
-/

namespace ThomsonCompact.CoeffMap

open ThomsonCompact.Packed
/-- Leaf checker (F2d): pieces `g0 ≤ g < g1` of block `bi`, coordinates `r0 ≤ r < r1` (bounds the work, hence the
kernel memory, of one leaf; any cover of `[0,8) × [0,100)` by such ranges gives every piece). -/
noncomputable def blockOkgr (c : Ctx) (A : TM) (WT : Nat → Nat → TM) (bi g0 g1 r0 r1 : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun g ih => cond (Nat.ble g0 g)
    (Nat.rec (motive := fun _ => Bool) true
      (fun r ih2 => cond (Nat.ble r0 r) ((blockTMg c A WT bi g r).ok && ih2) ih2) r1 && ih) ih) g1

end ThomsonCompact.CoeffMap
