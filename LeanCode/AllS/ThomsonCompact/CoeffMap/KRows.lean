import ThomsonCompact.Packed.Core2
import ThomsonCompact.CoeffMap.RFDen
import ThomsonCompact.CoeffMap.MomentProg
import ThomsonCompact.CoeffMap.ListUtil

/-!
# Column-matrix rows of the D12 Gram blocks at a height TM (Init only; F2b c)

* scalar blocks: record `k` of the packed RF tables at the height TM `A` is `recTM c A k = rfTM c 8 0 A num den`
  (F1's rational evaluation, Newton division without stored witnesses); row `u` of block `bi` lists the
  nonzero entries `(i, colRec bi i u)` (`none` for the exact `1`, record `0`; record `1` is `0` and skipped).
* moment blocks `k` (pivot `p`): row `p` holds `-ρᵢ = -momentP k (succAbove p i) / momentP k p` (`hornerQ` of the
  rational mirror `mP`, `divN`); every other row `r` holds the single exact `1` in column `r` or `r - 1`.
-/

namespace ThomsonCompact.CoeffMap

open ThomsonCompact.Packed

/-- Integer coefficient with denominator `M` as a `hornerQ` triple (`= Packed.qOfInt`). -/
def qOfIntI (M : Nat) (n : Int) : Bool × Nat × Nat := (decide (n < 0), n.natAbs, M)

noncomputable def numQ (k : Nat) : List (Bool × Nat × Nat) :=
  (D12RF.rec k).num.map (qOfIntI (D12RF.rec k).scaleN)

noncomputable def denQ (d : Nat) : List (Bool × Nat × Nat) :=
  (D12RF.denPoly d).map (qOfIntI (D12RF.denScale d))

/-- Record `k` at the height TM `A`. -/
noncomputable def recTM (c : Ctx) (A : TM) (k : Nat) : TM :=
  rfTM c 8 0 A (numQ k) (denQ (D12RF.denIdx k))

/-- Row `u` of scalar block `bi` (column count `d`). -/
noncomputable def scalarRow (c : Ctx) (A : TM) (bi d u : Nat) : List (Nat × Option TM) :=
  ((List.range d).filter fun i => !(Nat.beq (D12RF.colRec bi i u) 1)).map fun i =>
    (i, if Nat.beq (D12RF.colRec bi i u) 0 then none else some (recTM c A (D12RF.colRec bi i u)))

/-- `succAbove p i` on `ℕ`. -/
def sA (p i : Nat) : Nat := if i < p then i else i + 1

def momQ (k j : Nat) : List (Bool × Nat × Nat) := toQL (mP k j).r

/-- `-momentP k (succAbove p i) / momentP k p` at the height TM. -/
def rhoTM (c : Ctx) (A : TM) (k p i : Nat) : TM :=
  neg c (divN c 8 0 (hornerQ c A (momQ k (sA p i))) (hornerQ c A (momQ k p)))

/-- Row `r` of moment block `k` (pivot `p`, column count `d`). -/
def momentRow (c : Ctx) (A : TM) (k p d r : Nat) : List (Nat × Option TM) :=
  if r = p then (List.range d).map fun i => (i, some (rhoTM c A k p i))
  else [(if r < p then r else r - 1, none)]


/-! ## Faster records (F2c): `Nat`-only numerator decode, shared denominator inverses -/

/-- `qOfIntI M (unbias v)` with `Nat` operations only. -/
def qOfSlot (M v : Nat) : Bool × Nat × Nat :=
  (Nat.blt v 33554432, Nat.add (Nat.sub v 33554432) (Nat.sub 33554432 v), M)

/-- `numQ k` decoded with `Nat` operations only (`numQN_eq`). -/
noncomputable def numQN (k : Nat) : List (Bool × Nat × Nat) :=
  (fun s => List.casesOn (motive := fun _ => List (Bool × Nat × Nat)) s [] (fun lenN t1 =>
    List.casesOn (motive := fun _ => List (Bool × Nat × Nat)) t1 [] (fun sc t2 =>
      List.casesOn (motive := fun _ => List (Bool × Nat × Nat)) t2 [] (fun _ rest =>
        (rest.take lenN).map (qOfSlot sc)))))
  (tableSlots D12RF.recChunk 26 18 34 k)

/-- Inverse TMs of the shared denominators at the height TM (each evaluated once per leaf). -/
noncomputable def denInvTab (c : Ctx) (A : TM) : List TM :=
  mkList (fun d => invN c 8 0 (hornerQ c A (denQ d))) D12RF.nDen

/-- Record `k` at `A` through the denominator table (`recTMz_eq : recTMz c A k = recTM c A k`). -/
noncomputable def recTMz (c : Ctx) (A : TM) (k : Nat) : TM :=
  mul c (hornerQ c A (numQN k))
    (cond (Nat.blt (D12RF.denIdx k) D12RF.nDen) (listAt zeroTM (denInvTab c A) (D12RF.denIdx k))
      (invN c 8 0 (hornerQ c A (denQ (D12RF.denIdx k)))))

/-- `scalarRow` with `recTMz`. -/
noncomputable def scalarRowz (c : Ctx) (A : TM) (bi d u : Nat) : List (Nat × Option TM) :=
  ((List.range d).filter fun i => !(Nat.beq (D12RF.colRec bi i u) 1)).map fun i =>
    (i, if Nat.beq (D12RF.colRec bi i u) 0 then none else some (recTMz c A (D12RF.colRec bi i u)))

/-- Per-cell check: the inverse TMs of all shared denominators are valid (so no denominator vanishes on the
cell; `denOk_sound`). -/
noncomputable def denOk (c : Ctx) (A : TM) : Bool :=
  (List.range D12RF.nDen).all fun d => (invN c 8 0 (hornerQ c A (denQ d))).ok

end ThomsonCompact.CoeffMap
