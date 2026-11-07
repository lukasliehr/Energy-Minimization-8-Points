import ThomsonCompact.Floor.B.KernelC

/-!
# Centre-gate kernel without power-of-two products (F3e; Init only)

Same inequality as `Floor.B.KernelC.centreGateOk` (per retained coordinate, units `2^-S`):
`Σ_k |y_k - 3 d_k 2^F - 3 C_k 2^G| + 3 d_e 2^F ≤ 3 Er` with `y_k = qn h_k`, `F = G + F'`, `G = S - Sc`,
but evaluated without forming the products `d_k 2^F`, `C_k 2^G`: the kernel's caches hash a `Nat` literal by its low
64 bits, so thousands of distinct multiples of `2^64` share one bucket and the check becomes quadratic (34 s instead
of ~3 s for 100 coordinates of cell 4). Here `y_k = 2^G q_k + r_k` (`0 ≤ r_k < 2^G`), `u_k = 3 (d_k 2^F' + C_k)`,
`a_k = q_k - u_k`, so `|y_k - 2^G u_k| = 2^G |a_k| ± r_k` (`+` iff `a_k ≥ 0`), and the check is
`2^G (Σ|a_k| + 3 d_e 2^F') + Σ_{a_k ≥ 0} r_k ≤ 3 Er + Σ_{a_k < 0} r_k` (exact; soundness `Cells.D12Asm.cgateF_spec`).
Leaves cover coordinate ranges `[i0, i0 + n)` (`centreGateF`, `Nat.rec`).
-/

noncomputable section

namespace ThomsonCompact.Cells.D12Asm
open ThomsonCompact.Packed ThomsonCompact.Floor.B
open ThomsonCompact.Floor (slot)

/-- `0 ≤ x` (kernel form) -/
def nonnegB : Int → Bool
  | Int.ofNat _ => true
  | Int.negSucc _ => false

/-- `y_k = qn h_k` -/
def yK (c : Ctx) (Ht : TM) (dq : Bool × Nat) (k : Nat) : Int :=
  Int.mul (svK dq) (svK (pvGet c.W c.m Ht.v k))

/-- `u_k = 3 (d_k 2^F' + C_k)` -/
def uK (dr : List Nat) (F' wc cm k : Nat) : Int :=
  Int.mul 3 (Int.add (Int.mul (ThomsonCompact.CoeffMap.sdec (dr.getD k 0)) (Int.ofNat (Nat.pow 2 F')))
    (svK (smDec (slot wc cm k))))

/-- `a_k = ⌊y_k / 2^G⌋ - u_k` -/
def aK (c : Ctx) (Ht : TM) (dq : Bool × Nat) (dr : List Nat) (G F' wc cm k : Nat) : Int :=
  Int.sub (Int.ediv (yK c Ht dq k) (Int.ofNat (Nat.pow 2 G))) (uK dr F' wc cm k)

/-- `r_k = y_k mod 2^G` -/
def rK (c : Ctx) (Ht : TM) (dq : Bool × Nat) (G k : Nat) : Nat :=
  Int.toNat (Int.emod (yK c Ht dq k) (Int.ofNat (Nat.pow 2 G)))

/-- `Σ_k |a_k|` -/
def sumA (c : Ctx) (Ht : TM) (dq : Bool × Nat) (dr : List Nat) (G F' wc cm : Nat) : Nat :=
  lsum ((List.range c.m).map fun k => Int.natAbs (aK c Ht dq dr G F' wc cm k))

/-- `Σ_{a_k ≥ 0} r_k` -/
def sumP (c : Ctx) (Ht : TM) (dq : Bool × Nat) (dr : List Nat) (G F' wc cm : Nat) : Nat :=
  lsum ((List.range c.m).map fun k => cond (nonnegB (aK c Ht dq dr G F' wc cm k)) (rK c Ht dq G k) 0)

/-- `Σ_{a_k < 0} r_k` -/
def sumN (c : Ctx) (Ht : TM) (dq : Bool × Nat) (dr : List Nat) (G F' wc cm : Nat) : Nat :=
  lsum ((List.range c.m).map fun k => cond (nonnegB (aK c Ht dq dr G F' wc cm k)) 0 (rK c Ht dq G k))

/-- centre gate of one coordinate -/
def cgateF (c : Ctx) (Ht : TM) (dq : Bool × Nat) (dr : List Nat) (G F' wc cm Er : Nat) : Bool :=
  Nat.ble (Nat.add (Nat.shiftLeft (Nat.add (sumA c Ht dq dr G F' wc cm)
      (Nat.mul 3 (Nat.shiftLeft (dr.getD c.m 0) F'))) G) (sumP c Ht dq dr G F' wc cm))
    (Nat.add (Nat.mul 3 Er) (sumN c Ht dq dr G F' wc cm))

/-- **Centre-gate leaf**: coordinates `i0 ≤ i < i0 + n` -/
def centreGateF (c : Ctx) (Ht : Nat → TM) (dirT : Nat → Nat) (dirQ : Nat → Bool × Nat) (D : Nat → List Nat)
    (G F' wc : Nat) (cm Er : Nat → Nat) (i0 : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Bool) true fun j ih =>
    and (and (Nat.blt (dirT (Nat.add i0 j)) 12)
      (cgateF c (Ht (dirT (Nat.add i0 j))) (dirQ (Nat.add i0 j)) (D (Nat.add i0 j)) G F' wc (cm (Nat.add i0 j))
        (Er (Nat.add i0 j)))) ih

end ThomsonCompact.Cells.D12Asm

end
