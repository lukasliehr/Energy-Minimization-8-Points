import ThomsonCompact.Cells.D12GateK

/-!
# Degree-generic centre-gate leaves (F3g; Init only)

`centreGateT` is F3e's `D12Asm.centreGateF` with the number of target models `nT` as a parameter (`12` for D12,
`14`/`16`/`18` for the D14/D16/D18 cells): per retained coordinate `i0 ≤ i < i0 + n` the direction is a target
index (`dirT i < nT`) and the exact integer inequality `D12Asm.cgateF` holds (no products with powers of two;
soundness `Cells.DegAsm.centreGateT_spec`, `D12Asm.cgateF_spec`).
-/

noncomputable section

namespace ThomsonCompact.Cells.DegAsm
open ThomsonCompact.Packed ThomsonCompact.Floor.B ThomsonCompact.Cells.D12Asm

/-- **Centre-gate leaf** (any degree): coordinates `i0 ≤ i < i0 + n`, target directions `< nT` -/
def centreGateT (c : Ctx) (Ht : Nat → TM) (dirT : Nat → Nat) (dirQ : Nat → Bool × Nat) (D : Nat → List Nat)
    (G F' wc : Nat) (cm Er : Nat → Nat) (nT i0 : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Bool) true fun j ih =>
    and (and (Nat.blt (dirT (Nat.add i0 j)) nT)
      (cgateF c (Ht (dirT (Nat.add i0 j))) (dirQ (Nat.add i0 j)) (D (Nat.add i0 j)) G F' wc (cm (Nat.add i0 j))
        (Er (Nat.add i0 j)))) ih

end ThomsonCompact.Cells.DegAsm

end
