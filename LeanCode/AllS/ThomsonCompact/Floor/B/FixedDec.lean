import ThomsonCompact.Fixed.Kernel

/-!
# Init-only decoder of the compact fixed right-inverse tables (F3d bridge leaves)

The same definitions as the table accessors of workstream F4 (`Fixed.hC`, `Fixed.dzC`, `Fixed.lamG`, `Fixed.dqG`,
which live in Mathlib-level soundness modules), restated over `Init` only so that the one-time bridge leaves of the
D14/D16 re-expanded tables import nothing but the kernel and the data. `FixedDecEq` proves both sets equal.
-/

namespace ThomsonCompact.Floor.B.FD
open ThomsonCompact.Fixed (Slice GTab polyLen fld)

/-- `n` base-`2^W` digits of `x`, lowest first -/
def digitsN (W n x : Nat) : List Nat := (List.range n).map (fun k => x / 2 ^ (W * k) % 2 ^ W)

def hdrL (x : Nat) : Nat := Nat.land (Nat.shiftRight x 12) 255
def hdrW (x : Nat) : Nat := Nat.land (Nat.shiftRight x 20) 255

/-- coefficients (lowest first) of the polynomial record at the bottom of `x` -/
def recCoeffs (x : Nat) : List Int :=
  List.map (fun s : Nat => (s : Int) - 2 ^ (hdrW x - 1)) (digitsN (hdrW x) (hdrL x) (Nat.shiftRight x 28)).reverse

def decPolysC : Nat → Nat → List (Nat × List Int)
  | 0, _ => []
  | n + 1, x => (Nat.land x 4095, recCoeffs x) :: decPolysC n (Nat.shiftRight x (polyLen x))

def decPolyVecC (ch : Nat → Nat) : Nat → Nat → List (Nat × List Int)
  | 0, _ => []
  | n + 1, c => decPolysC (Nat.land (ch c) 255) (Nat.shiftRight (ch c) 8) ++ decPolyVecC ch n (c + 1)

def lookC (l : List (Nat × List Int)) (i : Nat) : List Int := ((l.find? fun e => e.1 = i).map Prod.snd).getD []

def sliceNil : Slice := ⟨0, 0, fun _ _ => 0, fun _ => 0, 0, 0⟩

def findSlice (sl : List Slice) (i : Nat) : Slice :=
  (sl.find? fun S => decide (S.i0 ≤ i ∧ i < S.i0 + S.len)).getD sliceNil

/-- stored table entry `H_ki` (coefficients, lowest first) -/
def hC (sl : List Slice) (k i : Nat) : List Int :=
  lookC (decPolyVecC ((findSlice sl i).hc k) ((findSlice sl i).hn k) 0) i

/-- `dz_k`, `λ_k`, `dq_k` of output `k` -/
def dzC (G : GTab) (k : Nat) : List Int := lookC (decPolyVecC G.dzc G.dzn 0) (fld (G.inf k) 320 16)
def lamG (G : GTab) (k : Nat) : Nat := fld (G.inf k) 0 128
def dqG (G : GTab) (k : Nat) : Nat := fld (G.inf k) 128 128

end ThomsonCompact.Floor.B.FD
