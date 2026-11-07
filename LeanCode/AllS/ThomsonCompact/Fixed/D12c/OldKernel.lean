import ThomsonCompact.Fixed.Kernel

/-!
# Identification with the old literal tables: kernel checks (Init only; workstream F4c)

Bool checkers comparing the compact `H` slices and the Γ/Q-link data of `Fixed.D12c`/`Fixed.D18c` with the old
`FixedTables.D12`/`D18` literals (`List ℤ`/`List ℚ` matrices), by exact equality of the decoded coefficient lists
(soundness: `Fixed.D12c.OldSound`). The decoders mirror `Fixed.Sound.recCoeffs`/`decPolysC`/`decPolyVecC` with
`Nat` shifts and masks only (no `Int` powers).
-/

namespace ThomsonCompact.Fixed

/-- The `L` biased slots of width `w` (mask `mk`, bias `b`) at the bottom of `y`, slot 0 = highest coefficient,
prepended (lowest coefficient first) to `acc`. -/
noncomputable def decAcc (w mk b : Nat) (L : Nat) : Nat → List Int → List Int :=
  Nat.rec (motive := fun _ => Nat → List Int → List Int) (fun _ acc => acc)
    (fun _ ih y acc => ih (Nat.shiftRight y w) (Int.subNatNat (Nat.land y mk) b :: acc)) L

/-- Coefficients (lowest first) of the polynomial record at the bottom of `x` (`= recCoeffs x`). -/
noncomputable def recK (x : Nat) : List Int :=
  decAcc (Nat.land (Nat.shiftRight x 20) 255) (Nat.sub (Nat.shiftLeft 1 (Nat.land (Nat.shiftRight x 20) 255)) 1)
    (Nat.shiftLeft 1 (Nat.sub (Nat.land (Nat.shiftRight x 20) 255) 1)) (Nat.land (Nat.shiftRight x 12) 255)
    (Nat.shiftRight x 28) []

/-- `n` polynomial records as `(index, coefficients)` (`= decPolysC`). -/
noncomputable def decPolysK (n : Nat) : Nat → List (Nat × List Int) :=
  Nat.rec (motive := fun _ => Nat → List (Nat × List Int)) (fun _ => [])
    (fun _ ih x => (Nat.land x 4095, recK x) :: ih (Nat.shiftRight x (polyLen x))) n

/-- Chunks `c, …, c+n-1` of a polynomial vector (`= decPolyVecC`). -/
noncomputable def decPolyVecK (ch : Nat → Nat) (n : Nat) : Nat → List (Nat × List Int) :=
  Nat.rec (motive := fun _ => Nat → List (Nat × List Int)) (fun _ => [])
    (fun _ ih c => decPolysK (Nat.land (ch c) 255) (Nat.shiftRight (ch c) 8) ++ ih (Nat.add c 1)) n

/-- Coefficients of index `i` (`[]` if absent; `= lookC`). -/
noncomputable def lookK (l : List (Nat × List Int)) (i : Nat) : List Int :=
  List.rec (motive := fun _ => List Int) [] (fun e _ ih => Bool.rec ih e.2 (Nat.beq e.1 i)) l

/-- Equality of integer lists. -/
noncomputable def zlEq : List Int → List Int → Bool :=
  List.rec (motive := fun _ => List Int → Bool) (fun l => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) l)
    (fun a _ ih l => List.rec (motive := fun _ => Bool) false (fun b bs _ => decide (a = b) && ih bs) l)

/-- Row `k` of slice `S` against the old row `old` on the slice's columns `i0, …, i0 + len - 1`. -/
noncomputable def rowOldOk (S : Slice) (k : Nat) (old : Nat → List Int) : Bool :=
  (fun l => Nat.rec (motive := fun _ => Bool) true
      (fun p ih => ih && zlEq (lookK l (Nat.add S.i0 p)) (old (Nat.add S.i0 p))) S.len)
    (decPolyVecK (S.hc k) (S.hn k) 0)

/-- Rows `k0, …, k0 + m - 1` of all slices `sl` against the old rows `old k`. -/
noncomputable def rowsOldOk (sl : List Slice) (old : Nat → Nat → List Int) (m : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih k => List.rec (motive := fun _ => Bool) true (fun S _ ih2 => rowOldOk S k (old k) && ih2) sl &&
      ih (Nat.add k 1)) m

/-- Denominator `dz` record of output `k` (`= dzC`). -/
noncomputable def dzK (G : GTab) (k : Nat) : List Int := lookK (decPolyVecK G.dzc G.dzn 0) (fld (G.inf k) 320 16)

end ThomsonCompact.Fixed
