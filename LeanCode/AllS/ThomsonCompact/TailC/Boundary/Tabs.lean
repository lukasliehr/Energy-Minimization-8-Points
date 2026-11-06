import ThomsonCompact.TailC.Boundary.Kernel

/-!
# TailC.Boundary: index-table checks (kernel programs, Init only; workstream TC1)

* `q2Ok`: every quadratic monomial `s < 105` has `qa s ≤ qb s ≤ 13`, and `qa 0 = qb 0 = 0`;
* `g1Ok`: `(qa, qb)(g1 a b) = (min a b, max a b)` for `a, b < 14` (so `x_a x_b = m_(g1 a b)`);
* `dOk`: `qa (dIdx j) = qb (dIdx j) = j + 1` for `j < 13`;
* `g2Ok`: the Batcher 2+2 merge of `(qa s, qb s)`, `(qa t, qb t)` packed in base 16 is the table entry `r4 (g2 s t)`,
  and `g2 s t < 2380` (so `m_s m_t = M4 (g2 s t)`).
-/

namespace ThomsonCompact.TailC.Boundary
open ThomsonCompact.TailC

/-- `f 0 && … && f (n-1)`. -/
noncomputable def allLt (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => ih && f k) n

/-- Table entry `gam s t` of a stage. -/
def gamF (P : SP) (s t : Nat) : Nat := fld (P.gam s) (Nat.mul P.gw t) P.gw

/-- Quartic monomial table entry (16 bits): `r1 | r2 << 4 | r3 << 8 | r4 << 12`. -/
noncomputable def r4 (γ : Nat) : Nat :=
  bif Nat.blt γ 1000 then fld r4c0 (Nat.mul 16 γ) 16
  else bif Nat.blt γ 2000 then fld r4c1 (Nat.mul 16 (Nat.sub γ 1000)) 16
  else fld r4c2 (Nat.mul 16 (Nat.sub γ 2000)) 16

noncomputable def minN (a b : Nat) : Nat := Bool.rec (motive := fun _ => Nat) b a (Nat.ble a b)

/-- Batcher merge of `(a, b)`, `(c, d)`, packed: `min a c | m1 << 4 | m2 << 8 | max b d << 12`. -/
noncomputable def merge4 (a b c d : Nat) : Nat :=
  Nat.add (minN a c) (Nat.add (Nat.mul 16 (minN (minN b d) (maxN a c)))
    (Nat.add (Nat.mul 256 (maxN (minN b d) (maxN a c))) (Nat.mul 4096 (maxN b d))))

noncomputable def q2Ok : Bool :=
  Nat.beq (qa 0) 0 && Nat.beq (qb 0) 0 && allLt 105 (fun s => Nat.ble (qa s) (qb s) && Nat.ble (qb s) 13)

noncomputable def g1Ok : Bool :=
  allLt 14 (fun a => allLt 14 (fun b =>
    Nat.blt (gamF sp1 a b) 105 && Nat.beq (qa (gamF sp1 a b)) (minN a b) && Nat.beq (qb (gamF sp1 a b)) (maxN a b)))

noncomputable def dOk : Bool :=
  allLt 13 (fun j => Nat.beq (qa (dIdx j)) (Nat.add j 1) && Nat.beq (qb (dIdx j)) (Nat.add j 1))

/-- Rows `[s0, s0 + k)` of the Level-2 table. -/
noncomputable def g2Ok (s0 k : Nat) : Bool :=
  allLt k (fun i => allLt 105 (fun t =>
    Nat.blt (gamF sp2 (Nat.add s0 i) t) 2380 &&
      Nat.beq (merge4 (qa (Nat.add s0 i)) (qb (Nat.add s0 i)) (qa t) (qb t)) (r4 (gamF sp2 (Nat.add s0 i) t))))

end ThomsonCompact.TailC.Boundary
