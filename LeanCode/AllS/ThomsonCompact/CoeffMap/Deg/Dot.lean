import ThomsonCompact.Packed.Core2
import ThomsonCompact.CoeffMap.ListUtil
import ThomsonCompact.CoeffMap.RFCodec

/-!
# Packed dot products (Init only; F2f)

`dotTM c [(A₀, B₀), …]` encloses `Σᵢ fᵢ gᵢ` with **one** truncation to degree `N` and **one** floor rounding, as
`Packed.mul` does for a single product: the packed products `Aᵢ.v Bᵢ.v` (signed coefficients, residues modulo `2^K`)
and `Aᵢ.a Bᵢ.a` (magnitude bounds) are summed before the slot-wise rounding, the product errors are summed before
one ceiling division. Per term the kernel does six multiplications and six additions of numbers (no slot masks, no
shifts, no digit sums), so a `d`-term dot product costs about `d/4` products of `Packed.mul`. The extra check
`Σ Aᵢ.s Bᵢ.s < 2^(2B)` replaces the per-factor bound that makes a single product overflow-free.

Constants (`constQ`: `±n/d` rounded to the scale, error one unit; `constI`: exact integers) make it a linear
combination. Soundness: `CoeffMap.Deg.DotSound.dotTM_sound`. Bit-exact mirror: `CoeffMap/Deg/gen/mirror.py`.
-/

namespace ThomsonCompact.CoeffMap.Deg

open ThomsonCompact.Packed

/-- `(Σ Aᵢ.v Bᵢ.v, Σ Aᵢ.a Bᵢ.a, Σ (Aᵢ.s Bᵢ.e + Bᵢ.s Aᵢ.e + Aᵢ.e Bᵢ.e), Σ Aᵢ.s Bᵢ.s, all ok)`. -/
noncomputable def dotAcc (L : List (TM × TM)) : Nat × Nat × Nat × Nat × Bool :=
  List.rec (motive := fun _ => Nat × Nat × Nat × Nat × Bool) (0, 0, 0, 0, true)
    (fun p _ ih => (Nat.add (Nat.mul p.1.v p.2.v) ih.1, Nat.add (Nat.mul p.1.a p.2.a) ih.2.1,
      Nat.add (Nat.add (Nat.add (Nat.mul p.1.s p.2.e) (Nat.mul p.2.s p.1.e)) (Nat.mul p.1.e p.2.e)) ih.2.2.1,
      Nat.add (Nat.mul p.1.s p.2.s) ih.2.2.2.1, p.1.ok && p.2.ok && ih.2.2.2.2)) L

/-- The TM of `Σᵢ fᵢ gᵢ` from the accumulators (the rounding of `Packed.mul`). -/
def dotFin (c : Ctx) (r : Nat × Nat × Nat × Nat × Bool) : TM :=
  let p := Nat.land (Nat.add r.1 c.biasP) c.maskK
  let a := Nat.shiftRight (Nat.land (Nat.add (Nat.land r.2.1 c.maskWm) c.ceilAdd) c.rmask) c.S
  let s := ssum c a
  ⟨Nat.land (Nat.add (Nat.shiftRight (Nat.land p c.rmask) c.S) c.unb) c.maskK, a, s,
   Nat.add (Nat.add (cdiv c.S r.2.2.1) (cdiv c.S (ssum c (Nat.shiftRight r.2.1 c.wm)))) c.m,
   r.2.2.2.2 && Nat.blt r.2.2.2.1 (Nat.mul c.twoB c.twoB) && Nat.blt s c.twoB⟩

/-- `Σᵢ fᵢ gᵢ` with one truncation and one rounding. -/
noncomputable def dotTM (c : Ctx) (L : List (TM × TM)) : TM := dotFin c (dotAcc L)

/-- The rational constant `±n/d` (rounded down to the scale, error one unit). -/
def constQ (c : Ctx) (ng : Bool) (n d : Nat) : TM := constTM c ng (ratMag c n d) 1

/-- The exact integer constant `m`. -/
def constI (c : Ctx) (m : Nat) : TM := constTM c false (Nat.mul m c.twoS) 0

/-- `A^j` (`A^0` is the exact `1`; each power evaluated once). -/
noncomputable def powA (c : Ctx) (A : TM) (j : Nat) : TM :=
  Nat.rec (motive := fun _ => TM) (constI c 1) (fun _ P => mul c P A) j

/-- The powers `A^0, …, A^(n-1)`. -/
noncomputable def powTab (c : Ctx) (A : TM) (n : Nat) : List TM := mkList (fun j => powA c A j) n

/-- `[(±nⱼ/dⱼ, Pⱼ)]`: coefficients paired with a list of TMs. -/
noncomputable def zipPow (c : Ctx) (L : List (Bool × Nat × Nat)) : List TM → List (TM × TM) :=
  List.rec (motive := fun _ => List TM → List (TM × TM)) (fun _ => [])
    (fun q _ ih pw => List.casesOn (motive := fun _ => List (TM × TM)) pw []
      (fun P pw' => (constQ c q.1 q.2.1 q.2.2, P) :: ih pw')) L

/-- `Σⱼ (±nⱼ/dⱼ) gʲ` at the TM `A` of `g` as one dot product with the powers of `A`. -/
noncomputable def polyD (c : Ctx) (A : TM) (L : List (Bool × Nat × Nat)) : TM :=
  dotTM c (zipPow c L (powTab c A L.length))

/-- Entry of a column-matrix row as a TM (`none` is the exact `1`). -/
def entTM (c : Ctx) : Option TM → TM
  | none => constI c 1
  | some K => K

end ThomsonCompact.CoeffMap.Deg

/-! ## Batched dot products (Kronecker packing) -/

namespace ThomsonCompact.CoeffMap.Deg

open ThomsonCompact.Packed

/-- `Σᵢ xᵢ 2^(sp i)` (low first). -/
noncomputable def packN (sp : Nat) (xs : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => Nat.add x (Nat.shiftLeft ih sp)) xs

/-- Slot width of the batches: `2 K + 20` (products of fields `< 2^K`, at most `2^16` terms). -/
def bsp (c : Ctx) : Nat := Nat.add (Nat.mul 2 c.K) 20

/-- Packed sums `(Σⱼ aⱼ.v Bⱼ.v, Σⱼ aⱼ.a Bⱼ.a, Σⱼ (aⱼ.s Bⱼ.e + aⱼ.e Bⱼ.s + aⱼ.e Bⱼ.e), Σⱼ aⱼ.s Bⱼ.s)` where `Bⱼ.f` is
the packed field `f` of the list `Bⱼ`. -/
noncomputable def bdotAcc (sp : Nat) (as : List TM) (Bs : List (List TM)) : Nat × Nat × Nat × Nat :=
  List.rec (motive := fun _ => List (List TM) → Nat × Nat × Nat × Nat) (fun _ => (0, 0, 0, 0))
    (fun a _ ih Bs => List.casesOn (motive := fun _ => Nat × Nat × Nat × Nat) Bs (0, 0, 0, 0) (fun B Bs' =>
      (fun r pv pa ps pe => (Nat.add (Nat.mul a.v pv) r.1, Nat.add (Nat.mul a.a pa) r.2.1,
          Nat.add (Nat.add (Nat.add (Nat.mul a.s pe) (Nat.mul a.e ps)) (Nat.mul a.e pe)) r.2.2.1,
          Nat.add (Nat.mul a.s ps) r.2.2.2))
        (ih Bs') (packN sp (B.map TM.v)) (packN sp (B.map TM.a)) (packN sp (B.map TM.s)) (packN sp (B.map TM.e))))
    as Bs

/-- All factors are `ok` with fields below `2^K`, and there are fewer than `2^16` terms. -/
noncomputable def bdotOk (c : Ctx) (as : List TM) (Bs : List (List TM)) : Bool :=
  (fun okT => as.all okT && Bs.all (fun B => B.all okT) && Nat.blt as.length 65536)
    (fun T => T.ok && Nat.blt T.v c.twoK && Nat.blt T.a c.twoK && Nat.blt T.s c.twoK && Nat.blt T.e c.twoK)

/-- **Batched dot products**: output `i < n` is `dotTM c [(aⱼ, Bⱼᵢ)]ⱼ` (`bdot_eq`), from four packed sums. -/
noncomputable def bdot (c : Ctx) (as : List TM) (Bs : List (List TM)) (n : Nat) : List TM :=
  (fun r ok => mkList (fun i => dotFin c (slotAt (bsp c) r.1 i, slotAt (bsp c) r.2.1 i, slotAt (bsp c) r.2.2.1 i,
      slotAt (bsp c) r.2.2.2 i, ok)) n)
    (bdotAcc (bsp c) as Bs) (bdotOk c as Bs)

end ThomsonCompact.CoeffMap.Deg
