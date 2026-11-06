import ThomsonCompact.CoeffMap.CellCodec
import ThomsonCompact.CoeffMap.ListUtil

/-!
# Packed W0 Gram entries (Init only; F2c)

For block `bi` of a cell (`CellData`, FORMAT.md §2 layout) the Gram coefficients of a whole column `q` are
computed at once by Kronecker packing: with `X = 2^W` (the TM slot width), `M = NW + 1` and `Y = X^M`,

* factor columns `C_{u,l}(Y) = Σ_{l ≤ p < n} F_u[p][l] Yᵖ` and metric columns `Cm_l` (`colPack`),
* factor Gram columns `D_{u,q} = Σ_{l ≤ q} F_u[q][l] C_{u,l}` (slot `p` = `dotI` of rows `p`, `q`; `dPack`),
* `G_q = Σ_u U_u(X) D_{u,q} + 2^(S-Lm) Dm_q` with `U_u(X) = Σ_k bernI(NW,u,k) 2^(S-Lf) Xᵏ` (`gPack`),

all modulo `2^(W M n)`. Slot `(p, k)` of `G_q` (bit `W (k + M p)`) is `coefI bi k p q · 2^(S-L)`; after one
bias, entry `(p, q)` is one shift and one mask (`entryTM`), laid out like a TM coefficient vector. Indices
are always recursor predecessors (literals), so every column and every entry is evaluated once by the kernel.
`w0Ok` is the per-block a-priori slot bound (no overflow in the biased decode). Soundness: `GramPackSound`.
Python mirror: `CoeffMap/gen/w0pack.py`.
-/

namespace ThomsonCompact.CoeffMap

open ThomsonCompact.Packed

/-- `p (p + 1) / 2` -/
def tri (p : Nat) : Nat := Nat.shiftRight (Nat.mul p (Nat.add p 1)) 1

/-- `(neg, mag)` of a sign-magnitude slot `2|x| + [x < 0]`. -/
def smSlot (z : Nat) : Bool × Nat := (Nat.beq (Nat.land z 1) 1, Nat.shiftRight z 1)

/-- Entry `(p, l)` (`l ≤ p`) of factor `u` of block `bi` (single chunk `0`). -/
def facEnt (d : CellData) (bi u p l : Nat) : Bool × Nat :=
  smSlot (slotAt (d.layout bi).2.1 (d.fac bi u 0) (Nat.add (tri p) l))

/-- Entry `(p, l)` (`l ≤ p`) of the metric of block `bi` scaled by `2^mb`: strict lower `klow · 2^(mb - mbits)`,
diagonal `2^(mb + dₚ)`. -/
noncomputable def metEnt (d : CellData) (bi p l : Nat) : Bool × Nat :=
  cond (Nat.blt l p)
    ((fun z => (Nat.beq (Nat.land z 1) 1, Nat.shiftLeft (Nat.shiftRight z 1) (Nat.sub (d.mb bi) d.mbits)))
      (slotAt d.kw (d.klow bi 0) (Nat.add (Nat.shiftRight (Nat.mul p (Nat.sub p 1)) 1) l)))
    (false, Nat.shiftLeft 1 (Nat.sub (Nat.add (d.mb bi) (slotAt 9 (d.kdiag bi) p)) 128))

/-- One column term: `±mag · Y^p` as a residue modulo `tw` (`mag · 2^(sw p) ≤ tw`). -/
def colTerm (tw sw p : Nat) (e : Bool × Nat) : Nat :=
  (fun y => cond e.1 (Nat.sub tw y) y) (Nat.shiftLeft e.2 (Nat.mul sw p))

/-- `Σ_{l ≤ p < k} colTerm p` (recursor over the row index `p`, so `ent p l` has literal indices and is shared
with the Gram pass `dPack`). -/
noncomputable def colAcc (ent : Nat → Nat → Bool × Nat) (sw tw l : Nat) (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun p ih =>
    cond (Nat.ble l p) (Nat.add (colTerm tw sw p (ent p l)) ih) ih) k

/-- Column `l`: `Σ_{l ≤ p < n} x(p, l) Yᵖ` modulo `tw = 2^Kt` (`Y = 2^sw`). -/
noncomputable def colPack (ent : Nat → Nat → Bool × Nat) (sw tw n l : Nat) : Nat :=
  Nat.land (colAcc ent sw tw l n) (Nat.sub tw 1)

/-- `tw - colPack` (the negated column, a residue of `-C`). -/
noncomputable def colNeg (ent : Nat → Nat → Bool × Nat) (sw tw n l : Nat) : Nat :=
  Nat.sub tw (colPack ent sw tw n l)

/-- `Σ_{l < k} x(q, l) · Cₗ` (signed scalars as residues). -/
noncomputable def dAcc (ent : Nat → Nat → Bool × Nat) (sw tw n q : Nat) (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun l ih =>
    Nat.add (cond (ent q l).1 (Nat.mul (ent q l).2 (colNeg ent sw tw n l))
      (Nat.mul (ent q l).2 (colPack ent sw tw n l))) ih) k

/-- Gram column `q`: `Σ_{l ≤ q} x(q, l) · Cₗ` modulo `tw`. -/
noncomputable def dPack (ent : Nat → Nat → Bool × Nat) (sw tw n q : Nat) : Nat :=
  Nat.land (dAcc ent sw tw n q (Nat.add q 1)) (Nat.sub tw 1)

/-- `bernI 8 u k` for `u, k ≤ 8`: sign-magnitude 16-bit slots, `(u, k) ↦ slot 9u + k` (checked once against
`bernI` in `GramPackSound`). -/
def bern8 : Nat :=
  0x2001000380070008c00700038001000020011006100e100e1000000e000e000600010003800e000e000e1023100e100e000e00038007100e100e002a0000002a100e100e00070008c0000023100000348000002310000008c007100e000e002a1000002a000e100e10070003800e100e000e0023100e000e000e100380011006000e100e0000000e100e0006100100002001100380071008c0071003800110002

/-- `(neg, |bernI nw u k|)` (table for `nw = 8`). -/
noncomputable def bernE (nw u k : Nat) : Bool × Nat :=
  cond (Nat.beq nw 8) (smSlot (slotAt 16 bern8 (Nat.add (Nat.mul 9 u) k)))
    (decide (bernI nw u k < 0), (bernI nw u k).natAbs)

/-- `Σ_{k < j}` of the positive / negative parts of `bernI(nw, u, k) 2^sh Xᵏ`, `X = 2^W`. -/
noncomputable def uAcc (W nw u sh : Nat) (j : Nat) : Nat × Nat :=
  Nat.rec (motive := fun _ => Nat × Nat) (0, 0) (fun k ih =>
    cond (bernE nw u k).1
      (ih.1, Nat.add (Nat.shiftLeft (bernE nw u k).2 (Nat.add sh (Nat.mul W k))) ih.2)
      (Nat.add (Nat.shiftLeft (bernE nw u k).2 (Nat.add sh (Nat.mul W k))) ih.1, ih.2)) j

/-- Positive and negative parts of `U_u(X) = Σ_{k ≤ nw} bernI(nw, u, k) 2^sh Xᵏ`, `X = 2^W`. -/
noncomputable def uPair (W nw u sh : Nat) : Nat × Nat := uAcc W nw u sh (Nat.add nw 1)

/-- Block geometry: `(n, M, sw, tw)` with `M = nw + 1`, `sw = W M`, `tw = 2^(sw n)`. -/
def geo (d : CellData) (c : Ctx) (bi : Nat) : Nat × Nat × Nat × Nat :=
  (d.order bi, Nat.add d.nw 1, Nat.mul c.W (Nat.add d.nw 1),
    Nat.pow 2 (Nat.mul (Nat.mul c.W (Nat.add d.nw 1)) (d.order bi)))

/-- Metric scale exponent `Lm = 2 mb - e`. -/
noncomputable def scaleM (d : CellData) (bi : Nat) : Nat := Int.toNat (2 * (d.mb bi : Int) - d.floorExp)

/-- `Σ_{u < k} (U⁺_u D_{u,q} + U⁻_u (tw - D_{u,q}))` over the Bernstein factors. -/
noncomputable def gAcc (d : CellData) (c : Ctx) (bi q : Nat) (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun u ih =>
    Nat.add (Nat.add
      (Nat.mul (uPair c.W d.nw u (Nat.sub c.S (Nat.add (Nat.mul 2 d.fb) d.nw))).1
        (dPack (facEnt d bi u) (geo d c bi).2.2.1 (geo d c bi).2.2.2 (geo d c bi).1 q))
      (Nat.mul (uPair c.W d.nw u (Nat.sub c.S (Nat.add (Nat.mul 2 d.fb) d.nw))).2
        (Nat.sub (geo d c bi).2.2.2
          (dPack (facEnt d bi u) (geo d c bi).2.2.1 (geo d c bi).2.2.2 (geo d c bi).1 q)))) ih) k

/-- The packed Gram column `q` of block `bi` (slot `(p, k)` at bit `W (k + M p)`), modulo `tw`. -/
noncomputable def gPack (d : CellData) (c : Ctx) (bi q : Nat) : Nat :=
  Nat.land (Nat.add (gAcc d c bi q (Nat.add d.nw 1))
    (Nat.shiftLeft (dPack (metEnt d bi) (geo d c bi).2.2.1 (geo d c bi).2.2.2 (geo d c bi).1 q)
      (Nat.sub c.S (scaleM d bi))))
    (Nat.sub (geo d c bi).2.2.2 1)

/-- Biased column: every slot `+ 2^(W-1)` (digits of the signed slots, no borrows). -/
noncomputable def gPackB (d : CellData) (c : Ctx) (bi q : Nat) : Nat :=
  Nat.land (Nat.add (gPack d c bi q) (Nat.mul c.hW (ones c.W (Nat.mul (geo d c bi).2.1 (geo d c bi).1))))
    (Nat.sub (geo d c bi).2.2.2 1)

/-- Entry TM `p` of a biased column (window of `M` slots, unbiased to a residue mod `2^K`, exact magnitudes,
error `0`); `ok0` is the block check. -/
noncomputable def entryTM (c : Ctx) (M Gb p : Nat) (ok0 : Bool) : TM :=
  (fun v => (fun a => (⟨v, a, ssum c a, 0, Nat.blt (ssum c a) c.twoB && ok0⟩ : TM)) (pabs c ⟨v, 0, 0, 0, true⟩))
    (Nat.land (Nat.add (Nat.land (Nat.shiftRight Gb (Nat.mul (Nat.mul c.W M) p))
      (Nat.sub (Nat.pow 2 (Nat.mul c.W M)) 1)) (Nat.sub c.twoK (Nat.mul c.hW (ones c.W M)))) c.maskK)

/-- `max` of the first `k` diagonal slots of the metric of block `bi`. -/
noncomputable def smaxAcc (d : CellData) (bi : Nat) (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun r ih => Nat.max ih (slotAt 9 (d.kdiag bi) r)) k

/-- Largest diagonal slot of the metric of block `bi`. -/
noncomputable def smaxK (d : CellData) (bi : Nat) : Nat := smaxAcc d bi (d.order bi)

/-- Bit bound of the scaled metric entries: `max(kw - 1 + mb - mbits, mb + smax - 128)`. -/
noncomputable def mxK (d : CellData) (bi : Nat) : Nat :=
  Nat.max (Nat.add (Nat.sub d.kw 1) (Nat.sub (d.mb bi) d.mbits)) (Nat.sub (Nat.add (d.mb bi) (smaxK d bi)) 128)

/-- A-priori bound of every slot `|coefI · 2^(S-L)|` of block `bi`. -/
noncomputable def crudeB (d : CellData) (c : Ctx) (bi : Nat) : Nat :=
  Nat.add
    (Nat.shiftLeft (Nat.mul (Nat.mul (Nat.mul (Nat.add d.nw 1) (Nat.add d.nw 1)) (Nat.pow 4 d.nw))
        (Nat.mul (d.order bi) (Nat.pow 4 (Nat.sub (d.layout bi).2.1 1))))
      (Nat.sub c.S (Nat.add (Nat.mul 2 d.fb) d.nw)))
    (Nat.shiftLeft (Nat.mul (d.order bi) (Nat.pow 4 (mxK d bi))) (Nat.sub c.S (scaleM d bi)))

/-- Block check: single chunks, `L ≤ S`, `nw ≤ N`, `e ≤ 2 mb`, entries below `2^sw`, and the a-priori slot
bound `(N+1) Cb < 2^(W-1)`. -/
noncomputable def w0Ok (d : CellData) (c : Ctx) (bi : Nat) : Bool :=
  Nat.ble (tri (d.order bi)) (d.layout bi).2.2 &&
  Nat.ble (Nat.shiftRight (Nat.mul (d.order bi) (Nat.sub (d.order bi) 1)) 1) (d.layout bi).1 &&
  Nat.ble (d.scaleL bi) c.S && Nat.ble d.nw c.N && decide (d.floorExp ≤ 2 * (d.mb bi : Int)) &&
  Nat.ble (d.layout bi).2.1 (geo d c bi).2.2.1 && Nat.blt (mxK d bi) (geo d c bi).2.2.1 &&
  Nat.blt (Nat.mul (Nat.add c.N 1) (crudeB d c bi)) c.hW

/-- Column `q` of entry TMs `[(0,q), …, (q,q)]`. -/
noncomputable def wCol (d : CellData) (c : Ctx) (bi q : Nat) : List TM :=
  (fun Gb ok0 => mkList (fun p => entryTM c (Nat.add d.nw 1) Gb p ok0) (Nat.add q 1)) (gPackB d c bi q) (w0Ok d c bi)

/-- All entry TMs of block `bi`, column by column (each evaluated once by the kernel). -/
noncomputable def wTab (d : CellData) (c : Ctx) (bi : Nat) : List (List TM) :=
  mkList (fun q => wCol d c bi q) (d.order bi)

/-- Packed W0 TMs of block `bi` on `ℕ` indices (symmetric; zero outside the block). -/
noncomputable def WTp (d : CellData) (c : Ctx) (bi i j : Nat) : TM :=
  cond (Nat.ble i j) (listAt zeroTM (listAt [] (wTab d c bi) j) i) (listAt zeroTM (listAt [] (wTab d c bi) i) j)

end ThomsonCompact.CoeffMap
