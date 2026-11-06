import ThomsonCompact.CoeffMap.RFCodec
import ThomsonCompact.CoeffMap.ListUtil
import ThomsonCompact.CoeffMap.MomentProg

/-!
# Raw scalar coordinates of any degree: computable mirror (Init only; F2e)

The old raw scalar tensors (`RawScalarTensors.D<2d>_*`) are only partly built for D14/D16. Instead of their catalogue,
the coefficients of `rawScalarCoordinates s` (old `RawScalarCatalogueSupport`) are computed here from the definition:

* sparse integer polynomials `SP` in the invariant coordinates `X0, X1, X2` (terms `(tag, coefficient)`, not
  necessarily normalized), `spMerge` (sorted merge by `tkey`, equal tags added: keeps the power sums normalized),
* the power sums `rawInvariantPowerSum`, `rawInvariantPairPowerSum` by their 3-term recurrences (`psSeq`),
* `par3 i j k = 3 · rawParityCoordinates i j k`, `even3`, `odd3`, the fixed weights (determinant, discriminant,
  standard pairing `· 81`), and `rscZ s = famDen s · rawScalarCoordinates s` (`famDen` = 1, 1, 81, 3, 3).

Soundness (`spEval (rscZ …) = famDen • rawScalarCoordinates …`): `CoeffMap.Deg.PolySound`. Bit-exact Python mirror:
`CoeffMap/Deg/gen/degdata.py` (`rsc`).
-/

namespace ThomsonCompact.CoeffMap.Deg

/-- Tags `(i, j, k)` (the old `Tag`). -/
abbrev T3 := Nat × Nat × Nat

/-- Sparse integer polynomial: terms `(tag, coefficient)`. -/
abbrev SP := List (T3 × Int)

def tadd (t u : T3) : T3 := (Nat.add t.1 u.1, Nat.add t.2.1 u.2.1, Nat.add t.2.2 u.2.2)

/-- Order key (additive; injective on tags with components `< 64`). -/
def tkey (t : T3) : Nat := Nat.add t.1 (Nat.add (Nat.mul 64 t.2.1) (Nat.mul 4096 t.2.2))

def teq (t u : T3) : Bool := Nat.beq t.1 u.1 && (Nat.beq t.2.1 u.2.1 && Nat.beq t.2.2 u.2.2)

def spShift (t : T3) (L : SP) : SP := L.map fun e => (tadd e.1 t, e.2)

def spScale (c : Int) (L : SP) : SP := L.map fun e => (e.1, c * e.2)

def spMul (L M : SP) : SP := L.flatMap fun e => M.map fun f => (tadd e.1 f.1, e.2 * f.2)

/-- Merge of two `tkey`-sorted lists (fuel; equal tags are added, zero sums dropped). With too little fuel the rest
is appended, which is still the same polynomial. -/
def spMergeF : Nat → SP → SP → SP :=
  Nat.rec (motive := fun _ => SP → SP → SP) (fun L M => L ++ M) (fun _ ih L M =>
    List.casesOn (motive := fun _ => SP) L M (fun a L' =>
      List.casesOn (motive := fun _ => SP) M (a :: L') (fun b M' =>
        cond (Nat.blt (tkey a.1) (tkey b.1)) (a :: ih L' (b :: M'))
          (cond (Nat.blt (tkey b.1) (tkey a.1)) (b :: ih (a :: L') M')
            (cond (teq a.1 b.1)
              (cond (decide (a.2 + b.2 = 0)) (ih L' M') ((a.1, a.2 + b.2) :: ih L' M'))
              (a :: b :: ih L' M'))))))

def spMerge (L M : SP) : SP := spMergeF (Nat.add L.length M.length) L M

/-! ## Power sums -/

/-- The sequence `x.1, (step x).1, (step² x).1, …` (`n` terms). -/
def seqOf (step : SP × SP × SP → SP × SP × SP) (n : Nat) (x : SP × SP × SP) : List SP :=
  (Nat.rec (motive := fun _ => SP × SP × SP → List SP) (fun _ => [])
    (fun _ ih y => y.1 :: ih (step y)) n) x

/-- `P(n+3) = X0 P(n+2) - X1 P(n+1) + X2 P(n)` (`rawInvariantPowerSum`). -/
def psStep (x : SP × SP × SP) : SP × SP × SP :=
  (x.2.1, x.2.2, spMerge (spMerge (spShift (1, 0, 0) x.2.2) (spScale (-1) (spShift (0, 1, 0) x.2.1)))
    (spShift (0, 0, 1) x.1))

/-- `P(n+3) = X1 P(n+2) - X0 X2 P(n+1) + X2² P(n)` (`rawInvariantPairPowerSum`). -/
def ppsStep (x : SP × SP × SP) : SP × SP × SP :=
  (x.2.1, x.2.2, spMerge (spMerge (spShift (0, 1, 0) x.2.2) (spScale (-1) (spShift (1, 0, 1) x.2.1)))
    (spShift (0, 0, 2) x.1))

def ps0 : SP × SP × SP := ([((0, 0, 0), 3)], [((1, 0, 0), 1)], [((2, 0, 0), 1), ((0, 1, 0), -2)])
def pps0 : SP × SP × SP := ([((0, 0, 0), 3)], [((0, 1, 0), 1)], [((0, 2, 0), 1), ((1, 0, 1), -2)])

/-- Power sums `0 … n-1`. -/
noncomputable def psTab (n : Nat) : List SP := seqOf psStep n ps0
noncomputable def ppsTab (n : Nat) : List SP := seqOf ppsStep n pps0

/-- `3 · rawParityCoordinates i j k` (power sums from the tables `P`, `PP`). -/
noncomputable def par3 (P PP : List SP) (i j k : Nat) : SP :=
  (List.range (Nat.add j 1)).flatMap fun l =>
    spScale (cond (Nat.beq (Nat.land l 1) 0) (1 : Int) (-1) * Int.ofNat (chooseI j l))
      (cond (Nat.ble k (Nat.add i l)) (spShift (Nat.sub j l, 0, k) (listAt [] P (Nat.sub (Nat.add i l) k)))
        (spShift (Nat.sub j l, 0, Nat.add i l) (listAt [] PP (Nat.sub k (Nat.add i l)))))

/-- `3 · rawEvenCoordinates t`. -/
noncomputable def even3 (P PP : List SP) (t : T3) : SP :=
  par3 P PP t.1 t.2.1 t.2.2 ++ spScale (-1) (par3 P PP (Nat.add t.1 2) t.2.1 t.2.2)

/-- `3 · rawOddCoordinates t`. -/
noncomputable def odd3 (P PP : List SP) (t : T3) : SP :=
  even3 P PP (t.1, Nat.add t.2.1 2, t.2.2) ++ spScale (-4) (even3 P PP (t.1, t.2.1, Nat.add t.2.2 1))

/-! ## Fixed weights and the raw scalar coordinates -/

/-- `rawDeterminantCoordinates = 1 - X0² + 2 X1 + 2 X2`. -/
def detSP : SP := [((0, 0, 0), 1), ((2, 0, 0), -1), ((0, 1, 0), 2), ((0, 0, 1), 2)]

/-- `rawSymmetricWeight det`. -/
def wSP (det : Bool) : SP := cond det detSP [((0, 0, 0), 1)]

/-- `rawDiscriminantCoordinates`. -/
def discSP : SP := [((2, 2, 0), 1), ((0, 3, 0), -4), ((3, 0, 1), -4), ((0, 0, 2), -27), ((1, 1, 1), 18)]

/-- `81 · rawStandardCoordinates p q`. -/
def std81 (p q : Bool) : SP :=
  cond (p && q) [((4, 0, 0), 4), ((2, 1, 0), -24), ((0, 2, 0), 36)]
    (cond (p || q) [((3, 0, 0), 12), ((1, 1, 0), -54), ((0, 0, 1), 162)] [((2, 0, 0), 36), ((0, 1, 0), -108)])

/-- Denominator of family `f` (`rscZ = famDen · rawScalarCoordinates`). -/
def famDen (f : Nat) : Nat := cond (Nat.beq f 2) 81 (cond (Nat.ble 3 f) 3 1)

/-- `famDen family · rawScalarCoordinates ⟨family, det, leftQ, rightQ, tag⟩` (power sums from `P`, `PP`). -/
noncomputable def rscZ (P PP : List SP) (family : Nat) (det lq rq : Bool) (t : T3) : SP :=
  cond (Nat.beq family 0) (spShift t (wSP det))
    (cond (Nat.beq family 1) (spShift t (spMul (wSP det) discSP))
      (cond (Nat.beq family 2) (spShift t (spMul (wSP det) (std81 lq rq)))
        (cond (Nat.beq family 3) (even3 P PP t)
          (cond (Nat.beq family 4) (odd3 P PP t) []))))

/-! ## Coefficients at the retained coordinates -/

/-- Accumulators `(Σ⁺ c 2^(W r), Σ⁻ |c| 2^(W r), Σ |c|)` over the terms with `ridx t < nc`, `r = ridx t`. -/
noncomputable def denseAcc (ridx : T3 → Nat) (nc W : Nat) (L : SP) : Nat × Nat × Nat :=
  List.rec (motive := fun _ => Nat × Nat × Nat) (0, 0, 0) (fun e _ ih =>
    (fun r => cond (Nat.blt r nc)
      (cond (decide (e.2 < 0))
        (ih.1, Nat.add ih.2.1 (Nat.shiftLeft e.2.natAbs (Nat.mul W r)), Nat.add ih.2.2 e.2.natAbs)
        (Nat.add ih.1 (Nat.shiftLeft e.2.natAbs (Nat.mul W r)), ih.2.1, Nat.add ih.2.2 e.2.natAbs))
      ih) (ridx e.1)) L

/-! ## Fused accumulation (kernel path of the one-time checks; `Nat` only in the hot loop) -/

/-- Sign-magnitude form of a sparse polynomial. -/
def smOf (L : SP) : List (T3 × Bool × Nat) := L.map fun e => (e.1, decide (e.2 < 0), e.2.natAbs)

/-- Add the terms `±c · zᵢ X^(tᵢ + m)` of a sign-magnitude list to the accumulators (`r = ridx (tᵢ + m) < nc`). -/
noncomputable def accSM (ridx : T3 → Nat) (nc W : Nat) (neg : Bool) (c : Nat) (m : T3) (L : List (T3 × Bool × Nat))
    (acc : Nat × Nat × Nat) : Nat × Nat × Nat :=
  List.rec (motive := fun _ => Nat × Nat × Nat → Nat × Nat × Nat) (fun a => a) (fun e _ ih a =>
    ih ((fun r v => cond (Nat.blt r nc)
        (cond (xor neg e.2.1) (a.1, Nat.add a.2.1 (Nat.shiftLeft v (Nat.mul W r)), Nat.add a.2.2 v)
          (Nat.add a.1 (Nat.shiftLeft v (Nat.mul W r)), a.2.1, Nat.add a.2.2 v)) a)
      (ridx (tadd e.1 m)) (Nat.mul c e.2.2))) L acc

/-- `± c · 3 rawParityCoordinates i j k` added to the accumulators (power sums `P`, `PP` in sign-magnitude form). -/
noncomputable def parAcc (ridx : T3 → Nat) (nc W : Nat) (P PP : List (List (T3 × Bool × Nat))) (neg : Bool) (c i j k : Nat)
    (acc : Nat × Nat × Nat) : Nat × Nat × Nat :=
  (List.range (Nat.add j 1)).foldl (fun a l =>
    accSM ridx nc W (xor neg (Nat.beq (Nat.land l 1) 1)) (Nat.mul c (chooseI j l))
      (cond (Nat.ble k (Nat.add i l)) (Nat.sub j l, 0, k) (Nat.sub j l, 0, Nat.add i l))
      (cond (Nat.ble k (Nat.add i l)) (listAt [] P (Nat.sub (Nat.add i l) k)) (listAt [] PP (Nat.sub k (Nat.add i l))))
      a) acc

/-- `± c · 3 rawEvenCoordinates t` added to the accumulators. -/
noncomputable def evenAcc (ridx : T3 → Nat) (nc W : Nat) (P PP : List (List (T3 × Bool × Nat))) (neg : Bool) (c : Nat)
    (t : T3) (acc : Nat × Nat × Nat) : Nat × Nat × Nat :=
  parAcc ridx nc W P PP (!neg) c (Nat.add t.1 2) t.2.1 t.2.2 (parAcc ridx nc W P PP neg c t.1 t.2.1 t.2.2 acc)

/-- The dense accumulators of `rscZ … family det lq rq t` (power sums in sign-magnitude form). -/
noncomputable def rscAcc (ridx : T3 → Nat) (nc W : Nat) (P PP : List (List (T3 × Bool × Nat))) (family : Nat)
    (det lq rq : Bool) (t : T3) : Nat × Nat × Nat :=
  cond (Nat.beq family 0) (accSM ridx nc W false 1 t (smOf (wSP det)) (0, 0, 0))
    (cond (Nat.beq family 1) (accSM ridx nc W false 1 t (smOf (spMul (wSP det) discSP)) (0, 0, 0))
      (cond (Nat.beq family 2) (accSM ridx nc W false 1 t (smOf (spMul (wSP det) (std81 lq rq))) (0, 0, 0))
        (cond (Nat.beq family 3) (evenAcc ridx nc W P PP false 1 t (0, 0, 0))
          (cond (Nat.beq family 4)
            (evenAcc ridx nc W P PP true 4 (t.1, t.2.1, Nat.add t.2.2 1)
              (evenAcc ridx nc W P PP false 1 (t.1, Nat.add t.2.1 2, t.2.2) (0, 0, 0)))
            (0, 0, 0)))))

/-- Coefficient at coordinate `r` from the accumulators (exact when `Σ |c| < 2^W`). -/
def denseCoef (W : Nat) (V : Nat × Nat × Nat) (r : Nat) : Int :=
  Int.subNatNat (slotAt W V.1 r) (slotAt W V.2.1 r)

end ThomsonCompact.CoeffMap.Deg
