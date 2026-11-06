import ThomsonCompact.Packed.Core2

/-!
# H target models (milestones T1–T3): kernel code (Init + `Packed` only)

From the exponent model `sTM ≈ s` and the height model `A ≈ aS ∘ s` only, the Hermite coefficients of the
target `hermitePolynomial s (aS s) m` (both D12 profiles; any profile `m` in canonical order
`[m(-1), m(c3), m(c1), m(c2), m(c0)]`):

* nodes in the source order of the old `sourceNodes` (labels `0..4` = `c0 = a`, `c2`, `c1 = 2a-1`, `c3`, `-1`),
  distances `d = 2 - 2x`, `log d` (verified centers), `1/d` (Newton);
* one formula for every `s ≥ 0` (replaces the entire/quotient branches of `cellcheck.py`):
  `phi = l Ψ(s l)`, `l = -log(d)/2`, `Ψ(z) = (e^z - 1)/z` (series at `z/2^j` + `j` doublings),
  `E = d^(-s/2) = 1 + s phi`; jets `J₁ = E/d`, `J_{k+1}/(k+1)! = (J_k/k!)·(s + 2k)/(d (k+1))` (Lemma 2.5.1);
* confluent divided differences column by column exactly as the old `confluentTable`, every division by a
  node gap through the residual lemma (`divR`), Newton → monomial as `sourceNewtonHorner`;
* accuracy (T3): the whole pipeline runs at the internal order `N + P.dN` (`liftTo` the inputs, one `truncTo` of
  the outputs, the exact tail `Σ_{k>N} |cₖ|` moving into the error), and in the quotient range `E = exp(-(s/2) log d)`
  (`P.expE`), whose height-error propagation is first-order tight.

Mirror: `tools/target_mirror.py` (bit-exact).
-/

namespace ThomsonCompact.Target
open ThomsonCompact.Packed

/-- per-cell parameters (chosen by `tools/target_mirror.py`; every choice is sound) -/
structure Par where
  r2 : Nat     -- ⌊2^S/√2⌋ (checked)
  l2 : Nat     -- ln 2 witness (checked through exp)
  nE : Nat     -- exp terms of the log-constant checks
  jE : Nat     -- squarings of the log-constant checks
  nL : Nat     -- log1p terms
  nP : Nat     -- Ψ series terms
  jP : Nat     -- Ψ doublings
  kN : Nat     -- Newton fuel
  tol : Nat    -- Newton tolerance
  cA : Nat     -- log center of d_A and its log witness
  gA : Bool
  lA : Nat
  cC : Nat     -- log center of d_C and its log witness
  gC : Bool
  lC : Nat
  cD : Nat     -- log center of d_D and its log witness
  gD : Bool
  lD : Nat
  expE : Bool  -- `E = d^(-s/2)` by `exp` (large `s`) instead of `1 + s·phi`
  nX : Nat     -- exp terms / squarings for `E` (when `expE`)
  jX : Nat
  l32 : Nat    -- ln(3/2) witness (Riesz balance)
  nB : Nat     -- exp terms / squarings of the Riesz-balanced node values
  jB : Nat
  mode : Nat   -- 0: jets of `phi`; 1: jets of `2^-ek·E` (then `/(2^-ek·s)`); ≥ 2: Riesz-balanced jets of `γ(s)·E`
  ek : Nat     -- scale `2^-ek` of the mode-1 jets (keeps `2^-ek·s·Hⱼ` in range)
  cR : Nat     -- Riesz balance center `c` (`balancedMultiplier c s`)
  dN : Nat     -- extra internal order: the pipeline runs at order `N + dN`, truncated once at the end

/-- `1/√2` from the witness `r2`, checked: `r2² ≤ 2^(2S-1) < (r2+1)²` -/
def ir2TM (c : Ctx) (r2 : Nat) : TM :=
  let T := constTM c false r2 1
  let X := Nat.pow 2 (Nat.sub (Nat.mul 2 c.S) 1)
  ⟨T.v, T.a, T.s, T.e, T.ok && Nat.ble 1 c.S && Nat.ble (Nat.mul r2 r2) X &&
    Nat.blt X (Nat.mul (Nat.add r2 1) (Nat.add r2 1))⟩

/-- `ln 2` with its verified error -/
def ln2TM (c : Ctx) (P : Par) : TM :=
  let k := logConst c P.nE P.jE (Nat.mul 2 c.twoS) false P.l2
  let T := constTM c false P.l2 k.2
  ⟨T.v, T.a, T.s, T.e, T.ok && k.1⟩

/-- `1 - a` -/
def oneSub (c : Ctx) (A : TM) : TM := addC c false c.twoS 0 (neg c A)

/-- nodes `[c0, c2, c1, c3, -1]` (source order), magnitudes refreshed -/
def nodeTMs (c : Ctx) (IR2 A : TM) : List TM :=
  let w := mul c IR2 (oneSub c A)
  [refresh c A, refresh c (add c (neg c A) w), refresh c (addC c true c.twoS 0 (add c A A)),
    refresh c (neg c (add c A w)), refresh c (constTM c true c.twoS 0)]

/-- `d = 2 - 2x` -/
def distTM (c : Ctx) (X : TM) : TM := refresh c (addC c false (Nat.mul 2 c.twoS) 0 (neg c (add c X X)))

/-! ## `Ψ(z) = (e^z - 1)/z` -/

/-- `1/(i+1)!` for `i < n` -/
def psiCoeffs (n : Nat) : List (Bool × Nat × Nat) := (List.range n).map (fun i => (false, 1, fact (i + 1)))

/-- `Ψ(G)` for `‖G‖ ≤ 1`: `n` terms plus the remainder `|x|ⁿ (n+2)/((n+1)!·(n+1))` -/
def psiSeries (c : Ctx) (n : Nat) (G0 : TM) : TM :=
  let G := refresh c G0
  let P := hornerQ c G (psiCoeffs n)
  let r := Nat.add G.s G.e
  let D := Nat.mul (Nat.mul (Nat.pow c.twoS (Nat.sub n 1)) (fact (n + 1))) (n + 1)
  let rem := Nat.div (Nat.add (Nat.mul (Nat.pow r n) (Nat.add n 2)) (Nat.sub D 1)) D
  ⟨P.v, P.a, P.s, Nat.add P.e rem, P.ok && G.ok && Nat.ble r c.twoS && Nat.blt 0 n⟩

/-- `k` doublings `Ψ(2w) = Ψ(w)·(1 + wΨ(w)/2)` -/
def psiDouble (c : Ctx) : Nat → TM → TM → TM
  | 0, _, P => P
  | k + 1, w, P => psiDouble c k (add c w w)
      (refresh c (mul c P (addC c false c.twoS 0 (smul c false (Nat.pow 2 (Nat.sub c.S 1)) 0 (mul c w P)))))

/-- `Ψ(Z)` by the series at `Z/2^j` and `j` doublings (`j ≤ S`) -/
def psiTM (c : Ctx) (n j : Nat) (Z : TM) : TM :=
  let w := smul c false (Nat.pow 2 (Nat.sub c.S j)) 0 Z
  let R := psiDouble c j w (psiSeries c n w)
  ⟨R.v, R.a, R.s, R.e, R.ok && Nat.ble j c.S && Nat.ble 1 c.S⟩

/-- `j` squarings with exact magnitude resets -/
def sqIterR (c : Ctx) : Nat → TM → TM
  | 0, H => H
  | j + 1, H => sqIterR c j (refresh c (mul c H H))

/-- `exp F = (exp (F/2^j))^(2^j)` with refreshed magnitudes (`j ≤ S`); no bound blow-up for `exp` of
negative arguments -/
def expR (c : Ctx) (n j : Nat) (F : TM) : TM :=
  let R := sqIterR c j (refresh c (expSeries c n (smul c false (Nat.pow 2 (Nat.sub c.S j)) 0 F)))
  ⟨R.v, R.a, R.s, R.e, R.ok && Nat.ble j c.S⟩

/-- `exp(-(s/2)·l)` (`= d^(-s/2)` for `l = log d`) with `expR` -/
def powLR (c : Ctx) (nX jX : Nat) (Lg Sv : TM) : TM :=
  let R := expR c nX jX (neg c (mul c (smul c false (Nat.pow 2 (Nat.sub c.S 1)) 0 Sv) Lg))
  ⟨R.v, R.a, R.s, R.e, R.ok && Nat.ble 1 c.S⟩

/-- `(phi, E)` at a node with `Ld ≈ log d`: `phi = l Ψ(s l)`, `l = -log(d)/2`, and `E = d^(-s/2)`, either as
`1 + s phi` (refreshed: it cancels) or, for large `s` (`expE`), as `exp(-(s/2)·log d)` (no cancellation) -/
def phiE (c : Ctx) (P : Par) (sTM Ld : TM) : TM × TM :=
  let l := smul c true (Nat.pow 2 (Nat.sub c.S 1)) 0 Ld
  let phi := mul c l (psiTM c P.nP P.jP (mul c sTM l))
  (phi, cond P.expE (powLR c P.nX P.jX Ld sTM) (refresh c (addC c false c.twoS 0 (mul c sTM phi))))

/-! ## Jets `J_k(x)/k!` (Lemma 2.5.1) -/

/-- `[V_k, V_{k+1}, …]` (`r` entries), `V_{k+1} = V_k·(s + 2k)·(1/d)/(k+1)` -/
def jetTail (c : Ctx) (sTM Rd : TM) : Nat → Nat → TM → List TM
  | _, 0, _ => []
  | k, r + 1, V => V :: jetTail c sTM Rd (k + 1) r
      (refresh c (smul c false (ratMag c 1 (k + 1)) 1
        (mul c (mul c V (addC c false (Nat.mul (Nat.mul 2 k) c.twoS) 0 sTM)) Rd)))

/-- the first `μ` jets `[phi, E/d, …]` -/
def jetsTM (c : Ctx) (sTM phi E Rd : TM) : Nat → List TM
  | 0 => []
  | μ + 1 => phi :: jetTail c sTM Rd 1 μ (mul c E Rd)

/-- jets of `W = α·E` (`α = 2^-ek` or the Riesz `γ(s)`): `[W, s·W/d, …]` (`= α·s·J_k/k!` for `k ≥ 1`) -/
def jetsW (c : Ctx) (sTM Wv Rd : TM) : Nat → List TM
  | 0 => []
  | μ + 1 => Wv :: jetTail c sTM Rd 1 μ (refresh c (mul c (mul c sTM Wv) Rd))

/-- `ln(3/2)` with its verified error -/
def ln32TM (c : Ctx) (P : Par) : TM :=
  let k := logConst c P.nE P.jE (Nat.mul 3 (Nat.pow 2 (Nat.sub c.S 1))) false P.l32
  let T := constTM c false P.l32 k.2
  ⟨T.v, T.a, T.s, T.e, T.ok && k.1⟩

/-- the head `W` of the mode ≥ 1 jets: `2^-ek·E`, or (Riesz) `exp(-(s/2)·log d + ((s - cR)/2)·log(3/2))/cR`
(the balanced value, computed as one `exp`: nearly constant at the dominant node) -/
def headW (c : Ctx) (P : Par) (sTM Ld L32 E : TM) : TM :=
  cond (Nat.beq P.mode 1) (smul c false (Nat.pow 2 (Nat.sub c.S P.ek)) 0 E)
    (smul c false (ratMag c 1 P.cR) 1 (expR c P.nB P.jB
      (add c (neg c (mul c (smul c false (Nat.pow 2 (Nat.sub c.S 1)) 0 sTM) Ld))
        (mul c (smul c false (Nat.pow 2 (Nat.sub c.S 1)) 0 (addC c true (Nat.mul P.cR c.twoS) 0 sTM)) L32))))

/-! ## Confluent divided differences and Newton → monomial -/

/-- column `k+1` of the confluent table from column `k` (`ls` labels from `start`, `hs` labels from `start+k+1`) -/
def colStep (c : Ctx) (Vs Hs Gs : List (List TM)) (k : Nat) : List Nat → List Nat → List TM → List TM
  | l :: ls, h :: hs, x :: y :: rest =>
    cond (Nat.beq h l) ((Vs.getD l []).getD (k + 1) zeroTM)
      (divR c (add c y (neg c x)) ((Hs.getD h []).getD l zeroTM) ((Gs.getD h []).getD l zeroTM)) ::
      colStep c Vs Hs Gs k ls hs (y :: rest)
  | _, _, _ => []

/-- the Newton coefficients `CT k 0` (heads of the columns) -/
def newtonCoeffs (c : Ctx) (Vs Hs Gs : List (List TM)) (labels : List Nat) : Nat → Nat → List TM → List TM
  | 0, _, _ => []
  | r + 1, k, col => col.headD zeroTM ::
      newtonCoeffs c Vs Hs Gs labels r (k + 1) (colStep c Vs Hs Gs k labels (labels.drop (k + 1)) col)

/-- `x·p` (exactly `-p` at the node `-1`) -/
def timesNode (c : Ctx) (x : TM) (neg1 : Bool) (p : TM) : TM := cond neg1 (neg c p) (mul c x p)

/-- coefficients `i ≥ 1` of `(X - x)·P` -/
def hrest (c : Ctx) (x : TM) (neg1 : Bool) : List TM → List TM
  | p :: q :: rest => refresh c (add c p (neg c (timesNode c x neg1 q))) :: hrest c x neg1 (q :: rest)
  | L => L

/-- coefficients of `C ci + (X - x)·P` -/
def hstep (c : Ctx) (x : TM) (neg1 : Bool) (ci : TM) : List TM → List TM
  | [] => [ci]
  | p :: ps => refresh c (add c ci (neg c (timesNode c x neg1 p))) :: hrest c x neg1 (p :: ps)

/-- monomial coefficients of the Newton form (`sourceNewtonHorner`) -/
def hornerN (c : Ctx) (Xs : List TM) : List Nat → List TM → List TM
  | l :: ls, ci :: cs => hstep c (Xs.getD l zeroTM) (Nat.beq l 4) ci (hornerN c Xs ls cs)
  | _, _ => []

/-! ## Assembly -/

/-- source-order multiplicities `[c0, c2, c1, c3, -1]` from canonical `[m(-1), m(c3), m(c1), m(c2), m(c0)]` -/
def srcMult (m : List Nat) : List Nat := [m.getD 4 0, m.getD 3 0, m.getD 2 0, m.getD 1 0, m.getD 0 0]

/-- expanded labels (`profileLabel` of the source multiplicities) -/
def labelsOf (μ : List Nat) : List Nat :=
  List.replicate (μ.getD 0 0) 0 ++ List.replicate (μ.getD 1 0) 1 ++ List.replicate (μ.getD 2 0) 2 ++
    List.replicate (μ.getD 3 0) 3 ++ List.replicate (μ.getD 4 0) 4

/-- `log d` at the five nodes (`d_B = 2 d_A`, `d_{-1} = 4`) -/
def ldsOf (c : Ctx) (P : Par) (L2 : TM) (Ds : List TM) : List TM :=
  let LdA := logTM c P.nL P.nE P.jE P.cA P.gA P.lA (Ds.getD 0 zeroTM)
  [LdA, logTM c P.nL P.nE P.jE P.cC P.gC P.lC (Ds.getD 1 zeroTM), add c LdA L2,
    logTM c P.nL P.nE P.jE P.cD P.gD P.lD (Ds.getD 3 zeroTM), add c L2 L2]

/-- `1/d` at the five nodes -/
def rdsOf (c : Ctx) (P : Par) (Ds : List TM) : List TM :=
  let RdA := invN c P.kN P.tol (Ds.getD 0 zeroTM)
  [RdA, invN c P.kN P.tol (Ds.getD 1 zeroTM), smul c false (Nat.pow 2 (Nat.sub c.S 1)) 0 RdA,
    invN c P.kN P.tol (Ds.getD 3 zeroTM), constTM c false (Nat.pow 2 (Nat.sub c.S 2)) 0]

/-- the jet lists of the five nodes -/
def vsOf (c : Ctx) (P : Par) (sTM : TM) (Lds Rds : List TM) (μ : List Nat) : List (List TM) :=
  (List.range 5).map (fun l =>
    let pe := phiE c P sTM (Lds.getD l zeroTM)
    cond (Nat.beq P.mode 0) (jetsTM c sTM pe.1 pe.2 (Rds.getD l zeroTM) (μ.getD l 0))
      (jetsW c sTM (headW c P sTM (Lds.getD l zeroTM) (ln32TM c P) pe.2) (Rds.getD l zeroTM) (μ.getD l 0)))

/-- node gaps `x_h - x_l` -/
def hsOf (c : Ctx) (Xs : List TM) : List (List TM) :=
  Xs.map (fun Xh => Xs.map (fun Xl => refresh c (add c Xh (neg c Xl))))

/-- reciprocal node gaps -/
def gsOf (c : Ctx) (P : Par) (Hs : List (List TM)) : List (List TM) := Hs.map (fun row => row.map (invN c P.kN P.tol))

/-- the Hermite coefficients `0 … D` of the target at the cell (`m` canonical, as a list) -/
def targetCoeffs0 (c : Ctx) (P : Par) (m : List Nat) (sTM A : TM) : List TM :=
  let μ := srcMult m
  let labels := labelsOf μ
  let Xs := nodeTMs c (ir2TM c P.r2) A
  let Ds := Xs.map (distTM c)
  let Vs := vsOf c P sTM (ldsOf c P (ln2TM c P) Ds) (rdsOf c P Ds) μ
  let Hs := hsOf c Xs
  let Gs := gsOf c P Hs
  hornerN c Xs labels
    (newtonCoeffs c Vs Hs Gs labels labels.length 0 (labels.map (fun l => (Vs.getD l []).getD 0 zeroTM)))

/-! ## Unit and Riesz-balanced outputs -/

/-- unit balance: the Hermite coefficients `1 … D` (mode 1: divide by `2^-ek·s` by the residual lemma) -/
def targetCoeffsU0 (c : Ctx) (P : Par) (m : List Nat) (sTM A : TM) : List TM :=
  let out := targetCoeffs0 c P m sTM A
  cond (Nat.beq P.mode 1)
    (let sS := smul c false (Nat.pow 2 (Nat.sub c.S P.ek)) 0 sTM
     let IS := invN c P.kN P.tol sS
     out.map (fun X => divR c X sS IS))
    out

/-! ## Internal order: the whole pipeline at order `N + dN`, one truncation at the end -/

/-- a TM of `c` (order `N`) as a TM of `c2` (order `≥ N`, same `S B W`): the biased digits re-centred -/
def liftTo (c c2 : Ctx) (A : TM) : TM :=
  ⟨Nat.land (Nat.add (Nat.land (Nat.add A.v c.hb) c.maskK) (Nat.sub c2.twoK c.hb)) c2.maskK, A.a, A.s, A.e, A.ok⟩

/-- a TM of `c2` truncated to the order of `c` (`≤` that of `c2`): the exact tail `Σ_{k>N} |cₖ|` moves into the
error, magnitudes exact; the flag `g` is and-ed into `ok` -/
def truncTo (c2 c : Ctx) (g : Bool) (T : TM) : TM :=
  let P := pabs c2 T
  let a := Nat.land P c.maskWm
  ⟨Nat.land (Nat.add (Nat.land (Nat.land (Nat.add T.v c2.hb) c2.maskK) c.maskWm) (Nat.sub c.twoK c.hb)) c.maskK,
   a, ssum c a, Nat.add T.e (ssum c2 (Nat.shiftRight P c.wm)), T.ok && g⟩

/-- the internal context of order `N + dN` -/
def innerCtx (c : Ctx) (dN : Nat) : Ctx := mkCtx (Nat.add c.N dN) c.S c.B c.W

/-- the internal order is admissible: `N + dN + 1 ≤ 2^B` -/
def innerOk (c : Ctx) (dN : Nat) : Bool := Nat.ble (Nat.add (Nat.add c.N dN) 1) c.twoB

/-- Hermite coefficients `0 … D` (all modes), computed at order `N + P.dN` and truncated to `N` -/
def targetCoeffs (c : Ctx) (P : Par) (m : List Nat) (sTM A : TM) : List TM :=
  (targetCoeffs0 (innerCtx c P.dN) P m (liftTo c (innerCtx c P.dN) sTM) (liftTo c (innerCtx c P.dN) A)).map
    (truncTo (innerCtx c P.dN) c (innerOk c P.dN))

/-- unit-balance coefficients (`targetCoeffsU0` at order `N + P.dN`, truncated to `N`) -/
def targetCoeffsU (c : Ctx) (P : Par) (m : List Nat) (sTM A : TM) : List TM :=
  (targetCoeffsU0 (innerCtx c P.dN) P m (liftTo c (innerCtx c P.dN) sTM) (liftTo c (innerCtx c P.dN) A)).map
    (truncTo (innerCtx c P.dN) c (innerOk c P.dN))

/-- all flags of a list of TMs -/
def allOkL : List TM → Bool
  | [] => true
  | T :: L => T.ok && allOkL L

end ThomsonCompact.Target
