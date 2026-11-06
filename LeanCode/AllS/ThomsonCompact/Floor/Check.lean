import ThomsonCompact.Floor.Kernel
/-!
# F3 leaf checks (Init only)

The `Bool` functions evaluated by the leaves (`decide +kernel`). Table data (per degree) and cell data enter
through accessors. Fixed parameters: jet order `K = 8`, height centre bits `hb = 16`, output scale `2^-256`
(`YSC`), centre scale `2^-128`, error scale `2^-256`, short metric `Z = Zi 2^-32`.
-/

namespace ThomsonCompact.Floor

/-! ## Data access -/

/-- Slot `m` of a chunked vector (`64` slots of width `w` per chunk). -/
def vget (w : Nat) (ch : Nat → Nat) (m : Nat) : Nat := slot w (ch (Nat.shiftRight m 6)) (Nat.land m 63)

/-- Records of a chunk: header `w` (8 bits), `L` (8 bits), then `16 + L w` further bits (`fuel` records). -/
noncomputable def parseChunk (hd fuel : Nat) : Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun _ ih c => Bool.rec
      (Nat.land c (mask (Nat.add hd (Nat.mul (recL c) (recW c)))) ::
        ih (Nat.shiftRight c (Nat.add hd (Nat.mul (recL c) (recW c)))))
      [] (Nat.beq c 0)) fuel

/-- All entry records of a row stored as chunks. -/
noncomputable def records (chunks : List Nat) : List Nat := chunks.flatMap (parseChunk 32 64)

def allSome {α : Type} : List (Option α) → Option (List α)
  | [] => some []
  | x :: xs => match x, allSome xs with
    | some a, some l => some (a :: l)
    | _, _ => none

/-- Degree table. `row j` lists the record chunks of row `j`. -/
structure Tab where
  n : Nat
  W : Nat
  hdr : Nat → Nat
  den : Nat → Nat
  row : Nat → List Nat

def K : Nat := 8
def hb : Nat := 16
def YSC : Nat := 256
def Sc : Nat := 128
def Se : Nat := 256

/-- `V` list of the box. -/
noncomputable def boxV (T : Tab) (mc : Nat) : List Nat :=
  vlist (Nat.add mc (Nat.shiftLeft 1 T.W)) hb T.n

/-- Rows `j0 … j0 + r - 1` of a block. -/
noncomputable def blockRows (T : Tab) (mc Y j0 r : Nat) : Option (List RowD) :=
  allSome ((List.range r).map fun i =>
    rowData T.W Y K hb mc (boxV T mc) (T.hdr (Nat.add j0 i)) (T.den (Nat.add j0 i)) (records (T.row (Nat.add j0 i))))

/-- Signed short-metric rows. -/
def zMatrix (nb wz : Nat) (zrows : List Nat) : List (List Int) := zrows.map (decodeSM wz nb)

/-! ## Leaf checks -/

/-- Power (or control) columns of one block: every computed bound is at most its claim (scale `2^-YSC`). -/
noncomputable def checkColumns (T : Tab) (mc Y j0 r nb wz : Nat) (zrows : List Nat) (cols : List (Nat → Nat))
    (claims : List Nat) : Bool :=
  match blockRows T mc Y j0 r with
  | none => false
  | some rs =>
    let cd := commonDen (sigmas hb T.n Sc 1 1 rs)
    let cc := congCoeffs (zMatrix nb wz zrows) nb rs cd.2
    (cols.zip claims).all fun x =>
      Nat.ble (columnBound T.W Y YSC T.n K nb x.1 cd.1 cc rs) x.2

/-- Error part of one block (`dirs`: direction columns with value `W num / den`, radii `herr`; `errAt` box radii). -/
noncomputable def checkError (T : Tab) (mc Y j0 r nb wz : Nat) (zrows : List Nat) (errAt : Nat → Nat)
    (dirs : List ((Nat → Nat) × Nat × Nat)) (herr : List Nat) (claim : Nat) : Bool :=
  match blockRows T mc Y j0 r with
  | none => false
  | some rs =>
    Nat.ble (young (absCong (zMatrix nb wz zrows)
      (matFromRows nb (rs.map (errorRow T.W Y YSC Se hb T.n errAt dirs herr))))) claim

/-- Short metric: `θ` numerator at scale `2^-(32 + mb)`, with the side conditions `bits ≤ mb`,
`0 ≤ mb + ex_i` and the data shapes. -/
def checkTheta (nb wz bits mb : Nat) (zrows : List Nat) (ex kl : List Int) (claim : Nat) : Bool :=
  Nat.ble (thetaNum (zMatrix nb wz zrows) nb bits mb ex kl (Nat.add 32 mb)) claim &&
    Nat.ble bits mb && ex.all (fun e => decide (0 ≤ (mb : Int) + e)) &&
    Nat.beq ex.length nb && Nat.beq zrows.length nb

/-- Totals and gap: `Σ γ_k + η ≤ γ` and `γ 2^-YSC < 2^-E (1 - θ 2^-sc)`. -/
def checkTotal (gk : List Nat) (eta gamma theta sc E : Nat) : Bool :=
  Nat.ble (Nat.add (gk.foldl Nat.add 0) eta) gamma &&
    Nat.blt (Nat.shiftLeft gamma (Nat.add sc E)) (Nat.shiftLeft (Nat.sub (Nat.shiftLeft 1 sc) theta) YSC) &&
    Nat.blt theta (Nat.shiftLeft 1 sc)

end ThomsonCompact.Floor

namespace ThomsonCompact.Floor

/-! ## Residual and center gates (`Residual12.gate`, `Residual12.center_gate`)

A dyadic interval model `(lo, hi, e)` stands for the `QModel` with coefficients `[lo_k, hi_k] 2^-S` and error
`e 2^-S`. Target directions are `q_ij = qn_ij / 3`; residual centres are `C_ik 2^-128`, radii `Er_i 2^-S`. -/

structure DQ where
  lo : List Int
  hi : List Int
  e : Nat

def zget1 (L : List Int) (k : Nat) : Int := L.getD k 0

/-- Coefficient `k` of coordinate `i`: `3 Rlo ≤ Σ_j min(qn lo, qn hi) - 3 Σ_b hi_b` and the mirror inequality. -/
def gateCoeff (H : List DQ) (qrow : List Int) (Bs : List DQ) (R : DQ) (k : Nat) : Bool :=
  decide (3 * zget1 R.lo k ≤
      sumZ H.length (fun j => min (zget1 qrow j * zget1 (H.getD j ⟨[], [], 0⟩).lo k)
        (zget1 qrow j * zget1 (H.getD j ⟨[], [], 0⟩).hi k)) -
      3 * sumZ Bs.length (fun b => zget1 (Bs.getD b ⟨[], [], 0⟩).hi k)) &&
  decide (sumZ H.length (fun j => max (zget1 qrow j * zget1 (H.getD j ⟨[], [], 0⟩).lo k)
        (zget1 qrow j * zget1 (H.getD j ⟨[], [], 0⟩).hi k)) -
      3 * sumZ Bs.length (fun b => zget1 (Bs.getD b ⟨[], [], 0⟩).lo k) ≤ 3 * zget1 R.hi k)

/-- `StructuredResidualGate` for all coordinates `i < r` and coefficients `k ≤ N`. -/
def checkGate (N r : Nat) (H : List DQ) (q : List (List Int)) (B : List (List DQ)) (R : List DQ) : Bool :=
  (List.range r).all fun i =>
    (List.range (N + 1)).all (fun k => gateCoeff H (q.getD i []) (B.getD i []) (R.getD i ⟨[], [], 0⟩) k) &&
    Nat.ble (sumN (B.getD i []).length (fun b => ((B.getD i []).getD b ⟨[], [], 0⟩).e)) (R.getD i ⟨[], [], 0⟩).e

/-- `StructuredCenterGate`: `Σ_k max(|lo_k - C_k 2^(S-128)|, |hi_k - C_k 2^(S-128)|) + e ≤ Er` per coordinate. -/
def checkCenter (S N r : Nat) (R : List DQ) (C : List (List Int)) (Er : List Nat) : Bool :=
  (List.range r).all fun i =>
    Nat.ble (Nat.add (sumN (N + 1) fun k =>
        Nat.max (zget1 (R.getD i ⟨[], [], 0⟩).lo k - zget1 (C.getD i []) k * (2 : Int) ^ (S - 128)).natAbs
          (zget1 (R.getD i ⟨[], [], 0⟩).hi k - zget1 (C.getD i []) k * (2 : Int) ^ (S - 128)).natAbs)
      (R.getD i ⟨[], [], 0⟩).e) (Er.getD i 0) && Nat.ble 128 S

end ThomsonCompact.Floor
