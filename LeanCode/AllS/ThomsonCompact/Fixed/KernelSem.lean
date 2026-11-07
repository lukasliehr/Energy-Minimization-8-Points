import ThomsonCompact.Fixed.Kernel

/-!
# Fixed right-inverse tables: one-time semantic checks (Init only; workstream F4)

Bool checkers for the facts that connect the kernel data with the canonical columns (soundness:
`Fixed.SoundSem`; mirror: `tools/f4_export.py`):

* `rtagOk`: the retained tag codes are pairwise distinct and none is flagged non-retained;
* `dcOk`: `Δc_k = S_{b,r} S_{b,c} rden_b` for every output;
* `denOk`: every RF denominator divides a block denominator, `den_d · cof_d = ρ_d · δ_{b_d}` at `2^R`;
* `rfOk`: every scalar κ entry is its RF record times the block denominator,
  `num · scD · S · δ_b = κ · scN · den` at `2^R`;
* `facOk`: `Q = ± Π f_r^{e_r}` at `2^R` (factor records), with per-check ℓ1 bounds below `2^R / 2`.
-/

namespace ThomsonCompact.Fixed

/-! ## Retained tags -/

/-- `notRetained D (rtag i) = false` for `i < n`, and `rtag j ≠ rtag i` for `j < i < n`. -/
noncomputable def rtagOk (L : LTab) (n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => ih && not (notRetained L.D (L.rtag i)) &&
    Nat.rec (motive := fun _ => Bool) true (fun j ih2 => ih2 && not (Nat.beq (L.rtag j) (L.rtag i))) i) n

/-! ## Signed values -/

/-- Equality of signed values (zero has both signs). -/
noncomputable def seq (x y : Bool × Nat) : Bool :=
  Bool.rec (Nat.beq x.2 y.2) (Nat.beq x.2 0 && Nat.beq y.2 0) (xor x.1 y.1)

/-- Product of signed values. -/
def smulS (x y : Bool × Nat) : Bool × Nat := (xor x.1 y.1, Nat.mul x.2 y.2)

/-- `e`-th power of a signed value. -/
def spow (x : Bool × Nat) (e : Nat) : Bool × Nat := (x.1 && Nat.beq (Nat.land e 1) 1, Nat.pow x.2 e)

/-- Header check of one polynomial record: `1 ≤ w ≤ wm`, `L ≤ Lm`. -/
def recOk (Lm wm x : Nat) : Bool :=
  Nat.ble 1 (Nat.land (Nat.shiftRight x 20) 255) && Nat.ble (Nat.land (Nat.shiftRight x 20) 255) wm &&
    Nat.ble (Nat.land (Nat.shiftRight x 12) 255) Lm

/-- ℓ1 bound `L · 2^(w-1)` from the record's own header. -/
def ownBound (x : Nat) : Nat := recBound (Nat.land (Nat.shiftRight x 12) 255) (Nat.land (Nat.shiftRight x 20) 255)

/-! ## Semantic data -/

/-- Column scales, raw denominators, RF records and Q factors of one degree. -/
structure STab where
  /-- column scale `S_{b,j}` -/
  sc : Nat → Nat → Nat
  /-- raw-tensor denominator `rden_b` -/
  rd : Nat → Nat
  /-- RF record `k`: numerator (polynomial record), its scale, its denominator index -/
  rnum : Nat → Nat
  rsc : Nat → Nat
  rdi : Nat → Nat
  /-- RF denominator `d`: record, scale, cofactor record, `ρ` (sign bit 0, magnitude `>> 1`), block -/
  rden : Nat → Nat
  rdsc : Nat → Nat
  rcof : Nat → Nat
  rrho : Nat → Nat
  rblk : Nat → Nat
  nden : Nat
  /-- RF record of block `b`, column `j`, raw row `u` -/
  col : Nat → Nat → Nat → Nat
  /-- columns and raw rows of the scalar blocks -/
  ncol : Nat → Nat
  nraw : Nat → Nat
  /-- header bounds: numerators, denominators, cofactors -/
  LN : Nat
  wN : Nat
  LD : Nat
  wD : Nat
  LC : Nat
  wC : Nat
  /-- Q factors: records, exponents, count, overall sign -/
  fac : Nat → Nat
  fexp : Nat → Nat
  nfac : Nat
  fsgn : Bool

/-- `Δc_k = S_{b,r} S_{b,c} rden_b` for the outputs `k < n`. -/
noncomputable def dcOk (G : GTab) (L : LTab) (S : STab) (n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => ih &&
    (fun oi => Nat.beq (fld (G.inf k) 256 64)
        (Nat.mul (Nat.mul (S.sc (Nat.land oi 255) (Nat.land (Nat.shiftRight oi 8) 255))
          (S.sc (Nat.land oi 255) (Nat.land (Nat.shiftRight oi 16) 255))) (S.rd (Nat.land oi 255))))
      (L.oinfo k)) n

/-- Every RF denominator `d < nden`: headers, `scD ≥ 1`, `ρ ≠ 0`, `den · cof = ρ δ_b` at `2^R` with its bound. -/
noncomputable def denOk (R : Nat) (G : GTab) (S : STab) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun d ih => ih &&
    recOk S.LD S.wD (S.rden d) && recOk S.LC S.wC (S.rcof d) && Nat.ble 1 (S.rdsc d) &&
    Nat.ble 1 (Nat.shiftRight (S.rrho d) 1) &&
    seq (smulS (polyVal R (S.rden d)) (polyVal R (S.rcof d)))
      (smulS (Nat.beq (Nat.land (S.rrho d) 1) 1, Nat.shiftRight (S.rrho d) 1)
        (lookV (S.rblk d) (decPolyVec R G.blc G.bln 0))) &&
    Nat.blt (Nat.mul 2 (Nat.add (Nat.mul (recBound S.LD S.wD) (recBound S.LC S.wC))
      (Nat.mul (Nat.shiftRight (S.rrho d) 1) (recBound G.LB G.wB)))) (Nat.shiftLeft 1 R)) S.nden

/-- One scalar κ entry `(b, j, u)` against its RF record. -/
noncomputable def rfEntOk (R : Nat) (G : GTab) (L : LTab) (S : STab) (LK wK b j u : Nat) : Bool :=
  (fun k => (fun d =>
    recOk S.LN S.wN (S.rnum k) && Nat.ble 1 (S.rsc k) && Nat.ble 1 (S.sc b j) && Nat.blt d S.nden &&
    seq (smulS (smulS (polyVal R (S.rnum k)) (false, Nat.mul (S.rdsc d) (S.sc b j)))
        (lookV b (decPolyVec R G.blc G.bln 0)))
      (smulS (smulS (lookV u (decPolyVec R (L.kc b j) (L.kn b j) 0)) (false, S.rsc k)) (polyVal R (S.rden d))) &&
    Nat.blt (Nat.mul 2 (Nat.add (Nat.mul (Nat.mul (S.rdsc d) (S.sc b j)) (Nat.mul (recBound S.LN S.wN) (recBound G.LB G.wB)))
      (Nat.mul (S.rsc k) (Nat.mul (recBound LK wK) (recBound S.LD S.wD))))) (Nat.shiftLeft 1 R))
    (S.rdi k)) (S.col b j u)

/-- All scalar κ entries of block `b`: columns `j < ncol b`, raw rows `u < nraw b`. -/
noncomputable def rfOk (R : Nat) (G : GTab) (L : LTab) (S : STab) (LK wK b : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun j ih => ih &&
    Nat.rec (motive := fun _ => Bool) true (fun u ih2 => ih2 && rfEntOk R G L S LK wK b j u) (S.nraw b)) (S.ncol b)

/-- `Q(2^R) = ± Π f_r(2^R)^{e_r}` with headers and the bound `2 (ℓ1(Q) + Π ℓ1(f_r)^{e_r}) < 2^R`. -/
noncomputable def facOk (R : Nat) (G : GTab) (S : STab) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun r ih => ih && Nat.ble 1 (Nat.land (Nat.shiftRight (S.fac r) 20) 255))
    S.nfac &&
  (fun p => seq (lookV 0 (decPolyVec R G.qc G.qn 0)) (xor S.fsgn p.1, p.2))
    (Nat.rec (motive := fun _ => Bool × Nat) (false, 1) (fun r acc => smulS acc (spow (polyVal R (S.fac r)) (S.fexp r)))
      S.nfac) &&
  Nat.blt (Nat.mul 2 (Nat.add (recBound G.LQ G.wQ)
    (Nat.rec (motive := fun _ => Nat) 1 (fun r acc => Nat.mul acc (Nat.pow (ownBound (S.fac r)) (S.fexp r))) S.nfac)))
    (Nat.shiftLeft 1 R)

end ThomsonCompact.Fixed
