/-!
# TailC: generic packed product-collapse stage (kernel program, Init only; workstream TC1)

Input: terms `(p, q, c)` of sparse vectors over `ℤ[√2]` (entries `(index, (sign, |u|), (sign, |v|))`, value
`u + v √2`) and a scale `c`. The stage computes the coefficients

  `C_γ = Σ_terms c · Σ_{e ∈ p} Σ_{f ∈ q} [gam e.i f.i = γ] e·f`        (`γ < N`)

by packed `Nat` arithmetic: rows `R_s = Σ_{e ∈ p, e.i = s} e ⊙ pack(c q)` (sign-split `(U⁺, U⁻, V⁺, V⁻)`,
slot width `W`), then every row slot is decoded (bias `2^(W-1)`) and scattered into the output accumulator
(slot width `W2`) at `gam s t` (row table `gam s`, entries of `gw` bits), which is decoded at the end.
Soundness: `TailC.StageSound`; bit-exact mirror: `tools/tailc_boundary_export.py` (`stage`).
-/

namespace ThomsonCompact.TailC

/-! ## Fields and records -/

def mask (w : Nat) : Nat := Nat.sub (Nat.shiftLeft 1 w) 1

/-- Bits `[off, off + w)` of `x`. -/
def fld (x off w : Nat) : Nat := Nat.land (Nat.shiftRight x off) (mask w)

/-- Sparse entry `(i, (su, mu), (sv, mv))`: value `(±mu) + (±mv) √2` at index `i` (sign `true` = negative). -/
abbrev Ent := Nat × (Bool × Nat) × (Bool × Nat)

/-- Packed sign-split row `(U⁺, U⁻, V⁺, V⁻)`. -/
abbrev R4 := Nat × Nat × Nat × Nat

/-- Record length: header `[i:12][su:1][sv:1][lu:8][lv:8]` (30 bits), then `mu` (`lu` bits), `mv` (`lv` bits). -/
def recLen (x : Nat) : Nat := Nat.add 30 (Nat.add (fld x 14 8) (fld x 22 8))

def recEnt (x : Nat) : Ent :=
  (fld x 0 12, (Nat.beq (fld x 12 1) 1, fld x 30 (fld x 14 8)),
    (Nat.beq (fld x 13 1) 1, fld x (Nat.add 30 (fld x 14 8)) (fld x 22 8)))

/-- Decode `n` records. -/
noncomputable def decEnts (n : Nat) : Nat → List Ent :=
  Nat.rec (motive := fun _ => Nat → List Ent) (fun _ => [])
    (fun _ ih x => recEnt x :: ih (Nat.shiftRight x (recLen x))) n

/-- A sparse vector numeral: count (8 bits), then the records. -/
noncomputable def decSV (x : Nat) : List Ent := decEnts (fld x 0 8) (Nat.shiftRight x 8)

/-- `[f 0, …, f (n-1)]`. -/
noncomputable def mkL {α : Type} (f : Nat → α) (n : Nat) : List α :=
  Nat.rec (motive := fun _ => Nat → List α) (fun _ => []) (fun _ ih k => f k :: ih (Nat.add k 1)) n 0

/-- `n` copies of `x`. -/
noncomputable def rep {α : Type} (x : α) (n : Nat) : List α :=
  Nat.rec (motive := fun _ => List α) [] (fun _ ih => x :: ih) n

/-! ## Rows -/

/-- `(s, m) · (P, N)` for a sign-split pair. -/
noncomputable def smulP (s : Bool) (m P N : Nat) : Nat × Nat :=
  Bool.rec (motive := fun _ => Nat × Nat) (Nat.mul m P, Nat.mul m N) (Nat.mul m N, Nat.mul m P) s

/-- `r + e ⊙ Q` in `ℤ[√2]`: `U += eu·Qu + 2 ev·Qv`, `V += eu·Qv + ev·Qu`. -/
noncomputable def addEnt (e : Ent) (Q r : R4) : R4 :=
  (Nat.add r.1 (Nat.add (smulP e.2.1.1 e.2.1.2 Q.1 Q.2.1).1 (smulP e.2.2.1 (Nat.mul 2 e.2.2.2) Q.2.2.1 Q.2.2.2).1),
   Nat.add r.2.1 (Nat.add (smulP e.2.1.1 e.2.1.2 Q.1 Q.2.1).2 (smulP e.2.2.1 (Nat.mul 2 e.2.2.2) Q.2.2.1 Q.2.2.2).2),
   Nat.add r.2.2.1 (Nat.add (smulP e.2.1.1 e.2.1.2 Q.2.2.1 Q.2.2.2).1 (smulP e.2.2.1 e.2.2.2 Q.1 Q.2.1).1),
   Nat.add r.2.2.2 (Nat.add (smulP e.2.1.1 e.2.1.2 Q.2.2.1 Q.2.2.2).2 (smulP e.2.2.1 e.2.2.2 Q.1 Q.2.1).2))

/-- `pack(c q)`: slot `f.i` (width `W`) receives `c·f`. -/
noncomputable def packQ (W c : Nat) (q : List Ent) : R4 :=
  List.rec (motive := fun _ => R4) (0, 0, 0, 0)
    (fun f _ r =>
      (Bool.rec (motive := fun _ => Nat) (Nat.add r.1 (Nat.shiftLeft (Nat.mul c f.2.1.2) (Nat.mul W f.1))) r.1 f.2.1.1,
       Bool.rec (motive := fun _ => Nat) r.2.1 (Nat.add r.2.1 (Nat.shiftLeft (Nat.mul c f.2.1.2) (Nat.mul W f.1))) f.2.1.1,
       Bool.rec (motive := fun _ => Nat) (Nat.add r.2.2.1 (Nat.shiftLeft (Nat.mul c f.2.2.2) (Nat.mul W f.1))) r.2.2.1
         f.2.2.1,
       Bool.rec (motive := fun _ => Nat) r.2.2.2 (Nat.add r.2.2.2 (Nat.shiftLeft (Nat.mul c f.2.2.2) (Nat.mul W f.1)))
         f.2.2.1)) q

/-- Walk the rows (positions from `pos`) and add `e ⊙ Q` to row `e.i` for the entries in order; returns the
new rows and the entries not consumed. -/
noncomputable def walk (Q : R4) : List R4 → List Ent → Nat → List R4 × List Ent :=
  List.rec (motive := fun _ => List Ent → Nat → List R4 × List Ent) (fun es _ => ([], es))
    (fun r rs ih es pos =>
      List.rec (motive := fun _ => List R4 × List Ent) (r :: rs, [])
        (fun e es' _ =>
          Bool.rec (motive := fun _ => List R4 × List Ent)
            ((r :: (ih (e :: es') (Nat.add pos 1)).1), (ih (e :: es') (Nat.add pos 1)).2)
            ((addEnt e Q r :: (ih es' (Nat.add pos 1)).1), (ih es' (Nat.add pos 1)).2)
            (Nat.beq e.1 pos)) es)

/-- `true` iff the list is empty. -/
noncomputable def isNil {α : Type} (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) l

/-- All indices `< n`. -/
noncomputable def idxOk (n : Nat) (l : List Ent) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun f _ ih => Nat.blt f.1 n && ih) l

/-- A term: left sparse vector, right sparse vector, scale. -/
abbrev Term := List Ent × List Ent × Nat

/-- Process the terms in order. -/
noncomputable def rowsGo (W n : Nat) : List Term → List R4 → Bool × List R4 :=
  List.rec (motive := fun _ => List R4 → Bool × List R4) (fun rows => (true, rows))
    (fun t _ ih rows =>
      ((isNil (walk (packQ W t.2.2 t.2.1) rows t.1 0).2 && idxOk n t.2.1) &&
          (ih (walk (packQ W t.2.2 t.2.1) rows t.1 0).1).1,
        (ih (walk (packQ W t.2.2 t.2.1) rows t.1 0).1).2))

/-! ## A-priori bound -/

/-- `Σ (|u| + |v|)` over the entries. -/
noncomputable def ellL (l : List Ent) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun f _ ih => Nat.add (Nat.add f.2.1.2 f.2.2.2) ih) l

/-- `Σ_terms c · ℓ(p) · ℓ(q)`. -/
noncomputable def bgSum (ts : List Term) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun t _ ih => Nat.add (Nat.mul t.2.2 (Nat.mul (ellL t.1) (ellL t.2.1))) ih) ts

/-! ## Collapse -/

/-- `Σ_{t<n} 2^(W-1) 2^(W t)`. -/
def biasN (W n : Nat) : Nat := Nat.div (Nat.mul (Nat.shiftLeft 1 (Nat.sub W 1)) (mask (Nat.mul W n))) (mask W)

/-- Scatter `k` slots of a row: digits of `Xu`, `Xv` (width `W`, bias `h`) to `gam` digits of `g` (width `gw`). -/
noncomputable def scatRow (W W2 gw h : Nat) (k : Nat) : Nat → Nat → Nat → R4 → R4 :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → R4 → R4) (fun _ _ _ C => C)
    (fun _ ih Xu Xv g C =>
      ih (Nat.shiftRight Xu W) (Nat.shiftRight Xv W) (Nat.shiftRight g gw)
        (Bool.rec (motive := fun _ => Nat)
            (Nat.add C.1 (Nat.shiftLeft (Nat.sub (Nat.land Xu (mask W)) h) (Nat.mul W2 (Nat.land g (mask gw)))))
            C.1 (Nat.blt (Nat.land Xu (mask W)) h),
         Bool.rec (motive := fun _ => Nat) C.2.1
            (Nat.add C.2.1 (Nat.shiftLeft (Nat.sub h (Nat.land Xu (mask W))) (Nat.mul W2 (Nat.land g (mask gw)))))
            (Nat.blt (Nat.land Xu (mask W)) h),
         Bool.rec (motive := fun _ => Nat)
            (Nat.add C.2.2.1 (Nat.shiftLeft (Nat.sub (Nat.land Xv (mask W)) h) (Nat.mul W2 (Nat.land g (mask gw)))))
            C.2.2.1 (Nat.blt (Nat.land Xv (mask W)) h),
         Bool.rec (motive := fun _ => Nat) C.2.2.2
            (Nat.add C.2.2.2 (Nat.shiftLeft (Nat.sub h (Nat.land Xv (mask W))) (Nat.mul W2 (Nat.land g (mask gw)))))
            (Nat.blt (Nat.land Xv (mask W)) h))) k

/-- Scatter all rows (row `s` uses the table row `gam s`). -/
noncomputable def scatAll (W W2 gw h bs n : Nat) (gam : Nat → Nat) : List R4 → Nat → R4 → R4 :=
  List.rec (motive := fun _ => Nat → R4 → R4) (fun _ C => C)
    (fun r _ ih s C => ih (Nat.add s 1)
      (scatRow W W2 gw h n (Nat.sub (Nat.add r.1 bs) r.2.1) (Nat.sub (Nat.add r.2.2.1 bs) r.2.2.2) (gam s) C))

/-- Sign-magnitude of `d - h`. -/
noncomputable def smd (d h : Nat) : Bool × Nat := (Nat.blt d h, Nat.add (Nat.sub d h) (Nat.sub h d))

/-- Decode `k` output slots (width `W2`, bias `h2`) starting at index `γ`. -/
noncomputable def decOut (W2 h2 : Nat) (k : Nat) : Nat → Nat → Nat → List Ent :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → List Ent) (fun _ _ _ => [])
    (fun _ ih γ Yu Yv =>
      (γ, smd (Nat.land Yu (mask W2)) h2, smd (Nat.land Yv (mask W2)) h2) ::
        ih (Nat.add γ 1) (Nat.shiftRight Yu W2) (Nat.shiftRight Yv W2)) k

/-! ## The stage -/

/-- Stage parameters: input dimension `n`, output dimension `N`, row width `W`, output width `W2`, table entry
width `gw`, table rows `gam`. -/
structure SP where
  n : Nat
  N : Nat
  W : Nat
  W2 : Nat
  gw : Nat
  gam : Nat → Nat

/-- The decoded output accumulator. -/
noncomputable def outOf (P : SP) (C : R4) : List Ent :=
  decOut P.W2 (Nat.shiftLeft 1 (Nat.sub P.W2 1)) P.N 0
    (Nat.sub (Nat.add C.1 (biasN P.W2 P.N)) C.2.1) (Nat.sub (Nat.add C.2.2.1 (biasN P.W2 P.N)) C.2.2.2)

/-- Run the stage: `(ok, output list)`. -/
noncomputable def stage (P : SP) (ts : List Term) : Bool × List Ent :=
  ((rowsGo P.W P.n ts (rep (0, 0, 0, 0) P.n)).1 &&
      Nat.blt (Nat.mul 2 (bgSum ts)) (Nat.shiftLeft 1 (Nat.sub P.W 1)) &&
      Nat.blt (Nat.mul (Nat.mul P.n P.n) (Nat.mul 2 (bgSum ts))) (Nat.shiftLeft 1 (Nat.sub P.W2 1)),
    outOf P (scatAll P.W P.W2 P.gw (Nat.shiftLeft 1 (Nat.sub P.W 1)) (biasN P.W P.n) P.n P.gam
      (rowsGo P.W P.n ts (rep (0, 0, 0, 0) P.n)).2 0 (0, 0, 0, 0)))

end ThomsonCompact.TailC
