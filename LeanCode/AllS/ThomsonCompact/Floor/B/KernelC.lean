import ThomsonCompact.Floor.B.Kernel
import ThomsonCompact.CoeffMap.CellCodec

/-!
# F3c kernel additions (Init only)

* `errLe f L i`: every TM of `L` (indexed from `i`) has error `≤ f index` (the target-model error claims `herr`);
* `centreGateOk`: the centre gate of the residual (`StructuredCenterGate` of `gateR` for point models) as one exact
  integer inequality per retained coordinate (scale `2^-S`): target TM slots, F2's checkpointed W0 sum records
  (sign-magnitude slots at `2^-(S-F)`), centre slots (`2^-Sc`) and radii.
-/

noncomputable section

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Packed
open ThomsonCompact.Floor (slot)

/-- `∀ t < L.length, (L.getD t).e ≤ f (i + t)`, one pass -/
def errLe (f : Nat → Nat) : List TM → Nat → Bool :=
  List.rec (fun _ => true) (fun T _ ih i => and (Nat.ble T.e (f i)) (ih (Nat.succ i)))

/-- signed value of a sign-magnitude pair (kernel form of `sv`) -/
def svK (x : Bool × Nat) : Int := cond x.1 (Int.neg (Int.ofNat x.2)) (Int.ofNat x.2)

/-- `|qn h_k - 3 d_k 2^F - 3 C_k 2^(S-Sc)|` of coefficient `k` -/
def cgateK (c : Ctx) (Ht : TM) (dq : Bool × Nat) (dr : List Nat) (F Sc wc cm k : Nat) : Nat :=
  Int.natAbs (svK dq * svK (pvGet c.W c.m Ht.v k) -
    3 * (ThomsonCompact.CoeffMap.sdec (dr.getD k 0) * Int.ofNat (Nat.pow 2 F)) -
    3 * (svK (smDec (slot wc cm k)) * Int.ofNat (Nat.pow 2 (Nat.sub c.S Sc))))

/-- centre gate of one coordinate: `Σ_k |qn h_k - 3 d_k 2^F - 3 C_k 2^(S-Sc)| + 3 d_e 2^F ≤ 3 Er` -/
def cgate1 (c : Ctx) (Ht : TM) (dq : Bool × Nat) (dr : List Nat) (F Sc wc cm Er : Nat) : Bool :=
  Nat.ble (Nat.add (lsum ((List.range c.m).map (cgateK c Ht dq dr F Sc wc cm)))
    (Nat.mul 3 (Nat.mul (dr.getD c.m 0) (Nat.pow 2 F)))) (Nat.mul 3 Er)

/-- **Centre gate leaf**: coordinates `i < nin` (`Ht t` target TMs, `D i` sum records, `cm i` centre numerals) -/
def centreGateOk (c : Ctx) (Ht : Nat → TM) (dirT : Nat → Nat) (dirQ : Nat → Bool × Nat) (D : Nat → List Nat)
    (F Sc wc : Nat) (cm Er : Nat → Nat) (nin : Nat) : Bool :=
  (List.range nin).all fun i => and (Nat.blt (dirT i) 12) (cgate1 c (Ht (dirT i)) (dirQ i) (D i) F Sc wc (cm i) (Er i))

end ThomsonCompact.Floor.B
