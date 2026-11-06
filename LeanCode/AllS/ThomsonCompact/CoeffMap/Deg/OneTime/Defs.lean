import ThomsonCompact.CoeffMap.Deg.Check

/-!
# One-time (per degree) table checks of the W0 link (Init only; F2h)

Besides the checks of `CoeffMap.Deg.Check` (`tagOk`, `clsOk`, `grpOk`, `eOkC`), the link `CoeffMap.Deg.W0LinkD` uses:

* `pairOkL L j`: for every pair `u ≤ v` of scalar block `j`, the fields of its class key are the raw product spec of
  the decoded raw tags (`rawScalarProductSpec`), and the power-sum indices are inside the tables;
* `momRatL`: the moment pivot polynomials `mP k j` (`j ≤ gdim k`) have no `√2` part;
* `denTabL`: every record has a shared denominator index `< nDen` and a positive denominator scale;
* `rec01L`: record `0` is the constant `1`, record `1` the constant `0`;
* `grpsOkL`: the group boundaries of all blocks (`grpOk`).
-/

namespace ThomsonCompact.CoeffMap.Deg.Link

open ThomsonCompact.CoeffMap ThomsonCompact.CoeffMap.Deg

/-- Decoded pair keys of scalar block `j`. -/
def pairOkL (L : DegD) (j : Nat) : Bool :=
  (List.range (L.rdim (Nat.add L.dH j))).all fun v => (List.range (Nat.add v 1)).all fun u =>
    (fun x su sv => teq (decT L.aA L.aB (Nat.land x 65535)) (tadd su.2 sv.2) &&
        (Nat.beq (Nat.land (Nat.shiftRight x 16) 1) 1 == (Nat.beq (famOf j) 2 && (su.1 && sv.1))) &&
        (Nat.beq (Nat.land (Nat.shiftRight x 17) 1) 1 == (Nat.beq (famOf j) 2 && (su.1 || sv.1))) &&
        (!(Nat.ble 3 (famOf j)) || (Nat.blt (Nat.add (Nat.add (tadd su.2 sv.2).1 (tadd su.2 sv.2).2.1) 4) L.nPS &&
          Nat.blt (Nat.add (tadd su.2 sv.2).2.2 2) L.nPS)))
      (L.pairKey (Nat.add L.dH j) u v) (L.stag j u) (L.stag j v)

/-- The pivot polynomials of the moment blocks are rational. -/
def momRatL (L : DegD) : Bool :=
  (List.range L.dH).all fun k => (List.range (Nat.add (L.gdim k) 1)).all fun j => qAllZero (mP k j).s

/-- Shared denominator indices and scales of all records. -/
def denTabL (L : DegD) : Bool :=
  (List.range L.nRec).all fun k => Nat.blt (L.denIdx k) L.nDen && Nat.blt 0 (L.denS (L.denIdx k))

/-- Records `0` and `1` are the constants `1` and `0`. -/
def rec01L (L : DegD) : Bool :=
  (L.numZ 0 == [1]) && Nat.beq (L.numS 0) 1 && (L.denZ (L.denIdx 0) == [1]) && Nat.beq (L.denS (L.denIdx 0)) 1 &&
    (L.numZ 1).isEmpty

/-- Group boundaries of all blocks. -/
def grpsOkL (L : DegD) : Bool := (List.range (Nat.add L.dH 8)).all L.grpOk

end ThomsonCompact.CoeffMap.Deg.Link
