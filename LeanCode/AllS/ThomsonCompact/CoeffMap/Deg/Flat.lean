import ThomsonCompact.CoeffMap.CellCodec

/-!
# Chunked W0 literal fields (Init only; F2e)

The D14/D16/D18 literal fields `klow`, `fac u` of the large blocks exceed one 16-kbit numeral; the exporter
(`CoeffMap/Deg/gen/w0cell.py`) splits them into numerals of `per` slots. `CellData.flat d nchK nchF` concatenates
the numerals of every field in the kernel (each masked to its `per` slots), so the D12 `CoeffMap.GramPack`
(single-numeral fields) applies to `d.flat …` unchanged; `CoeffMap.Deg.FlatSound.flat_block` shows that the
decoded literal blocks agree (`(d.flat …).block bi = d.block bi`).
-/

namespace ThomsonCompact.CoeffMap.Deg

open ThomsonCompact.CoeffMap

/-- `Σ_{c < nch} (ch c mod 2^(w·per)) · 2^(w·per·c)`: the numerals of a chunked field, concatenated. -/
def catChunks (ch : Nat → Nat) (w per nch : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun c ih =>
    Nat.add ih (Nat.shiftLeft (Nat.land (ch c) (Nat.sub (Nat.shiftLeft 1 (Nat.mul w per)) 1))
      (Nat.mul (Nat.mul w per) c))) nch

/-- The cell data with every chunked field concatenated into numeral `0` (`per = nch · per` slots). -/
def CellData.flat (d : CellData) (nchK nchF : Nat → Nat) : CellData :=
  { d with
    klow := fun bi _ => catChunks (d.klow bi) d.kw (d.layout bi).1 (nchK bi)
    fac := fun bi u _ => catChunks (d.fac bi u) (d.layout bi).2.1 (d.layout bi).2.2 (nchF bi)
    layout := fun bi => (Nat.mul (nchK bi) (d.layout bi).1, (d.layout bi).2.1, Nat.mul (nchF bi) (d.layout bi).2.2) }

end ThomsonCompact.CoeffMap.Deg
