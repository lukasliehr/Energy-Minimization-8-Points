import ThomsonCompact.Floor.B.TableFixed
import ThomsonCompact.Floor.Tables.D16b.Slices
import ThomsonCompact.Fixed.D16.Recovery

/-!
# The compact D16 right inverse (F4) in the form of the F3b row theorems (F3d)

`tab16`: `FixedD16.inverseMatrix` as a `TabSpec 202` (anchor `a0 = 68/2^8`, `σ = 2^-8`), `dl16_ne` (row
denominators on physical heights), `rowFacts16_of` (`RowFactsT` of a row from its bridge, denominator and coordinate
leaves, stated with the Init-only decoder `FD`).
-/

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Packed ThomsonCompact.Fixed

theorem slicesB16_eq : ThomsonCompact.Floor.Tables.D16b.slicesB = ThomsonCompact.Fixed.D16.slices := rfl

/-- the D16 table (anchor `68/2^8`, `σ = 2^-8`) -/
noncomputable def tab16 : TabSpec 202 :=
  fixedTab 202 ThomsonCompact.FixedD16.inverseMatrix ThomsonCompact.FixedD16.outputCoordinates
    ThomsonCompact.Floor.Tables.D16b.slicesB ThomsonCompact.Fixed.D16.gtab
    (fun a k i => by rw [slicesB16_eq]; rfl) 68 8 8

theorem dl16_ne : ∀ a, Blueprint.Thomson.Finite.physical a → ∀ j < 202, tab16.dl j a ≠ 0 :=
  fixedDl_ne 202 ThomsonCompact.Fixed.D16.gtab _
    (fun a ha k hk => ⟨(ThomsonCompact.Fixed.D16.out_ne a ha k hk).2.1, (ThomsonCompact.Fixed.D16.out_ne a ha k hk).2.2.1⟩)
    (fun k hk => (ThomsonCompact.Fixed.D16.gid k hk).1)

theorem rowFacts16_of (j : ℕ) (hj : j < 202) (r : RowT) (W Wd : ℕ) (hW : 2 ≤ W) (hWd : 2 ≤ Wd)
    (hb : rowBridgeOk 202 68 8 8 W 1 r (fun m => FD.hC ThomsonCompact.Floor.Tables.D16b.slicesB j m) = true)
    (hd : denOk 68 8 8 Wd r (FD.lamG ThomsonCompact.Fixed.D16.gtab j) (FD.dqG ThomsonCompact.Fixed.D16.gtab j)
      (FD.dzC ThomsonCompact.Fixed.D16.gtab j) = true)
    (hc : Nat.land (Nat.shiftRight (ThomsonCompact.Fixed.D16.ltab.oinfo j) 8) 255 = r.u ∧
      Nat.land (Nat.shiftRight (ThomsonCompact.Fixed.D16.ltab.oinfo j) 16) 255 = r.v) :
    RowFactsT tab16 j r :=
  rowFactsFixed_of tab16 _ ThomsonCompact.Fixed.D16.gtab ThomsonCompact.Fixed.D16.ltab rfl rfl (fun _ _ => rfl)
    (by decide) j hj r W Wd hW hWd hb hd hc

end ThomsonCompact.Floor.B
