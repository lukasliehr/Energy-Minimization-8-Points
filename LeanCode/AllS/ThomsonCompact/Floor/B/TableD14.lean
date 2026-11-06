import ThomsonCompact.Floor.B.TableFixed
import ThomsonCompact.Floor.Tables.D14b.Slices
import ThomsonCompact.Fixed.D14.Recovery

/-!
# The compact D14 right inverse (F4) in the form of the F3b row theorems (F3d)

`tab14`: `FixedD14.inverseMatrix` as a `TabSpec 145` (anchor `a0 = 35/2^7`, `σ = 2^-6`), `dl14_ne` (row
denominators on physical heights), `rowFacts14_of` (`RowFactsT` of a row from its bridge, denominator and coordinate
leaves, stated with the Init-only decoder `FD`).
-/

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Packed ThomsonCompact.Fixed

theorem slicesB14_eq : ThomsonCompact.Floor.Tables.D14b.slicesB = ThomsonCompact.Fixed.D14.slices := rfl

/-- the D14 table (anchor `35/2^7`, `σ = 2^-6`) -/
noncomputable def tab14 : TabSpec 145 :=
  fixedTab 145 ThomsonCompact.FixedD14.inverseMatrix ThomsonCompact.FixedD14.outputCoordinates
    ThomsonCompact.Floor.Tables.D14b.slicesB ThomsonCompact.Fixed.D14.gtab
    (fun a k i => by rw [slicesB14_eq]; rfl) 35 7 6

theorem dl14_ne : ∀ a, Blueprint.Thomson.Finite.physical a → ∀ j < 145, tab14.dl j a ≠ 0 :=
  fixedDl_ne 145 ThomsonCompact.Fixed.D14.gtab _
    (fun a ha k hk => ⟨(ThomsonCompact.Fixed.D14.out_ne a ha k hk).2.1, (ThomsonCompact.Fixed.D14.out_ne a ha k hk).2.2.1⟩)
    (fun k hk => (ThomsonCompact.Fixed.D14.gid k hk).1)

theorem rowFacts14_of (j : ℕ) (hj : j < 145) (r : RowT) (W Wd : ℕ) (hW : 2 ≤ W) (hWd : 2 ≤ Wd)
    (hb : rowBridgeOk 145 35 7 6 W 1 r (fun m => FD.hC ThomsonCompact.Floor.Tables.D14b.slicesB j m) = true)
    (hd : denOk 35 7 6 Wd r (FD.lamG ThomsonCompact.Fixed.D14.gtab j) (FD.dqG ThomsonCompact.Fixed.D14.gtab j)
      (FD.dzC ThomsonCompact.Fixed.D14.gtab j) = true)
    (hc : Nat.land (Nat.shiftRight (ThomsonCompact.Fixed.D14.ltab.oinfo j) 8) 255 = r.u ∧
      Nat.land (Nat.shiftRight (ThomsonCompact.Fixed.D14.ltab.oinfo j) 16) 255 = r.v) :
    RowFactsT tab14 j r :=
  rowFactsFixed_of tab14 _ ThomsonCompact.Fixed.D14.gtab ThomsonCompact.Fixed.D14.ltab rfl rfl (fun _ _ => rfl)
    (by decide) j hj r W Wd hW hWd hb hd hc

end ThomsonCompact.Floor.B
