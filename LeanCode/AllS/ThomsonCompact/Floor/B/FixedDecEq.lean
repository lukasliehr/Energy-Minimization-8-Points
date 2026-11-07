import ThomsonCompact.Floor.B.FixedDec
import ThomsonCompact.Fixed.SoundT
import ThomsonCompact.Fixed.SoundG

/-!
# The Init-only decoder `FD` is the F4 table decoder (F3d)

`FD.hC = Fixed.hC`, `FD.dzC = Fixed.dzC`, `FD.lamG = Fixed.lamG`, `FD.dqG = Fixed.dqG`: the bridge leaves of the
D14/D16 re-expanded tables (stated with `FD`) speak about the stored entries of the compact right inverses.
-/

namespace ThomsonCompact.Floor.B.FD

theorem recCoeffs_eq (x : Nat) : recCoeffs x = ThomsonCompact.Fixed.recCoeffs x := rfl

theorem decPolysC_eq : ∀ n x, decPolysC n x = ThomsonCompact.Fixed.decPolysC n x
  | 0, _ => rfl
  | n + 1, x => by
    simp only [decPolysC, ThomsonCompact.Fixed.decPolysC, recCoeffs_eq, decPolysC_eq n]

theorem decPolyVecC_eq (ch : Nat → Nat) : ∀ n c, decPolyVecC ch n c = ThomsonCompact.Fixed.decPolyVecC ch n c
  | 0, _ => rfl
  | n + 1, c => by
    simp only [decPolyVecC, ThomsonCompact.Fixed.decPolyVecC, decPolysC_eq, decPolyVecC_eq ch n]

theorem lookC_eq (l : List (Nat × List Int)) (i : Nat) : lookC l i = ThomsonCompact.Fixed.lookC l i := rfl

theorem findSlice_eq (sl : List ThomsonCompact.Fixed.Slice) (i : Nat) :
    findSlice sl i = ThomsonCompact.Fixed.findSlice sl i := rfl

theorem hC_eq (sl : List ThomsonCompact.Fixed.Slice) (k i : Nat) : hC sl k i = ThomsonCompact.Fixed.hC sl k i := by
  unfold hC ThomsonCompact.Fixed.hC ThomsonCompact.Fixed.hcoef ThomsonCompact.Fixed.hrowC
  rw [decPolyVecC_eq, lookC_eq, findSlice_eq]

theorem dzC_eq (G : ThomsonCompact.Fixed.GTab) (k : Nat) : dzC G k = ThomsonCompact.Fixed.dzC G k := by
  unfold dzC ThomsonCompact.Fixed.dzC
  rw [decPolyVecC_eq, lookC_eq]

theorem lamG_eq (G : ThomsonCompact.Fixed.GTab) (k : Nat) : lamG G k = ThomsonCompact.Fixed.lamG G k := rfl
theorem dqG_eq (G : ThomsonCompact.Fixed.GTab) (k : Nat) : dqG G k = ThomsonCompact.Fixed.dqG G k := rfl

end ThomsonCompact.Floor.B.FD
