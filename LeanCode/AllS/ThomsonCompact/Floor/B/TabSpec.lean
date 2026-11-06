import ThomsonCompact.Floor.B.SoundBridge
import Mathlib.Data.Matrix.Basic

/-!
# The right-inverse table of one degree, in the form of the F3b row theorems (F3d, degree-generic)

* `TabSpec nI`: a table `inv a = (H_jm(a) / dl_j(a))` on `nI` input/output coordinates with output coordinates
  `coords`, entries `Hd`, row denominators `dl` and the re-expansion anchor `a0 = p/2^q`, `σ = 2^-g`;
* `RowFactsT T j r`: the re-expanded row `r` encloses row `j` of `T` (`RowSem` at the anchor, `u_D = 1/2`),
  the entries off `r.msL` vanish, and `r` carries the output coordinate of row `j`;
* `rowFactsT_of`: `RowFactsT` from a bridge leaf (`rowBridgeOk`), a denominator leaf (`denOk`) and the
  identification of the table entries/denominators with integer polynomials.

Instances: D12/D18 (old `FixedTables` literals, `TableD12`, `TableD18`), D14/D16 (compact `Fixed` data,
`TableD14`, `TableD16`).
-/

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Packed

/-- the right-inverse table of one degree (`nI` coordinates) and its re-expansion anchor -/
structure TabSpec (nI : ℕ) where
  inv : ℝ → Matrix (Fin nI) (Fin nI) ℝ
  coords : Fin nI → String × ℕ × ℕ
  Hd : ℕ → ℕ → ℝ → ℝ
  dl : ℕ → ℝ → ℝ
  inv_eq : ∀ (a : ℝ) (j m : Fin nI), inv a j m = Hd j m a / dl j a
  p : ℕ
  q : ℕ
  g : ℕ

/-- the anchor `a0 = p/2^q` -/
noncomputable def TabSpec.a0 {nI : ℕ} (T : TabSpec nI) : ℝ := (T.p : ℝ) / 2 ^ T.q

/-- the scale `σ = 2^-g` -/
noncomputable def TabSpec.σ {nI : ℕ} (T : TabSpec nI) : ℝ := 1 / 2 ^ T.g

/-- what the one-time leaves of a degree give for row `j` -/
structure RowFactsT {nI : ℕ} (T : TabSpec nI) (j : ℕ) (r : RowT) : Prop where
  sem : RowSem nI r T.a0 T.σ (1 / 2) (T.Hd j) (T.dl j)
  zero : ∀ m < nI, m ∉ r.msL → ∀ a, T.Hd j m a = 0
  coord : ∀ hj : j < nI, (T.coords ⟨j, hj⟩).2 = (r.u, r.v)

theorem mAt_mem (r : RowT) (hl : r.msL.length = r.nms) (idx : ℕ) (hidx : idx < r.nms) : r.mAt idx ∈ r.msL := by
  unfold RowT.mAt
  rw [getD_of_lt _ _ (by omega)]
  exact List.getElem_mem _

/-- **`RowFactsT` of a row** from its bridge leaf, its denominator leaf and the table identification:
`Hd j m = evalZ (hrow m)` (`m < nI`), `dl j = λ/dq · evalZ dz`. -/
theorem rowFactsT_of {nI : ℕ} (T : TabSpec nI) (hgq : T.g ≤ T.q) (j : ℕ) (hj : j < nI) (r : RowT)
    (hrow : ℕ → List ℤ) (W Wd lam dq : ℕ) (dz : List ℤ) (hW : 2 ≤ W) (hWd : 2 ≤ Wd)
    (hb : rowBridgeOk nI T.p T.q T.g W 1 r hrow = true)
    (hd : denOk T.p T.q T.g Wd r lam dq dz = true)
    (hH : ∀ m < nI, ∀ a, T.Hd j m a = evalZ (hrow m) a)
    (hdl : ∀ a, T.dl j a = (lam : ℝ) / dq * evalZ dz a)
    (hcoord : (T.coords ⟨j, hj⟩).2 = (r.u, r.v)) :
    RowFactsT T j r := by
  obtain ⟨hent, hmag, hl, hw, ht, hL, -, hs, hn, hz⟩ := rowBridge_sound nI T.p T.q T.g W 1 r hrow hgq hW hb
  have hdn := denOk_sound T.p T.q T.g Wd r lam dq dz hgq hWd hd
  have ha : ∀ u : ℝ, T.a0 + T.σ * u = (T.p : ℝ) / 2 ^ T.q + 1 / 2 ^ T.g * u := fun u => rfl
  refine ⟨⟨?_, ?_, ?_, hl, hw, ht, hL, hs, hn⟩, ?_, fun _ => hcoord⟩
  · intro idx hidx u hu
    rw [ha, hH _ (hn _ (mAt_mem r hl idx hidx))]
    exact hent idx hidx u hu
  · intro u hu
    rw [ha, hdl]
    exact hdn u hu
  · intro idx hidx u hu
    rw [ha, hH _ (hn _ (mAt_mem r hl idx hidx))]
    exact hmag idx hidx u (by rw [pow_one]; exact hu)
  · intro m hm hnm a
    rw [hH m hm]
    exact evalZ_zeros _ (hz m hm hnm) _

end ThomsonCompact.Floor.B
