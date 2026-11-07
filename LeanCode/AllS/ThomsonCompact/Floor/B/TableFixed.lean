import ThomsonCompact.Floor.B.TabSpec
import ThomsonCompact.Floor.B.FixedDecEq
import ThomsonCompact.Fixed.SoundN

/-!
# A compact fixed right inverse (F4) as a `TabSpec` (F3d, degree-generic)

For the compact tables of `Fixed` (`inverseMatrix a k i = dq_k H_ki(a) / (λ_k dz_k(a))`, stored slices `sl`, link
data `G`, layout `L`):

* `fixedHd`, `fixedDl`, `fixedTab`: the entries `H_jm = evalZ (hC sl j m)` and row denominators
  `λ_j/dq_j · dz_j` (`fixed_inv_eq`), the table with its anchor;
* `fixedDl_ne`: the row denominators do not vanish where `λ_k dz_k(a) ≠ 0` and `dq_k ≥ 1`;
* `rowFactsFixed_of`: `RowFactsT` of a re-expanded row from its bridge leaf and denominator leaf, both stated with
  the Init-only decoder `FD`, and its output-coordinate leaf.
-/

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Packed ThomsonCompact.Fixed

/-- numerator entry `(j, m)` of a compact fixed table -/
noncomputable def fixedHd (nI : ℕ) (sl : List Slice) (j m : ℕ) (a : ℝ) : ℝ :=
  if j < nI ∧ m < nI then evalZ (hC sl j m) a else 0

/-- row denominator `λ_j/dq_j · dz_j(a)` of a compact fixed table -/
noncomputable def fixedDl (nI : ℕ) (G : GTab) (j : ℕ) (a : ℝ) : ℝ :=
  if j < nI then (lamG G j : ℝ) / (dqG G j : ℝ) * evalZ (dzC G j) a else 1

theorem fixed_inv_eq {nI : ℕ} (sl : List Slice) (G : GTab) (inv : ℝ → Matrix (Fin nI) (Fin nI) ℝ)
    (hinv : ∀ a (k i : Fin nI), inv a k i =
      (dqG G k.val : ℝ) * evalZ (hC sl k.val i.val) a / ((lamG G k.val : ℝ) * evalZ (dzC G k.val) a))
    (a : ℝ) (j m : Fin nI) : inv a j m = fixedHd nI sl j m a / fixedDl nI G j a := by
  rw [hinv, fixedHd, fixedDl, if_pos (And.intro j.isLt m.isLt), if_pos j.isLt, div_mul_eq_mul_div,
    div_div_eq_mul_div, mul_comm (evalZ (hC sl j.val m.val) a)]

/-- the compact fixed table as a `TabSpec` (anchor `p/2^q`, `σ = 2^-g`) -/
noncomputable def fixedTab (nI : ℕ) (inv : ℝ → Matrix (Fin nI) (Fin nI) ℝ) (coords : Fin nI → String × ℕ × ℕ)
    (sl : List Slice) (G : GTab)
    (hinv : ∀ a (k i : Fin nI), inv a k i =
      (dqG G k.val : ℝ) * evalZ (hC sl k.val i.val) a / ((lamG G k.val : ℝ) * evalZ (dzC G k.val) a))
    (p q g : ℕ) : TabSpec nI where
  inv := inv
  coords := coords
  Hd := fixedHd nI sl
  dl := fixedDl nI G
  inv_eq := fixed_inv_eq sl G inv hinv
  p := p
  q := q
  g := g

theorem fixedDl_ne (nI : ℕ) (G : GTab) (P : ℝ → Prop)
    (hne : ∀ a, P a → ∀ k < nI, evalZ (dzC G k) a ≠ 0 ∧ (lamG G k : ℝ) ≠ 0) (hdq : ∀ k < nI, 1 ≤ dqG G k) :
    ∀ a, P a → ∀ j < nI, fixedDl nI G j a ≠ 0 := by
  intro a ha j hj
  rw [fixedDl, if_pos hj]
  obtain ⟨h1, h2⟩ := hne a ha j hj
  have h3 : (dqG G j : ℝ) ≠ 0 := by have := hdq j hj; positivity
  exact mul_ne_zero (div_ne_zero h2 h3) h1

/-- **`RowFactsT` of a row of a compact fixed table** from its bridge leaf (`FD.hC`), its denominator leaf
(`FD.lamG`, `FD.dqG`, `FD.dzC`) and its output-coordinate leaf (bit fields of `L.oinfo j`). -/
theorem rowFactsFixed_of {nI : ℕ} (T : TabSpec nI) (sl : List Slice) (G : GTab) (L : LTab)
    (hHd : T.Hd = fixedHd nI sl) (hdl : T.dl = fixedDl nI G)
    (hco : ∀ j (hj : j < nI), (T.coords ⟨j, hj⟩).2 = (oRow L j, oCol L j)) (hgq : T.g ≤ T.q)
    (j : ℕ) (hj : j < nI) (r : RowT) (W Wd : ℕ) (hW : 2 ≤ W) (hWd : 2 ≤ Wd)
    (hb : rowBridgeOk nI T.p T.q T.g W 1 r (fun m => FD.hC sl j m) = true)
    (hd : denOk T.p T.q T.g Wd r (FD.lamG G j) (FD.dqG G j) (FD.dzC G j) = true)
    (hc : Nat.land (Nat.shiftRight (L.oinfo j) 8) 255 = r.u ∧ Nat.land (Nat.shiftRight (L.oinfo j) 16) 255 = r.v) :
    RowFactsT T j r := by
  refine rowFactsT_of T hgq j hj r _ W Wd _ _ _ hW hWd hb hd ?_ ?_ ?_
  · intro m hm a
    rw [hHd, fixedHd, if_pos (And.intro hj hm), FD.hC_eq]
  · intro a
    rw [hdl, fixedDl, if_pos hj, FD.lamG_eq, FD.dqG_eq, FD.dzC_eq]
  · rw [hco j hj]
    exact Prod.ext hc.1 hc.2

end ThomsonCompact.Floor.B
