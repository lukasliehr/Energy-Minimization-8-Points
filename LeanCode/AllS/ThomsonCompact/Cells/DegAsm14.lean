import ThomsonCompact.Cells.DegAsm
import ThomsonCompact.Interface.D14
import ThomsonCompact.Floor.B.Active14

/-!
# The D14 parts of the cell assemblies 19–25 (F3g)

* `q`, `hfun`, **`target_link`**: the `Residual14.target_link` field (unit balance `β = 1`) with the computable
  target table `q r j = targetQ (tags r) j` (`CoeffMap.retained_target_sum`, `FixedD14.retainedIndex_tag`);
* `box_of_height`: `box_of_heightG` at the D14 anchor `35/2^7`, `σ = 2^-6`, in the form of `CellFactsT tab14`;
* `blk`, `hord_of`: literal blocks of decoded W0 data in the D14 block order (moment blocks `F0 … F6`, then the
  scalar blocks `M0_plus … Mdet_standard`) and their orders (used by the assemblies until F2's `W0Parts` exist).
-/

namespace ThomsonCompact.Cells.DegAsm.D14

open ThomsonCompact.Packed ThomsonCompact.Floor.B ThomsonCompact.CoeffMap
open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite
open scoped BigOperators

/-- D14 target table (`t = 14` Hermite coefficients `1 … 14`); computable. -/
noncomputable def q (r : Fin 145) (j : Fin 14) : ℚ := targetQ (ThomsonCompact.FixedD14.coordinateTags r) j

/-- Hermite coefficient `j + 1` of the exact target at exponent `s x` (β = 1 for all D14 cells). -/
noncomputable def hfun (s : ℝ → ℝ) (m : Fin 5 → ℕ) (j : Fin 14) (x : ℝ) : ℝ :=
  (hermitePolynomial (s x) (aS (s x)) m).coeff (j.val + 1)

/-- **Exactly the `Residual14.target_link` field.** -/
theorem target_link (s : ℝ → ℝ) (m : Fin 5 → ℕ) :
    ∀ (x : ℝ) (_hx : x ∈ cellDomain) (hs : 0 ≤ s x) (hm : Profile.Valid 14 m) (r : Fin 145),
      retainCompatible (aS (s x)) 14 (ThomsonCompact.Interface.D14.target s m x hs hm)
        (ThomsonCompact.FixedD14.retainedIndex r) = ∑ j, (q r j : ℝ) * hfun s m j x := by
  intro x _ hs hm r
  unfold ThomsonCompact.Interface.D14.target
  rw [retained_target_sum _ _ _ 14 (by norm_num), ThomsonCompact.FixedD14.retainedIndex_tag]
  simp only [one_mul, q, hfun]

/-- the height leaf puts `aS (s x)` into the D14 box `a0 + σ uf(t)` of the row leaves (either sign of the centre) -/
theorem box_of_height {N B W : ℕ} (hg : Good N 256 B W) {A : TM} {s : ℝ → ℝ}
    (hA : Encl (mkCtx N 256 B W) A (fun x => aS (s x))) (cb : CellB) (acN rg : ℕ)
    (hok : heightOk (mkCtx N 256 B W) A acN rg = true)
    (hac : (2 : ℤ) ^ 6 * acN = ((35 : ℕ) : ℤ) * 2 ^ (256 - 7 + 6) +
      (if cb.ucNeg then -(cb.ucN : ℤ) else cb.ucN))
    (hrg : cb.rN = 2 ^ 6 * rg) (hr : 0 < cb.rN) :
    ∀ x ∈ cellDomain, ∃ t ∈ Set.Icc (-1 : ℝ) 1, aS (s x) = tab14.a0 + tab14.σ * cb.uf t := by
  intro x hx
  obtain ⟨t, ht, h⟩ := box_of_heightG hg hA cb acN rg hok 35 7 6 (by norm_num) hac hrg hr x hx
  exact ⟨t, ht, h⟩

/-- literal blocks of decoded W0 data (D14 block order: `F0 … F6`, then `M0_plus … Mdet_standard`) -/
noncomputable def blk (d : CellData) : GramBlock 7 → Literals.Block
  | .inl k => d.block k.val
  | .inr b => d.block (7 + (ThomsonCompact.CoeffMap.D12.finOfScalar b).val)

end ThomsonCompact.Cells.DegAsm.D14
