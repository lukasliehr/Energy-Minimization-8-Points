import ThomsonCompact.Cells.DegAsm
import ThomsonCompact.Interface.D18
import ThomsonCompact.Floor.B.Active18
import ThomsonCompact.Target.Link

/-!
# The D18 parts of the cell assemblies 29 (F3g; Riesz balance)

* `q`, **`target_link`**: the `Residual18.target_link` field for the Riesz normalization
  `β x = balancedMultiplier c (s x)` (`c` = cell center) with the computable target table `q r j = targetQ (tags r) j`
  and `hfun = Target.hfunR c s m` (`Target.riesz_target_link`, `Blueprint.CAP.FixedTables.D18.retainedIndex_tag`); `beta_pos`;
* `box_of_height`: `box_of_heightG` at the D18 anchor `1083/2^12`, `σ = 2^-10`, in the form of `CellFactsT tab18`;
* `blk`: literal blocks of decoded W0 data in the D18 block order (moment blocks `F0 … F8`, then the scalar blocks
  `M0_plus … Mdet_standard`; used by the assemblies until F2's `W0Parts` exist).
-/

namespace ThomsonCompact.Cells.DegAsm.D18

open ThomsonCompact.Packed ThomsonCompact.Floor.B ThomsonCompact.CoeffMap
open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite
open scoped BigOperators

/-- D18 target table (`t = 18` Hermite coefficients `1 … 18`); computable. -/
noncomputable def q (r : Fin 272) (j : Fin 18) : ℚ := targetQ (Blueprint.CAP.FixedTables.D18.coordinateTags r) j

/-- **Exactly the `Residual18.target_link` field** for `β x = balancedMultiplier c (s x)`. -/
theorem target_link (c : ℝ) (s : ℝ → ℝ) (m : Fin 5 → ℕ) :
    ∀ (x : ℝ) (_hx : x ∈ cellDomain) (hs : 0 ≤ s x) (hm : Profile.Valid 18 m) (r : Fin 272),
      retainCompatible (aS (s x)) 18
        (ThomsonCompact.Interface.D18.target s (fun y => balancedMultiplier c (s y)) m x hs hm)
        (Blueprint.CAP.FixedTables.D18.retainedIndex r) = ∑ j, (q r j : ℝ) * ThomsonCompact.Target.hfunR c s m j x := by
  intro x _ hs hm r
  have h := ThomsonCompact.Target.riesz_target_link c s 18 (by norm_num) m x hs hm (Blueprint.CAP.FixedTables.D18.retainedIndex r)
  rw [Blueprint.CAP.FixedTables.D18.retainedIndex_tag] at h
  exact h

/-- `β > 0` on the cell (`c > 0`, `s > 0`) -/
theorem beta_pos (c : ℝ) (s : ℝ → ℝ) (hc : 0 < c) (hs : ∀ x ∈ cellDomain, 0 < s x) :
    ∀ x ∈ cellDomain, 0 < balancedMultiplier c (s x) :=
  fun x hx => balancedMultiplier_pos c (s x) hc (hs x hx)

/-- the height leaf puts `aS (s x)` into the D18 box `a0 + σ uf(t)` of the row leaves (either sign of the centre) -/
theorem box_of_height {N B W : ℕ} (hg : Good N 256 B W) {A : TM} {s : ℝ → ℝ}
    (hA : Encl (mkCtx N 256 B W) A (fun x => aS (s x))) (cb : CellB) (acN rg : ℕ)
    (hok : heightOk (mkCtx N 256 B W) A acN rg = true)
    (hac : (2 : ℤ) ^ 10 * acN = ((1083 : ℕ) : ℤ) * 2 ^ (256 - 12 + 10) +
      (if cb.ucNeg then -(cb.ucN : ℤ) else cb.ucN))
    (hrg : cb.rN = 2 ^ 10 * rg) (hr : 0 < cb.rN) :
    ∀ x ∈ cellDomain, ∃ t ∈ Set.Icc (-1 : ℝ) 1, aS (s x) = tab18.a0 + tab18.σ * cb.uf t := by
  intro x hx
  obtain ⟨t, ht, h⟩ := box_of_heightG hg hA cb acN rg hok 1083 12 10 (by norm_num) hac hrg hr x hx
  exact ⟨t, ht, h⟩

/-- literal blocks of decoded W0 data (D18 block order: `F0 … F8`, then `M0_plus … Mdet_standard`) -/
noncomputable def blk (d : CellData) : GramBlock 9 → Literals.Block
  | .inl k => d.block k.val
  | .inr b => d.block (9 + (ThomsonCompact.CoeffMap.D12.finOfScalar b).val)

end ThomsonCompact.Cells.DegAsm.D18
