import ThomsonCompact.Cells.DegAsm
import ThomsonCompact.Interface.D16
import ThomsonCompact.Floor.B.Active16
import ThomsonCompact.Target.Link

/-!
# The D16 parts of the cell assemblies 26–28 (F3g; Riesz balance)

* `q`, **`target_link`**: the `Residual16.target_link` field for the Riesz normalization
  `β x = balancedMultiplier c (s x)` (`c` = cell center) with the computable target table `q r j = targetQ (tags r) j`
  and `hfun = Target.hfunR c s m` (`Target.riesz_target_link`, `ThomsonCompact.FixedD16.retainedIndex_tag`); `beta_pos`;
* `box_of_height`: `box_of_heightG` at the D16 anchor `68/2^8`, `σ = 2^-8`, in the form of `CellFactsT tab16`;
* `blk`: literal blocks of decoded W0 data in the D16 block order (moment blocks `F0 … F7`, then the scalar blocks
  `M0_plus … Mdet_standard`; used by the assemblies until F2's `W0Parts` exist).
-/

namespace ThomsonCompact.Cells.DegAsm.D16

open ThomsonCompact.Packed ThomsonCompact.Floor.B ThomsonCompact.CoeffMap
open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite
open scoped BigOperators

/-- D16 target table (`t = 16` Hermite coefficients `1 … 16`); computable. -/
noncomputable def q (r : Fin 202) (j : Fin 16) : ℚ := targetQ (ThomsonCompact.FixedD16.coordinateTags r) j

/-- **Exactly the `Residual16.target_link` field** for `β x = balancedMultiplier c (s x)`. -/
theorem target_link (c : ℝ) (s : ℝ → ℝ) (m : Fin 5 → ℕ) :
    ∀ (x : ℝ) (_hx : x ∈ cellDomain) (hs : 0 ≤ s x) (hm : Profile.Valid 16 m) (r : Fin 202),
      retainCompatible (aS (s x)) 16
        (ThomsonCompact.Interface.D16.target s (fun y => balancedMultiplier c (s y)) m x hs hm)
        (ThomsonCompact.FixedD16.retainedIndex r) = ∑ j, (q r j : ℝ) * ThomsonCompact.Target.hfunR c s m j x := by
  intro x _ hs hm r
  have h := ThomsonCompact.Target.riesz_target_link c s 16 (by norm_num) m x hs hm (ThomsonCompact.FixedD16.retainedIndex r)
  rw [ThomsonCompact.FixedD16.retainedIndex_tag] at h
  exact h

/-- `β > 0` on the cell (`c > 0`, `s > 0`) -/
theorem beta_pos (c : ℝ) (s : ℝ → ℝ) (hc : 0 < c) (hs : ∀ x ∈ cellDomain, 0 < s x) :
    ∀ x ∈ cellDomain, 0 < balancedMultiplier c (s x) :=
  fun x hx => balancedMultiplier_pos c (s x) hc (hs x hx)

/-- the height leaf puts `aS (s x)` into the D16 box `a0 + σ uf(t)` of the row leaves (either sign of the centre) -/
theorem box_of_height {N B W : ℕ} (hg : Good N 256 B W) {A : TM} {s : ℝ → ℝ}
    (hA : Encl (mkCtx N 256 B W) A (fun x => aS (s x))) (cb : CellB) (acN rg : ℕ)
    (hok : heightOk (mkCtx N 256 B W) A acN rg = true)
    (hac : (2 : ℤ) ^ 8 * acN = ((68 : ℕ) : ℤ) * 2 ^ (256 - 8 + 8) +
      (if cb.ucNeg then -(cb.ucN : ℤ) else cb.ucN))
    (hrg : cb.rN = 2 ^ 8 * rg) (hr : 0 < cb.rN) :
    ∀ x ∈ cellDomain, ∃ t ∈ Set.Icc (-1 : ℝ) 1, aS (s x) = tab16.a0 + tab16.σ * cb.uf t := by
  intro x hx
  obtain ⟨t, ht, h⟩ := box_of_heightG hg hA cb acN rg hok 68 8 8 (by norm_num) hac hrg hr x hx
  exact ⟨t, ht, h⟩

/-- literal blocks of decoded W0 data (D16 block order: `F0 … F7`, then `M0_plus … Mdet_standard`) -/
noncomputable def blk (d : CellData) : GramBlock 8 → Literals.Block
  | .inl k => d.block k.val
  | .inr b => d.block (8 + (ThomsonCompact.CoeffMap.D12.finOfScalar b).val)

end ThomsonCompact.Cells.DegAsm.D16
