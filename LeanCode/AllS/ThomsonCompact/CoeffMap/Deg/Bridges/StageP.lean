import ThomsonCompact.CoeffMap.Deg.W0Part
import ThomsonCompact.CoeffMap.Deg.StageZSound

/-!
# The `P` lookups of the two-stage leaves (F2h)

For the heavy blocks of the cells with large `N` or `N_W` the piece leaves read `P` from the stage-P lookup
`L.PS ctx A (WT b) zd b` (stored exact z columns, F2g's `CoeffMap.Deg.StageZ`). `hP_stage`: given the stage-Z facts
of the block (`hz`, from the `zStageOk` leaves via `zStageOk_spec`, `ZFacts.join_v/join_i`, `ZFacts.full`), the lookup
encloses the real `P` table `PfL` — the `hP` hypothesis of `w0Part_of<D>` (single-stage blocks: `hP_single`).
-/

namespace ThomsonCompact.CoeffMap.Deg.Link

open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite ThomsonCompact.CoeffMap ThomsonCompact.Packed
open ThomsonCompact.CoeffMap.Deg

variable {N S B W : ℕ}

theorem hmom_of (L : DegD) (d : ℕ) (p : MomentPivots d) (hF : LinkFacts L d p) (b : ℕ) :
    b < L.dH → L.piv b ≤ L.gdim b ∧ ∀ j, j ≤ L.gdim b → qAllZero (mP b j).s = true := by
  intro hb
  rw [hF.dH] at hb
  have h1 := hF.piv ⟨b, hb⟩
  have hp' := (p ⟨b, hb⟩).isLt
  refine ⟨by rw [h1, hF.gdim_mom ⟨b, hb⟩]; simp only at hp' ⊢; omega, fun j hj => hF.mom_rat ⟨b, hb⟩ j hj⟩

theorem hgood_of (L : DegD) (d : ℕ) (p : MomentPivots d) (hF : LinkFacts L d p) (b : ℕ) :
    b < L.dH → L.piv b ≤ L.gdim b ∧ L.rdim b = L.gdim b + 1 := by
  intro hb
  refine ⟨(hmom_of L d p hF b hb).1, ?_⟩
  rw [hF.dH] at hb
  rw [hF.rdim_mom ⟨b, hb⟩, hF.gdim_mom ⟨b, hb⟩]

/-- **`hP` for two-stage leaves**: the stage-P lookup of block `b` encloses the real `P` table, given the stage-Z
facts of the block. -/
theorem hP_stage (L : DegD) (d : ℕ) (p : MomentPivots d) (hF : LinkFacts L d p) (hg : Good N S B W) {A : TM}
    {a : ℝ → ℝ} (hA : Encl (mkCtx N S B W) A a) (data : CellData) (WT : ℕ → ℕ → ℕ → TM)
    (hW : ∀ b i j, EnclOk (mkCtx N S B W) (WT b i j) (litW data b i j)) (zd : ZData) (b : ℕ)
    (hz : ∀ v, v < L.rdim b → pivotOf (L.blockRow (mkCtx N S B W) A b v) = none → ∀ i, i < L.gdim b →
      L.zOk1 (mkCtx N S B W) zd b i v
        (zTMD (mkCtx N S B W) (L.blockRow (mkCtx N S B W) A b) (wRowsD (WT b) (L.gdim b)) i v) = true)
    (u v : ℕ) :
    EnclOk (mkCtx N S B W) (L.PS (mkCtx N S B W) A (WT b) zd b u v) (fun t => PfL L a data b u v t) :=
  PS_sound L hg zd b (hW b) (fun i j t ht => litW_symm data b i j t ht)
    (fun u => blockRow_ok L hg hA hF.rec0 b (hmom_of L d p hF b) u)
    (fun u hu => blockRow_good L _ A b (hgood_of L d p hF b) u hu) hz u v

#print axioms hP_stage

end ThomsonCompact.CoeffMap.Deg.Link
