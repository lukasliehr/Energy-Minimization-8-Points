import ThomsonCompact.CoeffMap.Deg.Bridges.StageP
import ThomsonCompact.CoeffMap.Deg.ShiftSound

/-!
# The `P` lookups of the leaves with re-centred records (F2i)

The D16/D18 cells evaluate the scalar RF records from the re-centred per-degree table `LS` (`CoeffMap.Deg.Shift`,
data `D<D>/RFS.lean`) at the shifted height TM; the rows still enclose the real rows `L.blockRowF` of the old records
(`DegD.blockRowC_ok`, from the one-time shift facts `OneTime/D<D>/ShiftFacts.shiftFacts`). Hence the `P` lookups
enclose the same real `P` tables `PfL` as `hP_single` / `hP_stage`, and `w0Part_of<D>` / `bsum_valid<D>` apply
unchanged:

* `hP_singleC`: single-stage leaves (`pLookC`, Gram lookup `WT` with TM symmetry, e.g. `WTn`);
* `hP_stageC`: two-stage leaves (`PSC`); stage Z may use another Gram lookup (`WTz`, e.g. `WTr`) than stage P
  (`WTp`, e.g. `WTt`), both enclosing the literal Gram entries.
-/

namespace ThomsonCompact.CoeffMap.Deg.Link

open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite ThomsonCompact.CoeffMap ThomsonCompact.Packed
open ThomsonCompact.CoeffMap.Deg

variable {N S B W : ℕ}

/-- **`hP` for single-stage leaves with re-centred records.** -/
theorem hP_singleC (L LS : DegD) (m k : ℕ) (d : ℕ) (p : MomentPivots d) (hF : LinkFacts L d p)
    (hsh : ∀ i, i < L.nRec → ∀ y : ℝ, (LS.rfRec i).value (y - m / 2 ^ k) = (L.rfRec i).value y)
    (hg : Good N S B W) {A : TM} {a : ℝ → ℝ} (hA : Encl (mkCtx N S B W) A a) (data : CellData)
    (WT : ℕ → ℕ → ℕ → TM) (hW : ∀ b i j, EnclOk (mkCtx N S B W) (WT b i j) (litW data b i j))
    (hWsym : ∀ b i j, WT b i j = WT b j i) (b : ℕ) (u v : ℕ) :
    EnclOk (mkCtx N S B W) (L.pLookC LS m k (mkCtx N S B W) A (WT b) b u v) (fun t => PfL L a data b u v t) :=
  pLookC_sound L LS m k hg b (hW b) (fun u => DegD.blockRowC_ok L LS m k hg hA hsh hF.rec0 b (hmom_of L d p hF b) u)
    (fun u hu => DegD.blockRowC_good L LS m k _ A b (hgood_of L d p hF b) u hu) (hWsym b)
    (fun i j t ht => litW_symm data b i j t ht) u v

/-- **`hP` for two-stage leaves with re-centred records** (stage-Z facts with `WTz`, stage-P lookup with `WTp`). -/
theorem hP_stageC (L LS : DegD) (m k : ℕ) (d : ℕ) (p : MomentPivots d) (hF : LinkFacts L d p)
    (hsh : ∀ i, i < L.nRec → ∀ y : ℝ, (LS.rfRec i).value (y - m / 2 ^ k) = (L.rfRec i).value y)
    (hg : Good N S B W) {A : TM} {a : ℝ → ℝ} (hA : Encl (mkCtx N S B W) A a) (data : CellData)
    (WTz WTp : ℕ → ℕ → ℕ → TM) (hWz : ∀ b i j, EnclOk (mkCtx N S B W) (WTz b i j) (litW data b i j))
    (hWp : ∀ b i j, EnclOk (mkCtx N S B W) (WTp b i j) (litW data b i j)) (zd : ZData) (b : ℕ)
    (hz : ∀ v, v < L.rdim b → pivotOf (L.blockRowC LS m k (mkCtx N S B W) A b v) = none → ∀ i, i < L.gdim b →
      L.zOk1 (mkCtx N S B W) zd b i v
        (zTMD (mkCtx N S B W) (L.blockRowC LS m k (mkCtx N S B W) A b) (wRowsD (WTz b) (L.gdim b)) i v) = true)
    (u v : ℕ) :
    EnclOk (mkCtx N S B W) (L.PSC LS m k (mkCtx N S B W) A (WTp b) zd b u v) (fun t => PfL L a data b u v t) :=
  PSC_sound L LS m k hg zd b (hWz b) (hWp b) (fun i j t ht => litW_symm data b i j t ht)
    (fun u => DegD.blockRowC_ok L LS m k hg hA hsh hF.rec0 b (hmom_of L d p hF b) u)
    (fun u hu => DegD.blockRowC_good L LS m k _ A b (hgood_of L d p hF b) u hu) hz u v

#print axioms hP_singleC
#print axioms hP_stageC

end ThomsonCompact.CoeffMap.Deg.Link
