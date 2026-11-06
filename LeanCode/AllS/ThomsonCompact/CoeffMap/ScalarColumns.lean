import ThomsonCompact.CoeffMap.Cols.M0Plus
import ThomsonCompact.CoeffMap.Cols.M0Sign
import ThomsonCompact.CoeffMap.Cols.M0Standard
import ThomsonCompact.CoeffMap.Cols.M1Even
import ThomsonCompact.CoeffMap.Cols.M1Odd
import ThomsonCompact.CoeffMap.Cols.MdetPlus
import ThomsonCompact.CoeffMap.Cols.MdetStandard

/-!
# D12 scalar columns from the packed RF tables (F2b a)

`Kpk a b u i = (rec (colRec (bIdx b) i u)).value a` are the 88 D12 scalar kernel columns, evaluated from the
packed records. `scalarColumns_of_den`: wherever the 28 shared denominator polynomials do not vanish (per cell:
from the reciprocal TMs of the denominators), `Kpk a` satisfies `ScalarColumns`, i.e. the hypothesis of
`W0_link`. The proof replays the 88 old `RFScalarFeatures` lemmas through the record bridges.
-/

namespace ThomsonCompact.CoeffMap.D12RF

open Blueprint.CAP Blueprint.Thomson.Finite ThomsonCompact.CoeffMap.D12 ThomsonCompact.Packed

/-- Block index in the RF tables (generator order). -/
def bIdx : ScalarBlockName → Nat
  | .m0Plus => 0
  | .m0Sign => 1
  | .m0Standard => 2
  | .m1Even => 3
  | .m1Odd => 4
  | .mdetPlus => 5
  | .mdetSign => 6
  | .mdetStandard => 7

/-- The packed scalar column matrices at height `a`. -/
noncomputable def Kpk (a : ℝ) : ScalarK := fun b u i => (rec (colRec (bIdx b) i.val u.val)).value a

theorem scalarColumns_rf (a : ℝ) (ha : physical a) (hdef : ∀ k, k < nRec → (rec k).toRatFun.DefinedAt a) :
    ScalarColumns a (Kpk a) := by
  intro b
  cases b
  · exact ⟨block_m0Plus_0 a ha hdef, fun h => absurd h (by decide)⟩
  · exact ⟨block_m0Sign_0 a ha hdef, fun h => absurd h (by decide)⟩
  · exact ⟨block_m0Standard_0 a ha hdef, fun _ => block_m0Standard_1 a ha hdef⟩
  · exact ⟨block_m1Even_0 a ha hdef, fun h => absurd h (by decide)⟩
  · exact ⟨block_m1Odd_0 a ha hdef, fun h => absurd h (by decide)⟩
  · exact ⟨block_mdetPlus_0 a ha hdef, fun h => absurd h (by decide)⟩
  · refine ⟨fun i => ?_, fun h => absurd h (by decide)⟩
    have h1 := i.isLt
    have h2 : scalarBlockDimension .mdetSign 6 = 0 := ThomsonCompact.Interface.D12.scalarDims .mdetSign
    omega
  · exact ⟨block_mdetStandard_0 a ha hdef, fun _ => block_mdetStandard_1 a ha hdef⟩

/-- **Scalar columns from nonvanishing shared denominators.** -/
theorem scalarColumns_of_den (a : ℝ) (ha : physical a) (hden : ∀ d, d < nDen → evalZ (denPoly d) a ≠ 0) :
    ScalarColumns a (Kpk a) :=
  scalarColumns_rf a ha (definedAt_of_den a hden)

/-- `W0_link` with the packed columns, given the per-cell denominator facts. -/
theorem W0_link_pk (s : ℝ → ℝ) (cell : Literals.Cell) (blk : GramBlock 6 → Literals.Block)
    (hord : ∀ b, (blk b).order = gramBlockDimension 6 b)
    (hden : ∀ x ∈ cellDomain, 0 ≤ s x → ∀ d, d < nDen → evalZ (denPoly d) (aS (s x)) ≠ 0) :
    ∀ (x : ℝ) (hx : x ∈ cellDomain) (hs : 0 ≤ s x) (r : Fin 100),
      retainCompatible (aS (s x)) 12
        (ThomsonCompact.Interface.D12.gramMap s x hs (ThomsonCompact.Interface.D12.W0 cell blk hord x hx))
        (FixedTables.D12.retainedIndex r) = ∑ b, g12 s Kpk cell blk hord b r x :=
  W0_link s Kpk cell blk hord (fun x hx hs => scalarColumns_of_den _ (aS_physical _ hs) (hden x hx hs))

#print axioms scalarColumns_of_den
#print axioms W0_link_pk

end ThomsonCompact.CoeffMap.D12RF
