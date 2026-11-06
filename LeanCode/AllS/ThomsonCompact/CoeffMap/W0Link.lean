import ThomsonCompact.Interface.D12
import ThomsonCompact.CoeffMap.Target
import ThomsonCompact.CoeffMap.RawD12
import AllS.Units.N_AI.N_fixed_tables.FullGramSourceSupport
import AllS.Units.N_AI.N_fixed_tables.RetainedGramSupport
import AllS.Units.N_AI.N_residual_replay.ScalarKernelPolynomialSupport

/-!
# Generic D12 W0 link (F2a, no Taylor models)

The retained coordinates of `gramMap s x hs W` are, for every Gram family `W`,
`∑ b, contribution a K W b t` with `a = aS (s x)`, `t = coordinateTags r` and

  `contribution a K W b t = ∑ i j, W b i j · ∑ u v, Kb u i · Kb v j · Cb(t) u v`,

where `Kb` is the block's raw column matrix (moment blocks: the proven `momentKernelMatrix a 6 pivots k`;
scalar blocks: any matrix `K b` whose columns expand the scalar features in the raw scalar basis,
`ScalarColumns a K`) and `Cb(t) u v = rawIntegerLookup (source u v) t / den` is the computable rational
coefficient of the proven raw tensor `RawMomentTensors.D12_Fk` / `RawScalarTensors.D12_b` at tag `t`.

Nothing here depends on a cell. `W0_link` is the `Residual12.W0_link` field for `g = g12 s K cell blk hord`
(`nb = 14`, blocks in `blockEquiv` order), under the per-cell hypothesis that `K (aS (s x))` are scalar columns
on the cell (from the RF kernel columns, see `CoeffMap/RFData` and the report).
-/

noncomputable section
open scoped BigOperators

namespace ThomsonCompact.CoeffMap.D12

open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite

abbrev pivots := ThomsonCompact.Interface.D12.pivots

/-! ## Scalar columns, source kernels and block contributions -/

/-- Scalar column matrices (one per scalar block). -/
abbrev ScalarK := (b : ScalarBlockName) → Matrix (Fin (rawSize b)) (Fin (scalarBlockDimension b 6)) ℝ

/-- `K` expands the D12 scalar features at height `a` in the raw scalar bases (both components of the
two-component blocks use the same columns). -/
def ScalarColumns (a : ℝ) (K : ScalarK) : Prop :=
  ∀ b : ScalarBlockName,
    (∀ i, scalarFeature b a 6 0 i = ∑ u, MvPolynomial.C (K b u i) * rawScalarBasis b false (rawTags b u)) ∧
    (scalarBlockStandard b = true →
      ∀ i, scalarFeature b a 6 1 i = ∑ u, MvPolynomial.C (K b u i) * rawScalarBasis b true (rawTags b u))

/-- Column matrix of every block: moment blocks by the proven pivot nullspace formula. -/
def blockMatrix (a : ℝ) (K : ScalarK) : (b : GramBlock 6) →
    Matrix (Fin (rawDim b)) (Fin (gramBlockDimension 6 b)) ℝ
  | .inl k => momentKernelMatrix a 6 pivots k
  | .inr b => K b

/-- Source kernel (invariant coordinates) of every Gram kernel entry. -/
def sourceKernel (a : ℝ) (K : ScalarK) : (b : GramBlock 6) →
    Fin (gramBlockDimension 6 b) → Fin (gramBlockDimension 6 b) → Poly3
  | .inl k => momentCoordinateKernel a 6 pivots k (momQ k)
  | .inr b => scalarCoordinateKernel b 6 (K b) (rawQ b)

theorem sourceKernel_subst (a : ℝ) (K : ScalarK) (hK : ScalarColumns a K) (b : GramBlock 6)
    (i j : Fin (gramBlockDimension 6 b)) :
    invariantSubst (sourceKernel a K b i j) = gramKernel a 6 pivots b i j := by
  cases b with
  | inl k => exact momentCoordinateKernel_subst a 6 pivots k (momQ k) (momQ_subst k) i j
  | inr b =>
    cases hst : scalarBlockStandard b
    · exact scalarCoordinateKernel_subst_nonstandard a b 6 (rawTags b) (K b) (rawQ b) hst
        (rawQ_subst b) (hK b).1 i j
    · exact scalarCoordinateKernel_subst a b 6 (rawTags b) (K b) (rawQ b) (rawQ_subst b) (hK b).1
        ((hK b).2 hst) i j

theorem sourceKernel_coeff (a : ℝ) (K : ScalarK) (b : GramBlock 6) (i j : Fin (gramBlockDimension 6 b))
    (t : Tag) :
    MvPolynomial.coeff (tagExponent t) (sourceKernel a K b i j) =
      ∑ u, ∑ v, blockMatrix a K b u i * blockMatrix a K b v j * (blockCoef b t u v : ℝ) := by
  cases b with
  | inl k =>
    simp only [sourceKernel, momentCoordinateKernel, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
      momQ, integerSparsePolynomial_coeff, blockMatrix, blockCoef]
    push_cast
    rfl
  | inr b =>
    simp only [sourceKernel, scalarCoordinateKernel, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
      rawQ, integerSparsePolynomial_coeff, blockMatrix, blockCoef]
    push_cast
    rfl

/-- W0 contribution of block `b` to the retained coordinate with tag `t`. -/
def contribution (a : ℝ) (K : ScalarK) (W : GramMatrices 6) (b : GramBlock 6) (t : Tag) : ℝ :=
  ∑ i, ∑ j, W b i j * ∑ u, ∑ v, blockMatrix a K b u i * blockMatrix a K b v j * (blockCoef b t u v : ℝ)

/-- **Generic retained Gram coordinates** (any Gram family, any height with scalar columns). -/
theorem retained_gram (a : ℝ) (ha : physical a) (K : ScalarK) (hK : ScalarColumns a K)
    (W : GramFamily 6) (r : Fin 100) :
    retainCompatible a 12 (gramCompatible a ha 12 (Or.inl rfl) pivots
      ThomsonCompact.Interface.D12.pivots_valid W) (FixedTables.D12.retainedIndex r) =
      ∑ b, contribution a K W.val b (FixedTables.D12.coordinateTags r) := by
  refine (fixedGram_retained_of_source a ha 6 (by norm_num) (by norm_num) pivots
    ThomsonCompact.Interface.D12.pivots_valid W (fixedGramSource (sourceKernel a K) W)
    (fixedGramSource_canonical a pivots (sourceKernel a K) (sourceKernel_subst a K hK) W)
    (FixedTables.D12.retainedIndex r)).trans ?_
  rw [fixedGramSource_coefficient, FixedTables.D12.retainedIndex_tag]
  simp only [contribution, sourceKernel_coeff]

/-! ## Interface form (`nb = 14`) -/

/-- Block contributions of the literal W0 of a cell (the `g` of `Residual12`). -/
def g12 (s : ℝ → ℝ) (K : ℝ → ScalarK) (cell : Literals.Cell) (blk : GramBlock 6 → Literals.Block)
    (hord : ∀ b, (blk b).order = gramBlockDimension 6 b) (b : Fin 14) (r : Fin 100) (x : ℝ) : ℝ :=
  contribution (aS (s x)) (K (aS (s x))) (ThomsonCompact.Interface.D12.W0mat cell blk hord x)
    (blockEquiv b) (FixedTables.D12.coordinateTags r)

/-- **`Residual12.W0_link`** for `g12`, given scalar columns on the cell. -/
theorem W0_link (s : ℝ → ℝ) (K : ℝ → ScalarK) (cell : Literals.Cell)
    (blk : GramBlock 6 → Literals.Block) (hord : ∀ b, (blk b).order = gramBlockDimension 6 b)
    (hK : ∀ x ∈ cellDomain, 0 ≤ s x → ScalarColumns (aS (s x)) (K (aS (s x)))) :
    ∀ (x : ℝ) (hx : x ∈ cellDomain) (hs : 0 ≤ s x) (r : Fin 100),
      retainCompatible (aS (s x)) 12
        (ThomsonCompact.Interface.D12.gramMap s x hs (ThomsonCompact.Interface.D12.W0 cell blk hord x hx))
        (FixedTables.D12.retainedIndex r) = ∑ b, g12 s K cell blk hord b r x := by
  intro x hx hs r
  rw [ThomsonCompact.Interface.D12.gramMap, retained_gram _ _ _ (hK x hx hs)]
  exact (Fintype.sum_equiv blockEquiv _ _ (fun _ => rfl)).symm

/-- `Residual12.target_link` verbatim (the interface target unfolds to the generic one). -/
theorem target_link_field (s : ℝ → ℝ) (m : Fin 5 → ℕ) :
    ∀ (x : ℝ) (_hx : x ∈ cellDomain) (hs : 0 ≤ s x) (hm : Profile.Valid 12 m) (r : Fin 100),
      retainCompatible (aS (s x)) 12 (ThomsonCompact.Interface.D12.target s m x hs hm)
        (FixedTables.D12.retainedIndex r) = ∑ j, (q r j : ℝ) * hfun s m j x :=
  target_link s m

#print axioms retained_gram
#print axioms W0_link
#print axioms target_link_field

end ThomsonCompact.CoeffMap.D12
