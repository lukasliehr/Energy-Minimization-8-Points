import ThomsonCompact.Fixed.D18c.Old
import AllS.Units.N_FI.N_certificate.N_corrected_gram
import AllS.Units.N_FI.N_cell_soundness.N_affine_cell
import AllS.Units.N_AI.N_gram_replay.LiteralGramSupport
import AllS.Units.N_AI.N_gram_replay.CorrectedShortMetricSupport
import AllS.Units.N_AI.N_correction_bounds.StructuredInverseInsertionSupport
import AllS.Units.N_AI.N_correction_bounds.OutputInsertionSupport
import AllS.Units.N_AI.N_correction_bounds.OutputInsertionSupportD18
import AllS.Units.N_AI.N_residual_replay.StructuredCenterSupport
import AllS.Units.N_F.N_height_upper

/-!
# Frozen per-cell interface for the D18 cells (workstream F0)

Same pattern as `ThomsonCompact.Interface.D18` (see its docstring for the list of products and their
old definitions), for degree 18: `GramBlock 9`, 272 retained coordinates, moment pivots
`[0,1,0,1,0,0,0,0,0]`, the proven `FixedTables.D18` right inverse, and a Riesz-balanced target
normalization `β x > 0` (all D16/D18 cells use `balance = riesz`; all D12 and D14 cells use `unit`).
The four corrected blocks are again F0, F1, M0_plus, M0_standard.
-/

noncomputable section
open scoped BigOperators

namespace ThomsonCompact.Interface.D18

open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite

/-! ## D18 layout -/

/-- Moment pivots `[0,1,0,1,0,0,0,0,0]` (the D18 witness; D14/D16 witnesses share the first two). -/
def pivots : MomentPivots 9 := fun k => ⟨![0, 1, 0, 1, 0, 0, 0, 0, 0] k, by fin_cases k <;> decide⟩

theorem pivots_valid : ValidMomentPivots pivots := by
  intro k
  fin_cases k
  · exact ⟨0, rfl⟩
  · exact ⟨6, rfl⟩
  · exact ⟨7, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨5, rfl⟩
  · exact ⟨8, rfl⟩
  · exact ⟨9, rfl⟩
  · exact ⟨10, rfl⟩

/-- The D18 fixed-table right inverse on compatible polynomials (recovery proven compactly in `Fixed/D18c`). -/
def rightInverse (a : ℝ) (f : Compatible a 18) : GramFamily 9 :=
  FixedTables.D18.correctionLinear a (ThomsonCompact.FixedD18.retainedVector a f)

theorem rightInverse_recovery (a : ℝ) (ha : physical a) (f : Compatible a 18) :
    gramPoly a 9 pivots (rightInverse a f) = f.val :=
  ThomsonCompact.FixedD18.correctionLinear_full_recovery_old a ha pivots pivots_valid rfl rfl f

/-- Scalar block dimensions of the D18 layout. -/
def scalarOrder : ScalarBlockName → ℕ
  | .m0Plus => 48
  | .m0Sign => 21
  | .m0Standard => 65
  | .m1Even => 83
  | .m1Odd => 61
  | .mdetPlus => 26
  | .mdetSign => 9
  | .mdetStandard => 32

theorem scalarDims (b : ScalarBlockName) : scalarBlockDimension b 9 = scalarOrder b := by
  cases b <;>
    simp only [scalarBlockDimension, scalarOrder, standardTagList, invariantPivots,
      signPivots, standardPivots, parityPivots, Nat.reduceSub, Bool.false_eq_true,
      if_false, if_true, RawCatalogue.invariantTagList_1, RawCatalogue.invariantTagList_2,
      RawCatalogue.invariantTagList_3, RawCatalogue.invariantTagList_4,
      RawCatalogue.invariantTagList_5, RawCatalogue.invariantTagList_6,
      RawCatalogue.invariantTagList_7, RawCatalogue.invariantTagList_8,
      RawCatalogue.invariantTagList_9, RawCatalogue.parityTagList_3,
      RawCatalogue.parityTagList_4, RawCatalogue.parityTagList_5, RawCatalogue.parityTagList_6,
      RawCatalogue.parityTagList_7, RawCatalogue.parityTagList_8, RawCatalogue.parityTagList_9] <;>
    decide +kernel

/-- `hord` from the 17 literal block orders. -/
theorem hord_of_orders (blk : GramBlock 9 → Literals.Block)
    (hm : ∀ k : Fin 9, (blk (.inl k)).order = 9 - k.val)
    (hs : ∀ b : ScalarBlockName, (blk (.inr b)).order = scalarOrder b) :
    ∀ b, (blk b).order = gramBlockDimension 9 b := by
  intro b
  cases b with
  | inl k => exact hm k
  | inr b => exact (hs b).trans (scalarDims b).symm

/-! ## Exponent, target, Gram map and the literal W0 -/

theorem s_nonneg_of_affine {c h : ℝ} {s : ℝ → ℝ} (hh : 0 < h) (hc0 : 0 ≤ c - h)
    (hsa : ∀ x, s x = c + h * x) : ∀ x ∈ cellDomain, 0 ≤ s x := by
  intro x hx
  rw [hsa x]
  have h1 : -1 ≤ x := hx.1
  nlinarith

/-- The balanced normalized target (normalization `β x`) at exponent `s x`. -/
def target (s β : ℝ → ℝ) (m : Fin 5 → ℕ) (x : ℝ) (hs : 0 ≤ s x) (hm : Profile.Valid 18 m) :
    Compatible (aS (s x)) 18 :=
  normalizedTargetCompatible (s x) (aS (s x)) (β x) 18 m hs (aS_physical _ hs)
    (aS_mem_and_root _ hs).2 hm

/-- The D18 Gram map at height `aS (s x)`. -/
def gramMap (s : ℝ → ℝ) (x : ℝ) (hs : 0 ≤ s x) :
    GramFamily 9 →ₗ[ℝ] Compatible (aS (s x)) 18 :=
  gramCompatible (aS (s x)) (aS_physical _ hs) 18 (Or.inr (Or.inr (Or.inr rfl))) pivots
    pivots_valid

/-- Literal Bernstein-square Gram blocks, transported to the Gram block dimensions. -/
def W0mat (cell : Literals.Cell) (blk : GramBlock 9 → Literals.Block)
    (hord : ∀ b, (blk b).order = gramBlockDimension 9 b) (x : ℝ) : GramMatrices 9 :=
  fun b => (literalGram cell (blk b) x).submatrix (finCongr (hord b)).symm (finCongr (hord b)).symm

theorem W0mat_posDef (cell : Literals.Cell) (blk : GramBlock 9 → Literals.Block)
    (hord : ∀ b, (blk b).order = gramBlockDimension 9 b) (x : ℝ) (hx : x ∈ cellDomain)
    (b : GramBlock 9) : (W0mat cell blk hord x b).PosDef :=
  (literalGram_floor cell (blk b) x hx).2.submatrix (finCongr (hord b)).symm.injective

theorem isSymm_of_posDef {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (h : M.PosDef) : M.IsSymm := by
  have hH := h.isHermitian
  unfold Matrix.IsHermitian at hH
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hH
  exact hH

/-- The generic initial Gram family of a D18 cell (the old per-cell `InitialGram_Data.W0`). -/
def W0 (cell : Literals.Cell) (blk : GramBlock 9 → Literals.Block)
    (hord : ∀ b, (blk b).order = gramBlockDimension 9 b) (x : ℝ) (hx : x ∈ cellDomain) :
    GramFamily 9 :=
  ⟨W0mat cell blk hord x, by
    intro b
    exact isSymm_of_posDef (W0mat_posDef cell blk hord x hx b)⟩

theorem W0_val (cell : Literals.Cell) (blk : GramBlock 9 → Literals.Block)
    (hord : ∀ b, (blk b).order = gramBlockDimension 9 b) (x : ℝ) (hx : x ∈ cellDomain) :
    (W0 cell blk hord x hx).val = W0mat cell blk hord x := rfl

/-! ## Products -/

/-- Residual products: TM-valid target and W0-contribution models, their links to the old target and
Gram map, the structured residual gate and the rational centers. -/
structure Residual18 (s β : ℝ → ℝ) (m : Fin 5 → ℕ) (cell : Literals.Cell)
    (blk : GramBlock 9 → Literals.Block) (hord : ∀ b, (blk b).order = gramBlockDimension 9 b)
    (N t nb : ℕ) where
  H : Fin t → QModel N
  hfun : Fin t → ℝ → ℝ
  H_valid : ∀ j, (H j).asTM.Valid (hfun j)
  q : Fin 272 → Fin t → ℚ
  target_link : ∀ (x : ℝ) (_hx : x ∈ cellDomain) (hs : 0 ≤ s x) (hm : Profile.Valid 18 m)
    (r : Fin 272), retainCompatible (aS (s x)) 18 (target s β m x hs hm)
      (FixedTables.D18.retainedIndex r) = ∑ j, (q r j : ℝ) * hfun j x
  B : Fin nb → Fin 272 → QModel N
  g : Fin nb → Fin 272 → ℝ → ℝ
  B_valid : ∀ b r, (B b r).asTM.Valid (g b r)
  W0_link : ∀ (x : ℝ) (hx : x ∈ cellDomain) (hs : 0 ≤ s x) (r : Fin 272),
    retainCompatible (aS (s x)) 18 (gramMap s x hs (W0 cell blk hord x hx))
      (FixedTables.D18.retainedIndex r) = ∑ b, g b r x
  Rm : Fin 272 → QModel N
  gate : StructuredResidualGate H B q Rm
  center : Fin 272 → Fin (N + 1) → ℚ
  err : Fin 272 → ℚ
  center_gate : StructuredCenterGate Rm center err

/-- Floor gate and power-decomposed correction bound of one corrected block `X` named `name`. -/
structure Active18 (s : ℝ → ℝ) (cell : Literals.Cell) (X : Literals.Block) (name : String)
    {N t : ℕ} (H : Fin t → QModel N) (q : Fin 272 → Fin t → ℚ)
    (center : Fin 272 → Fin (N + 1) → ℚ) (err : Fin 272 → ℚ) where
  Z : Matrix (Fin X.order) (Fin X.order) ℝ
  θ : ℝ
  γ : ℝ
  short_metric : QuadraticBound ((Z * literalMetric X cell.metricBits - 1) +
    (Z * literalMetric X cell.metricBits - 1).transpose) θ
  gap : γ < (2 : ℝ) ^ cell.floorExponent * (1 - θ)
  γk : Fin (N + 1) → ℝ
  η : ℝ
  total : ∑ k, γk k + η ≤ γ
  power : ∀ x ∈ cellDomain, ∀ k : Fin (N + 1), QuadraticBound
    (Z * outputInsertion FixedTables.D18.outputCoordinates name
      ((FixedTables.D18.inverseMatrix (aS (s x))).mulVec (fun r => (center r k : ℝ))) *
      Z.transpose) (γk k)
  error : ∀ x ∈ cellDomain, ∀ (e : Fin t → ℝ) (ε : Fin 272 → ℝ),
    (∀ j, |e j| ≤ ((H j).error : ℝ)) → (∀ r, |ε r| ≤ (err r : ℝ)) → QuadraticBound
      (Z * outputInsertion FixedTables.D18.outputCoordinates name
        ((FixedTables.D18.inverseMatrix (aS (s x))).mulVec
          ((∑ j, e j • fun r => (q r j : ℝ)) + ε)) * Z.transpose) η

/-- `Active18` with one whole-centre bound instead of the per-power decomposition (F3 interface, v2). -/
structure Active18' (s : ℝ → ℝ) (cell : Literals.Cell) (X : Literals.Block) (name : String)
    {N t : ℕ} (H : Fin t → QModel N) (q : Fin 272 → Fin t → ℚ)
    (center : Fin 272 → Fin (N + 1) → ℚ) (err : Fin 272 → ℚ) where
  Z : Matrix (Fin X.order) (Fin X.order) ℝ
  θ : ℝ
  γ : ℝ
  short_metric : QuadraticBound ((Z * literalMetric X cell.metricBits - 1) +
    (Z * literalMetric X cell.metricBits - 1).transpose) θ
  gap : γ < (2 : ℝ) ^ cell.floorExponent * (1 - θ)
  γc : ℚ
  η : ℝ
  total : (γc : ℝ) + η ≤ γ
  centerBound : ∀ x ∈ cellDomain, QuadraticBound
    (Z * outputInsertion FixedTables.D18.outputCoordinates name
      ((FixedTables.D18.inverseMatrix (aS (s x))).mulVec
        (fun r => scalarEval (fun k => (center r k : ℝ)) x)) * Z.transpose) (γc : ℝ)
  error : ∀ x ∈ cellDomain, ∀ (e : Fin t → ℝ) (ε : Fin 272 → ℝ),
    (∀ j, |e j| ≤ ((H j).error : ℝ)) → (∀ r, |ε r| ≤ (err r : ℝ)) → QuadraticBound
      (Z * outputInsertion FixedTables.D18.outputCoordinates name
        ((FixedTables.D18.inverseMatrix (aS (s x))).mulVec
          ((∑ j, e j • fun r => (q r j : ℝ)) + ε)) * Z.transpose) η

/-- Everything a D18 cell supplies. `c, h`: cell center and half-width; `s`: exponent on
`cellDomain = [-1,1]`; `β`: Riesz balance normalization; `m`: Hermite profile; `cell, blk`: W0 literal data; `N`: Taylor order;
`t`: number of shared target models; `nb`: number of W0 contribution pieces. -/
structure CellProducts18 (idx : Fin 30) (c h : ℝ) (s β : ℝ → ℝ) (m : Fin 5 → ℕ)
    (cell : Literals.Cell) (blk : GramBlock 9 → Literals.Block) (N t nb : ℕ) where
  hh : 0 < h
  hlo : c - h = Blueprint.lower idx
  hhi : c + h = Blueprint.upper idx
  s_affine : ∀ x, s x = c + h * x
  s_nonneg : ∀ x ∈ cellDomain, 0 ≤ s x
  β_pos : ∀ x ∈ cellDomain, 0 < β x
  profile : Profile.Valid 18 m
  hord : ∀ b, (blk b).order = gramBlockDimension 9 b
  res : Residual18 s β m cell blk hord N t nb
  F0 : Active18 s cell (blk (.inl 0)) "F0" res.H res.q res.center res.err
  F1 : Active18 s cell (blk (.inl 1)) "F1" res.H res.q res.center res.err
  M0plus : Active18 s cell (blk (.inr .m0Plus)) "M0_plus" res.H res.q res.center res.err
  M0standard : Active18 s cell (blk (.inr .m0Standard)) "M0_standard" res.H res.q res.center res.err

/-- `CellProducts18` with the whole-centre correction bounds `Active18'` (F3 interface, v2). -/
structure CellProducts18' (idx : Fin 30) (c h : ℝ) (s β : ℝ → ℝ) (m : Fin 5 → ℕ)
    (cell : Literals.Cell) (blk : GramBlock 9 → Literals.Block) (N t nb : ℕ) where
  hh : 0 < h
  hlo : c - h = Blueprint.lower idx
  hhi : c + h = Blueprint.upper idx
  s_affine : ∀ x, s x = c + h * x
  s_nonneg : ∀ x ∈ cellDomain, 0 ≤ s x
  β_pos : ∀ x ∈ cellDomain, 0 < β x
  profile : Profile.Valid 18 m
  hord : ∀ b, (blk b).order = gramBlockDimension 9 b
  res : Residual18 s β m cell blk hord N t nb
  F0 : Active18' s cell (blk (.inl 0)) "F0" res.H res.q res.center res.err
  F1 : Active18' s cell (blk (.inl 1)) "F1" res.H res.q res.center res.err
  M0plus : Active18' s cell (blk (.inr .m0Plus)) "M0_plus" res.H res.q res.center res.err
  M0standard : Active18' s cell (blk (.inr .m0Standard)) "M0_standard" res.H res.q res.center res.err

/-! ## The generic chain -/

section Chain

variable {s β : ℝ → ℝ} {m : Fin 5 → ℕ} {cell : Literals.Cell} {blk : GramBlock 9 → Literals.Block}
  {hord : ∀ b, (blk b).order = gramBlockDimension 9 b} {N t nb : ℕ}

/-- The residual in the fixed-table coordinate order. -/
def Residual18.res (R : Residual18 s β m cell blk hord N t nb) (r : Fin 272) (x : ℝ) : ℝ :=
  ∑ j, (R.q r j : ℝ) * R.hfun j x - ∑ b, R.g b r x

/-- Generic `correction_input` / `retained_residual`. -/
theorem Residual18.retained (R : Residual18 s β m cell blk hord N t nb) (x : ℝ)
    (hx : x ∈ cellDomain) (hs : 0 ≤ s x) (hm : Profile.Valid 18 m) :
    ThomsonCompact.FixedD18.retainedVector (aS (s x))
        (target s β m x hs hm - gramMap s x hs (W0 cell blk hord x hx)) =
      fun r => R.res r x := by
  funext r
  change retainCompatible (aS (s x)) 18
      (target s β m x hs hm - gramMap s x hs (W0 cell blk hord x hx))
      (FixedTables.D18.retainedIndex r) = R.res r x
  rw [map_sub, Pi.sub_apply, R.target_link x hx hs hm r, R.W0_link x hx hs r]
  rfl

/-- Generic `StructuredResidual.sound` + `centered`: the residual is a rational polynomial in `x`
plus shared target errors and coordinate errors. -/
theorem Residual18.decomposition (R : Residual18 s β m cell blk hord N t nb) :
    ∃ (e : Fin t → ℝ → ℝ) (ε : Fin 272 → ℝ → ℝ),
      (∀ j x, x ∈ cellDomain → |e j x| ≤ ((R.H j).error : ℝ)) ∧
      (∀ i x, x ∈ cellDomain → |ε i x| ≤ (R.err i : ℝ)) ∧
      ∀ i x, R.res i x = scalarEval (fun k => (R.center i k : ℝ)) x +
        (∑ j, (R.q i j : ℝ) * e j x) + ε i x :=
  structuredCenterSupport R.H R.q R.Rm R.res R.center R.err
    (structuredResidualSupport R.H R.B R.q R.Rm R.hfun R.g R.H_valid R.B_valid R.gate)
    R.center_gate

end Chain

theorem quadraticBound_mono {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} {γ γ' : ℝ}
    (h : QuadraticBound M γ) (hle : γ ≤ γ') : QuadraticBound M γ' := by
  refine ⟨h.1.trans hle, fun v => (h.2 v).trans ?_⟩
  have hv : 0 ≤ squaredEuclidean v := Finset.sum_nonneg fun i _ => sq_nonneg (v i)
  exact mul_le_mul_of_nonneg_right hle hv

/-- Generic `CorrectionUniform_X.bound` + `CorrectionUniform_X.corrected_positive` (in the literal
block's own indexing). -/
theorem Active18.posDef {s : ℝ → ℝ} {cell : Literals.Cell} {X : Literals.Block} {name : String}
    {N t : ℕ} {H : Fin t → QModel N} {q : Fin 272 → Fin t → ℚ}
    {center : Fin 272 → Fin (N + 1) → ℚ} {err : Fin 272 → ℚ}
    (A : Active18 s cell X name H q center err) (x : ℝ) (hx : x ∈ cellDomain)
    (v : Fin 272 → ℝ) (e : Fin t → ℝ) (ε : Fin 272 → ℝ)
    (he : ∀ j, |e j| ≤ ((H j).error : ℝ)) (hε : ∀ i, |ε i| ≤ (err i : ℝ))
    (hv : ∀ i, v i = scalarEval (fun k => (center i k : ℝ)) x + (∑ j, (q i j : ℝ) * e j) + ε i) :
    (literalGram cell X x + outputInsertion FixedTables.D18.outputCoordinates name
      ((FixedTables.D18.inverseMatrix (aS (s x))).mulVec v)).PosDef := by
  have hsum := structuredInverseInsertionQuadraticSupport
    (FixedTables.D18.inverseLinear (aS (s x))) FixedTables.D18.outputCoordinates name A.Z
    (fun i k => (center i k : ℝ)) (fun i j => (q i j : ℝ)) v ε e x hv hx A.γk A.η
    (fun k => A.power x hx k) (A.error x hx e ε he hε)
  have hbound : QuadraticBound (A.Z * outputInsertion FixedTables.D18.outputCoordinates name
      ((FixedTables.D18.inverseMatrix (aS (s x))).mulVec v) * A.Z.transpose) A.γ :=
    quadraticBound_mono hsum A.total
  have hfl := literalGram_floor cell X x hx
  exact correctedShortMetricSupport (literalGram cell X x) _ (literalMetric X cell.metricBits) A.Z
    (A.Z * literalMetric X cell.metricBits - 1) ((2 : ℝ) ^ cell.floorExponent) A.θ A.γ
    hfl.2.isHermitian (outputInsertion_isHermitian _ _ _) (zpow_pos (by norm_num) _).le hfl.1 rfl
    A.short_metric hbound A.gap

/-- Positivity of a corrected literal block for every structured residual vector. -/
def ActivePos (s : ℝ → ℝ) (cell : Literals.Cell) (X : Literals.Block) (name : String)
    {N t : ℕ} (H : Fin t → QModel N) (q : Fin 272 → Fin t → ℚ)
    (center : Fin 272 → Fin (N + 1) → ℚ) (err : Fin 272 → ℚ) : Prop :=
  ∀ x ∈ cellDomain, ∀ (v : Fin 272 → ℝ) (e : Fin t → ℝ) (ε : Fin 272 → ℝ),
    (∀ j, |e j| ≤ ((H j).error : ℝ)) → (∀ i, |ε i| ≤ (err i : ℝ)) →
    (∀ i, v i = scalarEval (fun k => (center i k : ℝ)) x + (∑ j, (q i j : ℝ) * e j) + ε i) →
    (literalGram cell X x + outputInsertion FixedTables.D18.outputCoordinates name
      ((FixedTables.D18.inverseMatrix (aS (s x))).mulVec v)).PosDef

theorem Active18.activePos {s : ℝ → ℝ} {cell : Literals.Cell} {X : Literals.Block} {name : String}
    {N t : ℕ} {H : Fin t → QModel N} {q : Fin 272 → Fin t → ℚ}
    {center : Fin 272 → Fin (N + 1) → ℚ} {err : Fin 272 → ℚ}
    (A : Active18 s cell X name H q center err) : ActivePos s cell X name H q center err :=
  fun x hx v e ε he hε hv => A.posDef x hx v e ε he hε hv

/-- Triangle inequality for quadratic bounds. -/
theorem quadraticBound_add {n : ℕ} {M M' : Matrix (Fin n) (Fin n) ℝ} {γ γ' : ℝ}
    (h : QuadraticBound M γ) (h' : QuadraticBound M' γ') : QuadraticBound (M + M') (γ + γ') := by
  refine ⟨add_nonneg h.1 h'.1, fun v => ?_⟩
  have hq : quadratic (M + M') v = quadratic M v + quadratic M' v := by
    simp only [quadratic, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  rw [hq, add_mul]
  exact (abs_add_le _ _).trans (add_le_add (h.2 v) (h'.2 v))

/-- Whole-centre version of `Active18.posDef`. -/
theorem Active18'.posDef {s : ℝ → ℝ} {cell : Literals.Cell} {X : Literals.Block} {name : String}
    {N t : ℕ} {H : Fin t → QModel N} {q : Fin 272 → Fin t → ℚ}
    {center : Fin 272 → Fin (N + 1) → ℚ} {err : Fin 272 → ℚ}
    (A : Active18' s cell X name H q center err) : ActivePos s cell X name H q center err := by
  intro x hx v e ε he hε hv
  set cvec : Fin 272 → ℝ := fun r => scalarEval (fun k => (center r k : ℝ)) x
  set evec : Fin 272 → ℝ := (∑ j, e j • fun r => (q r j : ℝ)) + ε
  have hsplit : v = cvec + evec := by
    funext i
    rw [hv i]
    simp only [cvec, evec, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have : ∑ j, (q i j : ℝ) * e j = ∑ j, e j * (q i j : ℝ) := Finset.sum_congr rfl (fun j _ => mul_comm _ _)
    rw [this]
    ring
  have hlin : A.Z * outputInsertion FixedTables.D18.outputCoordinates name
      ((FixedTables.D18.inverseMatrix (aS (s x))).mulVec v) * A.Z.transpose =
      A.Z * outputInsertion FixedTables.D18.outputCoordinates name
        ((FixedTables.D18.inverseMatrix (aS (s x))).mulVec cvec) * A.Z.transpose +
      A.Z * outputInsertion FixedTables.D18.outputCoordinates name
        ((FixedTables.D18.inverseMatrix (aS (s x))).mulVec evec) * A.Z.transpose := by
    rw [hsplit, Matrix.mulVec_add]
    have hadd := (outputInsertionLinear (n := X.order) FixedTables.D18.outputCoordinates name).map_add
      ((FixedTables.D18.inverseMatrix (aS (s x))).mulVec cvec)
      ((FixedTables.D18.inverseMatrix (aS (s x))).mulVec evec)
    change outputInsertion FixedTables.D18.outputCoordinates name _ =
      outputInsertion FixedTables.D18.outputCoordinates name _ +
        outputInsertion FixedTables.D18.outputCoordinates name _ at hadd
    rw [hadd, Matrix.mul_add, Matrix.add_mul]
  have hbound : QuadraticBound (A.Z * outputInsertion FixedTables.D18.outputCoordinates name
      ((FixedTables.D18.inverseMatrix (aS (s x))).mulVec v) * A.Z.transpose) A.γ := by
    rw [hlin]
    exact quadraticBound_mono (quadraticBound_add (A.centerBound x hx) (A.error x hx e ε he hε)) A.total
  have hfl := literalGram_floor cell X x hx
  exact correctedShortMetricSupport (literalGram cell X x) _ (literalMetric X cell.metricBits) A.Z
    (A.Z * literalMetric X cell.metricBits - 1) ((2 : ℝ) ^ cell.floorExponent) A.θ A.γ
    hfl.2.isHermitian (outputInsertion_isHermitian _ _ _) (zpow_pos (by norm_num) _).le hfl.1 rfl
    A.short_metric hbound A.gap

theorem posDef_of_source {n k : ℕ} (e : Fin n ≃ Fin k) (M : Matrix (Fin k) (Fin k) ℝ)
    (h : (M.submatrix e e).PosDef) : M.PosDef := by
  have he : (M.submatrix e e).submatrix e.symm e.symm = M := by
    ext i j
    simp only [Matrix.submatrix_apply, Equiv.apply_symm_apply]
  rw [← he]
  exact h.submatrix e.symm.injective

theorem corrected_posDef_of_source {n k : ℕ} (e : Fin n ≃ Fin k)
    (G : Matrix (Fin n) (Fin n) ℝ) (E : Matrix (Fin k) (Fin k) ℝ)
    (h : (G + E.submatrix e e).PosDef) : (G.submatrix e.symm e.symm + E).PosDef := by
  apply posDef_of_source e
  have he : (G.submatrix e.symm e.symm + E).submatrix e e = G + E.submatrix e e := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.add_apply, Equiv.symm_apply_apply]
  rw [he]
  exact h

theorem outputInsertion_reindex {n k : ℕ} (e : Fin n ≃ Fin k) (he : ∀ i, (e i).val = i.val)
    (name : String) (v : Fin 272 → ℝ) :
    (outputInsertion (n := k) FixedTables.D18.outputCoordinates name v).submatrix e e =
      outputInsertion (n := n) FixedTables.D18.outputCoordinates name v := by
  ext i j
  simp only [Matrix.submatrix_apply, outputInsertion, he]

/-- Generic `PositiveSupport.corrected_positive_reindex`. -/
theorem posDef_reindex {n k : ℕ} (e : Fin n ≃ Fin k) (he : ∀ i, (e i).val = i.val)
    (G : Matrix (Fin n) (Fin n) ℝ) (name : String) (v : Fin 272 → ℝ)
    (h : (G + outputInsertion FixedTables.D18.outputCoordinates name v).PosDef) :
    (G.submatrix e.symm e.symm + outputInsertion FixedTables.D18.outputCoordinates name v).PosDef := by
  apply corrected_posDef_of_source e
  rw [outputInsertion_reindex e he]
  exact h

/-- Block formula of `W + correctionLinear a v` (generic `corrected_block`). -/
theorem corrected_block (a : ℝ) (W : GramFamily 9) (v : Fin 272 → ℝ) (b : GramBlock 9) :
    (W + FixedTables.D18.correctionLinear a v).val b =
      W.val b + outputInsertion FixedTables.D18.outputCoordinates
        (FixedTables.D18.insertionBlockName b) ((FixedTables.D18.inverseMatrix a).mulVec v) := by
  rw [Submodule.coe_add, Pi.add_apply, FixedTables.D18.correctionLinear_apply,
    d18_insertionLinear_block]

theorem inactive_zero (w : Fin 272 → ℝ) (b : GramBlock 9)
    (h0 : FixedTables.D18.insertionBlockName b ≠ "F0")
    (h1 : FixedTables.D18.insertionBlockName b ≠ "F1")
    (hp : FixedTables.D18.insertionBlockName b ≠ "M0_plus")
    (hs : FixedTables.D18.insertionBlockName b ≠ "M0_standard") :
    outputInsertion FixedTables.D18.outputCoordinates (FixedTables.D18.insertionBlockName b) w =
      (0 : Matrix (Fin (gramBlockDimension 9 b)) (Fin (gramBlockDimension 9 b)) ℝ) := by
  rw [← d18_insertionLinear_block]
  exact FixedTables.D18.insertionLinear_inactive w b h0 h1 hp hs

/-- Generic `corrected_inactive`: blocks without a correction keep the positive literal Gram. -/
theorem inactive_posDef (cell : Literals.Cell) (blk : GramBlock 9 → Literals.Block)
    (hord : ∀ b, (blk b).order = gramBlockDimension 9 b) (x : ℝ) (hx : x ∈ cellDomain)
    (b : GramBlock 9) (w : Fin 272 → ℝ)
    (h0 : FixedTables.D18.insertionBlockName b ≠ "F0")
    (h1 : FixedTables.D18.insertionBlockName b ≠ "F1")
    (hp : FixedTables.D18.insertionBlockName b ≠ "M0_plus")
    (hs : FixedTables.D18.insertionBlockName b ≠ "M0_standard") :
    (W0mat cell blk hord x b + outputInsertion FixedTables.D18.outputCoordinates
      (FixedTables.D18.insertionBlockName b) w).PosDef := by
  rw [inactive_zero w b h0 h1 hp hs, add_zero]
  exact W0mat_posDef cell blk hord x hx b

section Assembly

variable {idx : Fin 30} {c h : ℝ} {s β : ℝ → ℝ} {m : Fin 5 → ℕ} {cell : Literals.Cell}
  {blk : GramBlock 9 → Literals.Block} {N t nb : ℕ}

/-- Generic `corrected_positive_of_four` + `corrected_positive`: every block of the exact
corrected Gram family is positive definite. -/
theorem corrected_posDef_of (hord : ∀ b, (blk b).order = gramBlockDimension 9 b)
    (res : Residual18 s β m cell blk hord N t nb)
    (hF0 : ActivePos s cell (blk (.inl 0)) "F0" res.H res.q res.center res.err)
    (hF1 : ActivePos s cell (blk (.inl 1)) "F1" res.H res.q res.center res.err)
    (hM0p : ActivePos s cell (blk (.inr .m0Plus)) "M0_plus" res.H res.q res.center res.err)
    (hM0s : ActivePos s cell (blk (.inr .m0Standard)) "M0_standard" res.H res.q res.center res.err)
    (x : ℝ) (hx : x ∈ cellDomain) (hs : 0 ≤ s x) (hm : Profile.Valid 18 m) (b : GramBlock 9) :
    ((correctedGram (gramMap s x hs) (rightInverse (aS (s x))) (target s β m x hs hm)
      (W0 cell blk hord x hx)).val b).PosDef := by
  obtain ⟨e, ε, he, hε, hdec⟩ := res.decomposition
  have hcorr : correctedGram (gramMap s x hs) (rightInverse (aS (s x))) (target s β m x hs hm)
      (W0 cell blk hord x hx) = W0 cell blk hord x hx +
        FixedTables.D18.correctionLinear (aS (s x)) (fun r => res.res r x) := by
    unfold correctedGram rightInverse
    rw [res.retained x hx hs hm]
  rw [hcorr, corrected_block, W0_val]
  have hv : ∀ i, res.res i x = scalarEval (fun k => (res.center i k : ℝ)) x +
      (∑ j, (res.q i j : ℝ) * e j x) + ε i x := fun i => hdec i x
  have he' : ∀ j, |e j x| ≤ ((res.H j).error : ℝ) := fun j => he j x hx
  have hε' : ∀ i, |ε i x| ≤ (res.err i : ℝ) := fun i => hε i x hx
  cases b with
  | inl k =>
    fin_cases k
    · exact posDef_reindex (finCongr (hord (.inl 0))) (fun _ => rfl) _ "F0" _
        (hF0 x hx _ (fun j => e j x) (fun i => ε i x) he' hε' hv)
    · exact posDef_reindex (finCongr (hord (.inl 1))) (fun _ => rfl) _ "F1" _
        (hF1 x hx _ (fun j => e j x) (fun i => ε i x) he' hε' hv)
    · exact inactive_posDef cell blk hord x hx _ _ (by decide) (by decide) (by decide) (by decide)
    · exact inactive_posDef cell blk hord x hx _ _ (by decide) (by decide) (by decide) (by decide)
    · exact inactive_posDef cell blk hord x hx _ _ (by decide) (by decide) (by decide) (by decide)
    · exact inactive_posDef cell blk hord x hx _ _ (by decide) (by decide) (by decide) (by decide)
    · exact inactive_posDef cell blk hord x hx _ _ (by decide) (by decide) (by decide) (by decide)
    · exact inactive_posDef cell blk hord x hx _ _ (by decide) (by decide) (by decide) (by decide)
    · exact inactive_posDef cell blk hord x hx _ _ (by decide) (by decide) (by decide) (by decide)
  | inr b =>
    cases b with
    | m0Plus =>
      exact posDef_reindex (finCongr (hord (.inr .m0Plus))) (fun _ => rfl) _ "M0_plus" _
        (hM0p x hx _ (fun j => e j x) (fun i => ε i x) he' hε' hv)
    | m0Standard =>
      exact posDef_reindex (finCongr (hord (.inr .m0Standard))) (fun _ => rfl) _ "M0_standard" _
        (hM0s x hx _ (fun j => e j x) (fun i => ε i x) he' hε' hv)
    | m0Sign =>
      exact inactive_posDef cell blk hord x hx _ _ (by decide) (by decide) (by decide) (by decide)
    | m1Even =>
      exact inactive_posDef cell blk hord x hx _ _ (by decide) (by decide) (by decide) (by decide)
    | m1Odd =>
      exact inactive_posDef cell blk hord x hx _ _ (by decide) (by decide) (by decide) (by decide)
    | mdetPlus =>
      exact inactive_posDef cell blk hord x hx _ _ (by decide) (by decide) (by decide) (by decide)
    | mdetSign =>
      exact inactive_posDef cell blk hord x hx _ _ (by decide) (by decide) (by decide) (by decide)
    | mdetStandard =>
      exact inactive_posDef cell blk hord x hx _ _ (by decide) (by decide) (by decide) (by decide)

theorem CellProducts18.corrected_posDef (P : CellProducts18 idx c h s β m cell blk N t nb)
    (x : ℝ) (hx : x ∈ cellDomain) (hs : 0 ≤ s x) (hm : Profile.Valid 18 m) (b : GramBlock 9) :
    ((correctedGram (gramMap s x hs) (rightInverse (aS (s x))) (target s β m x hs hm)
      (W0 cell blk P.hord x hx)).val b).PosDef :=
  corrected_posDef_of P.hord P.res P.F0.activePos P.F1.activePos P.M0plus.activePos P.M0standard.activePos
    x hx hs hm b

theorem CellProducts18'.corrected_posDef (P : CellProducts18' idx c h s β m cell blk N t nb)
    (x : ℝ) (hx : x ∈ cellDomain) (hs : 0 ≤ s x) (hm : Profile.Valid 18 m) (b : GramBlock 9) :
    ((correctedGram (gramMap s x hs) (rightInverse (aS (s x))) (target s β m x hs hm)
      (W0 cell blk P.hord x hx)).val b).PosDef :=
  corrected_posDef_of P.hord P.res P.F0.posDef P.F1.posDef P.M0plus.posDef P.M0standard.posDef x hx hs hm b

set_option maxRecDepth 8192 in
/-- Generic `certificate`: the exact certificate at every point of the cell. -/
theorem CellProducts18.certificate (P : CellProducts18 idx c h s β m cell blk N t nb)
    (x : ℝ) (hx : x ∈ cellDomain) : Certificate (s x) (aS (s x)) 18 m :=
  have hs := P.s_nonneg x hx
  certificate_of_exact_gram_correction (s x) (aS (s x)) (β x) 18 m hs (aS_physical _ hs)
    (aS_mem_and_root _ hs).2 (Or.inr (Or.inr (Or.inr rfl))) P.profile pivots pivots_valid
    (P.β_pos x hx)
    (rightInverse (aS (s x))) (rightInverse_recovery _ (aS_physical _ hs))
    (W0 cell blk P.hord x hx) (P.corrected_posDef x hx hs P.profile)

/-- **The generic D18 cell theorem**: the products of a cell prove its `CellSpec`. -/
theorem cellSpec_of_products18 (P : CellProducts18 idx c h s β m cell blk N t nb) :
    Blueprint.CellSpec idx := by
  apply cellSpec_of_affine_certificates idx c h P.hh P.hlo P.hhi 18 m
  intro x hx
  have hcert := P.certificate x hx
  rw [P.s_affine x] at hcert
  exact hcert

set_option maxRecDepth 8192 in
/-- `certificate` for the whole-centre products. -/
theorem CellProducts18'.certificate (P : CellProducts18' idx c h s β m cell blk N t nb)
    (x : ℝ) (hx : x ∈ cellDomain) : Certificate (s x) (aS (s x)) 18 m :=
  have hs := P.s_nonneg x hx
  certificate_of_exact_gram_correction (s x) (aS (s x)) (β x) 18 m hs (aS_physical _ hs)
    (aS_mem_and_root _ hs).2 (Or.inr (Or.inr (Or.inr rfl))) P.profile pivots pivots_valid
    (P.β_pos x hx)
    (rightInverse (aS (s x))) (rightInverse_recovery _ (aS_physical _ hs))
    (W0 cell blk P.hord x hx) (P.corrected_posDef x hx hs P.profile)

/-- **The generic D18 cell theorem, whole-centre version.** -/
theorem cellSpec_of_products18' (P : CellProducts18' idx c h s β m cell blk N t nb) :
    Blueprint.CellSpec idx := by
  apply cellSpec_of_affine_certificates idx c h P.hh P.hlo P.hhi 18 m
  intro x hx
  have hcert := P.certificate x hx
  rw [P.s_affine x] at hcert
  exact hcert

end Assembly

end ThomsonCompact.Interface.D18

#print axioms ThomsonCompact.Interface.D18.rightInverse_recovery
#print axioms ThomsonCompact.Interface.D18.Active18'.posDef
#print axioms ThomsonCompact.Interface.D18.cellSpec_of_products18'
#print axioms ThomsonCompact.Interface.D18.scalarDims
#print axioms ThomsonCompact.Interface.D18.Residual18.decomposition
#print axioms ThomsonCompact.Interface.D18.Active18.posDef
#print axioms ThomsonCompact.Interface.D18.CellProducts18.corrected_posDef
#print axioms ThomsonCompact.Interface.D18.cellSpec_of_products18
