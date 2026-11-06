import ThomsonCompact.Fixed.D16.Recovery
import AllS.Units.N_FI.N_certificate.N_corrected_gram
import AllS.Units.N_FI.N_cell_soundness.N_affine_cell
import AllS.Units.N_AI.N_gram_replay.LiteralGramSupport
import AllS.Units.N_AI.N_gram_replay.CorrectedShortMetricSupport
import AllS.Units.N_AI.N_correction_bounds.StructuredInverseInsertionSupport
import AllS.Units.N_AI.N_correction_bounds.OutputInsertionSupport
import AllS.Units.N_AI.N_residual_replay.StructuredCenterSupport
import AllS.Units.N_F.N_height_upper

/-!
# Frozen per-cell interface for the D16 cells (workstreams F0/F4)

Same pattern as `ThomsonCompact.Interface.D16` (whole-centre `'` variant only), for degree 16: `GramBlock 8`, 202
retained coordinates, moment pivots `[0,1,0,1,0,0,0,0]`, the compact kernel-checked right inverse
`ThomsonCompact.FixedD16` (`correctionLinear_full_recovery`), and the Riesz-balanced target normalization `β x > 0`
of all D16 cells (`Target/API.md`: `β x := balancedMultiplier c (s x)`, `hfun := hfunR c s m`, `target_link` from
`riesz_target_link`). The four corrected blocks are F0, F1, M0_plus, M0_standard.
-/

noncomputable section
open scoped BigOperators

namespace ThomsonCompact.Interface.D16

open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite

/-! ## D16 layout -/

/-- Moment pivots `[0,1,0,1,0,0,0,0]` (the D16 witness fixes `p 0 = 0`, `p 1 = 1`). -/
def pivots : MomentPivots 8 := fun k => ⟨![0, 1, 0, 1, 0, 0, 0, 0] k, by fin_cases k <;> decide⟩

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

/-- The compact D16 fixed-table right inverse on compatible polynomials. -/
def rightInverse (a : ℝ) (f : Compatible a 16) : GramFamily 8 :=
  FixedD16.correctionLinear a (FixedD16.retainedVector a f)

theorem rightInverse_recovery (a : ℝ) (ha : physical a) (f : Compatible a 16) :
    gramPoly a 8 pivots (rightInverse a f) = f.val :=
  FixedD16.correctionLinear_full_recovery a ha pivots pivots_valid rfl rfl f

/-- Scalar block dimensions of the D16 layout. -/
def scalarOrder : ScalarBlockName → ℕ
  | .m0Plus => 36
  | .m0Sign => 14
  | .m0Standard => 47
  | .m1Even => 58
  | .m1Odd => 41
  | .mdetPlus => 18
  | .mdetSign => 5
  | .mdetStandard => 20

theorem scalarDims (b : ScalarBlockName) : scalarBlockDimension b 8 = scalarOrder b := by
  cases b <;>
    simp only [scalarBlockDimension, scalarOrder, standardTagList, invariantPivots,
      signPivots, standardPivots, parityPivots, Nat.reduceSub, Bool.false_eq_true,
      if_false, if_true, RawCatalogue.invariantTagList_1, RawCatalogue.invariantTagList_2,
      RawCatalogue.invariantTagList_3, RawCatalogue.invariantTagList_4,
      RawCatalogue.invariantTagList_5, RawCatalogue.invariantTagList_6,
      RawCatalogue.invariantTagList_7, RawCatalogue.invariantTagList_8, RawCatalogue.parityTagList_3,
      RawCatalogue.parityTagList_4, RawCatalogue.parityTagList_5, RawCatalogue.parityTagList_6,
      RawCatalogue.parityTagList_7, RawCatalogue.parityTagList_8] <;>
    decide +kernel

/-- `hord` from the 16 literal block orders. -/
theorem hord_of_orders (blk : GramBlock 8 → Literals.Block)
    (hm : ∀ k : Fin 8, (blk (.inl k)).order = 8 - k.val)
    (hs : ∀ b : ScalarBlockName, (blk (.inr b)).order = scalarOrder b) :
    ∀ b, (blk b).order = gramBlockDimension 8 b := by
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
def target (s β : ℝ → ℝ) (m : Fin 5 → ℕ) (x : ℝ) (hs : 0 ≤ s x) (hm : Profile.Valid 16 m) :
    Compatible (aS (s x)) 16 :=
  normalizedTargetCompatible (s x) (aS (s x)) (β x) 16 m hs (aS_physical _ hs)
    (aS_mem_and_root _ hs).2 hm

/-- The D16 Gram map at height `aS (s x)`. -/
def gramMap (s : ℝ → ℝ) (x : ℝ) (hs : 0 ≤ s x) :
    GramFamily 8 →ₗ[ℝ] Compatible (aS (s x)) 16 :=
  gramCompatible (aS (s x)) (aS_physical _ hs) 16 (Or.inr (Or.inr (Or.inl rfl))) pivots
    pivots_valid

/-- Literal Bernstein-square Gram blocks, transported to the Gram block dimensions. -/
def W0mat (cell : Literals.Cell) (blk : GramBlock 8 → Literals.Block)
    (hord : ∀ b, (blk b).order = gramBlockDimension 8 b) (x : ℝ) : GramMatrices 8 :=
  fun b => (literalGram cell (blk b) x).submatrix (finCongr (hord b)).symm (finCongr (hord b)).symm

theorem W0mat_posDef (cell : Literals.Cell) (blk : GramBlock 8 → Literals.Block)
    (hord : ∀ b, (blk b).order = gramBlockDimension 8 b) (x : ℝ) (hx : x ∈ cellDomain)
    (b : GramBlock 8) : (W0mat cell blk hord x b).PosDef :=
  (literalGram_floor cell (blk b) x hx).2.submatrix (finCongr (hord b)).symm.injective

theorem isSymm_of_posDef {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (h : M.PosDef) : M.IsSymm := by
  have hH := h.isHermitian
  unfold Matrix.IsHermitian at hH
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hH
  exact hH

/-- The generic initial Gram family of a D16 cell (the old per-cell `InitialGram_Data.W0`). -/
def W0 (cell : Literals.Cell) (blk : GramBlock 8 → Literals.Block)
    (hord : ∀ b, (blk b).order = gramBlockDimension 8 b) (x : ℝ) (hx : x ∈ cellDomain) :
    GramFamily 8 :=
  ⟨W0mat cell blk hord x, by
    intro b
    exact isSymm_of_posDef (W0mat_posDef cell blk hord x hx b)⟩

theorem W0_val (cell : Literals.Cell) (blk : GramBlock 8 → Literals.Block)
    (hord : ∀ b, (blk b).order = gramBlockDimension 8 b) (x : ℝ) (hx : x ∈ cellDomain) :
    (W0 cell blk hord x hx).val = W0mat cell blk hord x := rfl

/-! ## Products -/

/-- Residual products: TM-valid target and W0-contribution models, their links to the old target and
Gram map, the structured residual gate and the rational centers. -/
structure Residual16 (s β : ℝ → ℝ) (m : Fin 5 → ℕ) (cell : Literals.Cell)
    (blk : GramBlock 8 → Literals.Block) (hord : ∀ b, (blk b).order = gramBlockDimension 8 b)
    (N t nb : ℕ) where
  H : Fin t → QModel N
  hfun : Fin t → ℝ → ℝ
  H_valid : ∀ j, (H j).asTM.Valid (hfun j)
  q : Fin 202 → Fin t → ℚ
  target_link : ∀ (x : ℝ) (_hx : x ∈ cellDomain) (hs : 0 ≤ s x) (hm : Profile.Valid 16 m)
    (r : Fin 202), retainCompatible (aS (s x)) 16 (target s β m x hs hm)
      (FixedD16.retainedIndex r) = ∑ j, (q r j : ℝ) * hfun j x
  B : Fin nb → Fin 202 → QModel N
  g : Fin nb → Fin 202 → ℝ → ℝ
  B_valid : ∀ b r, (B b r).asTM.Valid (g b r)
  W0_link : ∀ (x : ℝ) (hx : x ∈ cellDomain) (hs : 0 ≤ s x) (r : Fin 202),
    retainCompatible (aS (s x)) 16 (gramMap s x hs (W0 cell blk hord x hx))
      (FixedD16.retainedIndex r) = ∑ b, g b r x
  Rm : Fin 202 → QModel N
  gate : StructuredResidualGate H B q Rm
  center : Fin 202 → Fin (N + 1) → ℚ
  err : Fin 202 → ℚ
  center_gate : StructuredCenterGate Rm center err

/-- Floor gate and whole-centre correction bound of one corrected block `X` named `name` (F3 interface, v2). -/
structure Active16' (s : ℝ → ℝ) (cell : Literals.Cell) (X : Literals.Block) (name : String)
    {N t : ℕ} (H : Fin t → QModel N) (q : Fin 202 → Fin t → ℚ)
    (center : Fin 202 → Fin (N + 1) → ℚ) (err : Fin 202 → ℚ) where
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
    (Z * outputInsertion FixedD16.outputCoordinates name
      ((FixedD16.inverseMatrix (aS (s x))).mulVec
        (fun r => scalarEval (fun k => (center r k : ℝ)) x)) * Z.transpose) (γc : ℝ)
  error : ∀ x ∈ cellDomain, ∀ (e : Fin t → ℝ) (ε : Fin 202 → ℝ),
    (∀ j, |e j| ≤ ((H j).error : ℝ)) → (∀ r, |ε r| ≤ (err r : ℝ)) → QuadraticBound
      (Z * outputInsertion FixedD16.outputCoordinates name
        ((FixedD16.inverseMatrix (aS (s x))).mulVec
          ((∑ j, e j • fun r => (q r j : ℝ)) + ε)) * Z.transpose) η

/-- Everything a D16 cell supplies (whole-centre correction bounds `Active16'`, F3 interface v2). `c, h`: cell
center and half-width; `s`: exponent on `cellDomain = [-1,1]`; `β`: Riesz balance normalization; `m`: Hermite
profile; `cell, blk`: W0 literal data; `N`: Taylor order; `t`: shared target models; `nb`: W0 contribution pieces. -/
structure CellProducts16' (idx : Fin 30) (c h : ℝ) (s β : ℝ → ℝ) (m : Fin 5 → ℕ)
    (cell : Literals.Cell) (blk : GramBlock 8 → Literals.Block) (N t nb : ℕ) where
  hh : 0 < h
  hlo : c - h = Blueprint.lower idx
  hhi : c + h = Blueprint.upper idx
  s_affine : ∀ x, s x = c + h * x
  s_nonneg : ∀ x ∈ cellDomain, 0 ≤ s x
  β_pos : ∀ x ∈ cellDomain, 0 < β x
  profile : Profile.Valid 16 m
  hord : ∀ b, (blk b).order = gramBlockDimension 8 b
  res : Residual16 s β m cell blk hord N t nb
  F0 : Active16' s cell (blk (.inl 0)) "F0" res.H res.q res.center res.err
  F1 : Active16' s cell (blk (.inl 1)) "F1" res.H res.q res.center res.err
  M0plus : Active16' s cell (blk (.inr .m0Plus)) "M0_plus" res.H res.q res.center res.err
  M0standard : Active16' s cell (blk (.inr .m0Standard)) "M0_standard" res.H res.q res.center res.err

/-! ## The generic chain -/

section Chain

variable {s β : ℝ → ℝ} {m : Fin 5 → ℕ} {cell : Literals.Cell} {blk : GramBlock 8 → Literals.Block}
  {hord : ∀ b, (blk b).order = gramBlockDimension 8 b} {N t nb : ℕ}

/-- The residual in the fixed-table coordinate order. -/
def Residual16.res (R : Residual16 s β m cell blk hord N t nb) (r : Fin 202) (x : ℝ) : ℝ :=
  ∑ j, (R.q r j : ℝ) * R.hfun j x - ∑ b, R.g b r x

/-- Generic `correction_input` / `retained_residual`. -/
theorem Residual16.retained (R : Residual16 s β m cell blk hord N t nb) (x : ℝ)
    (hx : x ∈ cellDomain) (hs : 0 ≤ s x) (hm : Profile.Valid 16 m) :
    FixedD16.retainedVector (aS (s x))
        (target s β m x hs hm - gramMap s x hs (W0 cell blk hord x hx)) =
      fun r => R.res r x := by
  funext r
  change retainCompatible (aS (s x)) 16
      (target s β m x hs hm - gramMap s x hs (W0 cell blk hord x hx))
      (FixedD16.retainedIndex r) = R.res r x
  rw [map_sub, Pi.sub_apply, R.target_link x hx hs hm r, R.W0_link x hx hs r]
  rfl

/-- Generic `StructuredResidual.sound` + `centered`: the residual is a rational polynomial in `x`
plus shared target errors and coordinate errors. -/
theorem Residual16.decomposition (R : Residual16 s β m cell blk hord N t nb) :
    ∃ (e : Fin t → ℝ → ℝ) (ε : Fin 202 → ℝ → ℝ),
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

/-- Positivity of a corrected literal block for every structured residual vector. -/
def ActivePos (s : ℝ → ℝ) (cell : Literals.Cell) (X : Literals.Block) (name : String)
    {N t : ℕ} (H : Fin t → QModel N) (q : Fin 202 → Fin t → ℚ)
    (center : Fin 202 → Fin (N + 1) → ℚ) (err : Fin 202 → ℚ) : Prop :=
  ∀ x ∈ cellDomain, ∀ (v : Fin 202 → ℝ) (e : Fin t → ℝ) (ε : Fin 202 → ℝ),
    (∀ j, |e j| ≤ ((H j).error : ℝ)) → (∀ i, |ε i| ≤ (err i : ℝ)) →
    (∀ i, v i = scalarEval (fun k => (center i k : ℝ)) x + (∑ j, (q i j : ℝ) * e j) + ε i) →
    (literalGram cell X x + outputInsertion FixedD16.outputCoordinates name
      ((FixedD16.inverseMatrix (aS (s x))).mulVec v)).PosDef

/-- Triangle inequality for quadratic bounds. -/
theorem quadraticBound_add {n : ℕ} {M M' : Matrix (Fin n) (Fin n) ℝ} {γ γ' : ℝ}
    (h : QuadraticBound M γ) (h' : QuadraticBound M' γ') : QuadraticBound (M + M') (γ + γ') := by
  refine ⟨add_nonneg h.1 h'.1, fun v => ?_⟩
  have hq : quadratic (M + M') v = quadratic M v + quadratic M' v := by
    simp only [quadratic, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  rw [hq, add_mul]
  exact (abs_add_le _ _).trans (add_le_add (h.2 v) (h'.2 v))

/-- Corrected-block positivity from the whole-centre bound (generic `CorrectionUniform_X.corrected_positive`). -/
theorem Active16'.posDef {s : ℝ → ℝ} {cell : Literals.Cell} {X : Literals.Block} {name : String}
    {N t : ℕ} {H : Fin t → QModel N} {q : Fin 202 → Fin t → ℚ}
    {center : Fin 202 → Fin (N + 1) → ℚ} {err : Fin 202 → ℚ}
    (A : Active16' s cell X name H q center err) : ActivePos s cell X name H q center err := by
  intro x hx v e ε he hε hv
  set cvec : Fin 202 → ℝ := fun r => scalarEval (fun k => (center r k : ℝ)) x
  set evec : Fin 202 → ℝ := (∑ j, e j • fun r => (q r j : ℝ)) + ε
  have hsplit : v = cvec + evec := by
    funext i
    rw [hv i]
    simp only [cvec, evec, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have : ∑ j, (q i j : ℝ) * e j = ∑ j, e j * (q i j : ℝ) := Finset.sum_congr rfl (fun j _ => mul_comm _ _)
    rw [this]
    ring
  have hlin : A.Z * outputInsertion FixedD16.outputCoordinates name
      ((FixedD16.inverseMatrix (aS (s x))).mulVec v) * A.Z.transpose =
      A.Z * outputInsertion FixedD16.outputCoordinates name
        ((FixedD16.inverseMatrix (aS (s x))).mulVec cvec) * A.Z.transpose +
      A.Z * outputInsertion FixedD16.outputCoordinates name
        ((FixedD16.inverseMatrix (aS (s x))).mulVec evec) * A.Z.transpose := by
    rw [hsplit, Matrix.mulVec_add]
    have hadd := (outputInsertionLinear (n := X.order) FixedD16.outputCoordinates name).map_add
      ((FixedD16.inverseMatrix (aS (s x))).mulVec cvec)
      ((FixedD16.inverseMatrix (aS (s x))).mulVec evec)
    change outputInsertion FixedD16.outputCoordinates name _ =
      outputInsertion FixedD16.outputCoordinates name _ +
        outputInsertion FixedD16.outputCoordinates name _ at hadd
    rw [hadd, Matrix.mul_add, Matrix.add_mul]
  have hbound : QuadraticBound (A.Z * outputInsertion FixedD16.outputCoordinates name
      ((FixedD16.inverseMatrix (aS (s x))).mulVec v) * A.Z.transpose) A.γ := by
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
    (name : String) (v : Fin 202 → ℝ) :
    (outputInsertion (n := k) FixedD16.outputCoordinates name v).submatrix e e =
      outputInsertion (n := n) FixedD16.outputCoordinates name v := by
  ext i j
  simp only [Matrix.submatrix_apply, outputInsertion, he]

/-- Generic `PositiveSupport.corrected_positive_reindex`. -/
theorem posDef_reindex {n k : ℕ} (e : Fin n ≃ Fin k) (he : ∀ i, (e i).val = i.val)
    (G : Matrix (Fin n) (Fin n) ℝ) (name : String) (v : Fin 202 → ℝ)
    (h : (G + outputInsertion FixedD16.outputCoordinates name v).PosDef) :
    (G.submatrix e.symm e.symm + outputInsertion FixedD16.outputCoordinates name v).PosDef := by
  apply corrected_posDef_of_source e
  rw [outputInsertion_reindex e he]
  exact h

theorem outputEntryQ_D16_cast (k : Fin 202) (name : String) (i j : ℕ) :
    (outputEntryQ FixedD16.outputCoordinates k name i j : ℝ) = FixedD16.outputEntry k name i j := by
  unfold outputEntryQ FixedD16.outputEntry
  split_ifs <;> norm_num

theorem d16_insertionLinear_block (v : Fin 202 → ℝ) (b : GramBlock 8) :
    (FixedD16.insertionLinear v).val b =
      outputInsertion FixedD16.outputCoordinates (FixedD16.insertionBlockName b) v := by
  ext i j
  rw [FixedD16.insertionLinear_entry]
  simp only [outputInsertion, outputEntryQ_D16_cast]

/-- Block formula of `W + correctionLinear a v` (generic `corrected_block`). -/
theorem corrected_block (a : ℝ) (W : GramFamily 8) (v : Fin 202 → ℝ) (b : GramBlock 8) :
    (W + FixedD16.correctionLinear a v).val b =
      W.val b + outputInsertion FixedD16.outputCoordinates
        (FixedD16.insertionBlockName b) ((FixedD16.inverseMatrix a).mulVec v) := by
  rw [Submodule.coe_add, Pi.add_apply, FixedD16.correctionLinear_apply,
    d16_insertionLinear_block]

theorem inactive_zero (w : Fin 202 → ℝ) (b : GramBlock 8)
    (h0 : FixedD16.insertionBlockName b ≠ "F0")
    (h1 : FixedD16.insertionBlockName b ≠ "F1")
    (hp : FixedD16.insertionBlockName b ≠ "M0_plus")
    (hs : FixedD16.insertionBlockName b ≠ "M0_standard") :
    outputInsertion FixedD16.outputCoordinates (FixedD16.insertionBlockName b) w =
      (0 : Matrix (Fin (gramBlockDimension 8 b)) (Fin (gramBlockDimension 8 b)) ℝ) := by
  rw [← d16_insertionLinear_block]
  exact FixedD16.insertionLinear_inactive w b h0 h1 hp hs

/-- Generic `corrected_inactive`: blocks without a correction keep the positive literal Gram. -/
theorem inactive_posDef (cell : Literals.Cell) (blk : GramBlock 8 → Literals.Block)
    (hord : ∀ b, (blk b).order = gramBlockDimension 8 b) (x : ℝ) (hx : x ∈ cellDomain)
    (b : GramBlock 8) (w : Fin 202 → ℝ)
    (h0 : FixedD16.insertionBlockName b ≠ "F0")
    (h1 : FixedD16.insertionBlockName b ≠ "F1")
    (hp : FixedD16.insertionBlockName b ≠ "M0_plus")
    (hs : FixedD16.insertionBlockName b ≠ "M0_standard") :
    (W0mat cell blk hord x b + outputInsertion FixedD16.outputCoordinates
      (FixedD16.insertionBlockName b) w).PosDef := by
  rw [inactive_zero w b h0 h1 hp hs, add_zero]
  exact W0mat_posDef cell blk hord x hx b

section Assembly

variable {idx : Fin 30} {c h : ℝ} {s β : ℝ → ℝ} {m : Fin 5 → ℕ} {cell : Literals.Cell}
  {blk : GramBlock 8 → Literals.Block} {N t nb : ℕ}

/-- Generic `corrected_positive_of_four` + `corrected_positive`: every block of the exact
corrected Gram family is positive definite. -/
theorem corrected_posDef_of (hord : ∀ b, (blk b).order = gramBlockDimension 8 b)
    (res : Residual16 s β m cell blk hord N t nb)
    (hF0 : ActivePos s cell (blk (.inl 0)) "F0" res.H res.q res.center res.err)
    (hF1 : ActivePos s cell (blk (.inl 1)) "F1" res.H res.q res.center res.err)
    (hM0p : ActivePos s cell (blk (.inr .m0Plus)) "M0_plus" res.H res.q res.center res.err)
    (hM0s : ActivePos s cell (blk (.inr .m0Standard)) "M0_standard" res.H res.q res.center res.err)
    (x : ℝ) (hx : x ∈ cellDomain) (hs : 0 ≤ s x) (hm : Profile.Valid 16 m) (b : GramBlock 8) :
    ((correctedGram (gramMap s x hs) (rightInverse (aS (s x))) (target s β m x hs hm)
      (W0 cell blk hord x hx)).val b).PosDef := by
  obtain ⟨e, ε, he, hε, hdec⟩ := res.decomposition
  have hcorr : correctedGram (gramMap s x hs) (rightInverse (aS (s x))) (target s β m x hs hm)
      (W0 cell blk hord x hx) = W0 cell blk hord x hx +
        FixedD16.correctionLinear (aS (s x)) (fun r => res.res r x) := by
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

theorem CellProducts16'.corrected_posDef (P : CellProducts16' idx c h s β m cell blk N t nb)
    (x : ℝ) (hx : x ∈ cellDomain) (hs : 0 ≤ s x) (hm : Profile.Valid 16 m) (b : GramBlock 8) :
    ((correctedGram (gramMap s x hs) (rightInverse (aS (s x))) (target s β m x hs hm)
      (W0 cell blk P.hord x hx)).val b).PosDef :=
  corrected_posDef_of P.hord P.res P.F0.posDef P.F1.posDef P.M0plus.posDef P.M0standard.posDef x hx hs hm b

set_option maxRecDepth 8192 in
/-- `certificate` for the whole-centre products. -/
theorem CellProducts16'.certificate (P : CellProducts16' idx c h s β m cell blk N t nb)
    (x : ℝ) (hx : x ∈ cellDomain) : Certificate (s x) (aS (s x)) 16 m :=
  have hs := P.s_nonneg x hx
  certificate_of_exact_gram_correction (s x) (aS (s x)) (β x) 16 m hs (aS_physical _ hs)
    (aS_mem_and_root _ hs).2 (Or.inr (Or.inr (Or.inl rfl))) P.profile pivots pivots_valid
    (P.β_pos x hx)
    (rightInverse (aS (s x))) (rightInverse_recovery _ (aS_physical _ hs))
    (W0 cell blk P.hord x hx) (P.corrected_posDef x hx hs P.profile)

/-- **The generic D16 cell theorem, whole-centre version.** -/
theorem cellSpec_of_products16' (P : CellProducts16' idx c h s β m cell blk N t nb) :
    Blueprint.CellSpec idx := by
  apply cellSpec_of_affine_certificates idx c h P.hh P.hlo P.hhi 16 m
  intro x hx
  have hcert := P.certificate x hx
  rw [P.s_affine x] at hcert
  exact hcert

end Assembly

end ThomsonCompact.Interface.D16

#print axioms ThomsonCompact.Interface.D16.rightInverse_recovery
#print axioms ThomsonCompact.Interface.D16.Active16'.posDef
#print axioms ThomsonCompact.Interface.D16.cellSpec_of_products16'
#print axioms ThomsonCompact.Interface.D16.scalarDims
#print axioms ThomsonCompact.Interface.D16.Residual16.decomposition
