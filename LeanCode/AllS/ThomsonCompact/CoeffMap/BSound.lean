import ThomsonCompact.CoeffMap.BProg
import ThomsonCompact.CoeffMap.KRowsSound
import ThomsonCompact.CoeffMap.ECheck

/-!
# Soundness of the D12 W0 block-contribution program (F2b b, c)

`blockTM_sound`: for a height TM `A` enclosing `aS ∘ s` on the cell and Gram TMs `WT` enclosing the literal
Gram entries `W0f`, every `ok` TM `blockTM c A WT bi r` encloses `g12 s Kpk cell blk hord bi r`, the W0 block
contribution of `Residual12` (with the packed RF columns `Kpk`). Ingredients: `gTM_sound` (`Contract`),
`gF_eq` (`Rep`), the one-time table check `eList_eq` (`ECheck`) and the row lemmas (`KRowsSound`).
-/

namespace ThomsonCompact.CoeffMap

open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite ThomsonCompact.Packed
open ThomsonCompact.CoeffMap.D12
open scoped BigOperators

variable {N S B W : ℕ}

/-- The literal Gram entries of block `b` on `ℕ` indices (zero outside the block). -/
noncomputable def W0f (cell : Literals.Cell) (blk : GramBlock 6 → Literals.Block)
    (hord : ∀ b, (blk b).order = gramBlockDimension 6 b) (b : GramBlock 6) (i j : ℕ) (t : ℝ) : ℝ :=
  if h : i < gramBlockDimension 6 b ∧ j < gramBlockDimension 6 b then
    ThomsonCompact.Interface.D12.W0mat cell blk hord t b ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

/-- Real rows of block `bi`. -/
noncomputable def blockRowF (a : ℝ → ℝ) (bi : ℕ) : ℕ → List (ℕ × (ℝ → ℝ)) :=
  if bi < 6 then momentRowF a bi (pivN bi) (6 - bi) else scalarRowF a (bi - 6) (sDimN (bi - 6))

theorem blockRow_ok (hg : Good N S B W) {A : TM} {a : ℝ → ℝ} (hA : Encl (mkCtx N S B W) A a) (bi : Fin 14)
    (u : ℕ) : RowOk (mkCtx N S B W) (blockRow (mkCtx N S B W) A bi u) (blockRowF a bi u) := by
  unfold blockRow blockRowF
  by_cases h : bi.val < 6
  · simp only [h, if_true]
    have hp : pivN bi ≤ 6 - bi := by fin_cases bi <;> simp_all [pivN]
    exact momentRow_ok hg hA bi (pivN bi) (6 - bi) u h hp rfl
  · simp only [h, if_false]
    exact scalarRow_ok hg hA _ _ _

/-- **Generic contribution soundness** for one block `b` with rows `row`/`rowF` and table index `bi`. -/
theorem contrib_sound (hg : Good N S B W) (s : ℝ → ℝ) (cell : Literals.Cell)
    (blk : GramBlock 6 → Literals.Block) (hord : ∀ b, (blk b).order = gramBlockDimension 6 b)
    (WT : ℕ → ℕ → TM) (b : GramBlock 6) (row : ℕ → List (ℕ × Option TM)) (rowF : ℕ → List (ℕ × (ℝ → ℝ)))
    (hW : ∀ i j, EnclOk (mkCtx N S B W) (WT i j) (W0f cell blk hord b i j))
    (hrow : ∀ u, RowOk (mkCtx N S B W) (row u) (rowF u))
    (hrep : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ∀ u : Fin (rawDim b), ∀ F : ℕ → ℝ,
      ((rowF u).map fun q => q.2 t * F q.1).sum =
        ∑ i : Fin (gramBlockDimension 6 b), blockMatrix (aS (s t)) (D12RF.Kpk (aS (s t))) b u i * F i)
    (E : List (ℕ × ℕ × Bool × ℕ)) (tag : Tag) (hE : E = symEntries (zG b tag) (rawDim b)) :
    EnclOk (mkCtx N S B W) (gTM (mkCtx N S B W) WT row E (blockDen b))
      (fun t => contribution (aS (s t)) (D12RF.Kpk (aS (s t)))
        (ThomsonCompact.Interface.D12.W0mat cell blk hord t) b tag) := by
  intro hok
  have h := gTM_sound hg hW hrow E (blockDen b) hok
  refine h.congr (fun t ht => ?_)
  rw [hE]
  refine (gF_eq (W0f cell blk hord b) rowF (zG b tag) (blockDen b)
    (blockMatrix (aS (s t)) (D12RF.Kpk (aS (s t))) b) (ThomsonCompact.Interface.D12.W0mat cell blk hord t b)
    (fun u v => (blockCoef b tag u v : ℝ)) t ?_ (hrep t ht) ?_ ?_).trans ?_
  · intro u v
    rw [blockCoef_eq, zG, dif_pos ⟨u.isLt, v.isLt⟩]
    push_cast
    rfl
  · intro i j
    simp only [W0f, dif_pos (And.intro i.isLt j.isLt)]
  · intro i j
    have hx : t ∈ cellDomain := ht
    have hs := ThomsonCompact.Interface.D12.isSymm_of_posDef
      (ThomsonCompact.Interface.D12.W0mat_posDef cell blk hord t hx b)
    have h1 := congrFun (congrFun hs i) j
    rw [Matrix.transpose_apply] at h1
    exact h1.symm
  · rfl

theorem pivN_eq (k : Fin 6) : pivN k = (ThomsonCompact.Interface.D12.pivots k).val := by
  fin_cases k <;> rfl

theorem symm_inl (k : Fin 6) : (blockEquiv.symm (.inl k)).val = k.val := by
  fin_cases k <;> rfl

theorem symm_inr (sb : ScalarBlockName) : (blockEquiv.symm (.inr sb)).val = 6 + D12RF.bIdx sb := by
  cases sb <;> rfl

theorem sDim_eq (sb : ScalarBlockName) : scalarBlockDimension sb 6 = sDimN (D12RF.bIdx sb) := by
  rw [ThomsonCompact.Interface.D12.scalarDims]
  cases sb <;> rfl

/-- **B soundness for one Gram block** (indexed by the block itself). -/
theorem blockTM_sound_b (hg : Good N S B W) {A : TM} (s : ℝ → ℝ)
    (hA : Encl (mkCtx N S B W) A (fun t => aS (s t))) (cell : Literals.Cell)
    (blk : GramBlock 6 → Literals.Block) (hord : ∀ b, (blk b).order = gramBlockDimension 6 b)
    (WT : ℕ → ℕ → TM) (b : GramBlock 6)
    (hW : ∀ i j, EnclOk (mkCtx N S B W) (WT i j) (W0f cell blk hord b i j)) (r : Fin 100) :
    EnclOk (mkCtx N S B W) (blockTM (mkCtx N S B W) A WT (blockEquiv.symm b).val r)
      (fun t => contribution (aS (s t)) (D12RF.Kpk (aS (s t)))
        (ThomsonCompact.Interface.D12.W0mat cell blk hord t) b (tagN r)) := by
  have hE := eList_eq (blockEquiv.symm b) r r.isLt
  rw [Equiv.apply_symm_apply] at hE
  have hD := eDen_eq (blockEquiv.symm b)
  rw [Equiv.apply_symm_apply] at hD
  have hS := eSize_eq (blockEquiv.symm b)
  rw [Equiv.apply_symm_apply] at hS
  unfold blockTM
  rw [hD, hS, gTMp_eq _ (by rw [hE]; exact symEntries_range _ _)]
  cases b with
  | inl k =>
    have hrow : blockRow (mkCtx N S B W) A (blockEquiv.symm (.inl k)).val =
        momentRow (mkCtx N S B W) A k (pivN k) (6 - k) := by
      rw [symm_inl]; simp [blockRow, k.isLt]
    rw [hrow]
    refine contrib_sound hg s cell blk hord WT (.inl k) _ (momentRowF (fun t => aS (s t)) k (pivN k) (6 - k))
      hW (fun u => momentRow_ok hg hA k (pivN k) (6 - k) u k.isLt ?_ rfl) ?_ _ (tagN r) hE
    · rw [pivN_eq]; exact Nat.lt_succ_iff.mp (ThomsonCompact.Interface.D12.pivots k).isLt
    · intro t _ u F
      rw [pivN_eq]
      exact momentRow_rep (fun t => aS (s t)) t k F u
  | inr sb =>
    have hrow : blockRow (mkCtx N S B W) A (blockEquiv.symm (.inr sb)).val =
        scalarRow (mkCtx N S B W) A (D12RF.bIdx sb) (sDimN (D12RF.bIdx sb)) := by
      rw [symm_inr]; simp [blockRow]
    rw [hrow]
    refine contrib_sound hg s cell blk hord WT (.inr sb) _
      (scalarRowF (fun t => aS (s t)) (D12RF.bIdx sb) (sDimN (D12RF.bIdx sb)))
      hW (fun u => scalarRow_ok hg hA _ _ u) ?_ _ (tagN r) hE
    intro t _ u F
    exact scalarRow_rep (fun t => aS (s t)) t sb _ (sDim_eq sb) u F

/-- **B soundness, `Residual12` form** (`g12` with the packed columns, `nb = 14`). -/
theorem blockTM_sound (hg : Good N S B W) {A : TM} (s : ℝ → ℝ)
    (hA : Encl (mkCtx N S B W) A (fun t => aS (s t))) (cell : Literals.Cell)
    (blk : GramBlock 6 → Literals.Block) (hord : ∀ b, (blk b).order = gramBlockDimension 6 b)
    (WT : ℕ → ℕ → TM) (bi : Fin 14)
    (hW : ∀ i j, EnclOk (mkCtx N S B W) (WT i j) (W0f cell blk hord (blockEquiv bi) i j)) (r : Fin 100) :
    EnclOk (mkCtx N S B W) (blockTM (mkCtx N S B W) A WT bi r) (fun t => g12 s D12RF.Kpk cell blk hord bi r t) := by
  have h := blockTM_sound_b hg s hA cell blk hord WT (blockEquiv bi) hW r
  rw [Equiv.symm_apply_apply] at h
  refine h.congr (fun t _ => ?_)
  simp only [g12, tagN, dif_pos r.isLt]

#print axioms blockTM_sound

/-! ## Pieces over pair groups, tabled contraction (F2c) -/

theorem W0f_symm (cell : Literals.Cell) (blk : GramBlock 6 → Literals.Block)
    (hord : ∀ b, (blk b).order = gramBlockDimension 6 b) (b : GramBlock 6) (i j : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) : W0f cell blk hord b i j t = W0f cell blk hord b j i t := by
  unfold W0f
  by_cases h : i < gramBlockDimension 6 b ∧ j < gramBlockDimension 6 b
  · rw [dif_pos h, dif_pos ⟨h.2, h.1⟩]
    have hx : t ∈ cellDomain := ht
    have hs := ThomsonCompact.Interface.D12.isSymm_of_posDef
      (ThomsonCompact.Interface.D12.W0mat_posDef cell blk hord t hx b)
    have h1 := congrFun (congrFun hs ⟨j, h.2⟩) ⟨i, h.1⟩
    rw [Matrix.transpose_apply] at h1
    exact h1
  · rw [dif_neg h, dif_neg (fun h' => h ⟨h'.2, h'.1⟩)]

theorem blockRowz_eq (c : Ctx) (A : TM) (bi : ℕ) : blockRowz c A bi = blockRow c A bi := by
  unfold blockRowz blockRow
  split
  · rfl
  · funext u
    exact scalarRowz_eq c A _ _ u

/-- The real contraction over the full sparse list is the block contribution (core of `contrib_sound`). -/
theorem gF_contrib (s : ℝ → ℝ) (cell : Literals.Cell) (blk : GramBlock 6 → Literals.Block)
    (hord : ∀ b, (blk b).order = gramBlockDimension 6 b) (b : GramBlock 6) (rowF : ℕ → List (ℕ × (ℝ → ℝ)))
    (hrep : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ∀ u : Fin (rawDim b), ∀ F : ℕ → ℝ,
      ((rowF u).map fun q => q.2 t * F q.1).sum =
        ∑ i : Fin (gramBlockDimension 6 b), blockMatrix (aS (s t)) (D12RF.Kpk (aS (s t))) b u i * F i)
    (tag : Tag) (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    gF (W0f cell blk hord b) rowF (symEntries (zG b tag) (rawDim b)) (blockDen b) t =
      contribution (aS (s t)) (D12RF.Kpk (aS (s t))) (ThomsonCompact.Interface.D12.W0mat cell blk hord t) b tag := by
  refine (gF_eq (W0f cell blk hord b) rowF (zG b tag) (blockDen b)
    (blockMatrix (aS (s t)) (D12RF.Kpk (aS (s t))) b) (ThomsonCompact.Interface.D12.W0mat cell blk hord t b)
    (fun u v => (blockCoef b tag u v : ℝ)) t ?_ (hrep t ht) ?_ ?_).trans ?_
  · intro u v
    rw [blockCoef_eq, zG, dif_pos ⟨u.isLt, v.isLt⟩]
    push_cast
    rfl
  · intro i j
    simp only [W0f, dif_pos (And.intro i.isLt j.isLt)]
  · intro i j
    have hx : t ∈ cellDomain := ht
    have hs := ThomsonCompact.Interface.D12.isSymm_of_posDef
      (ThomsonCompact.Interface.D12.W0mat_posDef cell blk hord t hx b)
    have h1 := congrFun (congrFun hs i) j
    rw [Matrix.transpose_apply] at h1
    exact h1.symm
  · rfl

theorem gF_block_b (s : ℝ → ℝ) (cell : Literals.Cell) (blk : GramBlock 6 → Literals.Block)
    (hord : ∀ b, (blk b).order = gramBlockDimension 6 b) (b : GramBlock 6) (r : Fin 100) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    gF (W0f cell blk hord b) (blockRowF (fun t => aS (s t)) (blockEquiv.symm b).val)
        (D12E.eList (blockEquiv.symm b).val r) (D12E.eDen (blockEquiv.symm b).val) t =
      contribution (aS (s t)) (D12RF.Kpk (aS (s t))) (ThomsonCompact.Interface.D12.W0mat cell blk hord t) b (tagN r) := by
  have hE := eList_eq (blockEquiv.symm b) r r.isLt
  rw [Equiv.apply_symm_apply] at hE
  have hD := eDen_eq (blockEquiv.symm b)
  rw [Equiv.apply_symm_apply] at hD
  rw [hE, hD]
  cases b with
  | inl k =>
    have hrow : blockRowF (fun t => aS (s t)) (blockEquiv.symm (.inl k)).val =
        momentRowF (fun t => aS (s t)) k (pivN k) (6 - k) := by
      rw [symm_inl]; simp [blockRowF, k.isLt]
    rw [hrow]
    refine gF_contrib s cell blk hord (.inl k) _ ?_ (tagN r) t ht
    intro t _ u F
    rw [pivN_eq]
    exact momentRow_rep (fun t => aS (s t)) t k F u
  | inr sb =>
    have hrow : blockRowF (fun t => aS (s t)) (blockEquiv.symm (.inr sb)).val =
        scalarRowF (fun t => aS (s t)) (D12RF.bIdx sb) (sDimN (D12RF.bIdx sb)) := by
      rw [symm_inr]; simp [blockRowF]
    rw [hrow]
    refine gF_contrib s cell blk hord (.inr sb) _ ?_ (tagN r) t ht
    intro t _ u F
    exact scalarRow_rep (fun t => aS (s t)) t sb _ (sDim_eq sb) u F

theorem gF_block (s : ℝ → ℝ) (cell : Literals.Cell) (blk : GramBlock 6 → Literals.Block)
    (hord : ∀ b, (blk b).order = gramBlockDimension 6 b) (bi : Fin 14) (r : Fin 100) (t : ℝ)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    gF (W0f cell blk hord (blockEquiv bi)) (blockRowF (fun t => aS (s t)) bi) (D12E.eList bi r) (D12E.eDen bi) t =
      g12 s D12RF.Kpk cell blk hord bi r t := by
  have h := gF_block_b s cell blk hord (blockEquiv bi) r t ht
  rw [Equiv.symm_apply_apply] at h
  rw [h]
  simp only [g12, tagN, dif_pos r.isLt]

theorem sum_filter_groups {α : Type*} (key : α → ℕ) (G : ℕ) (hk : ∀ a, key a < G) (f : α → ℝ) :
    ∀ E : List α, ∑ g ∈ Finset.range G, ((E.filter fun e => Nat.beq (key e) g).map f).sum = (E.map f).sum
  | [] => by simp
  | e :: E => by
    have ih := sum_filter_groups key G hk f E
    have hsplit : ∀ g, ((((e :: E).filter fun e => Nat.beq (key e) g)).map f).sum =
        (if key e = g then f e else 0) + ((E.filter fun e => Nat.beq (key e) g).map f).sum := by
      intro g
      rw [List.filter_cons]
      by_cases h : key e = g
      · rw [if_pos (by simp [h]), if_pos h, List.map_cons, List.sum_cons]
      · rw [if_neg (by simpa using h), if_neg h, zero_add]
    simp only [hsplit, Finset.sum_add_distrib, ih, List.map_cons, List.sum_cons]
    rw [Finset.sum_ite_eq (Finset.range G) (key e) (fun _ => f e), if_pos (Finset.mem_range.mpr (hk e))]

theorem grpOf_lt (gmap G : ℕ) (hG : 0 < G) (e : ℕ × ℕ × Bool × ℕ) : grpOf gmap G e < G := by
  unfold grpOf
  exact lt_of_le_of_lt (Nat.min_le_right _ _) (show Nat.sub G 1 < G from by show G - 1 < G; omega)

/-- The real function of piece `g` of block `bi` at coordinate `r`. -/
noncomputable def gPiece (s : ℝ → ℝ) (cell : Literals.Cell) (blk : GramBlock 6 → Literals.Block)
    (hord : ∀ b, (blk b).order = gramBlockDimension 6 b) (bi : Fin 14) (gmap G g : ℕ) (r : Fin 100) (t : ℝ) : ℝ :=
  gF (W0f cell blk hord (blockEquiv bi)) (blockRowF (fun t => aS (s t)) bi)
    ((D12E.eList bi r).filter fun e => Nat.beq (grpOf gmap G e) g) (D12E.eDen bi) t

/-- **The pieces of a block sum to its contribution.** -/
theorem gPiece_sum (s : ℝ → ℝ) (cell : Literals.Cell) (blk : GramBlock 6 → Literals.Block)
    (hord : ∀ b, (blk b).order = gramBlockDimension 6 b) (bi : Fin 14) (gmap G : ℕ) (hG : 0 < G) (r : Fin 100)
    (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    ∑ g ∈ Finset.range G, gPiece s cell blk hord bi gmap G g r t = g12 s D12RF.Kpk cell blk hord bi r t := by
  rw [← gF_block s cell blk hord bi r t ht]
  unfold gPiece gF
  exact sum_filter_groups (grpOf gmap G) G (grpOf_lt gmap G hG) _ _

/-- **B soundness for one piece** (tabled contraction, faster records), on the filtered coefficient list. -/
theorem blockTMf_sound (hg : Good N S B W) {A : TM} (s : ℝ → ℝ)
    (hA : Encl (mkCtx N S B W) A (fun t => aS (s t))) (cell : Literals.Cell)
    (blk : GramBlock 6 → Literals.Block) (hord : ∀ b, (blk b).order = gramBlockDimension 6 b)
    (WT : ℕ → ℕ → TM) (bi : Fin 14)
    (hW : ∀ i j, EnclOk (mkCtx N S B W) (WT i j) (W0f cell blk hord (blockEquiv bi) i j)) (gmap G g : ℕ)
    (r : Fin 100) :
    EnclOk (mkCtx N S B W) (gTMz (mkCtx N S B W) WT (blockRowz (mkCtx N S B W) A bi) (gDimN bi) (D12E.eSize bi)
      ((D12E.eList bi r).filter fun e => Nat.beq (grpOf gmap G e) g) (D12E.eDen bi))
      (gPiece s cell blk hord bi gmap G g r) := by
  unfold gPiece
  rw [blockRowz_eq]
  refine gTMz_sound hg hW (blockRow_ok hg hA bi) (fun i j t ht => W0f_symm cell blk hord _ i j t ht) _ _ _ _ ?_
  intro e he
  have he' := (List.mem_filter.mp he).1
  rw [eList_eq bi r r.isLt] at he'
  rw [eSize_eq bi]
  exact symEntries_range _ _ e he'

#print axioms gPiece_sum
#print axioms blockTMf_sound

end ThomsonCompact.CoeffMap
