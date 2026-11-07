import ThomsonCompact.CoeffMap.Deg.RepSound
import ThomsonCompact.CoeffMap.GramPackSound
import ThomsonCompact.CoeffMap.Deg.OneTime.Defs
import AllS.Units.N_AI.N_fixed_tables.FullGramSourceSupport
import AllS.Units.N_AI.N_fixed_tables.RetainedGramSupport
import AllS.Units.N_AI.N_residual_replay.ScalarKernelPolynomialSupport
import AllS.Units.N_AI.N_residual_replay.RawSparseLookupSupport
import AllS.Units.N_AI.N_gram_replay.LiteralGramSupport

/-!
# Degree-generic W0 link (F2h): retained Gram coordinates as the sum of the W0 pieces

For half degree `d` (`6 ≤ d ≤ 9`), valid moment pivots `p` and per-degree W0 data `L : DegD` (`CoeffMap.Deg.Codec`)
whose tables are checked once per degree (`LinkFacts`, `DegLink`), the retained coordinates of `gramPoly a d p W`
are, for every Gram family `W`,

  `Σ_{b < d+8} Σ_{u,v < rdim b} Cc b r u v · Σ_{i,j < gdim b} K b u i · K b v j · W b i j`   (`retained_gramL`)

with the column matrices `KnL` (moment blocks: the pivot nullspace formula of `momentKernelMatrix`; scalar blocks: the
RF records of `L`) and the class coefficients `Cc` of `CoeffMap.Deg.RepSound`. With the representation theorem
`rep_sum` this is the sum of the W0 pieces (`pieces_link`): the real contraction of the kernel rows `blockRowF`
(`pLF_eq`) at the literal Gram entries `litW`. Nothing here depends on a degree beyond `d`; the per-degree inputs are
the fields of `DegLink` (`CoeffMap/Deg/Bridges/D<D>`).

Proof route as `CoeffMap.W0Link` (D12): source kernel (moment blocks: the old raw moment tensors; scalar blocks:
`rawScalarCoordinates (rawScalarProductSpec …)` of the decoded raw tags, whose coefficients are those of the mirror
`rscZ` by `rscZ_eval`), `fixedGramSource_canonical`, `fixedGram_retained_of_source`, `fixedGramSource_coefficient`.
-/

noncomputable section
open scoped BigOperators

namespace ThomsonCompact.CoeffMap.Deg.Link

open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite ThomsonCompact.CoeffMap ThomsonCompact.Packed
open ThomsonCompact.CoeffMap.Deg

/-! ## Block indexing -/

/-- Scalar block index (`rawScalarProductSpec` order; the order of the scalar blocks in `DegD`). -/
def sIdx : ScalarBlockName → ℕ
  | .m0Plus => 0
  | .m0Sign => 1
  | .m0Standard => 2
  | .m1Even => 3
  | .m1Odd => 4
  | .mdetPlus => 5
  | .mdetSign => 6
  | .mdetStandard => 7

theorem sIdx_lt (sb : ScalarBlockName) : sIdx sb < 8 := by cases sb <;> decide

/-- Scalar blocks in index order. -/
def sOf : Fin 8 → ScalarBlockName :=
  ![.m0Plus, .m0Sign, .m0Standard, .m1Even, .m1Odd, .mdetPlus, .mdetSign, .mdetStandard]

def sEquiv : Fin 8 ≃ ScalarBlockName where
  toFun := sOf
  invFun sb := ⟨sIdx sb, sIdx_lt sb⟩
  left_inv i := by fin_cases i <;> rfl
  right_inv sb := by cases sb <;> rfl

/-- Index of a Gram block in `DegD` (moment blocks `0 … d-1`, then the scalar blocks). -/
def bIdx (d : ℕ) : GramBlock d → ℕ
  | .inl k => k.val
  | .inr sb => d + sIdx sb

theorem bIdx_lt (d : ℕ) (b : GramBlock d) : bIdx d b < d + 8 := by
  cases b with
  | inl k => exact lt_of_lt_of_le k.isLt (Nat.le_add_right _ _)
  | inr sb => show d + sIdx sb < d + 8; have := sIdx_lt sb; omega

/-- Sums over the Gram blocks as sums over their indices. -/
theorem sum_blocks {M : Type*} [AddCommMonoid M] (d : ℕ) (G : ℕ → M) :
    ∑ b : GramBlock d, G (bIdx d b) = ∑ bi ∈ Finset.range (d + 8), G bi := by
  have h1 : ∑ k : Fin d, G (bIdx d (Sum.inl k)) = ∑ x ∈ Finset.range d, G x :=
    Fin.sum_univ_eq_sum_range (fun k => G k) d
  have h2 : ∑ sb : ScalarBlockName, G (bIdx d (Sum.inr sb)) = ∑ x ∈ Finset.range 8, G (d + x) := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => G (d + j)) 8]
    exact (Fintype.sum_equiv sEquiv _ _ (fun i => by fin_cases i <;> rfl)).symm
  rw [Fintype.sum_sum_type, Finset.sum_range_add, h1, h2]

/-- Literal blocks of decoded cell data in the Gram block order of degree `2 d`. -/
def blkOfD (d : ℕ) (data : CellData) : GramBlock d → Literals.Block := fun b => data.block (bIdx d b)

/-! ## The real column matrices and the kernel rows -/

/-- Real column-matrix entry `(u, i)` of block `bi` at height `a`: moment blocks by the pivot nullspace formula,
scalar blocks by the RF record of the column table. -/
def KnL (L : DegD) (a : ℝ) (bi u i : ℕ) : ℝ :=
  if bi < L.dH then
    (if u = sAb (L.piv bi) i then 1 else 0) -
      momentP bi (sAb (L.piv bi) i) a / momentP bi (L.piv bi) a * (if u = L.piv bi then 1 else 0)
  else (L.rfRec (L.colRec (bi - L.dH) i u)).value a

theorem filter_range_sumD (p : ℕ → Bool) (g : ℕ → ℝ) : ∀ n, (∀ i, i < n → p i = false → g i = 0) →
    (((List.range n).filter p).map g).sum = ∑ i ∈ Finset.range n, g i
  | 0, _ => by simp
  | n + 1, h => by
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append,
      filter_range_sumD p g n (fun i hi => h i (by omega)), Finset.sum_range_succ]
    by_cases hp : p n
    · simp [hp]
    · simp [hp, h n (by omega) (by simpa using hp)]

theorem sAb_ne (p i : ℕ) : sAb p i ≠ p := by unfold sAb; split_ifs <;> omega

/-- **The kernel rows represent the column matrix** (both block kinds). -/
theorem blockRowF_rep (L : DegD) (a : ℝ → ℝ) (t : ℝ) (bi u : ℕ) (hu : u < L.rdim bi)
    (h1 : ∀ y, (L.rfRec 1).value y = 0)
    (hmom : bi < L.dH → L.piv bi ≤ L.gdim bi ∧ L.rdim bi = L.gdim bi + 1) (F : ℕ → ℝ) :
    ((L.blockRowF a bi u).map fun q => q.2 t * F q.1).sum =
      ∑ i ∈ Finset.range (L.gdim bi), KnL L (a t) bi u i * F i := by
  unfold DegD.blockRowF KnL
  by_cases hb : bi < L.dH
  · simp only [if_pos hb]
    obtain ⟨hp, hr⟩ := hmom hb
    by_cases hup : u = L.piv bi
    · rw [if_pos hup, List.map_map, list_sum_range]
      apply Finset.sum_congr rfl
      intro i _
      have hne : u ≠ sAb (L.piv bi) i := by rw [hup]; exact (sAb_ne _ _).symm
      rw [if_neg hne, if_pos hup]
      simp only [Function.comp_apply]
      ring
    · rw [if_neg hup]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul, hup, if_false,
        mul_zero, sub_zero]
      have key : ∀ i, (u = sAb (L.piv bi) i ↔ i = (if u < L.piv bi then u else u - 1)) := by
        intro i
        unfold sAb
        constructor
        · intro h; split_ifs at h ⊢ <;> omega
        · intro h; split_ifs at h ⊢ <;> omega
      rw [Finset.sum_eq_single (if u < L.piv bi then u else u - 1)]
      · rw [if_pos ((key _).mpr rfl), one_mul]
      · intro i _ hi
        rw [if_neg (fun h => hi ((key i).mp h)), zero_mul]
      · intro h
        exact absurd (Finset.mem_range.mpr (by split_ifs <;> omega)) h
  · simp only [if_neg hb]
    unfold DegD.scalarRowF
    rw [List.map_map]
    have hjb : Nat.add L.dH (bi - L.dH) = bi := by show L.dH + (bi - L.dH) = bi; omega
    rw [hjb]
    refine filter_range_sumD _ (fun i => (L.rfRec (L.colRec (bi - L.dH) i u)).value (a t) * F i) _ ?_
    intro i _ hp
    have h' : L.colRec (bi - L.dH) i u = 1 := by simpa using hp
    simp [h', h1]

/-- **The real `P` table is the contraction `K W Kᵀ`** of the column matrix (rows `u, v < rdim`). -/
theorem pLF_eq (L : DegD) (a : ℝ → ℝ) (Wf : ℕ → ℕ → ℝ → ℝ) (t : ℝ) (bi u v : ℕ) (hu : u < L.rdim bi)
    (hv : v < L.rdim bi) (h1 : ∀ y, (L.rfRec 1).value y = 0)
    (hmom : bi < L.dH → L.piv bi ≤ L.gdim bi ∧ L.rdim bi = L.gdim bi + 1) :
    pLF Wf (L.blockRowF a bi) (L.rdim bi) u v t =
      ∑ i ∈ Finset.range (L.gdim bi), ∑ j ∈ Finset.range (L.gdim bi),
        KnL L (a t) bi u i * KnL L (a t) bi v j * Wf i j t := by
  unfold pLF pF
  rw [if_pos ⟨hu, hv⟩, blockRowF_rep L a t bi u hu h1 hmom (fun i => zF Wf (L.blockRowF a bi) i v t)]
  apply Finset.sum_congr rfl
  intro i _
  unfold zF
  rw [blockRowF_rep L a t bi v hv h1 hmom (fun j => Wf i j t), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-! ## Per-degree facts -/

/-- The per-degree table facts used by the link (each a `decide` check of the degree's data). -/
structure LinkFacts (L : DegD) (d : ℕ) (p : MomentPivots d) : Prop where
  dH : L.dH = d
  gdim_mom : ∀ k : Fin d, L.gdim k.val = d - k.val
  rdim_mom : ∀ k : Fin d, L.rdim k.val = d - k.val + 1
  piv : ∀ k : Fin d, L.piv k.val = (p k).val
  gdim_sc : ∀ sb : ScalarBlockName, L.gdim (d + sIdx sb) = scalarBlockDimension sb d
  bden_sc : ∀ sb : ScalarBlockName, L.bden (d + sIdx sb) = famDen (famOf (sIdx sb))
  pairs : ∀ sb : ScalarBlockName, pairOkL L (sIdx sb) = true
  rec0 : ∀ y, (L.rfRec 0).value y = 1
  rec1 : ∀ y, (L.rfRec 1).value y = 0
  mom_rat : ∀ k : Fin d, ∀ j, j ≤ L.gdim k.val → ThomsonCompact.CoeffMap.qAllZero (mP k.val j).s = true
  den_tab : ∀ k, k < L.nRec → L.denIdx k < L.nDen ∧ 0 < L.denS (L.denIdx k)

/-! ### The Bool checks of `OneTime.Defs` -/

theorem rec01_spec (L : DegD) (h : rec01L L = true) :
    L.numZ 0 = [1] ∧ L.numS 0 = 1 ∧ L.denZ (L.denIdx 0) = [1] ∧ L.denS (L.denIdx 0) = 1 ∧ L.numZ 1 = [] := by
  unfold rec01L at h
  simp only [Bool.and_eq_true, beq_iff_eq, Nat.beq_eq, List.isEmpty_iff] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem rec0_of (L : DegD) (h : rec01L L = true) (y : ℝ) : (L.rfRec 0).value y = 1 := by
  obtain ⟨h1, h2, h3, h4, -⟩ := rec01_spec L h
  simp [RFRec.value, DegD.rfRec, h1, h2, h3, h4, evalZ, horner]

theorem rec1_of (L : DegD) (h : rec01L L = true) (y : ℝ) : (L.rfRec 1).value y = 0 := by
  obtain ⟨-, -, -, -, h5⟩ := rec01_spec L h
  simp [RFRec.value, DegD.rfRec, h5, evalZ]

theorem momRat_of (L : DegD) (d : ℕ) (hd : L.dH = d) (h : momRatL L = true) :
    ∀ k : Fin d, ∀ j, j ≤ L.gdim k.val → ThomsonCompact.CoeffMap.qAllZero (mP k.val j).s = true := by
  intro k j hj
  unfold momRatL at h
  rw [List.all_eq_true] at h
  have h2 := h k.val (List.mem_range.mpr (by rw [hd]; exact k.isLt))
  rw [List.all_eq_true] at h2
  exact h2 j (List.mem_range.mpr (by show j < L.gdim k.val + 1; omega))

theorem denTab_of (L : DegD) (h : denTabL L = true) :
    ∀ k, k < L.nRec → L.denIdx k < L.nDen ∧ 0 < L.denS (L.denIdx k) := by
  intro k hk
  unfold denTabL at h
  rw [List.all_eq_true] at h
  have := h k (List.mem_range.mpr hk)
  simp only [Bool.and_eq_true, Nat.blt_eq] at this
  exact this

theorem grpsOk_of (L : DegD) (h : grpsOkL L = true) : ∀ b, b < L.dH + 8 → L.grpOk b = true := by
  intro b hb
  unfold grpsOkL at h
  rw [List.all_eq_true] at h
  exact h b (List.mem_range.mpr hb)

/-! ## Scalar columns and the source kernel -/

/-- Raw dimension of a scalar block. -/
def rawSizeL (L : DegD) (d : ℕ) (sb : ScalarBlockName) : ℕ := L.rdim (d + sIdx sb)

/-- Raw scalar tags of a scalar block (decoded from `L`). -/
def tagsL (L : DegD) (d : ℕ) (sb : ScalarBlockName) (u : Fin (rawSizeL L d sb)) : StandardTag :=
  L.stag (sIdx sb) u.val

/-- The scalar column matrix of the RF records at height `a`. -/
def KpkL (L : DegD) (d : ℕ) (a : ℝ) (sb : ScalarBlockName) :
    Matrix (Fin (rawSizeL L d sb)) (Fin (scalarBlockDimension sb d)) ℝ :=
  fun u i => (L.rfRec (L.colRec (sIdx sb) i.val u.val)).value a

/-- `KpkL` expands the scalar features at height `a` in the raw scalar bases of the decoded tags (both components of
the standard blocks use the same columns): the hypothesis of the scalar kernel identities. -/
def ScalarColumnsL (L : DegD) (d : ℕ) (a : ℝ) : Prop :=
  ∀ sb : ScalarBlockName,
    (∀ i, scalarFeature sb a d 0 i = ∑ u, MvPolynomial.C (KpkL L d a sb u i) * rawScalarBasis sb false (tagsL L d sb u)) ∧
    (scalarBlockStandard sb = true →
      ∀ i, scalarFeature sb a d 1 i = ∑ u, MvPolynomial.C (KpkL L d a sb u i) * rawScalarBasis sb true (tagsL L d sb u))

/-- Raw scalar source polynomials (`rawScalarCoordinates` of the raw product spec of the tags). -/
def QsL (L : DegD) (d : ℕ) (sb : ScalarBlockName) (u v : Fin (rawSizeL L d sb)) : Poly3 :=
  rawScalarCoordinates (rawScalarProductSpec sb (tagsL L d sb u) (tagsL L d sb v))

/-- Raw dimension of a Gram block. -/
def rawDimL (L : DegD) (d : ℕ) : GramBlock d → ℕ
  | .inl k => d - k.val + 1
  | .inr sb => rawSizeL L d sb

/-- Column matrix of every block. -/
def blockMatL (L : DegD) (d : ℕ) (p : MomentPivots d) (a : ℝ) : (b : GramBlock d) →
    Matrix (Fin (rawDimL L d b)) (Fin (gramBlockDimension d b)) ℝ
  | .inl k => momentKernelMatrix a d p k
  | .inr sb => KpkL L d a sb

/-- Raw source polynomials of every block. -/
def blockQL (L : DegD) (d : ℕ) (momQ : (k : Fin d) → Matrix (Fin (d - k.val + 1)) (Fin (d - k.val + 1)) Poly3) :
    (b : GramBlock d) → Matrix (Fin (rawDimL L d b)) (Fin (rawDimL L d b)) Poly3
  | .inl k => momQ k
  | .inr sb => QsL L d sb

/-- Source kernel (invariant coordinates) of every Gram kernel entry. -/
def sourceKernelL (L : DegD) (d : ℕ) (p : MomentPivots d) (a : ℝ)
    (momQ : (k : Fin d) → Matrix (Fin (d - k.val + 1)) (Fin (d - k.val + 1)) Poly3) :
    (b : GramBlock d) → Fin (gramBlockDimension d b) → Fin (gramBlockDimension d b) → Poly3
  | .inl k => momentCoordinateKernel a d p k (momQ k)
  | .inr sb => scalarCoordinateKernel sb d (KpkL L d a sb) (QsL L d sb)

theorem sourceKernelL_subst (L : DegD) (d : ℕ) (p : MomentPivots d) (a : ℝ)
    (momQ : (k : Fin d) → Matrix (Fin (d - k.val + 1)) (Fin (d - k.val + 1)) Poly3)
    (hsub : ∀ k u v, invariantSubst (momQ k u v) = kernelRPoly k.val u.val v.val)
    (hK : ScalarColumnsL L d a) (b : GramBlock d) (i j : Fin (gramBlockDimension d b)) :
    invariantSubst (sourceKernelL L d p a momQ b i j) = gramKernel a d p b i j := by
  cases b with
  | inl k => exact momentCoordinateKernel_subst a d p k (momQ k) (hsub k) i j
  | inr sb =>
    have hQ : ∀ r c, invariantSubst (QsL L d sb r c) = rawScalarBilinear sb (tagsL L d sb r) (tagsL L d sb c) :=
      fun r c => rawScalarProductSpec_subst sb _ _
    cases hst : scalarBlockStandard sb
    · exact scalarCoordinateKernel_subst_nonstandard a sb d (tagsL L d sb) (KpkL L d a sb) (QsL L d sb) hst hQ
        (hK sb).1 i j
    · exact scalarCoordinateKernel_subst a sb d (tagsL L d sb) (KpkL L d a sb) (QsL L d sb) hQ (hK sb).1
        ((hK sb).2 hst) i j

theorem sourceKernelL_coeff (L : DegD) (d : ℕ) (p : MomentPivots d) (a : ℝ)
    (momQ : (k : Fin d) → Matrix (Fin (d - k.val + 1)) (Fin (d - k.val + 1)) Poly3)
    (b : GramBlock d) (i j : Fin (gramBlockDimension d b)) (t : Tag) :
    MvPolynomial.coeff (tagExponent t) (sourceKernelL L d p a momQ b i j) =
      ∑ u, ∑ v, blockMatL L d p a b u i * blockMatL L d p a b v j *
        MvPolynomial.coeff (tagExponent t) (blockQL L d momQ b u v) := by
  cases b with
  | inl k =>
    simp only [sourceKernelL, momentCoordinateKernel, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
    rfl
  | inr sb =>
    simp only [sourceKernelL, scalarCoordinateKernel, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
    rfl

/-- **Generic retained Gram coordinates** in block form (any Gram family, any height with scalar columns). -/
theorem retained_gram_blocks (L : DegD) (d : ℕ) (hl : 6 ≤ d) (hu : d ≤ 9) (p : MomentPivots d)
    (hp : ValidMomentPivots p) (a : ℝ) (ha : physical a)
    (momQ : (k : Fin d) → Matrix (Fin (d - k.val + 1)) (Fin (d - k.val + 1)) Poly3)
    (hsub : ∀ k u v, invariantSubst (momQ k u v) = kernelRPoly k.val u.val v.val)
    (hK : ScalarColumnsL L d a) (W : GramFamily d) (t : RetainedIndex (2 * d)) :
    retainCompatible a (2 * d) ⟨gramPoly a d p W, gramPoly_compatible a ha d hl hu p hp W⟩ t =
      ∑ b, ∑ i, ∑ j, W.val b i j * ∑ u, ∑ v, blockMatL L d p a b u i * blockMatL L d p a b v j *
        MvPolynomial.coeff (tagExponent t.val) (blockQL L d momQ b u v) := by
  refine (fixedGram_retained_of_source a ha d hl hu p hp W (fixedGramSource (sourceKernelL L d p a momQ) W)
    (fixedGramSource_canonical a p (sourceKernelL L d p a momQ) (sourceKernelL_subst L d p a momQ hsub hK) W)
    t).trans ?_
  rw [fixedGramSource_coefficient]
  simp only [sourceKernelL_coeff]

/-! ## Coefficients: the class coefficients `Cc` are the raw-tensor coefficients -/

theorem spec_symm (sb : ScalarBlockName) (t u : StandardTag) :
    rawScalarProductSpec sb t u = rawScalarProductSpec sb u t := by
  have h1 : rawTagAdd t.2 u.2 = rawTagAdd u.2 t.2 := by
    simp only [rawTagAdd, Nat.add_comm]
  cases sb <;> simp only [rawScalarProductSpec, h1, Bool.and_comm, Bool.or_comm]

theorem famOf_spec (sb : ScalarBlockName) (t u : StandardTag) :
    (rawScalarProductSpec sb t u).family = famOf (sIdx sb) ∧ (rawScalarProductSpec sb t u).det = detOf (sIdx sb) := by
  cases sb <;> exact ⟨rfl, rfl⟩

theorem spec_q (sb : ScalarBlockName) (t u : StandardTag) :
    (rawScalarProductSpec sb t u).leftQ = (Nat.beq (famOf (sIdx sb)) 2 && (t.1 && u.1)) ∧
    (rawScalarProductSpec sb t u).rightQ = (Nat.beq (famOf (sIdx sb)) 2 && (t.1 || u.1)) ∧
    (rawScalarProductSpec sb t u).tag = tadd t.2 u.2 := by
  cases sb <;> exact ⟨rfl, rfl, rfl⟩

theorem spec_eta (s : RawScalarSpec) : s = ⟨s.family, s.det, s.leftQ, s.rightQ, s.tag⟩ := rfl

theorem pairOkL_spec (L : DegD) (j : ℕ) (h : pairOkL L j = true) (u v : ℕ) (huv : u ≤ v)
    (hv : v < L.rdim (L.dH + j)) :
    decT L.aA L.aB (Nat.land (L.pairKey (L.dH + j) u v) 65535) = tadd (L.stag j u).2 (L.stag j v).2 ∧
    Nat.beq (Nat.land (Nat.shiftRight (L.pairKey (L.dH + j) u v) 16) 1) 1 =
      (Nat.beq (famOf j) 2 && ((L.stag j u).1 && (L.stag j v).1)) ∧
    Nat.beq (Nat.land (Nat.shiftRight (L.pairKey (L.dH + j) u v) 17) 1) 1 =
      (Nat.beq (famOf j) 2 && ((L.stag j u).1 || (L.stag j v).1)) ∧
    (3 ≤ famOf j → (tadd (L.stag j u).2 (L.stag j v).2).1 + (tadd (L.stag j u).2 (L.stag j v).2).2.1 + 4 < L.nPS ∧
      (tadd (L.stag j u).2 (L.stag j v).2).2.2 + 2 < L.nPS) := by
  unfold pairOkL at h
  rw [List.all_eq_true] at h
  have h2 := h v (List.mem_range.mpr hv)
  rw [List.all_eq_true] at h2
  have h3 := h2 u (List.mem_range.mpr (by show u < v + 1; omega))
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true', Nat.ble_eq, Nat.blt_eq] at h3
  obtain ⟨⟨⟨h4, h5⟩, h6⟩, h7⟩ := h3
  refine ⟨teq_eq h4, h5, h6, fun hf => ?_⟩
  rcases h7 with h7 | h7
  · exact absurd (Nat.ble_eq.mpr hf) (by rw [h7]; decide)
  · exact ⟨h7.1, h7.2⟩

/-- The scalar raw-tensor coefficient is the class coefficient. -/
theorem scalar_coeff (L : DegD) (d : ℕ) (p : MomentPivots d) (hF : LinkFacts L d p) (sb : ScalarBlockName)
    (u v : Fin (rawSizeL L d sb)) (r : ℕ) :
    MvPolynomial.coeff (tagExponent (L.rtag r)) (QsL L d sb u v) = L.Cc (d + sIdx sb) r u.val v.val := by
  -- reduce to `u ≤ v`
  have key : ∀ u' v' : Fin (rawSizeL L d sb), u'.val ≤ v'.val →
      MvPolynomial.coeff (tagExponent (L.rtag r)) (QsL L d sb u' v') =
        (L.kcoef (d + sIdx sb) (L.pairKey (d + sIdx sb) u'.val v'.val) r : ℝ) / L.bden (d + sIdx sb) := by
    intro u' v' hle
    have hv : v'.val < L.rdim (L.dH + sIdx sb) := by rw [hF.dH]; exact v'.isLt
    obtain ⟨e1, e2, e3, e4⟩ := pairOkL_spec L (sIdx sb) (hF.pairs sb) u'.val v'.val hle hv
    rw [hF.dH] at e1 e2 e3
    obtain ⟨hfam, hdet⟩ := famOf_spec sb (tagsL L d sb u') (tagsL L d sb v')
    obtain ⟨hlq, hrq, htg⟩ := spec_q sb (tagsL L d sb u') (tagsL L d sb v')
    have hf4 : famOf (sIdx sb) ≤ 4 := by cases sb <;> decide
    have hb : 3 ≤ famOf (sIdx sb) → (rawScalarProductSpec sb (tagsL L d sb u') (tagsL L d sb v')).tag.1 +
        (rawScalarProductSpec sb (tagsL L d sb u') (tagsL L d sb v')).tag.2.1 + 4 < L.nPS ∧
        (rawScalarProductSpec sb (tagsL L d sb u') (tagsL L d sb v')).tag.2.2 + 2 < L.nPS := by
      rw [htg]; exact e4
    have hev := rscZ_eval L.nPS (famOf (sIdx sb)) hf4 (detOf (sIdx sb))
      (rawScalarProductSpec sb (tagsL L d sb u') (tagsL L d sb v')).leftQ
      (rawScalarProductSpec sb (tagsL L d sb u') (tagsL L d sb v')).rightQ
      (rawScalarProductSpec sb (tagsL L d sb u') (tagsL L d sb v')).tag hb
    have hspec : rawScalarProductSpec sb (tagsL L d sb u') (tagsL L d sb v') =
        ⟨famOf (sIdx sb), detOf (sIdx sb), (rawScalarProductSpec sb (tagsL L d sb u') (tagsL L d sb v')).leftQ,
          (rawScalarProductSpec sb (tagsL L d sb u') (tagsL L d sb v')).rightQ,
          (rawScalarProductSpec sb (tagsL L d sb u') (tagsL L d sb v')).tag⟩ := by
      cases sb <;> rfl
    rw [← hspec] at hev
    have hc := congrArg (MvPolynomial.coeff (tagExponent (L.rtag r))) hev
    rw [spEval_coeff, MvPolynomial.coeff_C_mul] at hc
    have hden : ((famDen (famOf (sIdx sb)) : ℕ) : ℝ) ≠ 0 := by
      have : 0 < famDen (famOf (sIdx sb)) := by cases sb <;> decide
      exact_mod_cast this.ne'
    unfold QsL
    rw [hF.bden_sc sb, eq_div_iff hden, mul_comm, ← hc]
    -- the class polynomial of the key is the mirror `rscZ` of the spec
    unfold DegD.kcoef DegD.clsPoly
    have hblt : Nat.blt (d + sIdx sb) L.dH = false := by
      rw [hF.dH]; exact Bool.eq_false_iff.mpr (fun h => by have := Nat.blt_eq.mp h; omega)
    have hsub : Nat.sub (d + sIdx sb) L.dH = sIdx sb := by
      show d + sIdx sb - L.dH = sIdx sb
      rw [hF.dH]; omega
    rw [hblt, cond_false, hsub, e1, e2, e3, hlq, hrq, htg]
    rfl
  rcases le_total u.val v.val with h | h
  · rw [key u v h]
    unfold DegD.Cc
    rw [min_eq_left h, max_eq_right h]
  · have hs : QsL L d sb u v = QsL L d sb v u := by unfold QsL; rw [spec_symm]
    rw [hs, key v u h]
    unfold DegD.Cc
    rw [min_eq_right h, max_eq_left h]

/-! ## The block identity and the retained coordinates -/

theorem block_identity {n g : ℕ} (rd gd : ℕ) (hn : n = rd) (hg : g = gd)
    (Wm : Matrix (Fin g) (Fin g) ℝ) (K : Matrix (Fin n) (Fin g) ℝ) (C : Matrix (Fin n) (Fin n) ℝ)
    (Cn Kn Wn : ℕ → ℕ → ℝ) (hC : ∀ u v : Fin n, C u v = Cn u v) (hK : ∀ u i, K u i = Kn u i)
    (hW : ∀ i j, Wm i j = Wn i j) :
    ∑ i, ∑ j, Wm i j * ∑ u, ∑ v, K u i * K v j * C u v =
      ∑ u ∈ Finset.range rd, ∑ v ∈ Finset.range rd, Cn u v *
        ∑ i ∈ Finset.range gd, ∑ j ∈ Finset.range gd, Kn u i * Kn v j * Wn i j := by
  subst hn hg
  simp only [hC, hK, hW, Finset.sum_range, Finset.mul_sum]
  simp_rw [← Fintype.sum_prod_type']
  let e : Fin g × Fin g × Fin n × Fin n ≃ Fin n × Fin n × Fin g × Fin g :=
    ⟨fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1), fun y => (y.2.2.1, y.2.2.2, y.1, y.2.1), fun _ => rfl,
      fun _ => rfl⟩
  apply Fintype.sum_equiv e
  intro x
  simp only [e, Equiv.coe_fn_mk]
  ring

/-- Moment column entries on `ℕ` indices. -/
theorem val_succAboveD {n : ℕ} (p : Fin (n + 1)) (i : Fin n) : (p.succAbove i).val = sAb p.val i.val := by
  unfold Fin.succAbove sAb
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (Fin.lt_def.mp h1) (by simpa using h2)
  · exact absurd (Fin.lt_def.mpr (by simpa using h2)) h1
  · rfl

theorem moment_entry (L : DegD) (d : ℕ) (p : MomentPivots d) (hF : LinkFacts L d p) (a : ℝ) (k : Fin d)
    (u : Fin (d - k.val + 1)) (i : Fin (d - k.val)) :
    momentKernelMatrix a d p k u i = KnL L a k.val u.val i.val := by
  rw [gram_map_family_and_map.2.2]
  unfold KnL
  rw [if_pos (show k.val < L.dH by rw [hF.dH]; exact k.isLt), hF.piv k, ← val_succAboveD]
  simp only [Fin.ext_iff]

/-- **Generic retained Gram coordinates** (ℕ form): the class coefficients times the contraction `K W Kᵀ`. -/
theorem retained_gramL (L : DegD) (d : ℕ) (hl : 6 ≤ d) (hu : d ≤ 9) (p : MomentPivots d)
    (hp : ValidMomentPivots p) (hF : LinkFacts L d p)
    (momQ : (k : Fin d) → Matrix (Fin (d - k.val + 1)) (Fin (d - k.val + 1)) Poly3)
    (hsub : ∀ k u v, invariantSubst (momQ k u v) = kernelRPoly k.val u.val v.val)
    (hcoef : ∀ (k : Fin d) (u v : Fin (d - k.val + 1)) (r : ℕ),
      MvPolynomial.coeff (tagExponent (L.rtag r)) (momQ k u v) = L.Cc k.val r u.val v.val)
    (a : ℝ) (ha : physical a) (hK : ScalarColumnsL L d a)
    (W : GramFamily d) (Wn : ℕ → ℕ → ℕ → ℝ) (hW : ∀ b i j, W.val b i j = Wn (bIdx d b) i.val j.val)
    (t : RetainedIndex (2 * d)) (r : ℕ) (ht : t.val = L.rtag r) :
    retainCompatible a (2 * d) ⟨gramPoly a d p W, gramPoly_compatible a ha d hl hu p hp W⟩ t =
      ∑ bi ∈ Finset.range (d + 8), ∑ u ∈ Finset.range (L.rdim bi), ∑ v ∈ Finset.range (L.rdim bi),
        L.Cc bi r u v * ∑ i ∈ Finset.range (L.gdim bi), ∑ j ∈ Finset.range (L.gdim bi),
          KnL L a bi u i * KnL L a bi v j * Wn bi i j := by
  rw [retained_gram_blocks L d hl hu p hp a ha momQ hsub hK W t, ht]
  rw [← sum_blocks d (fun bi => ∑ u ∈ Finset.range (L.rdim bi), ∑ v ∈ Finset.range (L.rdim bi),
    L.Cc bi r u v * ∑ i ∈ Finset.range (L.gdim bi), ∑ j ∈ Finset.range (L.gdim bi),
      KnL L a bi u i * KnL L a bi v j * Wn bi i j)]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  cases b with
  | inl k =>
    exact block_identity (L.rdim k.val) (L.gdim k.val) (hF.rdim_mom k).symm (hF.gdim_mom k).symm _ _ _ _ _ _
      (fun u v => hcoef k u v r) (fun u i => moment_entry L d p hF a k u i) (fun i j => hW (.inl k) i j)
  | inr sb =>
    refine block_identity (L.rdim (d + sIdx sb)) (L.gdim (d + sIdx sb)) rfl (hF.gdim_sc sb).symm _ _ _ _ _ _
      (fun u v => scalar_coeff L d p hF sb u v r) (fun u i => ?_) (fun i j => hW (.inr sb) i j)
    show (L.rfRec (L.colRec (sIdx sb) i.val u.val)).value a = KnL L a (d + sIdx sb) u.val i.val
    unfold KnL
    rw [if_neg (by rw [hF.dH]; omega), show d + sIdx sb - L.dH = sIdx sb by rw [hF.dH]; omega]

/-! ## The literal W0 entries and the pieces -/

theorem isSymm_of_posDefD {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ} (h : M.PosDef) : M.IsSymm := by
  have hH := h.isHermitian
  unfold Matrix.IsHermitian at hH
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hH
  exact hH

/-- The literal Gram entries are symmetric on the cell. -/
theorem litW_symm (data : CellData) (bi i j : ℕ) (t : ℝ) (ht : t ∈ cellDomain) :
    litW data bi i j t = litW data bi j i t := by
  unfold litW
  by_cases h : i < data.order bi ∧ j < data.order bi
  · rw [dif_pos h, dif_pos ⟨h.2, h.1⟩]
    have hs := isSymm_of_posDefD (literalGram_floor data.cell (data.block bi) t ht).2
    have := congrFun (congrFun hs ⟨j, h.2⟩) ⟨i, h.1⟩
    rw [Matrix.transpose_apply] at this
    exact this
  · rw [dif_neg h, dif_neg (fun h' => h ⟨h'.2, h'.1⟩)]

/-- The real `P` table of block `bi` of a cell (the function enclosed by the `P` lookups of the leaves). -/
def PfL (L : DegD) (a : ℝ → ℝ) (data : CellData) (bi u v : ℕ) (t : ℝ) : ℝ :=
  pLF (litW data bi) (L.blockRowF a bi) (L.rdim bi) u v t

/-- The real function of piece `(b, g, h)` at coordinate `r` (`CoeffMap.Deg.ProgSound.pieceF` of `PfL`). -/
def pieceFL (L : DegD) (sd : SumD) (a : ℝ → ℝ) (data : CellData) (b g h r : ℕ) (t : ℝ) : ℝ :=
  L.pieceF sd (fun u v => PfL L a data b u v t) b g (sd.plo b h) (sd.plo b (h + 1)) ((L.eTab (32 * b + g)).getD r [])

/-- **The W0 link in piece form**: for a Gram family whose entries are the literal Gram entries at `x`, the retained
coordinate `r` is the sum of the real piece functions at `x`. -/
theorem pieces_link (L : DegD) (d : ℕ) (hl : 6 ≤ d) (hu : d ≤ 9) (p : MomentPivots d)
    (hp : ValidMomentPivots p) (hF : LinkFacts L d p)
    (momQ : (k : Fin d) → Matrix (Fin (d - k.val + 1)) (Fin (d - k.val + 1)) Poly3)
    (hsub : ∀ k u v, invariantSubst (momQ k u v) = kernelRPoly k.val u.val v.val)
    (hcoef : ∀ (k : Fin d) (u v : Fin (d - k.val + 1)) (r : ℕ),
      MvPolynomial.coeff (tagExponent (L.rtag r)) (momQ k u v) = L.Cc k.val r u.val v.val)
    (hc : ∀ b, b < d + 8 → L.BlockChecks b) (sd : SumD) (hpo : L.partsOk sd = true)
    (data : CellData) (a : ℝ → ℝ) (x : ℝ) (hx : x ∈ cellDomain) (ha : physical (a x))
    (hK : ScalarColumnsL L d (a x))
    (W : GramFamily d) (hW : ∀ b i j, W.val b i j = litW data (bIdx d b) i.val j.val x)
    (t : RetainedIndex (2 * d)) (r : ℕ) (hr : r < L.nc) (ht : t.val = L.rtag r) :
    retainCompatible (a x) (2 * d) ⟨gramPoly (a x) d p W, gramPoly_compatible (a x) ha d hl hu p hp W⟩ t =
      ∑ b ∈ Finset.range (d + 8), ∑ g ∈ Finset.range (L.nGrp b), ∑ h ∈ Finset.range (sd.np b),
        pieceFL L sd a data b g h r x := by
  rw [retained_gramL L d hl hu p hp hF momQ hsub hcoef (a x) ha hK W (fun bi i j => litW data bi i j x) hW t r ht]
  refine Finset.sum_congr rfl (fun b hb => ?_)
  have hb' : b < Nat.add L.dH 8 := by rw [hF.dH]; exact Finset.mem_range.mp hb
  have hmom : b < L.dH → L.piv b ≤ L.gdim b ∧ L.rdim b = L.gdim b + 1 := by
    intro hbd
    rw [hF.dH] at hbd
    have := hF.piv ⟨b, hbd⟩
    have hp' := (p ⟨b, hbd⟩).isLt
    exact ⟨by rw [this, hF.gdim_mom ⟨b, hbd⟩]; simp only at hp' ⊢; omega,
      by rw [hF.rdim_mom ⟨b, hbd⟩, hF.gdim_mom ⟨b, hbd⟩]⟩
  have hP : ∀ u v, u < L.rdim b → v < L.rdim b → PfL L a data b u v x =
      ∑ i ∈ Finset.range (L.gdim b), ∑ j ∈ Finset.range (L.gdim b),
        KnL L (a x) b u i * KnL L (a x) b v j * litW data b i j x :=
    fun u v hu hv => pLF_eq L a (litW data b) x b u v hu hv hF.rec1 hmom
  have hsym : ∀ u v, u < L.rdim b → v < L.rdim b → PfL L a data b u v x = PfL L a data b v u x := by
    intro u v hu hv
    rw [hP u v hu hv, hP v u hv hu, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [litW_symm data b i j x hx]
    ring
  have hrep := L.rep_sum sd b r hb' (hc b (Finset.mem_range.mp hb)) hpo hr (fun u v => PfL L a data b u v x) hsym
  unfold pieceFL
  rw [hrep]
  refine Finset.sum_congr rfl (fun u hu => Finset.sum_congr rfl (fun v hv => ?_))
  rw [hP u v (Finset.mem_range.mp hu) (Finset.mem_range.mp hv)]

#print axioms retained_gramL
#print axioms pieces_link

end ThomsonCompact.CoeffMap.Deg.Link
