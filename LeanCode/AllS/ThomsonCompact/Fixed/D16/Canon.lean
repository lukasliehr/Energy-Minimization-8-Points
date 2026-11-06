import ThomsonCompact.Fixed.D16.Poly
import ThomsonCompact.Fixed.SoundC
import ThomsonCompact.Fixed.D16.ColsM0Plus
import ThomsonCompact.Fixed.D16.ColsM0Standard
import ThomsonCompact.CoeffMap.MomentSound
import AllS.Units.N_FI.N_raw_projection.RawMomentTensors.D16_F0
import AllS.Units.N_FI.N_raw_projection.RawMomentTensors.D16_F1
import AllS.Units.N_FI.N_raw_projection.RawContractionSupport
import AllS.Units.N_AI.N_residual_replay.ScalarKernelPolynomialSupport
import AllS.Units.N_AI.N_residual_replay.RawSparseLookupSupport
import AllS.Units.N_AI.N_fixed_tables.FactorCatalogue
import AllS.Units.N_AI.N_fixed_tables.LayoutSupport
import AllS.Units.N_AI.N_fixed_tables.GramInsertionSupport

/-!
# D16 canonical columns (workstream F4)

For every table column `k` (output `(b, r, c)` with multiplicity `mult`) the source polynomial
`P a p k = C mult · srcN a p b r c` (moment blocks: `momentCoordinateKernel` with the proven
`RawMomentTensors.D16_F0/F1`; scalar blocks: `scalarCoordinateKernel` with the RF column matrices `Kpk` and the raw
products `rawScalarProductSpec`) and

* `P_subst`: `invariantSubst (P a p k) = gramPoly a 8 p (fixedGramUnit b r c)` on the physical domain;
* `P_coeff`: its coefficient at the retained tag `t_i` is `N_ik(a) / (Δc_k δ_b(a)²)` (`nC` of `SoundT`);
* `Q_ne`, `out_ne`: `Q(a)`, `δ_b(a)`, `dz_k(a)`, `λ_k`, `Δc_k` do not vanish for physical `a`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 200000

noncomputable section
open scoped BigOperators

namespace ThomsonCompact.Fixed.D16

open Blueprint.CAP Blueprint.Thomson.Finite ThomsonCompact.Fixed ThomsonCompact.Packed ThomsonCompact.CoeffMap

/-! ## Nonvanishing on the physical domain -/

theorem evalZ_prodF (S : STab) (t : ℝ) :
    ∀ m, evalZ (prodF S m) t = ∏ r ∈ Finset.range m, evalZ (recCoeffs (S.fac r)) t ^ (S.fexp r)
  | 0 => by simp [prodF, evalZ]
  | m + 1 => by rw [prodF, evalZ_convL, evalZ_powL, evalZ_prodF S t m, Finset.prod_range_succ]

theorem evalZ_rat : ∀ (l : List ℤ) (a : ℝ), evalZ l a = evalRationalList (l.map (Int.cast : ℤ → ℚ)) a
  | [], a => by simp [evalZ, evalRationalList]
  | c :: l, a => by
    have ih := evalZ_rat l a
    simp only [evalZ, List.map_cons, horner_cons] at ih ⊢
    rw [ih]; simp [evalRationalList]

theorem fac0 : (recCoeffs (stab.fac 0)).map (Int.cast : ℤ → ℚ) = FixedTableDenominators.factor00 := by decide +kernel
theorem fac1 : (recCoeffs (stab.fac 1)).map (Int.cast : ℤ → ℚ) = FixedTableDenominators.factor02 := by decide +kernel
theorem fac2 : (recCoeffs (stab.fac 2)).map (Int.cast : ℤ → ℚ) = FixedTableDenominators.factor03 := by decide +kernel
theorem fac3 : (recCoeffs (stab.fac 3)).map (Int.cast : ℤ → ℚ) = FixedTableDenominators.factor04 := by decide +kernel
theorem fac4 : (recCoeffs (stab.fac 4)).map (Int.cast : ℤ → ℚ) = FixedTableDenominators.factor06 := by decide +kernel
theorem fac5 : (recCoeffs (stab.fac 5)).map (Int.cast : ℤ → ℚ) = FixedTableDenominators.factor05 := by decide +kernel
theorem fac6 : (recCoeffs (stab.fac 6)).map (Int.cast : ℤ → ℚ) = FixedTableDenominators.factor07 := by decide +kernel
theorem fac7 : (recCoeffs (stab.fac 7)).map (Int.cast : ℤ → ℚ) = FixedTableDenominators.factor08 := by decide +kernel
theorem fac8 : (recCoeffs (stab.fac 8)).map (Int.cast : ℤ → ℚ) = FixedTableDenominators.factor09 := by decide +kernel

theorem fac_ne (a : ℝ) (ha : physical a) (r : ℕ) (hr : r < 9) : evalZ (recCoeffs (stab.fac r)) a ≠ 0 := by
  rw [evalZ_rat]
  interval_cases r
  · rw [fac0]; exact FixedTableDenominators.factor00_nonzero a ha
  · rw [fac1]; exact FixedTableDenominators.factor02_nonzero a ha
  · rw [fac2]; exact FixedTableDenominators.factor03_nonzero a ha
  · rw [fac3]; exact FixedTableDenominators.factor04_nonzero a ha
  · rw [fac4]; exact FixedTableDenominators.factor06_nonzero a ha
  · rw [fac5]; exact FixedTableDenominators.factor05_nonzero a ha
  · rw [fac6]; exact FixedTableDenominators.factor07_nonzero a ha
  · rw [fac7]; exact FixedTableDenominators.factor08_nonzero a ha
  · rw [fac8]; exact FixedTableDenominators.factor09_nonzero a ha

/-- `Q(a) ≠ 0` on the physical domain. -/
theorem Q_ne (a : ℝ) (ha : physical a) : evalZ (qC gtab) a ≠ 0 := by
  rw [qfac, evalZ_prodF]
  have hn : stab.nfac = 9 := rfl
  have hs : stab.fsgn = false := rfl
  simp only [hs, hn, Bool.false_eq_true, if_false, one_mul]
  exact Finset.prod_ne_zero_iff.mpr fun r hr => pow_ne_zero _ (fac_ne a ha r (Finset.mem_range.mp hr))

theorem s_pos : 0 < gtab.s := by decide

/-- The denominators of the inverse and of the canonical columns do not vanish. -/
theorem out_ne (a : ℝ) (ha : physical a) (k : ℕ) (hk : k < 202) :
    evalZ (blC gtab k) a ≠ 0 ∧ evalZ (dzC gtab k) a ≠ 0 ∧ (lamG gtab k : ℝ) ≠ 0 ∧ (dcG gtab k : ℝ) ≠ 0 := by
  obtain ⟨hdq, hid⟩ := gid k hk
  have hr : ((gtab.s * dqG gtab k : ℕ) : ℝ) * evalZ (qC gtab) a ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp s_pos) (by omega)) (Q_ne a ha)
  rw [← hid a] at hr
  push_cast at hr
  refine ⟨fun h0 => hr (by rw [h0]; ring), fun h0 => hr (by rw [h0]; ring), fun h0 => hr (by rw [h0]; ring),
    fun h0 => hr (by rw [h0]; ring)⟩

theorem gblk_check : (List.range 202).all (fun k => fld (gtab.inf k) 336 16 == oBlk ltab k) = true := by
  decide +kernel

theorem blC_eq (k : ℕ) (hk : k < 202) : blC gtab k = blkC gtab (oBlk ltab k) := by
  have := List.all_eq_true.mp gblk_check k (List.mem_range.mpr hk)
  unfold blC blkC
  rw [beq_iff_eq.mp this]

/-- One output of each block (`F0`, `F1`, `M0_plus`, `M0_standard`). -/
theorem rep_check : oBlk ltab 0 = 0 ∧ oBlk ltab 11 = 1 ∧ oBlk ltab 15 = 2 ∧ oBlk ltab 194 = 3 := by decide +kernel

theorem delta_ne (a : ℝ) (ha : physical a) (b : ℕ) (hb : b < 4) : evalZ (blkC gtab b) a ≠ 0 := by
  obtain ⟨h0, h1, h2, h3⟩ := rep_check
  interval_cases b
  · have := (out_ne a ha 0 (by norm_num)).1; rwa [blC_eq 0 (by norm_num), h0] at this
  · have := (out_ne a ha 11 (by norm_num)).1; rwa [blC_eq 11 (by norm_num), h1] at this
  · have := (out_ne a ha 15 (by norm_num)).1; rwa [blC_eq 15 (by norm_num), h2] at this
  · have := (out_ne a ha 194 (by norm_num)).1; rwa [blC_eq 194 (by norm_num), h3] at this

/-! ## Retained coordinates -/

/-- Retained tag of row `i` (decoded from the packed codes). -/
def coordinateTags (i : Fin 202) : Tag := decodeTag (ltab.rtag i.val)

theorem coordinateTags_source : List.ofFn coordinateTags = retainedTagList 16 :=
  (fixedRetainedList_literal 16 _ (by decide +kernel) (by decide +kernel) (by decide +kernel)).symm

theorem retainedTagList_length : (retainedTagList 16).length = 202 := by
  rw [← coordinateTags_source, List.length_ofFn]

/-- The table's retained coordinate order. -/
def retainedIndex (i : Fin 202) : RetainedIndex 16 :=
  retainedTagEnum 16 ⟨i.val, by rw [retainedTagList_length]; exact i.isLt⟩

theorem retainedIndex_tag (i : Fin 202) : (retainedIndex i).val = coordinateTags i := by
  simp only [retainedIndex, retainedTagEnum_apply]
  simp only [← coordinateTags_source, List.get_eq_getElem, List.getElem_ofFn]

theorem retainedIndex_bijective : Function.Bijective retainedIndex := by
  constructor
  · intro i j hij
    have h := (retainedTagEnum 16).injective hij
    exact Fin.ext (congrArg (fun x : Fin (retainedTagList 16).length => x.val) h)
  · intro t
    obtain ⟨i, hi⟩ := (retainedTagEnum 16).surjective t
    refine ⟨⟨i.val, by rw [← retainedTagList_length]; exact i.isLt⟩, ?_⟩
    exact hi

/-! ## Tags and codes -/

theorem decodeTag_eq (c : ℕ) : decodeTag c = (c % 32, c / 32 % 32, c / 1024) := by
  have e : ∀ x : ℕ, Nat.land x 31 = x % 32 := fun x => Nat.and_two_pow_sub_one_eq_mod x 5
  unfold decodeTag
  rw [e, e, nat_shiftRight, nat_shiftRight]
  norm_num

theorem decodeTag_injective : Function.Injective decodeTag := by
  intro c c' h
  rw [decodeTag_eq, decodeTag_eq] at h
  simp only [Prod.mk.injEq] at h
  omega

theorem decodeTag_add (c c' : ℕ) (h1 : c % 32 + c' % 32 < 32) (h2 : c / 32 % 32 + c' / 32 % 32 < 32) :
    decodeTag (c + c') = rawTagAdd (decodeTag c) (decodeTag c') := by
  simp only [decodeTag_eq, rawTagAdd, Prod.mk.injEq]
  omega

/-- `rawIntegerLookup` of the decoded raw terms is `zsum`. -/
noncomputable def zlistB (b u v : ℕ) : List (Tag × ℤ) :=
  (zterms ltab.rt ltab.zt b u v).map fun x => (decodeTag x.1, sv x.2)

theorem lookup_zlist (b u v c : ℕ) : rawIntegerLookup (zlistB b u v) (decodeTag c) = zsum ltab b u v c := by
  unfold rawIntegerLookup zlistB zsum
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro x _
  simp only [Function.comp, decodeTag_injective.eq_iff]

/-! ## Outputs -/

/-- Block dimensions by block index. -/
def bdim : ℕ → ℕ
  | 0 => 8
  | 1 => 7
  | 2 => 36
  | _ => 47

/-- Block of a block index (0 = F0, 1 = F1, 2 = M0_plus, 3 = M0_standard). -/
def blockOf (b : ℕ) : GramBlock 8 :=
  if b = 0 then .inl 0 else if b = 1 then .inl 1 else if b = 2 then .inr .m0Plus else .inr .m0Standard

theorem gbd (b : ℕ) (hb : b < 4) : gramBlockDimension 8 (blockOf b) = bdim b := by
  interval_cases b
  · rfl
  · rfl
  · exact dims_m0Plus
  · exact dims_m0Standard

theorem outs_check : (List.range 202).all (fun k => decide (oBlk ltab k < 4 ∧ oRow ltab k < bdim (oBlk ltab k) ∧
    oCol ltab k < bdim (oBlk ltab k) ∧ oMult ltab k = (if oRow ltab k = oCol ltab k then 1 else 2))) = true := by
  decide +kernel

theorem outs (k : ℕ) (hk : k < 202) : oBlk ltab k < 4 ∧ oRow ltab k < bdim (oBlk ltab k) ∧
    oCol ltab k < bdim (oBlk ltab k) ∧ oMult ltab k = (if oRow ltab k = oCol ltab k then 1 else 2) :=
  of_decide_eq_true (List.all_eq_true.mp outs_check k (List.mem_range.mpr hk))

/-! ## Raw column matrices -/

/-- Moment raw tensors. -/
def momQ0 : Matrix (Fin 9) (Fin 9) Poly3 := RawMomentTensors.D16_F0.coordinatePolynomial
def momQ1 : Matrix (Fin 8) (Fin 8) Poly3 := RawMomentTensors.D16_F1.coordinatePolynomial

def zcheck0 : Bool := (List.finRange 9).all fun u => (List.finRange 9).all fun v =>
  zlistB 0 u.val v.val == RawMomentTensors.D16_F0.source u v
def zcheck1 : Bool := (List.finRange 8).all fun u => (List.finRange 8).all fun v =>
  zlistB 1 u.val v.val == RawMomentTensors.D16_F1.source u v
theorem zcheck0_ok : zcheck0 = true := by decide +kernel
theorem zcheck1_ok : zcheck1 = true := by decide +kernel

theorem zlist_F0 (u v : Fin 9) : zlistB 0 u.val v.val = RawMomentTensors.D16_F0.source u v := by
  have h := List.all_eq_true.mp zcheck0_ok u (List.mem_finRange u)
  exact beq_iff_eq.mp (List.all_eq_true.mp h v (List.mem_finRange v))

theorem zlist_F1 (u v : Fin 8) : zlistB 1 u.val v.val = RawMomentTensors.D16_F1.source u v := by
  have h := List.all_eq_true.mp zcheck1_ok u (List.mem_finRange u)
  exact beq_iff_eq.mp (List.all_eq_true.mp h v (List.mem_finRange v))

theorem momQ0_coeff (t : Tag) (u v : Fin 9) : MvPolynomial.coeff (tagExponent t) (momQ0 u v) =
    (rawIntegerLookup (zlistB 0 u.val v.val) t : ℝ) / (RawMomentTensors.D16_F0.denominator : ℝ) := by
  rw [zlist_F0]; exact integerSparsePolynomial_coeff _ _ t

theorem momQ1_coeff (t : Tag) (u v : Fin 8) : MvPolynomial.coeff (tagExponent t) (momQ1 u v) =
    (rawIntegerLookup (zlistB 1 u.val v.val) t : ℝ) / (RawMomentTensors.D16_F1.denominator : ℝ) := by
  rw [zlist_F1]; exact integerSparsePolynomial_coeff _ _ t

/-- Scalar raw sizes and indices. -/
def rawSize : ScalarBlockName → ℕ
  | .m0Plus => 41
  | _ => 54

def scalarIdx : ScalarBlockName → ℕ
  | .m0Plus => 2
  | _ => 3

def rdenS : ScalarBlockName → ℕ
  | .m0Plus => 1
  | _ => 81

def rawTags (b : ScalarBlockName) (u : Fin (rawSize b)) : StandardTag := rawTag (scalarIdx b) u.val

/-- The scalar column matrices from the RF records. -/
def Kpk (a : ℝ) (b : ScalarBlockName) : Matrix (Fin (rawSize b)) (Fin (scalarBlockDimension b 8)) ℝ :=
  fun u i => (rfrec (stab.col (scalarIdx b) i.val u.val)).value a

/-- Scalar raw products as sparse integer polynomials of the kernel's raw terms. -/
def rawQ (b : ScalarBlockName) (u v : Fin (rawSize b)) : Poly3 :=
  RawCatalogue.ratToReal (RawCatalogue.sparsePolynomial
    (normalizeIntegerRawEntry (rdenS b) (zlistB (scalarIdx b) u.val v.val)))

theorem rawQ_coeff (t : Tag) (b : ScalarBlockName) (u v : Fin (rawSize b)) :
    MvPolynomial.coeff (tagExponent t) (rawQ b u v) =
      (rawIntegerLookup (zlistB (scalarIdx b) u.val v.val) t : ℝ) / (rdenS b : ℝ) :=
  integerSparsePolynomial_coeff _ _ t

/-! ## Scalar columns: `K = κ / (S δ)` -/

theorem rdi_check : (List.range nRec).all (fun k => decide (stab.rdi k < stab.nden)) = true := by decide +kernel
theorem rblk_check : (List.range stab.nden).all (fun d => decide (stab.rblk d < 4)) = true := by decide +kernel

theorem den_ne (a : ℝ) (ha : physical a) (d : ℕ) (hd : d < stab.nden) : evalZ (recCoeffs (stab.rden d)) a ≠ 0 := by
  obtain ⟨-, hρ, -, hid⟩ := dens d hd
  have hb : stab.rblk d < 4 := of_decide_eq_true (List.all_eq_true.mp rblk_check d (List.mem_range.mpr hd))
  intro h0
  have := hid a
  rw [h0, zero_mul] at this
  exact mul_ne_zero (by exact_mod_cast hρ) (delta_ne a ha _ hb) this.symm

/-- The old RFs are defined on the physical domain. -/
theorem hdef_of (a : ℝ) (ha : physical a) : ∀ k, k < nRec → (rfrec k).toRatFun.DefinedAt a := by
  intro k hk
  have hd : stab.rdi k < stab.nden := of_decide_eq_true (List.all_eq_true.mp rdi_check k (List.mem_range.mpr hk))
  rw [RFRec.definedAt_iff]
  have h1 := (dens _ hd).1
  have h2 : (stab.rdsc (stab.rdi k) : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp h1)
  exact div_ne_zero (den_ne a ha _ hd) h2

theorem Kpk_eq (a : ℝ) (ha : physical a) (b : ScalarBlockName) (hb : b = .m0Plus ∨ b = .m0Standard)
    (u : Fin (rawSize b)) (i : Fin (scalarBlockDimension b 8)) :
    Kpk a b u i = evalZ (kapE ltab (scalarIdx b) i.val u.val) a /
      ((stab.sc (scalarIdx b) i.val : ℝ) * evalZ (blkC gtab (scalarIdx b)) a) := by
  have hbi : scalarIdx b = 2 ∨ scalarIdx b = 3 := by rcases hb with rfl | rfl <;> simp [scalarIdx]
  have hj : i.val < stab.ncol (scalarIdx b) := by
    rcases hb with rfl | rfl
    · exact lt_of_lt_of_eq i.isLt dims_m0Plus
    · exact lt_of_lt_of_eq i.isLt dims_m0Standard
  have hu : u.val < stab.nraw (scalarIdx b) := by rcases hb with rfl | rfl <;> exact u.isLt
  obtain ⟨h1, h2, h3, hid⟩ := rf (scalarIdx b) hbi i.val u.val hj hu
  have hden := den_ne a ha _ h3
  have hδ := delta_ne a ha (scalarIdx b) (by rcases hbi with h | h <;> omega)
  have hsN : (stab.rsc (stab.col (scalarIdx b) i.val u.val) : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp h1)
  have hS : (stab.sc (scalarIdx b) i.val : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp h2)
  have hsD : (stab.rdsc (stab.rdi (stab.col (scalarIdx b) i.val u.val)) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.pos_iff_ne_zero.mp (dens _ h3).1)
  have e := hid a
  push_cast at e
  show (evalZ (recCoeffs (stab.rnum (stab.col (scalarIdx b) i.val u.val))) a /
      (stab.rsc (stab.col (scalarIdx b) i.val u.val) : ℝ)) /
      (evalZ (recCoeffs (stab.rden (stab.rdi (stab.col (scalarIdx b) i.val u.val)))) a /
        (stab.rdsc (stab.rdi (stab.col (scalarIdx b) i.val u.val)) : ℝ)) = _
  rw [div_div_div_eq, div_eq_div_iff (mul_ne_zero hsN hden) (mul_ne_zero hS hδ)]
  linear_combination e

/-! ## Moment columns: `K = κ / (S δ)` -/

def saOf (k i : ℕ) : ℕ := if i < k then i else i + 1
def kapQ (b j u : ℕ) : List ℚ := (kapE ltab b j u).map (Int.cast : ℤ → ℚ)
def blkQ (b : ℕ) : List ℚ := (blkC gtab b).map (Int.cast : ℤ → ℚ)
def qeqv (p q : List ℚ) : Bool := qAllZero (qadd p (qscale (-1) q))
def pivC (k : ℕ) : ℚ := (mP k k).r.getLastD 0 / (blkQ k).getLastD 1

def momEntOk (k i r : ℕ) : Bool :=
  if r = saOf k i then kapE ltab k i r == scaleL (stab.sc k i : ℤ) (blkC gtab k)
  else if r = k then
    qeqv (qmul (kapQ k i r) (mP k k).r) (qscale (-(stab.sc k i : ℚ)) (qmul (blkQ k) (mP k (saOf k i)).r))
  else kapE ltab k i r == []

def momOk : Bool :=
  (List.range 2).all fun k => ((List.range (9 - k)).all fun j => qAllZero (mP k j).s) &&
    qeqv (mP k k).r (qscale (pivC k) (blkQ k)) && pivC k != 0 &&
    (List.range (8 - k)).all fun i => decide (1 ≤ stab.sc k i) && (List.range (9 - k)).all fun r => momEntOk k i r

theorem mom_ok : momOk = true := by decide +kernel

theorem mom_parts (k : ℕ) (hk : k < 2) : ((List.range (9 - k)).all fun j => qAllZero (mP k j).s) = true ∧
    qeqv (mP k k).r (qscale (pivC k) (blkQ k)) = true ∧ pivC k ≠ 0 ∧
    ∀ i, i < 8 - k → 1 ≤ stab.sc k i ∧ ∀ r, r < 9 - k → momEntOk k i r = true := by
  have h := List.all_eq_true.mp mom_ok k (List.mem_range.mpr hk)
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact ⟨by simpa using h.1.1.1, h.1.1.2, h.1.2, fun i hi => ⟨(h.2 i hi).1, (h.2 i hi).2⟩⟩

theorem evq_cast : ∀ (l : List ℤ) (a : ℝ), evq (l.map (Int.cast : ℤ → ℚ)) a = evalZ l a
  | [], a => by simp [evq, evalZ]
  | c :: l, a => by
    have ih := evq_cast l a
    simp only [evalZ, List.map_cons, horner_cons, evq] at ih ⊢
    rw [ih]; push_cast; ring

theorem evq_qeqv (p q : List ℚ) (h : qeqv p q = true) (a : ℝ) : evq p a = evq q a := by
  have := evq_allZero _ a h
  rw [evq_qadd, evq_qscale] at this
  push_cast at this
  linarith

theorem momentP_r (k j : ℕ) (hk : k < 2) (hj : j < 9 - k) (a : ℝ) : momentP k j a = evq (mP k j).r a := by
  have h := (mom_parts k hk).1
  rw [List.all_eq_true] at h
  rw [momentP_eq, ev2, evq_allZero _ a (h j (List.mem_range.mpr hj)), mul_zero, add_zero]

theorem succAbove_val {n : ℕ} (q : Fin (n + 1)) (i : Fin n) : (q.succAbove i).val = saOf q.val i.val := by
  unfold Fin.succAbove saOf
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (Fin.lt_def.mp h1) (by simpa using h2)
  · exact absurd (Fin.lt_def.mpr (by simpa using h2)) h1
  · rfl

theorem Kmom (a : ℝ) (ha : physical a) (p : MomentPivots 8) (hp0 : (p 0).val = 0) (hp1 : (p 1).val = 1)
    (k : Fin 8) (hk : k.val < 2) (r : Fin (8 - k.val + 1)) (i : Fin (8 - k.val)) :
    momentKernelMatrix a 8 p k r i =
      evalZ (kapE ltab k.val i.val r.val) a / ((stab.sc k.val i.val : ℝ) * evalZ (blkC gtab k.val) a) := by
  have hpk : (p k).val = k.val := by
    have : k = 0 ∨ k = 1 := by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
      · left; exact Fin.ext (by simpa using h)
      · right; exact Fin.ext (by simpa using h)
    rcases this with rfl | rfl
    · exact hp0
    · exact hp1
  obtain ⟨m1, m2, m3, m4⟩ := mom_parts k.val hk
  have hi : i.val < 8 - k.val := i.isLt
  have hr : r.val < 9 - k.val := by have := r.isLt; omega
  obtain ⟨hS1, hent⟩ := m4 i.val hi
  have he := hent r.val hr
  have hδ := delta_ne a ha k.val (by omega)
  have hS : (stab.sc k.val i.val : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hS1)
  have hsa : ((p k).succAbove i).val = saOf k.val i.val := by rw [succAbove_val, hpk]
  have hsa_lt : saOf k.val i.val < 9 - k.val := by unfold saOf; split_ifs <;> omega
  have hpiv : momentP k.val (p k).val a ≠ 0 := by
    rw [hpk, momentP_r k.val k.val hk (by omega) a, evq_qeqv _ _ m2 a, evq_qscale]
    exact mul_ne_zero (by exact_mod_cast m3) (by rw [blkQ, evq_cast]; exact hδ)
  rw [(gram_map_family_and_map).2.2 a 8 p k r i]
  unfold momEntOk at he
  by_cases h1 : r.val = saOf k.val i.val
  · have hr1 : r = (p k).succAbove i := Fin.ext (by rw [h1, hsa])
    have hr2 : r ≠ p k := by
      intro h; have := congrArg Fin.val h; rw [hpk] at this; unfold saOf at h1; split_ifs at h1 <;> omega
    rw [if_pos hr1, if_neg hr2, mul_zero, sub_zero]
    rw [if_pos h1] at he
    rw [beq_iff_eq.mp he, evalZ_scaleL]
    push_cast
    field_simp
  · rw [if_neg h1] at he
    have hr1 : r ≠ (p k).succAbove i := fun h => h1 (by rw [h, hsa])
    rw [if_neg hr1, zero_sub]
    by_cases h2 : r.val = k.val
    · have hr2 : r = p k := Fin.ext (by rw [h2, hpk])
      rw [if_pos h2] at he
      have hpiv' : evq (mP k.val k.val).r a ≠ 0 := by
        rwa [hpk, momentP_r k.val k.val hk (by omega) a] at hpiv
      rw [if_pos hr2, mul_one, hsa, hpk, momentP_r k.val _ hk hsa_lt a, momentP_r k.val k.val hk (by omega) a]
      have e := evq_qeqv _ _ he a
      rw [evq_qmul, evq_qscale, evq_qmul, kapQ, blkQ, evq_cast, evq_cast] at e
      push_cast at e
      field_simp
      linear_combination -e
    · have hr2 : r ≠ p k := fun h => h2 (by rw [h, hpk])
      rw [if_neg h2] at he
      rw [if_neg hr2, mul_zero, neg_zero, beq_iff_eq.mp he]
      simp [evalZ]

/-! ## Scalar raw products -/

theorem rt_check : ((List.range 41).all fun u => decide (ltab.rt 2 u < 65536 ∧ ltab.rt 2 u % 32 < 14 ∧
      ltab.rt 2 u / 32 % 32 < 14)) = true ∧
    ((List.range 54).all fun u => decide (ltab.rt 3 u < 65536 ∧ ltab.rt 3 u % 32 < 14 ∧
      ltab.rt 3 u / 32 % 32 < 14)) = true := by decide +kernel

theorem rt_bounds (b : ScalarBlockName) (hb : b = .m0Plus ∨ b = .m0Standard) (u : Fin (rawSize b)) :
    ltab.rt (scalarIdx b) u.val < 65536 ∧ ltab.rt (scalarIdx b) u.val % 32 < 14 ∧
      ltab.rt (scalarIdx b) u.val / 32 % 32 < 14 := by
  rcases hb with rfl | rfl
  · exact of_decide_eq_true (List.all_eq_true.mp rt_check.1 u.val (List.mem_range.mpr u.isLt))
  · exact of_decide_eq_true (List.all_eq_true.mp rt_check.2 u.val (List.mem_range.mpr u.isLt))

theorem coordinateMonomial_add (t u : Tag) :
    coordinateMonomial (rawTagAdd t u) = coordinateMonomial t * coordinateMonomial u := by
  simp only [coordinateMonomial, rawTagAdd, pow_add]; ring

theorem sparse_norm_cons (D : ℕ) (t : Tag) (z : ℤ) (l : List (Tag × ℤ)) :
    RawCatalogue.ratToReal (RawCatalogue.sparsePolynomial (normalizeIntegerRawEntry D ((t, z) :: l))) =
      MvPolynomial.C ((z : ℝ) / D) * coordinateMonomial t +
        RawCatalogue.ratToReal (RawCatalogue.sparsePolynomial (normalizeIntegerRawEntry D l)) := by
  simp [normalizeIntegerRawEntry, RawCatalogue.sparsePolynomial, RawCatalogue.ratToReal, coordinateMonomial,
    mul_assoc]

theorem sparse_norm_nil (D : ℕ) :
    RawCatalogue.ratToReal (RawCatalogue.sparsePolynomial (normalizeIntegerRawEntry D [])) = 0 := by
  simp [normalizeIntegerRawEntry, RawCatalogue.sparsePolynomial]

theorem decodeTag_add3 (c c' off : ℕ) (h1 : c % 32 < 14) (h2 : c / 32 % 32 < 14) (h3 : c' % 32 < 14)
    (h4 : c' / 32 % 32 < 14) (ho1 : off % 32 ≤ 4) (ho2 : off / 32 % 32 ≤ 2) :
    decodeTag (Nat.add (Nat.add (Nat.land c 32767) (Nat.land c' 32767)) off) =
      rawTagAdd (rawTagAdd (decodeTag (Nat.land c 32767)) (decodeTag (Nat.land c' 32767))) (decodeTag off) := by
  have e : ∀ x : ℕ, Nat.land x 32767 = x % 32768 := fun x => Nat.and_two_pow_sub_one_eq_mod x 15
  simp only [decodeTag_eq, rawTagAdd, nat_add, e, Prod.mk.injEq]
  omega

theorem rawTagAdd_zero (t : Tag) : rawTagAdd t (0, 0, 0) = t := by simp [rawTagAdd]

theorem flag_cases (c : ℕ) (hc : c < 65536) : Nat.shiftRight c 15 = 0 ∨ Nat.shiftRight c 15 = 1 := by
  rw [nat_shiftRight]; norm_num; omega

theorem rawQ_eq (b : ScalarBlockName) (hb : b = .m0Plus ∨ b = .m0Standard) (u v : Fin (rawSize b)) :
    rawQ b u v = rawScalarCoordinates (rawScalarProductSpec b (rawTags b u) (rawTags b v)) := by
  obtain ⟨u1, u2, u3⟩ := rt_bounds b hb u
  obtain ⟨v1, v2, v3⟩ := rt_bounds b hb v
  rcases hb with rfl | rfl
  · -- m0Plus: one term `t_u + t_v`
    simp only [scalarIdx] at u1 u2 u3 v1 v2 v3
    have hT0 := decodeTag_add3 (ltab.rt 2 u.val) (ltab.rt 2 v.val) 0 u2 u3 v2 v3 (by norm_num) (by norm_num)
    rw [show decodeTag 0 = (0, 0, 0) from rfl, rawTagAdd_zero] at hT0
    have hz : zlistB 2 u.val v.val =
        [(decodeTag (Nat.add (Nat.add (Nat.land (ltab.rt 2 u.val) 32767) (Nat.land (ltab.rt 2 v.val) 32767)) 0), 1)] := by
      unfold zlistB; rw [zterms_eq, if_neg (by norm_num), if_pos rfl]; rfl
    show RawCatalogue.ratToReal (RawCatalogue.sparsePolynomial (normalizeIntegerRawEntry 1 (zlistB 2 u.val v.val))) = _
    rw [hz, hT0, sparse_norm_cons, sparse_norm_nil]
    show _ = rawSymmetricWeight false * coordinateMonomial (rawTagAdd (rawTag 2 u.val).2 (rawTag 2 v.val).2)
    simp [rawSymmetricWeight, rawTag]
  · -- m0Standard: the standard pairing of the two flags, shifted by `t_u + t_v`
    simp only [scalarIdx] at u1 u2 u3 v1 v2 v3
    have hT := fun off h1 h2 => decodeTag_add3 (ltab.rt 3 u.val) (ltab.rt 3 v.val) off u2 u3 v2 v3 h1 h2
    have hland : ∀ x y : ℕ, (x = 0 ∨ x = 1) → (y = 0 ∨ y = 1) → Nat.land x y = (if x = 1 ∧ y = 1 then 1 else 0) := by
      intro x y hx hy; rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rfl
    have hlor : ∀ x y : ℕ, (x = 0 ∨ x = 1) → (y = 0 ∨ y = 1) → Nat.lor x y = (if x = 1 ∨ y = 1 then 1 else 0) := by
      intro x y hx hy; rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rfl
    have hu' := flag_cases _ u1
    have hv' := flag_cases _ v1
    have e4 := hT 4 (by norm_num) (by norm_num)
    have e34 := hT 34 (by norm_num) (by norm_num)
    have e64 := hT 64 (by norm_num) (by norm_num)
    have e3 := hT 3 (by norm_num) (by norm_num)
    have e33 := hT 33 (by norm_num) (by norm_num)
    have e1024 := hT 1024 (by norm_num) (by norm_num)
    have e2 := hT 2 (by norm_num) (by norm_num)
    have e32 := hT 32 (by norm_num) (by norm_num)
    rw [show decodeTag 4 = (4, 0, 0) from rfl] at e4
    rw [show decodeTag 34 = (2, 1, 0) from rfl] at e34
    rw [show decodeTag 64 = (0, 2, 0) from rfl] at e64
    rw [show decodeTag 3 = (3, 0, 0) from rfl] at e3
    rw [show decodeTag 33 = (1, 1, 0) from rfl] at e33
    rw [show decodeTag 1024 = (0, 0, 1) from rfl] at e1024
    rw [show decodeTag 2 = (2, 0, 0) from rfl] at e2
    rw [show decodeTag 32 = (0, 1, 0) from rfl] at e32
    show RawCatalogue.ratToReal (RawCatalogue.sparsePolynomial (normalizeIntegerRawEntry 81 (zlistB 3 u.val v.val))) =
      rawSymmetricWeight false * rawStandardCoordinates ((rawTag 3 u.val).1 && (rawTag 3 v.val).1)
        ((rawTag 3 u.val).1 || (rawTag 3 v.val).1) * coordinateMonomial (rawTagAdd (rawTag 3 u.val).2 (rawTag 3 v.val).2)
    unfold zlistB
    rw [zterms_eq, if_pos rfl, hland _ _ hu' hv', hlor _ _ hu' hv']
    have ht : ∀ w : ℕ, (rawTag 3 w).2 = decodeTag (Nat.land (ltab.rt 3 w) 32767) := fun w => rfl
    have hf : ∀ w : ℕ, (rawTag 3 w).1 = Nat.beq (Nat.shiftRight (ltab.rt 3 w) 15) 1 := fun w => rfl
    rw [ht, ht, hf, hf]
    rcases hu' with hu0 | hu0 <;> rcases hv' with hv0 | hv0 <;> rw [hu0, hv0] <;>
      simp only [List.map_cons, List.map_nil, sv, Bool.false_eq_true, ↓reduceIte, if_true, if_false,
        and_self, and_true, true_and, and_false, false_and, or_self, or_true, true_or, or_false, false_or,
        one_ne_zero, zero_ne_one, show Nat.beq 1 1 = true from rfl, show Nat.beq 0 1 = false from rfl,
        Bool.and_self, Bool.and_true, Bool.and_false, Bool.true_and, Bool.false_and, Bool.or_self, Bool.or_true,
        Bool.or_false, Bool.true_or, Bool.false_or] <;>
      simp only [e4, e34, e64, e3, e33, e1024, e2, e32]
    all_goals
      generalize rawTagAdd (decodeTag (Nat.land (ltab.rt 3 u.val) 32767)) (decodeTag (Nat.land (ltab.rt 3 v.val) 32767)) = T0
    all_goals simp only [sparse_norm_cons, sparse_norm_nil, coordinateMonomial_add]
    all_goals generalize coordinateMonomial T0 = M
    all_goals simp only [rawSymmetricWeight, rawStandardCoordinates, coordinateMonomial, pow_zero, pow_one, mul_one,
      one_mul, Bool.true_and, Bool.and_true, Bool.false_and, Bool.or_true, Bool.true_or, Bool.false_or, Bool.or_false,
      ↓reduceIte, Bool.false_eq_true, Bool.and_self, Bool.or_self, add_zero]
    all_goals push_cast
    all_goals simp only [show ((-24 : ℝ) / 81) = -(8 / 27) by norm_num, show ((36 : ℝ) / 81) = 4 / 9 by norm_num,
      show ((12 : ℝ) / 81) = 4 / 27 by norm_num, show ((-54 : ℝ) / 81) = -(2 / 3) by norm_num,
      show ((162 : ℝ) / 81) = 2 by norm_num, show ((-108 : ℝ) / 81) = -(4 / 3) by norm_num, map_neg, map_ofNat]
    all_goals ring

/-! ## The source polynomials -/

/-- Source kernel of output `(b, r, c)` (block index `b`; zero outside the block). -/
def srcN (a : ℝ) (p : MomentPivots 8) (b r c : ℕ) : Poly3 :=
  if b = 0 then (if h : r < 8 ∧ c < 8 then momentCoordinateKernel a 8 p 0 momQ0 ⟨r, h.1⟩ ⟨c, h.2⟩ else 0)
  else if b = 1 then (if h : r < 7 ∧ c < 7 then momentCoordinateKernel a 8 p 1 momQ1 ⟨r, h.1⟩ ⟨c, h.2⟩ else 0)
  else if b = 2 then
    (if h : r < 36 ∧ c < 36 then scalarCoordinateKernel .m0Plus 8 (Kpk a .m0Plus) (rawQ .m0Plus)
      ⟨r, by rw [dims_m0Plus]; exact h.1⟩ ⟨c, by rw [dims_m0Plus]; exact h.2⟩ else 0)
  else
    (if h : r < 47 ∧ c < 47 then scalarCoordinateKernel .m0Standard 8 (Kpk a .m0Standard) (rawQ .m0Standard)
      ⟨r, by rw [dims_m0Standard]; exact h.1⟩ ⟨c, by rw [dims_m0Standard]; exact h.2⟩ else 0)

/-- The canonical source polynomial of table column `k`. -/
def P (a : ℝ) (p : MomentPivots 8) (k : Fin 202) : Poly3 :=
  MvPolynomial.C (if oRow ltab k.val = oCol ltab k.val then (1 : ℝ) else 2) *
    srcN a p (oBlk ltab k.val) (oRow ltab k.val) (oCol ltab k.val)

/-! ## Substitution -/

theorem rawQ_subst (b : ScalarBlockName) (hb : b = .m0Plus ∨ b = .m0Standard) (u v : Fin (rawSize b)) :
    invariantSubst (rawQ b u v) = rawScalarBilinear b (rawTags b u) (rawTags b v) := by
  rw [rawQ_eq b hb, rawScalarProductSpec_subst]

theorem srcN_subst (a : ℝ) (ha : physical a) (p : MomentPivots 8) (b r c : ℕ) (hb : b < 4)
    (hr : r < gramBlockDimension 8 (blockOf b)) (hc : c < gramBlockDimension 8 (blockOf b)) :
    invariantSubst (srcN a p b r c) = gramKernel a 8 p (blockOf b) ⟨r, hr⟩ ⟨c, hc⟩ := by
  have hr' := hr
  have hc' := hc
  rw [gbd b hb] at hr' hc'
  interval_cases b
  · rw [srcN, if_pos rfl, dif_pos ⟨hr', hc'⟩]
    exact momentCoordinateKernel_subst a 8 p 0 momQ0 RawMomentTensors.D16_F0.subst_coordinatePolynomial _ _
  · rw [srcN, if_neg (by norm_num), if_pos rfl, dif_pos ⟨hr', hc'⟩]
    exact momentCoordinateKernel_subst a 8 p 1 momQ1 RawMomentTensors.D16_F1.subst_coordinatePolynomial _ _
  · rw [srcN, if_neg (by norm_num), if_neg (by norm_num), if_pos rfl, dif_pos ⟨hr', hc'⟩]
    exact scalarCoordinateKernel_subst_nonstandard a .m0Plus 8 (rawTags .m0Plus) (Kpk a .m0Plus) (rawQ .m0Plus) rfl
      (rawQ_subst .m0Plus (Or.inl rfl)) (block_m0Plus_0 a ha (hdef_of a ha)) _ _
  · rw [srcN, if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), dif_pos ⟨hr', hc'⟩]
    exact scalarCoordinateKernel_subst a .m0Standard 8 (rawTags .m0Standard) (Kpk a .m0Standard) (rawQ .m0Standard)
      (rawQ_subst .m0Standard (Or.inr rfl)) (block_m0Standard_0 a ha (hdef_of a ha))
      (block_m0Standard_1 a ha (hdef_of a ha)) _ _

/-- **Canonical columns**: `invariantSubst (P a p k)` is the Gram polynomial of the output unit. -/
theorem P_subst (a : ℝ) (ha : physical a) (p : MomentPivots 8) (k : Fin 202)
    (hr : oRow ltab k.val < gramBlockDimension 8 (blockOf (oBlk ltab k.val)))
    (hc : oCol ltab k.val < gramBlockDimension 8 (blockOf (oBlk ltab k.val))) :
    invariantSubst (P a p k) =
      gramPoly a 8 p (fixedGramUnit (blockOf (oBlk ltab k.val)) ⟨oRow ltab k.val, hr⟩ ⟨oCol ltab k.val, hc⟩) := by
  rw [gramPoly_fixedGramUnit, P, map_mul, srcN_subst a ha p _ _ _ (outs k.val k.isLt).1 hr hc]
  congr 1
  · simp only [invariantSubst, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, Fin.mk.injEq]

/-! ## Coefficients -/

theorem kidx_check : ((List.range 4).all fun b => (List.range (bdim b)).all fun j =>
    (kapC ltab b j).all fun e => decide (e.1 < [9, 8, 41, 54].getD b 0)) = true := by decide +kernel

theorem kap_facts (b j : ℕ) (hb : b < 4) (hj : j < bdim b) :
    IncI 0 ((kapC ltab b j).map Prod.fst) ∧ ∀ e ∈ kapC ltab b j, e.1 < [9, 8, 41, 54].getD b 0 := by
  refine ⟨?_, fun e he => ?_⟩
  · have hj' : j < 256 := by interval_cases b <;> simp [bdim] at hj <;> omega
    obtain ⟨p1, -, -⟩ := polyVecOk_spec 448 _ _ _ _ _ _ _ ((kapHdrOk_spec ltab 202 15 26 64 kap_ok).1 b j hb hj')
    have h := congrArg (List.map Prod.fst) (decPolyVec_sv 448 (by norm_num) (ltab.kc b j) (ltab.kn b j) 0)
    simp only [List.map_map] at h
    exact incI_of_inc _ _ p1 h
  · have h := List.all_eq_true.mp kidx_check b (List.mem_range.mpr hb)
    have h2 := List.all_eq_true.mp h j (List.mem_range.mpr hj)
    exact of_decide_eq_true (List.all_eq_true.mp h2 e he)

theorem rd_check : RawMomentTensors.D16_F0.denominator = stab.rd 0 ∧ RawMomentTensors.D16_F1.denominator = stab.rd 1 ∧
    rdenS .m0Plus = stab.rd 2 ∧ rdenS .m0Standard = stab.rd 3 := by decide +kernel

theorem sum_fin_range (m : ℕ) (f : ℕ → ℕ → ℝ) :
    ∑ u : Fin m, ∑ v : Fin m, f u.val v.val = ∑ u ∈ Finset.range m, ∑ v ∈ Finset.range m, f u v := by
  rw [Fin.sum_univ_eq_sum_range (fun u => ∑ v : Fin m, f u v.val)]
  apply Finset.sum_congr rfl
  intro u _
  exact Fin.sum_univ_eq_sum_range (fun v => f u v) m

/-- `coef_formula` over `Fin` sums. -/
theorem coef_fin (b r c mult code m : ℕ) (a δ Sr Sc rden : ℝ) (hδ : δ ≠ 0) (hr : Sr ≠ 0) (hc : Sc ≠ 0)
    (hd : rden ≠ 0) (Kr Kc : Fin m → ℝ) (Lk : Fin m → Fin m → ℝ)
    (hKr : ∀ u : Fin m, Kr u = evalZ (kapE ltab b r u.val) a / (Sr * δ))
    (hKc : ∀ v : Fin m, Kc v = evalZ (kapE ltab b c v.val) a / (Sc * δ))
    (hL : ∀ u v : Fin m, Lk u v = (zsum ltab b u.val v.val code : ℝ) / rden)
    (ir : IncI 0 ((kapC ltab b r).map Prod.fst)) (ic : IncI 0 ((kapC ltab b c).map Prod.fst))
    (br : ∀ e ∈ kapC ltab b r, e.1 < m) (bc : ∀ e ∈ kapC ltab b c, e.1 < m) :
    (mult : ℝ) * ∑ u : Fin m, ∑ v : Fin m, Kr u * Kc v * Lk u v =
      evalZ (ncomp ltab b r c mult code) a / (Sr * Sc * rden * δ ^ 2) := by
  have e : ∑ u : Fin m, ∑ v : Fin m, Kr u * Kc v * Lk u v = ∑ u ∈ Finset.range m, ∑ v ∈ Finset.range m,
      evalZ (kapE ltab b r u) a / (Sr * δ) * (evalZ (kapE ltab b c v) a / (Sc * δ)) *
        ((zsum ltab b u v code : ℝ) / rden) := by
    rw [← sum_fin_range m (fun u v => evalZ (kapE ltab b r u) a / (Sr * δ) * (evalZ (kapE ltab b c v) a / (Sc * δ)) *
        ((zsum ltab b u v code : ℝ) / rden))]
    apply Finset.sum_congr rfl; intro u _; apply Finset.sum_congr rfl; intro v _
    rw [hKr, hKc, hL]
  rw [e]
  exact coef_formula ltab b r c mult code m a δ Sr Sc rden hδ hr hc hd _ _ _ (fun u _ => rfl) (fun v _ => rfl)
    (fun u v => rfl) ir ic br bc

/-- **Coefficient formula** of the canonical columns: `C_ik(a) = N_ik(a) / (Δc_k δ_b(a)²)`. -/
theorem P_coeff (a : ℝ) (ha : physical a) (p : MomentPivots 8) (hp0 : (p 0).val = 0) (hp1 : (p 1).val = 1)
    (i k : Fin 202) :
    MvPolynomial.coeff (tagExponent (coordinateTags i)) (P a p k) =
      evalZ (nC ltab k.val i.val) a / ((dcG gtab k.val : ℝ) * evalZ (blC gtab k.val) a ^ 2) := by
  obtain ⟨hb4, hrb, hcb, hmult⟩ := outs k.val k.isLt
  rw [blC_eq k.val k.isLt, dc k.val k.isLt, P, MvPolynomial.coeff_C_mul]
  unfold nC
  have hm : (if oRow ltab k.val = oCol ltab k.val then (1 : ℝ) else 2) = ((oMult ltab k.val : ℕ) : ℝ) := by
    rw [hmult]; split_ifs <;> norm_num
  rw [hm]
  have hδ := delta_ne a ha _ hb4
  obtain ⟨rd0, rd1, rd2, rd3⟩ := rd_check
  have hcode : coordinateTags i = decodeTag (ltab.rtag i.val) := rfl
  obtain ⟨ir, br⟩ := kap_facts _ _ hb4 hrb
  obtain ⟨ic, bc⟩ := kap_facts _ _ hb4 hcb
  push_cast
  generalize oBlk ltab k.val = b at hb4 hrb hcb hδ ir br ic bc ⊢
  generalize oRow ltab k.val = r at hrb ir br ⊢
  generalize oCol ltab k.val = c at hcb ic bc ⊢
  interval_cases b
  · -- F0
    simp only [bdim] at hrb hcb
    obtain ⟨-, -, -, m4⟩ := mom_parts 0 (by norm_num)
    have hSr : (stab.sc 0 r : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp (m4 r (by omega)).1)
    have hSc : (stab.sc 0 c : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp (m4 c (by omega)).1)
    rw [srcN, if_pos rfl, dif_pos ⟨hrb, hcb⟩]
    simp only [momentCoordinateKernel, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
    refine coef_fin 0 r c _ _ 9 a _ _ _ _ hδ hSr hSc (by rw [← rd0]; norm_num [RawMomentTensors.D16_F0.denominator,
      RawMomentCatalogue.Moment0_0_0.denominator16]) _ _ _ (fun u => ?_) (fun v => ?_) (fun u v => ?_) ir ic br bc
    · exact Kmom a ha p hp0 hp1 0 (by norm_num) u ⟨r, hrb⟩
    · exact Kmom a ha p hp0 hp1 0 (by norm_num) v ⟨c, hcb⟩
    · rw [momQ0_coeff, hcode, lookup_zlist, rd0]
  · -- F1
    simp only [bdim] at hrb hcb
    obtain ⟨-, -, -, m4⟩ := mom_parts 1 (by norm_num)
    have hSr : (stab.sc 1 r : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp (m4 r (by omega)).1)
    have hSc : (stab.sc 1 c : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp (m4 c (by omega)).1)
    rw [srcN, if_neg (by norm_num), if_pos rfl, dif_pos ⟨hrb, hcb⟩]
    simp only [momentCoordinateKernel, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
    refine coef_fin 1 r c _ _ 8 a _ _ _ _ hδ hSr hSc (by rw [← rd1]; norm_num [RawMomentTensors.D16_F1.denominator,
      RawMomentCatalogue.Moment1_0_0.denominator16]) _ _ _ (fun u => ?_) (fun v => ?_) (fun u v => ?_) ir ic br bc
    · exact Kmom a ha p hp0 hp1 1 (by norm_num) u ⟨r, hrb⟩
    · exact Kmom a ha p hp0 hp1 1 (by norm_num) v ⟨c, hcb⟩
    · rw [momQ1_coeff, hcode, lookup_zlist, rd1]
  · -- M0_plus
    simp only [bdim] at hrb hcb
    have hSr : (stab.sc 2 r : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp (rf 2 (Or.inl rfl) r 0 hrb (by decide)).2.1)
    have hSc : (stab.sc 2 c : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp (rf 2 (Or.inl rfl) c 0 hcb (by decide)).2.1)
    rw [srcN, if_neg (by norm_num), if_neg (by norm_num), if_pos rfl, dif_pos ⟨hrb, hcb⟩]
    simp only [scalarCoordinateKernel, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
    refine coef_fin 2 r c _ _ 41 a _ _ _ _ hδ hSr hSc (by rw [← rd2]; norm_num [rdenS]) _ _ _ (fun u => ?_) (fun v => ?_)
      (fun u v => ?_) ir ic br bc
    · exact Kpk_eq a ha .m0Plus (Or.inl rfl) u _
    · exact Kpk_eq a ha .m0Plus (Or.inl rfl) v _
    · rw [hcode]; refine (rawQ_coeff _ .m0Plus u v).trans ?_; rw [lookup_zlist, rd2]; rfl
  · -- M0_standard
    simp only [bdim] at hrb hcb
    have hSr : (stab.sc 3 r : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp (rf 3 (Or.inr rfl) r 0 hrb (by decide)).2.1)
    have hSc : (stab.sc 3 c : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp (rf 3 (Or.inr rfl) c 0 hcb (by decide)).2.1)
    rw [srcN, if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), dif_pos ⟨hrb, hcb⟩]
    simp only [scalarCoordinateKernel, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
    refine coef_fin 3 r c _ _ 54 a _ _ _ _ hδ hSr hSc (by rw [← rd3]; norm_num [rdenS]) _ _ _ (fun u => ?_) (fun v => ?_)
      (fun u v => ?_) ir ic br bc
    · exact Kpk_eq a ha .m0Standard (Or.inr rfl) u _
    · exact Kpk_eq a ha .m0Standard (Or.inr rfl) v _
    · rw [hcode]; refine (rawQ_coeff _ .m0Standard u v).trans ?_; rw [lookup_zlist, rd3]; rfl

#print axioms P_subst
#print axioms P_coeff
#print axioms Q_ne

end ThomsonCompact.Fixed.D16
