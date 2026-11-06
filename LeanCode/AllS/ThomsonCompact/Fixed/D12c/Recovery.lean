import ThomsonCompact.Fixed.D12c.Canon
import ThomsonCompact.Fixed.Recovery
import AllS.Units.N_AI.N_fixed_tables.GramEntrySupport

/-!
# The compact D12 fixed right inverse (workstream F4c)

`FixedD12` mirrors the old `FixedTables.D12` API (`Fin 100`, `GramBlock 6`, pivots `p 0 = 0`, `p 1 = 3`), built on the
kernel leaves of `Fixed.D12c` (replaces the old per-degree closure of `FixedTables.D12`):

* `coordinateTags`, `retainedIndex` (bijective), `outputCoordinates`, `insertionBlockName`, `insertionUnit`,
  `insertionLinear`, `insertionLinear_inactive`, `insertionUnit_eq_fixed`;
* `inverseMatrix a k i = dq_k H_ki(a) / (λ_k dz_k(a))` (the stored table), `inverseLinear`, `correctionLinear`;
* `coefficientMatrix_right_inverse`: `C(a) · inverseMatrix a = 1` on the physical domain (from (T), (G), `Q(a) ≠ 0`);
* **`correctionLinear_full_recovery`** (via `Fixed.recovery_of_rightInverse`).
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

noncomputable section
open scoped BigOperators

namespace ThomsonCompact.FixedD12

open Blueprint.CAP Blueprint.Thomson.Finite ThomsonCompact.Fixed ThomsonCompact.Packed
open ThomsonCompact.Fixed.D12c (ltab gtab stab slices)

abbrev coordinateTags : Fin 100 → Tag := ThomsonCompact.Fixed.D12c.coordinateTags
abbrev retainedIndex : Fin 100 → RetainedIndex 12 := ThomsonCompact.Fixed.D12c.retainedIndex

theorem retainedIndex_tag (i : Fin 100) : (retainedIndex i).val = coordinateTags i :=
  ThomsonCompact.Fixed.D12c.retainedIndex_tag i

theorem retainedIndex_bijective : Function.Bijective retainedIndex :=
  ThomsonCompact.Fixed.D12c.retainedIndex_bijective

/-- Retained coordinates in the table's row order. -/
def retainedVector (a : ℝ) (f : Compatible a 12) : Fin 100 → ℝ :=
  fun i => retainCompatible a 12 f (retainedIndex i)

/-! ## Insertion (as the old `FixedTables.D18.Insertion`) -/

/-- Names of the actual Gram blocks. -/
def insertionBlockName : GramBlock 6 → String
  | .inl k => !["F0", "F1", "F2", "F3", "F4", "F5"] k
  | .inr .m0Plus => "M0_plus"
  | .inr .m0Sign => "M0_sign"
  | .inr .m0Standard => "M0_standard"
  | .inr .m1Even => "M1_even"
  | .inr .m1Odd => "M1_odd"
  | .inr .mdetPlus => "Mdet_plus"
  | .inr .mdetSign => "Mdet_sign"
  | .inr .mdetStandard => "Mdet_standard"

/-- The output coordinates `(block, r, c)` of the 100 table columns. -/
def outputCoordinates (k : Fin 100) : String × ℕ × ℕ :=
  (insertionBlockName (D12c.blockOf (oBlk ltab k.val)), oRow ltab k.val, oCol ltab k.val)

def outputEntry (j : Fin 100) (name : String) (r c : ℕ) : ℝ :=
  if name = (outputCoordinates j).1 ∧
    ((r = (outputCoordinates j).2.1 ∧ c = (outputCoordinates j).2.2) ∨
     (r = (outputCoordinates j).2.2 ∧ c = (outputCoordinates j).2.1)) then 1 else 0

theorem outputEntry_symm (j : Fin 100) (name : String) (r c : ℕ) :
    outputEntry j name c r = outputEntry j name r c := by
  simp only [outputEntry, and_comm, or_comm]

def insertionUnit (j : Fin 100) : GramFamily 6 :=
  ⟨fun b r c => outputEntry j (insertionBlockName b) r.val c.val,
    fun b => by ext r c; exact outputEntry_symm j (insertionBlockName b) r.val c.val⟩

/-- Linear insertion of the 100 physical symmetric Gram coordinates. -/
def insertionLinear : (Fin 100 → ℝ) →ₗ[ℝ] GramFamily 6 where
  toFun v := ∑ j, v j • insertionUnit j
  map_add' v w := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' x v := by simp only [Pi.smul_apply, smul_smul, Finset.smul_sum, RingHom.id_apply, smul_eq_mul]

theorem insertionLinear_apply (v : Fin 100 → ℝ) : insertionLinear v = ∑ j, v j • insertionUnit j := rfl

theorem insertionLinear_entry (v : Fin 100 → ℝ) (b : GramBlock 6) (r c : Fin (gramBlockDimension 6 b)) :
    (insertionLinear v).val b r c = ∑ j, v j * outputEntry j (insertionBlockName b) r.val c.val :=
  fixedGramCombination_apply insertionUnit v b r c

theorem outputCoordinates_active : ∀ j : Fin 100,
    (outputCoordinates j).1 = "F0" ∨ (outputCoordinates j).1 = "F1" ∨
    (outputCoordinates j).1 = "M0_plus" ∨ (outputCoordinates j).1 = "M0_standard" := by
  decide +kernel

theorem insertionLinear_inactive (v : Fin 100 → ℝ) (b : GramBlock 6)
    (h0 : insertionBlockName b ≠ "F0") (h1 : insertionBlockName b ≠ "F1")
    (hp : insertionBlockName b ≠ "M0_plus") (hs : insertionBlockName b ≠ "M0_standard") :
    (insertionLinear v).val b = 0 := by
  ext r c
  rw [insertionLinear_entry]
  apply Finset.sum_eq_zero
  intro j _
  have h : insertionBlockName b ≠ (outputCoordinates j).1 := by
    rcases outputCoordinates_active j with h | h | h | h
    · exact h ▸ h0
    · exact h ▸ h1
    · exact h ▸ hp
    · exact h ▸ hs
  simp [outputEntry, h]

theorem insertionBlockName_injective : Function.Injective insertionBlockName := by
  decide +kernel

theorem insertionUnit_eq_fixed (k : Fin 100) (b : GramBlock 6) (i j : Fin (gramBlockDimension 6 b))
    (h : outputCoordinates k = (insertionBlockName b, i.val, j.val)) :
    insertionUnit k = fixedGramUnit b i j := by
  apply Subtype.ext
  funext c r s
  by_cases hc : c = b
  · subst c
    rw [fixedGramUnit_same_block_apply]
    change outputEntry k (insertionBlockName b) r.val s.val = _
    simp only [outputEntry, h, true_and, Fin.ext_iff]
  · rw [fixedGramUnit_other_block b c i j hc]
    have hn : insertionBlockName c ≠ insertionBlockName b := fun he => hc (insertionBlockName_injective he)
    change outputEntry k (insertionBlockName c) r.val s.val = 0
    simp [outputEntry, h, hn]

/-! ## The right inverse -/

/-- **The D12 fixed-table right inverse**: `dq_k H_ki(a) / (λ_k dz_k(a))` from the stored table. -/
def inverseMatrix (a : ℝ) : Matrix (Fin 100) (Fin 100) ℝ :=
  fun k i => (dqG gtab k.val : ℝ) * evalZ (hC D12c.slices k.val i.val) a /
    ((lamG gtab k.val : ℝ) * evalZ (dzC gtab k.val) a)

def inverseLinear (a : ℝ) : (Fin 100 → ℝ) →ₗ[ℝ] (Fin 100 → ℝ) where
  toFun r := (inverseMatrix a).mulVec r
  map_add' v w := Matrix.mulVec_add _ v w
  map_smul' x v := Matrix.mulVec_smul _ x v

def correctionLinear (a : ℝ) : (Fin 100 → ℝ) →ₗ[ℝ] GramFamily 6 := insertionLinear.comp (inverseLinear a)

theorem correctionLinear_apply (a : ℝ) (r : Fin 100 → ℝ) :
    correctionLinear a r = insertionLinear ((inverseMatrix a).mulVec r) := rfl

/-- The source columns. -/
def sourceColumns (a : ℝ) (p : MomentPivots 6) : Fin 100 → Poly3 := fun k => D12c.P a p k

theorem out_dims (k : Fin 100) :
    oRow ltab k.val < gramBlockDimension 6 (D12c.blockOf (oBlk ltab k.val)) ∧
      oCol ltab k.val < gramBlockDimension 6 (D12c.blockOf (oBlk ltab k.val)) := by
  obtain ⟨h1, h2, h3, -⟩ := D12c.outs k.val k.isLt
  rw [D12c.gbd _ h1]
  exact ⟨h2, h3⟩

theorem columns_canonical (a : ℝ) (ha : physical a) (p : MomentPivots 6) (k : Fin 100) :
    invariantSubst (sourceColumns a p k) = gramPoly a 6 p (insertionUnit k) := by
  rw [insertionUnit_eq_fixed k _ ⟨_, (out_dims k).1⟩ ⟨_, (out_dims k).2⟩ rfl]
  exact D12c.P_subst a ha p k _ _

/-- `C(a) · inverseMatrix a = 1` on the physical domain. -/
theorem coefficientMatrix_right_inverse (a : ℝ) (ha : physical a) (p : MomentPivots 6)
    (hp0 : (p 0).val = 0) (hp1 : (p 1).val = 3) :
    coefMatrix retainedIndex (sourceColumns a p) * inverseMatrix a = 1 := by
  ext i i'
  simp only [Matrix.mul_apply, coefMatrix, Matrix.of_apply, retainedIndex_tag, Matrix.one_apply, sourceColumns]
  have hQ := D12c.Q_ne a ha
  have hs : (gtab.s : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp D12c.s_pos)
  have key : ∀ k : Fin 100, MvPolynomial.coeff (tagExponent (coordinateTags i)) (D12c.P a p k) * inverseMatrix a k i' =
      evalZ (nC ltab k.val i.val) a * (evalZ (gamC gtab k.val) a * evalZ (hC D12c.slices k.val i'.val) a) /
        ((gtab.s : ℝ) * evalZ (qC gtab) a) := by
    intro k
    rw [D12c.P_coeff a ha p hp0 hp1 i k]
    obtain ⟨hb, hdz, hl, hdc⟩ := D12c.out_ne a ha k.val k.isLt
    obtain ⟨_, hid⟩ := D12c.gid k.val k.isLt
    have e := hid a
    push_cast at e
    unfold inverseMatrix
    field_simp
    linear_combination (-(evalZ (nC ltab k.val i.val) a * evalZ (hC D12c.slices k.val i'.val) a)) * e
  rw [Finset.sum_congr rfl (fun k _ => key k), ← Finset.sum_div]
  have ht := D12c.table i.val i'.val i.isLt i'.isLt a
  rw [← Fin.sum_univ_eq_sum_range (fun k => evalZ (nC ltab k i.val) a *
    (evalZ (gamC gtab k) a * evalZ (hC D12c.slices k i'.val) a)) 100] at ht
  rw [ht]
  by_cases h : i = i'
  · rw [if_pos (congrArg Fin.val h), if_pos h]; field_simp
  · rw [if_neg (fun h' => h (Fin.ext h')), if_neg h, zero_div]

/-- **Full recovery** with the compact D12 right inverse. -/
theorem correctionLinear_full_recovery (a : ℝ) (ha : physical a) (p : MomentPivots 6) (hp : ValidMomentPivots p)
    (hp0 : (p 0).val = 0) (hp1 : (p 1).val = 3) (f : Compatible a 12) :
    gramPoly a 6 p (correctionLinear a (retainedVector a f)) = f.val := by
  have h := recovery_of_rightInverse a ha 6 (by norm_num) (by norm_num) p hp retainedIndex retainedIndex_bijective
    insertionUnit (sourceColumns a p) (columns_canonical a ha p) (inverseMatrix a)
    (coefficientMatrix_right_inverse a ha p hp0 hp1) f
  rw [correctionLinear_apply, insertionLinear_apply]
  exact h

#print axioms coefficientMatrix_right_inverse
#print axioms correctionLinear_full_recovery

end ThomsonCompact.FixedD12
