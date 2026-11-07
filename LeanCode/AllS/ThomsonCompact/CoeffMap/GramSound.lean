import ThomsonCompact.CoeffMap.CellCodec
import ThomsonCompact.CoeffMap.MomentSound
import ThomsonCompact.CoeffMap.Rep
import ThomsonCompact.Packed.BridgeIn
import AllS.Units.N_AI.N_gram_replay.LiteralGramCoefficientSupport

/-!
# Soundness of the exact integer Gram coefficients (F2c 2)

For the literal block `d.block bi` decoded from the cell data, `coeffQ_eq` gives
`literalGramCoeffQ (d.cell) (d.block bi) k i j = coefI bi k i j / 2^L` (`k ≤ NW`), via the row/flat-index
lemma `getD_lowerRow`, the dot-product lemmas `factorGram_eq`, `metricGram_eq` and the binomial weight
identity `bern_eq`. `w0_valid`: the W0 entry polynomial equals `Σₖ (coefI/2^L) xᵏ`, so the boxes of `w0TM`
form a valid old TM and F1's `ofBoxes_sound` encloses the literal Gram entry.
-/

namespace ThomsonCompact.CoeffMap

open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite ThomsonCompact.Packed
open scoped BigOperators

/-- The literal block of the decoded data. -/
def CellData.block (d : CellData) (bi : ℕ) : Literals.Block where
  name := ""
  order := d.order bi
  diagonalExponents := d.kdiagL bi
  strictLower := d.klowL bi
  factors := (List.range (d.nw + 1)).map (d.facL bi)

/-- The literal cell of the decoded data (only the W0 fields matter). -/
def CellData.cell (d : CellData) : Literals.Cell where
  id := ""
  degree := 12
  center := 0
  halfwidth := 0
  validationOrder := 0
  bernsteinDegree := d.nw
  profile := .original
  balance := .unit
  factorBits := d.fb
  metricBits := d.mbits
  floorExponent := d.floorExp
  momentPivots := []
  auxiliaryNodes := []
  rootCoefficients := []
  jointDepth := 0
  jointExactBlocks := []
  blocks := []

/-! ## Lists -/

theorem dotI_eq_sum : ∀ (xs ys : List ℤ) (n : ℕ), xs.length ≤ n →
    dotI xs ys = ∑ l ∈ Finset.range n, xs.getD l 0 * ys.getD l 0
  | [], ys, n, _ => by simp [dotI]
  | x :: xs, [], n, _ => by
    simp only [dotI]
    symm
    apply Finset.sum_eq_zero
    intro l _
    simp
  | x :: xs, y :: ys, n + 1, h => by
    simp only [List.length_cons] at h
    rw [dotI, dotI_eq_sum xs ys n (by omega), Finset.sum_range_succ']
    simp [add_comm]
  | _ :: _, _ :: _, 0, h => by simp at h

theorem getD_lowerRow (flat : List ℤ) (r l : ℕ) :
    (lowerRow flat r).getD l 0 = if l ≤ r then flat.getD (r * (r + 1) / 2 + l) 0 else 0 := by
  unfold lowerRow
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  by_cases h : l ≤ r
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]
    rfl

theorem length_lowerRow (flat : List ℤ) (r : ℕ) : (lowerRow flat r).length ≤ r + 1 := by
  unfold lowerRow
  simp

theorem getD_map_range {α : Type*} (f : ℕ → α) (d : α) (n i : ℕ) (hi : i < n) :
    ((List.range n).map f).getD i d = f i := by
  simp [List.getD_eq_getElem?_getD, hi]

/-! ## The two Gram products -/

theorem factorGram_eq (d : CellData) (bi u : ℕ) (hu : u ≤ d.nw) (i j : Fin (d.block bi).order) :
    (literalFactorQ (d.block bi) d.fb u * (literalFactorQ (d.block bi) d.fb u).transpose) i j =
      (dotI (lowerRow (d.facL bi u) i) (lowerRow (d.facL bi u) j) : ℚ) / 2 ^ (2 * d.fb) := by
  have hf : (d.block bi).factors.getD u [] = d.facL bi u := getD_map_range _ _ _ _ (by omega)
  rw [dotI_eq_sum _ _ (d.block bi).order ((length_lowerRow _ _).trans (by omega)), Matrix.mul_apply]
  push_cast
  rw [Finset.sum_div, ← Fin.sum_univ_eq_sum_range
    (fun l => ((lowerRow (d.facL bi u) i).getD l 0 : ℚ) * ((lowerRow (d.facL bi u) j).getD l 0 : ℚ) / 2 ^ (2 * d.fb))]
  apply Finset.sum_congr rfl
  intro l _
  have h2f : (2 : ℚ) ^ (2 * d.fb) = (2 ^ d.fb) ^ 2 := by rw [mul_comm, pow_mul]
  simp only [literalFactorQ, Matrix.transpose_apply, hf, getD_lowerRow, h2f]
  by_cases h1 : l.val ≤ i.val <;> by_cases h2 : l.val ≤ j.val <;>
    simp [Fin.le_def, h1, h2] <;> ring

theorem metricRow_getD (d : CellData) (bi r l : ℕ) :
    (d.metricRow bi r).getD l 0 =
      if l < r then (d.klowL bi).getD (r * (r - 1) / 2 + l) 0 * 2 ^ (d.mb bi - d.mbits)
      else if l = r then 2 ^ (Int.toNat ((d.mb bi : ℤ) + (d.kdiagL bi).getD r 0)) else 0 := by
  unfold CellData.metricRow
  by_cases hl : l < r + 1
  · rw [getD_map_range _ _ _ _ hl]
    by_cases h1 : l < r
    · simp [h1]
    · have : l = r := by omega
      simp [h1, this]
  · simp [List.getD_eq_getElem?_getD, hl]
    rw [if_neg (by omega), if_neg (by omega)]

theorem mb_ge (d : CellData) (bi : ℕ) : d.mbits ≤ d.mb bi ∧ ∀ x ∈ d.kdiagL bi, -x ≤ (d.mb bi : ℤ) := by
  unfold CellData.mb
  generalize d.kdiagL bi = L
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.foldr_cons, List.mem_cons, forall_eq_or_imp]
    refine ⟨ih.1.trans (Nat.le_max_left _ _), ?_, fun y hy => (ih.2 y hy).trans ?_⟩
    · have h := Nat.le_max_right (List.foldr (fun x m => Nat.max m (-x).toNat) d.mbits L) (-x).toNat
      have h' : ((-x).toNat : ℤ) ≤ ((Nat.max (List.foldr (fun x m => Nat.max m (-x).toNat) d.mbits L)
          (-x).toNat : ℕ) : ℤ) := by exact_mod_cast h
      exact (Int.self_le_toNat _).trans h'
    · exact_mod_cast Nat.le_max_left _ _

theorem metricGram_eq (d : CellData) (bi : ℕ) (i j : Fin (d.block bi).order) :
    (literalMetricQ (d.block bi) d.mbits * (literalMetricQ (d.block bi) d.mbits).transpose) i j =
      (dotI (d.metricRow bi i) (d.metricRow bi j) : ℚ) / 2 ^ (2 * d.mb bi) := by
  obtain ⟨hm1, hm2⟩ := mb_ge d bi
  have hlen : ∀ r, (d.metricRow bi r).length ≤ r + 1 := by intro r; simp [CellData.metricRow]
  have hM : ∀ r l : Fin (d.block bi).order, literalMetricQ (d.block bi) d.mbits r l =
      ((d.metricRow bi r).getD l 0 : ℚ) / 2 ^ d.mb bi := by
    intro r l
    rw [metricRow_getD]
    simp only [literalMetricQ]
    rw [show (d.block bi).strictLower = d.klowL bi from rfl,
      show (d.block bi).diagonalExponents = d.kdiagL bi from rfl]
    by_cases h1 : l.val < r.val
    · rw [if_pos (Fin.lt_def.mpr h1), if_pos h1]
      push_cast
      have hp : (2 : ℚ) ^ d.mb bi = 2 ^ (d.mb bi - d.mbits) * 2 ^ d.mbits := by
        rw [← pow_add, Nat.sub_add_cancel hm1]
      rw [hp]
      field_simp
    · rw [if_neg (fun h => h1 (Fin.lt_def.mp h)), if_neg h1]
      by_cases h2 : l.val = r.val
      · have hrl : r = l := Fin.ext h2.symm
        rw [if_pos hrl, if_pos h2]
        have hk : -(d.kdiagL bi).getD r 0 ≤ (d.mb bi : ℤ) := by
          by_cases hr : r.val < (d.kdiagL bi).length
          · exact hm2 _ (by rw [List.getD_eq_getElem _ _ hr]; exact List.getElem_mem hr)
          · rw [List.getD_eq_default _ _ (by omega)]; simp
        have hnn : 0 ≤ (d.mb bi : ℤ) + (d.kdiagL bi).getD r 0 := by omega
        push_cast
        rw [show ((2 : ℚ) ^ (Int.toNat ((d.mb bi : ℤ) + (d.kdiagL bi).getD r 0))) =
            (2 : ℚ) ^ ((d.mb bi : ℤ) + (d.kdiagL bi).getD r 0) by
              rw [← zpow_natCast, Int.toNat_of_nonneg hnn],
          zpow_add₀ (by norm_num), zpow_natCast]
        field_simp
      · rw [if_neg (fun h => h2 (congrArg Fin.val h).symm), if_neg h2]
        simp
  rw [dotI_eq_sum _ _ (d.block bi).order ((hlen _).trans (by omega)), Matrix.mul_apply]
  push_cast
  rw [Finset.sum_div, ← Fin.sum_univ_eq_sum_range
    (fun l => ((d.metricRow bi i).getD l 0 : ℚ) * ((d.metricRow bi j).getD l 0 : ℚ) / 2 ^ (2 * d.mb bi))]
  apply Finset.sum_congr rfl
  intro l _
  rw [Matrix.transpose_apply, hM i l, hM j l, show (2 : ℚ) ^ (2 * d.mb bi) = (2 ^ d.mb bi) ^ 2 by
    rw [mul_comm, pow_mul]]
  ring

/-! ## The Bernstein weights -/

theorem bern_eq (nw u k : ℕ) (hu : u ≤ nw) (hk : k ≤ nw) :
    ((nw.choose u : ℚ) * (nw.choose k : ℚ) / 2 ^ nw) * rationalBernsteinTransform nw u k =
      (bernI nw u k : ℚ) / 2 ^ nw := by
  have hck : (nw.choose k : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  unfold rationalBernsteinTransform bernI
  have hsum : ∑ j ∈ Finset.Icc (k + u - nw) (min u k),
      (-1 : ℚ) ^ (k - j) * (u.choose j : ℚ) * ((nw - u).choose (k - j) : ℚ) =
      ∑ j ∈ Finset.range (Nat.min u k + 1),
        ((if (k - j) % 2 = 0 then (1 : ℤ) else -1) * (chooseI u j : ℤ) * (chooseI (nw - u) (k - j) : ℤ) : ℚ) := by
    rw [Finset.sum_subset (s₁ := Finset.Icc (k + u - nw) (min u k)) (s₂ := Finset.range (Nat.min u k + 1))]
    · apply Finset.sum_congr rfl
      intro j _
      rw [chooseI_eq, chooseI_eq]
      push_cast
      congr 1
      rcases Nat.even_or_odd (k - j) with h | h
      · simp [h.neg_one_pow, Nat.even_iff.mp h]
      · have h2 : ¬ (k - j) % 2 = 0 := by have := Nat.odd_iff.mp h; omega
        simp [h.neg_one_pow, h2]
    · intro j hj
      simp only [Finset.mem_Icc] at hj
      simp only [Finset.mem_range]
      have : min u k = Nat.min u k := rfl
      omega
    · intro j hj hnot
      simp only [Finset.mem_range] at hj
      simp only [Finset.mem_Icc, not_and_or, not_le] at hnot
      have hlt : nw - u < k - j := by
        rcases hnot with h | h
        · omega
        · exfalso; have : min u k = Nat.min u k := rfl; omega
      rw [Nat.choose_eq_zero_of_lt hlt]
      simp
  rw [hsum]
  have hfold : ∀ (L : List ℚ), L.foldr (· + ·) 0 = L.sum := fun L => rfl
  push_cast
  rw [show ((List.range (Nat.min u k + 1)).map fun j =>
        (if (k - j) % 2 = 0 then (1 : ℤ) else -1) * (chooseI u j : ℤ) * (chooseI (nw - u) (k - j) : ℤ)).foldr
        (· + ·) 0 = ((List.range (Nat.min u k + 1)).map fun j =>
        (if (k - j) % 2 = 0 then (1 : ℤ) else -1) * (chooseI u j : ℤ) * (chooseI (nw - u) (k - j) : ℤ)).sum from rfl,
    list_sum_range]
  push_cast
  rw [chooseI_eq]
  field_simp

/-! ## The coefficient identity and the W0 entry polynomial -/

theorem coeffQ_eq (d : CellData) (bi k : ℕ) (hk : k ≤ d.nw) (he : d.floorExp ≤ 2 * (d.mb bi : ℤ))
    (i j : Fin (d.block bi).order) :
    literalGramCoeffQ d.cell (d.block bi) k i j = (d.coefI bi k i j : ℚ) / 2 ^ d.scaleL bi := by
  have hL1 : 2 * d.fb + d.nw ≤ d.scaleL bi := Nat.le_max_left _ _
  have hL2 : Int.toNat (2 * (d.mb bi : ℤ) - d.floorExp) ≤ d.scaleL bi := Nat.le_max_right _ _
  have hT : ((Int.toNat (2 * (d.mb bi : ℤ) - d.floorExp) : ℕ) : ℤ) = 2 * (d.mb bi : ℤ) - d.floorExp :=
    Int.toNat_of_nonneg (by omega)
  unfold literalGramCoeffQ CellData.coefI
  rw [show d.cell.floorExponent = d.floorExp from rfl, show d.cell.metricBits = d.mbits from rfl,
    show d.cell.factorBits = d.fb from rfl, show d.cell.bernsteinDegree = d.nw from rfl]
  rw [show ((List.range (d.nw + 1)).map fun u => bernI d.nw u k * 2 ^ (d.scaleL bi - 2 * d.fb - d.nw) *
      dotI (lowerRow (d.facL bi u) i) (lowerRow (d.facL bi u) j)).foldr (· + ·) 0 =
      ((List.range (d.nw + 1)).map fun u => bernI d.nw u k * 2 ^ (d.scaleL bi - 2 * d.fb - d.nw) *
      dotI (lowerRow (d.facL bi u) i) (lowerRow (d.facL bi u) j)).sum from rfl, list_sum_range]
  push_cast
  rw [add_div, Finset.sum_div, ← Fin.sum_univ_eq_sum_range (fun u => ((bernI d.nw u k : ℚ) *
      2 ^ (d.scaleL bi - 2 * d.fb - d.nw) *
      (dotI (lowerRow (d.facL bi u) i) (lowerRow (d.facL bi u) j) : ℚ)) / 2 ^ d.scaleL bi)]
  congr 1
  · split_ifs with h0
    · rw [metricGram_eq]
      have h2 : (2 : ℚ) ^ (d.scaleL bi - Int.toNat (2 * (d.mb bi : ℤ) - d.floorExp)) * 2 ^ (2 * d.mb bi) =
          2 ^ d.floorExp * 2 ^ d.scaleL bi := by
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast (n := d.scaleL bi), ← zpow_add₀ (by norm_num),
          ← zpow_add₀ (by norm_num)]
        congr 1
        push_cast [Nat.cast_sub hL2]
        rw [hT]
        ring
      have hL : (2 : ℚ) ^ d.scaleL bi =
          2 ^ (d.scaleL bi - Int.toNat (2 * (d.mb bi : ℤ) - d.floorExp)) * 2 ^ (2 * d.mb bi) / 2 ^ d.floorExp := by
        rw [h2]
        field_simp
      rw [hL]
      field_simp
    · simp
  · apply Finset.sum_congr rfl
    intro u _
    rw [factorGram_eq d bi u (Nat.lt_succ_iff.mp u.isLt), bern_eq d.nw u k (Nat.lt_succ_iff.mp u.isLt) hk]
    have h3 : (2 : ℚ) ^ (d.scaleL bi - 2 * d.fb - d.nw) * (2 ^ (2 * d.fb) * 2 ^ d.nw) = 2 ^ d.scaleL bi := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    rw [← h3]
    field_simp

/-- **The literal W0 entry is the exact polynomial of the integer coefficients.** -/
theorem w0_entry (d : CellData) (bi : ℕ) (he : d.floorExp ≤ 2 * (d.mb bi : ℤ)) (x : ℝ)
    (i j : Fin (d.block bi).order) :
    literalGram d.cell (d.block bi) x i j =
      scalarEval (fun k : Fin (d.nw + 1) => ((mkRat (d.coefI bi k i j) (2 ^ d.scaleL bi) : ℚ) : ℝ)) x := by
  rw [← literalGramPolynomial_eval]
  rw [polynomial_eval_eq_scalarEval_of_natDegree _ d.nw (by
    have := gramPolynomial_natDegree ((2:ℝ)^d.cell.floorExponent) (literalMetric (d.block bi) d.cell.metricBits)
      (fun u : Fin (d.cell.bernsteinDegree+1) => literalFactor (d.block bi) d.cell.factorBits u.val) i j
    exact this)]
  congr 1
  funext k
  rw [← literalGramCoeffQ_cast, coeffQ_eq d bi k (Nat.lt_succ_iff.mp k.isLt) he, Rat.mkRat_eq_div]
  push_cast
  rfl

theorem ofFn_eq_map_range {α : Type*} (n : ℕ) (f : ℕ → α) :
    List.ofFn (fun k : Fin n => f k.val) = (List.range n).map f := by
  apply List.ext_getElem
  · simp
  · intro m h1 h2
    simp

/-- **The W0 entry TM encloses the literal Gram entry.** -/
theorem w0TM_sound {N S B W : ℕ} (hg : Good N S B W) (d : CellData) (bi : ℕ)
    (he : d.floorExp ≤ 2 * (d.mb bi : ℤ)) (i j : Fin (d.block bi).order)
    (hok : (d.w0TM (mkCtx N S B W) bi i j).ok = true) :
    Encl (mkCtx N S B W) (d.w0TM (mkCtx N S B W) bi i j) (fun x => literalGram d.cell (d.block bi) x i j) := by
  let M : Blueprint.CAP.TM d.nw :=
    ⟨fun k => Box.point (mkRat (d.coefI bi k i j) (2 ^ d.scaleL bi)), 0⟩
  have hM : M.Valid (fun x => literalGram d.cell (d.block bi) x i j) := by
    refine ⟨le_refl _, fun k => ((mkRat (d.coefI bi k i j) (2 ^ d.scaleL bi) : ℚ) : ℝ),
      fun k => Box.contains_point _, fun x _ => ?_⟩
    show |literalGram d.cell (d.block bi) x i j - _| ≤ _
    rw [w0_entry d bi he x i j, sub_self, abs_zero]
    simp [M]
  have hEq : ofOldTM (mkCtx N S B W) M = d.w0TM (mkCtx N S B W) bi i j := by
    unfold ofOldTM CellData.w0TM boxList
    rw [show List.ofFn (fun k : Fin (d.nw + 1) => ((M.coeff k).lo, (M.coeff k).hi)) =
        (List.range (d.nw + 1)).map fun k => (mkRat (d.coefI bi k i j) (2 ^ d.scaleL bi),
          mkRat (d.coefI bi k i j) (2 ^ d.scaleL bi)) from
      ofFn_eq_map_range (d.nw + 1) (fun k => (mkRat (d.coefI bi k i j) (2 ^ d.scaleL bi),
          mkRat (d.coefI bi k i j) (2 ^ d.scaleL bi)))]
  have h := ofBoxes_sound hg M hM (hEq ▸ hok)
  rwa [hEq] at h

#print axioms coeffQ_eq
#print axioms w0TM_sound

#print axioms factorGram_eq
#print axioms metricGram_eq
#print axioms bern_eq

end ThomsonCompact.CoeffMap
