import ThomsonNegative.Certificate.CoefficientSound

/-! Matrix multiplication and the raw coefficient map compose uniformly. -/
noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Certificate
open ThomsonNegative.Compact.Packed
open Bridges

def multiplyFunction (n : ℕ) (a b : ℕ → ℕ → ℝ → ℝ) (i j : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, a i k t * b k j t

def imageFunction (block row : ℕ) (basis gram : ℕ → ℕ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (RawData.size block), ∑ j ∈ Finset.range (RawData.size block),
    rawCoefficient block (BasisLayout.fullRow row) i j *
      multiplyFunction (BasisLayout.freeOrder block)
        (multiplyFunction (BasisLayout.freeOrder block) basis gram)
        (fun u v => basis v u) i j t

lemma layout_raw_size (b : Fin 8) : RawData.size b.val=BasisLayout.rawOrder b.val := by
  fin_cases b <;> rfl

theorem blockImage_sound {N S B W : ℕ} (hg : Good N S B W)
    (models : List TM) (b : Fin 8) (G : TMMatrix) (basis gram : ℕ → ℕ → ℝ → ℝ)
    (hB : ∀ i<BasisLayout.rawOrder b.val, ∀ j<BasisLayout.freeOrder b.val,
      Encl (mkCtx N S B W) (entry (basisMatrix models b.val) i j) (basis i j))
    (hG : ∀ i<BasisLayout.freeOrder b.val, ∀ j<BasisLayout.freeOrder b.val,
      Encl (mkCtx N S B W) (entry G i j) (gram i j))
    (hok : (blockImage (mkCtx N S B W) models b.val G).ok=true)
    (r : ℕ) (hr : r<68) :
    Encl (mkCtx N S B W)
      ((blockImage (mkCtx N S B W) models b.val G).coefficients.getD r zeroTM)
      (imageFunction b.val r basis gram) := by
  let c := mkCtx N S B W
  let m := BasisLayout.rawOrder b.val
  let n := BasisLayout.freeOrder b.val
  let B := basisMatrix models b.val
  let BG := matmulTM c m n n B G
  let raw := matmulTM c m n m BG (transposeTM m n B)
  have hh : allOk BG=true ∧ allOk raw=true ∧
      ((List.range 68).map (fun r => rawRowTM c b.val (BasisLayout.fullRow r) raw)).all TM.ok=true := by
    have he : (allOk BG && allOk raw &&
      ((List.range 68).map (fun r => rawRowTM c b.val (BasisLayout.fullRow r) raw)).all TM.ok)=true := hok
    simp only [Bool.and_eq_true] at he
    exact ⟨he.1.1,he.1.2,he.2⟩
  have hBG := matmulTM_sound hg m n n B G basis gram hB hG
    (fun i _ j _ => allOk_entry hh.1 i j)
  have hBt (i : ℕ) (hi : i<n) (j : ℕ) (hj : j < m) :
      Encl c (entry (transposeTM m n B) i j) (basis j i) := by
    rw [show entry (transposeTM m n B) i j=entry B j i from entry_tabulate _ hi hj]
    exact hB j hj i hi
  have hraw := matmulTM_sound hg m n m BG (transposeTM m n B)
    (multiplyFunction n basis gram) (fun i j => basis j i) hBG hBt
    (fun i _ j _ => allOk_entry hh.2.1 i j)
  have he : ((blockImage c models b.val G).coefficients.getD r zeroTM)=
      rawRowTM c b.val (BasisLayout.fullRow r) raw := by
    change ((List.range 68).map (fun r => rawRowTM c b.val (BasisLayout.fullRow r) raw)).getD r zeroTM=_
    simp [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hr]
  rw [he]
  apply rawRowTM_sound hg b.val (BasisLayout.fullRow r) raw
    (multiplyFunction n (multiplyFunction n basis gram) (fun i j => basis j i))
  · intro i hi j hj
    rw [layout_raw_size b] at hi hj
    exact hraw i hi j hj
  · have h := list_all_getD TM.ok _ zeroTM rfl hh.2.2 r
    change ((blockImage c models b.val G).coefficients.getD r zeroTM).ok=true at h
    simpa only [he] using h

#print axioms blockImage_sound
end ThomsonNegative.Certificate
