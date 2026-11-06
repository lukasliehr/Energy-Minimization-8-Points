import ThomsonNegative.Certificate.MatrixKernel
import ThomsonNegative.Compact.Packed.Comp

/-! One semantic proof for all finite dot products and matrix products. -/
namespace ThomsonNegative.Certificate
open ThomsonNegative.Compact.Packed
open scoped BigOperators

variable {N S B W : ℕ}

theorem sumTM_sound (hg : Good N S B W) (F : ℕ → TM) (f : ℕ → ℝ → ℝ)
    (n : ℕ) (hf : ∀ i < n, Encl (mkCtx N S B W) (F i) (f i))
    (hok : (sumTM (mkCtx N S B W) F n).ok = true) :
    Encl (mkCtx N S B W) (sumTM (mkCtx N S B W) F n)
      (fun t => ∑ i ∈ Finset.range n, f i t) := by
  induction n with
  | zero => simpa [sumTM] using (zero_sound (N := N) (S := S) (B := B) (W := W))
  | succ n ih =>
    have he : sumTM (mkCtx N S B W) F (n+1) =
        add (mkCtx N S B W) (sumTM (mkCtx N S B W) F n) (F n) := rfl
    rw [he] at hok ⊢
    have hp := add_ok hok
    have h := add_sound (ih (fun i hi => hf i (by omega)) hp.1)
      (hf n (by omega)) hok
    simpa only [Finset.sum_range_succ] using h

theorem sumTM_ok (c : Ctx) (F : ℕ → TM) (n : ℕ) :
    (sumTM c F n).ok = true → ∀ i < n, (F i).ok = true := by
  induction n with
  | zero => intro _ i hi; omega
  | succ n ih =>
    intro h i hi
    have hp := add_ok h
    by_cases he : i=n
    · simpa only [he] using hp.2
    · exact ih hp.1 i (by omega)

theorem dotTM_sound (hg : Good N S B W) (F G : ℕ → TM) (f g : ℕ → ℝ → ℝ)
    (n : ℕ) (hf : ∀ i < n, Encl (mkCtx N S B W) (F i) (f i))
    (hG : ∀ i < n, Encl (mkCtx N S B W) (G i) (g i))
    (hok : (dotTM (mkCtx N S B W) F G n).ok = true) :
    Encl (mkCtx N S B W) (dotTM (mkCtx N S B W) F G n)
      (fun t => ∑ i ∈ Finset.range n, f i t * g i t) := by
  have hs : (sumTM (mkCtx N S B W) (fun i => mul (mkCtx N S B W) (F i) (G i)) n).ok = true := hok
  have hall := sumTM_ok _ _ n hs
  apply refresh_sound hg
  exact sumTM_sound hg _ _ n (fun i hi => mul_sound hg (hf i hi) (hG i hi) (hall i hi)) hs

theorem entry_tabulate {rows cols i j : ℕ} (f : ℕ → ℕ → TM)
    (hi : i < rows) (hj : j < cols) : entry (tabulate rows cols f) i j = f i j := by
  simp [entry, tabulate, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi, List.getElem?_range hj]

theorem matmulTM_sound (hg : Good N S B W) (rows inner cols : ℕ)
    (A D : TMMatrix) (a d : ℕ → ℕ → ℝ → ℝ)
    (ha : ∀ i < rows, ∀ j < inner, Encl (mkCtx N S B W) (entry A i j) (a i j))
    (hd : ∀ i < inner, ∀ j < cols, Encl (mkCtx N S B W) (entry D i j) (d i j))
    (hok : ∀ i < rows, ∀ j < cols,
      (entry (matmulTM (mkCtx N S B W) rows inner cols A D) i j).ok = true) :
    ∀ i < rows, ∀ j < cols,
      Encl (mkCtx N S B W) (entry (matmulTM (mkCtx N S B W) rows inner cols A D) i j)
        (fun t => ∑ k ∈ Finset.range inner, a i k t * d k j t) := by
  intro i hi j hj
  have he : entry (matmulTM (mkCtx N S B W) rows inner cols A D) i j =
      dotTM (mkCtx N S B W) (fun k => entry A i k) (fun k => entry D k j) inner :=
    entry_tabulate _ hi hj
  rw [he]
  exact dotTM_sound hg _ _ _ _ inner (ha i hi) (fun k hk => hd k hk j hj)
    (by simpa only [he] using hok i hi j hj)

#print axioms sumTM_sound
#print axioms dotTM_sound
#print axioms matmulTM_sound
end ThomsonNegative.Certificate
