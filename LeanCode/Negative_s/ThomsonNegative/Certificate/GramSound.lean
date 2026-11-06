import ThomsonNegative.Certificate.FactorSound
import ThomsonNegative.Certificate.MetricSound
import ThomsonNegative.Reduction.CorrectionFloor

/-! The same square-factor data prove positivity and coefficient enclosures. -/
noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Certificate
open ThomsonNegative.Compact.Packed

def bernsteinWeight (degree r : ℕ) (t : ℝ) : ℝ :=
  (degree.choose r:ℝ) * ((1+t)/2)^r * ((1-t)/2)^(degree-r)

def gramValue (degree count : ℕ) (K : FactorData) (F : ℕ → FactorData)
    (t : ℝ) (i j : ℕ) : ℝ :=
  (1/2:ℝ) * K.square i j +
    ∑ r ∈ Finset.range count, bernsteinWeight degree r t * (F r).square i j

variable {N S B W : ℕ}

theorem blockEntryTM_sound (hg : Good N S B W) {T : TM} {x : ℝ → ℝ}
    (hT : Encl (mkCtx N S B W) T x) (degree count : ℕ) (K : FactorData)
    (F : ℕ → FactorData) (i j : ℕ)
    (hok : (blockEntryTM (mkCtx N S B W) degree count T K F i j).ok=true) :
    Encl (mkCtx N S B W) (blockEntryTM (mkCtx N S B W) degree count T K F i j)
      (fun t => gramValue degree count K F (x t) i j) := by
  have hparts := add_ok hok
  have hf := mul_ok hparts.1
  have hhalf := rationalTM_sound hg (false,1,2) hf.1
  have hK := squareEntryTM_sound hg K i j hf.2
  have hfloor := mul_sound hg hhalf hK hparts.1
  have hs : Encl (mkCtx N S B W)
      (sumTM (mkCtx N S B W) (fun r => mul (mkCtx N S B W)
        (bernsteinTM (mkCtx N S B W) degree r T) (squareEntryTM (mkCtx N S B W) (F r) i j)) count)
      (fun t => ∑ r ∈ Finset.range count, bernsteinWeight degree r (x t) * (F r).square i j) := by
    apply sumTM_sound hg _ _ count _ hparts.2
    intro r hr
    have hok' := sumTM_ok _ _ count hparts.2 r hr
    have hrow := mul_ok hok'
    exact mul_sound hg (bernsteinTM_sound hg hT degree r hrow.1)
      (squareEntryTM_sound hg (F r) i j hrow.2) hok'
  have h := refresh_sound hg (add_sound hfloor hs hok)
  exact h.congr (fun t _ => by simp only [qval,gramValue]; norm_num)

theorem factor_square_psd (n : ℕ) (F : FactorData) :
    Matrix.PosSemidef (fun i j : Fin n => F.square i.val j.val) := by
  let L : Matrix (Fin n) (Fin F.order) ℝ := fun i j => F.eval i.val j.val
  have h := Reduction.factor_gram_psd L
  convert h using 1
  refine Iff.of_eq (congrArg Matrix.PosSemidef ?_)
  ext i j
  simp only [L,FactorData.square]
  exact (Fin.sum_univ_eq_sum_range (fun k => F.eval i.val k * F.eval j.val k) F.order).symm

theorem gramValue_psd (n degree count : ℕ) (K : FactorData) (F : ℕ → FactorData)
    (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    Matrix.PosSemidef (fun i j : Fin n => gramValue degree count K F t i.val j.val) := by
  have hfloor := (factor_square_psd n K).smul (show (0:ℝ) ≤ 1/2 by norm_num)
  have hs : Matrix.PosSemidef (∑ r ∈ Finset.range count,
      bernsteinWeight degree r t • (fun i j : Fin n => (F r).square i.val j.val)) := by
    apply Matrix.posSemidef_sum
    intro r hr
    exact (factor_square_psd n (F r)).smul (Reduction.bernstein_weight_nonneg degree r t ht)
  have hfun : (fun i j : Fin n => gramValue degree count K F t i.val j.val) =
      (1/2:ℝ) • (fun i j : Fin n => K.square i.val j.val) + ∑ r ∈ Finset.range count,
        bernsteinWeight degree r t • (fun i j : Fin n => (F r).square i.val j.val) := by
    funext i j
    simp [gramValue,Finset.sum_apply,smul_eq_mul]
  rw [hfun]
  exact hfloor.add hs

#print axioms blockEntryTM_sound
#print axioms gramValue_psd
end ThomsonNegative.Certificate
