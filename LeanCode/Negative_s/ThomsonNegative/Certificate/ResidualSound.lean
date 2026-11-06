import ThomsonNegative.Certificate.ResidualKernel
import ThomsonNegative.Certificate.CoefficientSound
import ThomsonNegative.Certificate.LayoutCheck

/-! Enclosures of all retained target-minus-Gram coefficients. -/
noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Certificate
open ThomsonNegative.Compact.Packed

theorem basis_index_lt (b : Fin 8) (i j : ℕ)
    (hi : i<BasisLayout.rawOrder b.val) (hj : j<BasisLayout.freeOrder b.val) :
    BasisLayout.index b.val i j<BasisData.records.length := by
  have hb := allBelow_sound 8 _ basis_indices_pass b.val b.isLt
  have hrow := allBelow_sound _ _ hb i hi
  have hcol := allBelow_sound _ _ hrow j hj
  simpa only [Nat.blt_eq] using hcol

theorem target_degree_lt (r : ℕ) (hr : r<68) (hz : (TargetData.entry r).2.2 ≠ 0) :
    (TargetData.entry r).1<8 := by
  have h := allBelow_sound 68 _ target_degrees_pass r hr
  simpa only [Bool.or_eq_true,Nat.beq_eq,Nat.blt_eq,hz,false_or] using h

def targetFunction (H : ℕ → ℝ → ℝ) (r : ℕ) (t : ℝ) : ℝ :=
  let d := TargetData.entry r
  qval (d.2.1,d.2.2,3) * H d.1 t

theorem targetRowTM_sound {N S B W : ℕ} (hg : Good N S B W) (H : List TM)
    (h : ℕ → ℝ → ℝ) (hH : ∀ i<8, Encl (mkCtx N S B W) (H.getD i zeroTM) (h i))
    (r : ℕ) (hr : r<68) (hok : (targetRowTM (mkCtx N S B W) H r).ok=true) :
    Encl (mkCtx N S B W) (targetRowTM (mkCtx N S B W) H r) (targetFunction h r) := by
  by_cases hz : (TargetData.entry r).2.2=0
  · have he : targetRowTM (mkCtx N S B W) H r=zeroTM := by
      simp only [targetRowTM,Bool.cond_eq_ite,Nat.beq_eq,hz,if_true]
    rw [he]
    exact zero_sound.congr (fun t _ => by simp [targetFunction,qval,hz])
  · have he : targetRowTM (mkCtx N S B W) H r=
        rationalScale (mkCtx N S B W) (TargetData.entry r).2.1 (TargetData.entry r).2.2 3
          (H.getD (TargetData.entry r).1 zeroTM) := by
      simp only [targetRowTM,Bool.cond_eq_ite,Nat.beq_eq,hz,if_false]
    rw [he] at hok ⊢
    exact rationalScale_sound hg (hH _ (target_degree_lt r hr hz)) _ _ _ hok

theorem residualRowTM_sound {N S B W : ℕ} (hg : Good N S B W)
    (images : List (List TM)) (H : List TM) (image : ℕ → ℕ → ℝ → ℝ) (h : ℕ → ℝ → ℝ)
    (hI : ∀ b<8, ∀ r<68, Encl (mkCtx N S B W) ((images.getD b []).getD r zeroTM) (image b r))
    (hH : ∀ i<8, Encl (mkCtx N S B W) (H.getD i zeroTM) (h i))
    (r : ℕ) (hr : r<68) (hok : (residualRowTM (mkCtx N S B W) images H r).ok=true) :
    Encl (mkCtx N S B W) (residualRowTM (mkCtx N S B W) images H r)
      (fun t => targetFunction h r t - ∑ b ∈ Finset.range 8, image b r t) := by
  have hp := add_ok hok
  have htarget := targetRowTM_sound hg H h hH r hr hp.1
  have himage := refresh_sound hg (sumTM_sound hg _ _ 8 (fun b hb => hI b hb r hr) hp.2)
  have hm := refresh_sound hg (add_sound htarget (neg_sound himage) hok)
  exact hm.congr (fun t _ => by ring)

#print axioms residualRowTM_sound
end ThomsonNegative.Certificate
