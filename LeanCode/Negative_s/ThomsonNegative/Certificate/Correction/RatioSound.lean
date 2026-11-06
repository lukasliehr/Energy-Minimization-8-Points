import ThomsonNegative.Certificate.Correction.RatioKernel
import ThomsonNegative.Certificate.Correction.RecordSound

noncomputable section
namespace ThomsonNegative.Certificate.Correction
open ThomsonNegative.Compact.Packed
open ThomsonNegative.Structure.Exact (recCoeffs)
local notation "seval" => ThomsonNegative.Structure.Packed.evalZ

variable {N S B W : ℕ}

theorem denominatorInverse_sound (hg : Good N S B W)
    {A : TM} {a : ℝ → ℝ} (ha : Encl (mkCtx N S B W) A a)
    (denominator normalizer : ℕ)
    (hok : (denominatorInverse (mkCtx N S B W) A denominator normalizer).ok=true) :
    Encl (mkCtx N S B W) (denominatorInverse (mkCtx N S B W) A denominator normalizer)
      (fun t => (seval (recCoeffs denominator) (a t)/(normalizer:ℝ))⁻¹) := by
  have hi := invN_sound hg
    (recordTM_sound hg ha denominator normalizer ((mul_ok (recip_ok hok).2).2)) 9 1 hok
  exact hi.2

/-- The normalizer only rescales a numerator and its denominator. It is a
positive integer chosen to keep the order-zero model in range. -/
theorem ratioTM_sound (hg : Good N S B W)
    {A inverse : TM} {a : ℝ → ℝ} (ha : Encl (mkCtx N S B W) A a)
    (numerator denominator normalizer inputScale : ℕ)
    (hn : normalizer≠0)
    (hi : Encl (mkCtx N S B W) inverse
      (fun t => (seval (recCoeffs denominator) (a t)/(normalizer:ℝ))⁻¹))
    (hok : (ratioTM (mkCtx N S B W) A inverse numerator normalizer inputScale).ok=true) :
    Encl (mkCtx N S B W)
      (ratioTM (mkCtx N S B W) A inverse numerator normalizer inputScale)
      (fun t => (seval (recCoeffs numerator) (a t)/(inputScale:ℝ)) /
        seval (recCoeffs denominator) (a t)) := by
  have hm := mul_ok hok
  have hp := recordTM_sound hg ha numerator (normalizer*inputScale) hm.1
  have h := refresh_sound hg (mul_sound hg hp hi hok)
  apply h.congr
  intro t ht
  have hn' : (normalizer:ℝ)≠0 := Nat.cast_ne_zero.mpr hn
  simp only [Nat.cast_mul,div_eq_mul_inv,mul_inv_rev,inv_inv]
  calc
    _ = (normalizer:ℝ)⁻¹*(normalizer:ℝ)*
      (seval (recCoeffs numerator) (a t)*(inputScale:ℝ)⁻¹*
        (seval (recCoeffs denominator) (a t))⁻¹) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hn',one_mul]

#print axioms denominatorInverse_sound
#print axioms ratioTM_sound
end ThomsonNegative.Certificate.Correction
