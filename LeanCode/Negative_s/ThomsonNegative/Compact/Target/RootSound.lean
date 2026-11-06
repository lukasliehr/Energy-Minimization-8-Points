import ThomsonNegative.Compact.Target.SeriesSound
import ThomsonNegative.Analytic.LipschitzTransfer

noncomputable section
namespace ThomsonNegative.Compact.Target
open ThomsonNegative.Compact.Packed
variable {N S B W : ℕ}

theorem ir2TM_sound (hg : Good N S B W) (r2 : ℕ) (hok : (ir2TM (mkCtx N S B W) r2).ok = true) :
    Encl (mkCtx N S B W) (ir2TM (mkCtx N S B W) r2) (fun _ => (Real.sqrt 2)⁻¹) := by
  have hokE : (ir2TM (mkCtx N S B W) r2).ok = ((constTM (mkCtx N S B W) false r2 1).ok && Nat.ble 1 S &&
      Nat.ble (r2 * r2) (2 ^ (2 * S - 1)) && Nat.blt (2 ^ (2 * S - 1)) ((r2 + 1) * (r2 + 1))) := rfl
  rw [hokE] at hok
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hok
  obtain ⟨⟨⟨hc, hS⟩, h1⟩, h2⟩ := hok
  have hD : (0 : ℝ) < 2 ^ S := by positivity
  have hX : ((2 ^ (2 * S - 1) : ℕ) : ℝ) = (2 ^ S) ^ 2 / 2 := by
    rw [show (2 : ℝ) ^ S = 2 ^ S from rfl, ← pow_mul, show S * 2 = (2 * S - 1) + 1 by omega, pow_succ]
    push_cast; ring
  have hkap : (Real.sqrt 2)⁻¹ = Real.sqrt 2⁻¹ := (Real.sqrt_inv 2).symm
  have hu0 : (0 : ℝ) ≤ (r2 : ℝ) / 2 ^ S := by positivity
  have hu2 : ((r2 : ℝ) / 2 ^ S) ^ 2 ≤ 2⁻¹ := by
    have : ((r2 * r2 : ℕ) : ℝ) ≤ ((2 ^ (2 * S - 1) : ℕ) : ℝ) := by exact_mod_cast h1
    rw [hX] at this
    push_cast at this
    rw [div_pow, div_le_iff₀ (by positivity)]
    nlinarith
  have hv2 : 2⁻¹ < (((r2 : ℝ) + 1) / 2 ^ S) ^ 2 := by
    have : ((2 ^ (2 * S - 1) : ℕ) : ℝ) < (((r2 + 1) * (r2 + 1) : ℕ) : ℝ) := by exact_mod_cast h2
    rw [hX] at this
    push_cast at this
    rw [div_pow, lt_div_iff₀ (by positivity)]
    nlinarith
  have hlo : (r2 : ℝ) / 2 ^ S ≤ (Real.sqrt 2)⁻¹ := by
    rw [hkap]
    calc (r2 : ℝ) / 2 ^ S = Real.sqrt (((r2 : ℝ) / 2 ^ S) ^ 2) := (Real.sqrt_sq hu0).symm
      _ ≤ Real.sqrt 2⁻¹ := Real.sqrt_le_sqrt hu2
  have hhi : (Real.sqrt 2)⁻¹ < ((r2 : ℝ) + 1) / 2 ^ S := by
    rw [hkap]
    calc Real.sqrt 2⁻¹ < Real.sqrt ((((r2 : ℝ) + 1) / 2 ^ S) ^ 2) := Real.sqrt_lt_sqrt (by norm_num) hv2
      _ = ((r2 : ℝ) + 1) / 2 ^ S := Real.sqrt_sq (by positivity)
  have hpos : (0 : ℝ) < 1 / 2 ^ S := by positivity
  refine (constTM_sound hg false r2 1 ((Real.sqrt 2)⁻¹) ?_ ?_).of_fields rfl rfl rfl rfl
  · simp only [Bool.false_eq_true, if_false, Nat.cast_one]
    rw [abs_le]
    constructor
    · linarith
    · rw [add_div] at hhi; linarith
  · exact hc


theorem addC_eok (hg : Good N S B W) {A : TM} {f : ℝ → ℝ}
    (hA : EOK (mkCtx N S B W) A f) (ng : Bool) (mag err : ℕ) (z : ℝ)
    (hz : |z-(if ng then -(mag:ℝ) else mag)/2^S| ≤ (err:ℝ)/2^S) :
    EOK (mkCtx N S B W) (addC (mkCtx N S B W) ng mag err A) (fun t => f t+z) := by
  intro hok
  exact addC_sound (hA (addC_ok hok)) ng mag err z hz hok hg

theorem oneSub_eok (hg : Good N S B W) {A : TM} {f : ℝ → ℝ}
    (hA : EOK (mkCtx N S B W) A f) :
    EOK (mkCtx N S B W) (refresh (mkCtx N S B W)
      (addC (mkCtx N S B W) false (mkCtx N S B W).twoS 0 (neg (mkCtx N S B W) A)))
      (fun t => 1-f t) := by
  apply (refresh_eok hg (addC_eok hg (neg_eok hA rfl) false (2^S) 0 1 (by simp))).congr
  intro t _; ring

theorem proposalTube_sound (hg : Good N S B W) {P : TM} {p : ℝ → ℝ}
    (hP : Encl (mkCtx N S B W) P p)
    (hok : proposalTubeOK (mkCtx N S B W) P = true) :
    ∀ t ∈ Set.Icc (-1:ℝ) 1, p t ∈ Set.Ioo (5/16:ℝ) (1/3) := by
  have hb : (proposalTube (mkCtx N S B W) P).ok = true ∧
      Nat.mul 96 (rangeX (mkCtx N S B W) (proposalTube (mkCtx N S B W) P)) < 2^S := by
    simpa only [proposalTubeOK,Bool.and_eq_true,Nat.blt_eq,mk_twoS] using hok
  have hc := ratMag_err (N:=N) (S:=S) (B:=B) (W:=W) (true,31,96)
  have hh := addC_sound hP true (ratMag (mkCtx N S B W) 31 96) 1 (-(31/96:ℝ))
    (by simpa [qval] using hc) hb.1 hg
  have hr := rangeX_sound hg hh
  have hpos : (0:ℝ)<2^S := by positivity
  have hb' : (96:ℝ)*(rangeX (mkCtx N S B W) (proposalTube (mkCtx N S B W) P):ℝ) < 2^S := by
    exact_mod_cast hb.2
  have hsmall : (rangeX (mkCtx N S B W) (proposalTube (mkCtx N S B W) P):ℝ)/2^S < 1/96 := by
    apply (div_lt_iff₀ hpos).2
    linarith
  intro t ht
  have h := (hr t ht).trans_lt hsmall
  rw [abs_lt] at h
  constructor <;> linarith

/-- On cell endpoints outside the requested open q interval, use the proposed
height itself. This keeps the generic packed semantics on all of `[-1,1]`. -/
def extendedHeight (q p : ℝ → ℝ) (t : ℝ) : ℝ :=
  if 0 < q t ∧ q t < 1 then aStar (2*q t-2) else p t

theorem extendedHeight_interior (q p : ℝ → ℝ) (t : ℝ)
    (hq : q t ∈ Set.Ioo (0:ℝ) 1) :
    extendedHeight q p t = aStar (2*q t-2) := by
  simp [extendedHeight,hq.1,hq.2]

theorem extendedHeight_range (q p : ℝ → ℝ)
    (hp : ∀ t ∈ Set.Icc (-1:ℝ) 1, p t ∈ Set.Ioo (5/16:ℝ) (1/3)) :
    ∀ t ∈ Set.Icc (-1:ℝ) 1, extendedHeight q p t ∈ Set.Ioo (5/16:ℝ) (1/3) := by
  intro t ht
  by_cases hq : 0<q t ∧ q t<1
  · simpa [extendedHeight,hq] using aStar_negative_range (q t) ⟨hq.1,hq.2.le⟩
  · simpa [extendedHeight,hq] using hp t ht

theorem extendedHeight_error (hg : Good N S B W) {R : TM} {q p r : ℝ → ℝ}
    (hR : Encl (mkCtx N S B W) R r)
    (hp : ∀ t ∈ Set.Icc (-1:ℝ) 1, p t ∈ Set.Ioo (5/16:ℝ) (1/3))
    (hr : ∀ t ∈ Set.Icc (-1:ℝ) 1, 0<q t ∧ q t<1 → r t=seriesRoot (q t) (p t)) :
    ∀ t ∈ Set.Icc (-1:ℝ) 1,
      |extendedHeight q p t-p t| ≤ (divUp (rangeX (mkCtx N S B W) R) 96:ℝ)/2^S := by
  have hrange := rangeX_sound hg hR
  have hceil := le_ceil_div (rangeX (mkCtx N S B W) R) 96 (by norm_num)
  have hscale : (0:ℝ)<2^S := by positivity
  intro t ht
  by_cases hq : 0<q t ∧ q t<1
  · rw [extendedHeight,if_pos hq]
    have h := aStar_residual_error (q t) (p t) ⟨hq.1,hq.2.le⟩
      ⟨by linarith [(hp t ht).1],(hp t ht).2.le⟩
    rw [← hr t ht hq] at h
    calc
      _ ≤ |r t|/96 := h
      _ ≤ ((rangeX (mkCtx N S B W) R:ℝ)/2^S)/96 := div_le_div_of_nonneg_right (hrange t ht) (by norm_num)
      _ = ((rangeX (mkCtx N S B W) R:ℝ)/96)/2^S := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hceil hscale.le
  · simp only [extendedHeight,if_neg hq,sub_self,abs_zero]
    positivity

theorem extendedHeight_sound (hg : Good N S B W) {P R : TM} {q p r : ℝ → ℝ}
    (hP : Encl (mkCtx N S B W) P p) (hR : Encl (mkCtx N S B W) R r)
    (hp : ∀ t ∈ Set.Icc (-1:ℝ) 1, p t ∈ Set.Ioo (5/16:ℝ) (1/3))
    (hr : ∀ t ∈ Set.Icc (-1:ℝ) 1, 0<q t ∧ q t<1 → r t=seriesRoot (q t) (p t)) :
    Encl (mkCtx N S B W) (widen P (divUp (rangeX (mkCtx N S B W) R) 96))
      (extendedHeight q p) :=
  widen_sound _ hP (extendedHeight_error hg hR hp hr)

#print axioms ir2TM_sound
#print axioms proposalTube_sound
#print axioms extendedHeight_sound
end ThomsonNegative.Compact.Target
