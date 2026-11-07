import ThomsonCompact.Packed.SoundMul
import ThomsonCompact.Packed.PAbs

/-!
# Soundness of scalar multiplication, reciprocal-from-witness and data inputs
-/

namespace ThomsonCompact.Packed
open Nat

variable {N S B W : ℕ}

theorem take_append_left {α : Type*} : ∀ (L M : List α) (n : ℕ), L.length = n → (L ++ M).take n = L
  | [], M, n, h => by subst h; simp
  | x :: L, M, n, h => by
    subst h
    simp [take_append_left L M L.length rfl]

theorem smul_err_real {D σ F P s0 q dq sA eA Zc c1 m : ℝ} (hD : 0 < D)
    (hF : |F - P / D| ≤ eA / D) (hP : |P| ≤ sA) (hs0 : |s0| = q) (hσ : |σ - s0 / D| ≤ dq / D)
    (heA : 0 ≤ eA) (hround : |s0 * P - D * Zc| ≤ m * D) (hc1 : (q * eA + dq * (sA + eA)) / D ≤ c1) :
    |σ * F - Zc / D| ≤ (c1 + m) / D := by
  have hDD : 0 < D * D := by positivity
  have hσa : |σ| ≤ q / D + dq / D := by
    have h1 : |s0 / D| = q / D := by rw [abs_div, hs0, abs_of_pos hD]
    calc |σ| = |s0 / D + (σ - s0 / D)| := by ring_nf
      _ ≤ |s0 / D| + |σ - s0 / D| := abs_add_le _ _
      _ ≤ q / D + dq / D := by rw [h1]; linarith
  have key : σ * F - Zc / D = σ * (F - P / D) + (σ - s0 / D) * (P / D) + (s0 * P - D * Zc) / (D * D) := by
    field_simp; ring
  have b1 : |σ * (F - P / D)| ≤ (q / D + dq / D) * (eA / D) := by
    rw [abs_mul]; exact mul_le_mul hσa hF (abs_nonneg _) ((abs_nonneg σ).trans hσa)
  have b2 : |(σ - s0 / D) * (P / D)| ≤ dq / D * (sA / D) := by
    rw [abs_mul, abs_div, abs_of_pos hD]
    exact mul_le_mul hσ (div_le_div_of_nonneg_right hP hD.le) (by positivity)
      ((abs_nonneg _).trans hσ)
  have b3 : |(s0 * P - D * Zc) / (D * D)| ≤ m / D := by
    rw [abs_div, abs_of_pos hDD, div_le_div_iff₀ hDD hD]
    nlinarith [abs_nonneg (s0 * P - D * Zc)]
  have b4 : (q / D + dq / D) * (eA / D) + dq / D * (sA / D) = (q * eA + dq * (sA + eA)) / D / D := by
    field_simp; ring
  have b5 : (q * eA + dq * (sA + eA)) / D / D ≤ c1 / D := div_le_div_of_nonneg_right hc1 hD.le
  rw [key]
  calc |σ * (F - P / D) + (σ - s0 / D) * (P / D) + (s0 * P - D * Zc) / (D * D)|
      ≤ |σ * (F - P / D)| + |(σ - s0 / D) * (P / D)| + |(s0 * P - D * Zc) / (D * D)| := abs_add_three _ _ _
    _ ≤ c1 / D + m / D := by linarith
    _ = (c1 + m) / D := by ring

/-- Scalar multiplication encloses `σ f` for every `σ` within `dq·2^-S` of `±q·2^-S`. -/
theorem smul_sound (hg : Good N S B W) {A : TM} {f : ℝ → ℝ} (hA : Encl (mkCtx N S B W) A f)
    (ng : Bool) (q dq : ℕ) (σ : ℝ) (hσ : |σ - (if ng then -(q : ℝ) else q) / 2 ^ S| ≤ (dq : ℝ) / 2 ^ S)
    (hok : (smul (mkCtx N S B W) ng q dq A).ok = true) :
    Encl (mkCtx N S B W) (smul (mkCtx N S B W) ng q dq A) (fun t => σ * f t) := by
  obtain ⟨cs, al, hR, hf⟩ := hA
  have hW1 := hg.W1
  have hW0 : 0 < W := by omega
  have hokE : (smul (mkCtx N S B W) ng q dq A).ok =
      (A.ok && Nat.blt q (2 ^ B) && Nat.blt (smul (mkCtx N S B W) ng q dq A).s (2 ^ B)) := rfl
  rw [hokE] at hok
  simp only [Bool.and_eq_true, Nat.blt_eq] at hok
  obtain ⟨⟨_, hq⟩, hs⟩ := hok
  have hl : cs.length = N + 1 := hR.lcs
  have hla : al.length = N + 1 := hR.lal
  have hsA := hR.sB
  simp only [mk_B] at hsA
  set L := scaleL (q : ℤ) cs with hL
  set Λ := scaleL q al with hΛ
  have hLlen : L.length = N + 1 := by rw [hL, length_scaleL, hl]
  have hΛlen : Λ.length = N + 1 := by rw [hΛ, length_scaleL, hla]
  have hdomL : Dom L Λ := hR.dom.scaleL (x := (q : ℤ)) (y := q) (by simp)
  have hΛsum : Λ.sum = q * A.s := by rw [hΛ, sum_scaleL_nat, hR.hs]
  have hqs : q * A.s < 2 ^ (2 * B) := by
    rw [two_mul, pow_add]; exact Nat.mul_lt_mul_of_lt_of_lt hq hsA
  set z := L ++ List.replicate N 0 with hz
  have hzlen : z.length = 2 * N + 1 := by rw [hz, List.length_append, hLlen, List.length_replicate]; omega
  have hzb : ∀ x ∈ z, |x| < 2 ^ (2 * B) := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have h1 := hdomL.abs_le_sum hx
      have h2 : ((Λ.sum : ℕ) : ℤ) < 2 ^ (2 * B) := by rw [hΛsum]; exact_mod_cast hqs
      linarith
    · rw [List.eq_of_mem_replicate hx]; simp
  have hV : ((A.v * q : ℕ) : ℤ) % 2 ^ (W * (2 * N + 1)) = horner (2 ^ W : ℤ) z % 2 ^ (W * (2 * N + 1)) := by
    have hv := hR.hv
    simp only [mk_W, mk_K] at hv
    push_cast
    rw [Int.mul_emod, hv, Int.emod_emod, ← Int.mul_emod, hz, horner_append_zeros, hL, horner_scaleL, mul_comm]
  have hv := round_signed hg z hzlen hzb (A.v * q) hV
  rw [hz, take_append_left L _ (N + 1) hLlen] at hv
  set csR := L.map (fun x => x / 2 ^ S) with hcsR
  -- magnitudes
  have hΛb : ∀ d ∈ Λ, d < 2 ^ (2 * B) := fun d hd => (mem_le_sum hd).trans_lt (hΛsum ▸ hqs)
  have ha := round_abs hg Λ hΛlen hΛb
  have hAa : A.a * q = Nat.ofDigits (2 ^ W) Λ := by
    rw [hR.ha, hΛ, ofDigits_scaleL, mul_comm]; rfl
  set alR := Λ.map (fun g => (g + (2 ^ S - 1)) / 2 ^ S) with halR
  have hsumR : alR.sum ≤ q * A.s := (sum_map_ceil_le S Λ).trans hΛsum.le
  have hmodR : Nat.ofDigits (2 ^ W) alR % (2 ^ W - 1) = alR.sum :=
    ofDigits_mod_pred (by have := hg.BW; omega) alR (by have := hg.pow_lt; omega)
  have haR : (smul (mkCtx N S B W) ng q dq A).a = Nat.ofDigits (2 ^ W) alR := by
    show (((A.a * q) + (mkCtx N S B W).ceilAdd) &&& (mkCtx N S B W).rmask) >>> (mkCtx N S B W).S = _
    rw [hAa]; exact ha
  have hsR : (smul (mkCtx N S B W) ng q dq A).s = alR.sum := by
    show (smul (mkCtx N S B W) ng q dq A).a % (mkCtx N S B W).modW = _
    rw [haR, mk_modW, hmodR]
  have hdomR : Dom csR alR := by
    have := dom_round S hdomL (N + 1)
    rwa [List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at this
  -- the signed result
  set vR := ((((((A.v * q + (mkCtx N S B W).biasP) &&& (mkCtx N S B W).maskK) &&& (mkCtx N S B W).rmask) >>>
    (mkCtx N S B W).S) + (mkCtx N S B W).unb) &&& (mkCtx N S B W).maskK) with hvR
  have hvRlt : vR ≤ 2 ^ (W * (2 * N + 1)) := by
    rw [hvR, mk_maskK, Nat.and_two_pow_sub_one_eq_mod]; exact (Nat.mod_lt _ (Nat.two_pow_pos _)).le
  refine ⟨if ng then csR.map (fun x => -x) else csR, alR, ⟨?_, ?_, ?_, haR, ?_, hsR, hsR ▸ hs⟩, ?_⟩
  · cases ng <;> simp [hcsR, hLlen]
  · rw [halR, List.length_map, hΛlen]; rfl
  · show (((cond ng ((2 ^ (W * (2 * N + 1)) - vR) &&& (2 ^ (W * (2 * N + 1)) - 1)) vR) : ℕ) : ℤ) = _
    cases ng
    · simp only [cond_false, Bool.false_eq_true, if_false]; exact hv
    · simp only [cond_true, if_true]
      rw [toZ_mod_mask, Nat.cast_sub hvRlt, mk_W, mk_K, horner_neg]
      rw [show ((2 ^ (W * (2 * N + 1)) : ℕ) : ℤ) - (vR : ℤ) = -(vR : ℤ) + 2 ^ (W * (2 * N + 1)) * 1 by
        push_cast; ring, Int.add_mul_emod_self_left, hv, neg_emod_emod]
  · cases ng
    · simpa using hdomR
    · simpa using hdomR.neg
  · intro t ht
    have hta : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
    have hD : (0 : ℝ) < 2 ^ S := by positivity
    have hF := hf t ht
    simp only [mk_S] at hF
    have hP := abs_evalZ_le_s hR t hta
    have hround := eval_round S t hta L
    rw [hLlen] at hround
    have hLe : evalZ L t = (q : ℝ) * evalZ cs t := by rw [hL, evalZ_scaleL]; push_cast; ring
    have hcd := le_cdiv S (q * A.e + dq * (A.s + A.e))
    push_cast at hcd hround
    show |σ * f t - evalZ (if ng then csR.map (fun x => -x) else csR) t / 2 ^ S| ≤
      ((cdiv S (q * A.e + dq * (A.s + A.e)) + (N + 1) : ℕ) : ℝ) / 2 ^ S
    push_cast
    cases ng
    · simp only [Bool.false_eq_true, if_false] at hσ ⊢
      refine smul_err_real hD hF hP (by simp) hσ (by positivity) ?_ hcd
      rw [← hLe]; exact hround
    · simp only [if_true] at hσ ⊢
      rw [evalZ_neg, show -evalZ csR t / 2 ^ S = (-evalZ csR t) / 2 ^ S by ring]
      refine smul_err_real hD hF hP (by simp) hσ (by positivity) ?_ hcd
      rw [show -(q : ℝ) * evalZ cs t - 2 ^ S * -evalZ csR t = -(evalZ L t - 2 ^ S * evalZ csR t) by
        rw [hLe]; ring, abs_neg]
      exact hround

/-! ## Exact range bound -/

/-- The exact range bound `rangeX` (decoded `Σ|cₖ| + e`) bounds `|f|` on `[-1,1]`. -/
theorem rangeX_sound (hg : Good N S B W) {T : TM} {f : ℝ → ℝ} (h : Encl (mkCtx N S B W) T f) :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1, |f t| ≤ (rangeX (mkCtx N S B W) T : ℝ) / 2 ^ S := by
  obtain ⟨cs, al, hR, hf⟩ := h
  have hrx := hR.rangeX_eq hg
  intro t ht
  have hta : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
  have h1 := hf t ht
  simp only [mk_S] at h1
  have hD : (0 : ℝ) < 2 ^ S := by positivity
  have h3 : ∀ l : List ℤ, ((l.map (Int.cast : ℤ → ℝ)).map abs).sum = (((l.map Int.natAbs).sum : ℕ) : ℝ) := by
    intro l
    induction l with
    | nil => simp
    | cons z zs ih =>
      simp only [List.map_cons, List.sum_cons, Nat.cast_add]
      rw [ih]
      have hz : |(z : ℝ)| = ((z.natAbs : ℕ) : ℝ) := by
        rw [← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
      rw [hz]
  have hp : |evalZ cs t| ≤ (((cs.map Int.natAbs).sum : ℕ) : ℝ) := by
    rw [evalZ, ← h3 cs]; exact abs_horner_le t hta _
  have hp' : |evalZ cs t / 2 ^ S| ≤ (((cs.map Int.natAbs).sum : ℕ) : ℝ) / 2 ^ S := by
    rw [abs_div, abs_of_pos hD]; exact div_le_div_of_nonneg_right hp hD.le
  rw [hrx]
  push_cast
  calc |f t| ≤ |f t - evalZ cs t / 2 ^ S| + |evalZ cs t / 2 ^ S| := by
        have := abs_sub_abs_le_abs_sub (f t) (evalZ cs t / 2 ^ S); linarith
    _ ≤ (T.e : ℝ) / 2 ^ S + (((cs.map Int.natAbs).sum : ℕ) : ℝ) / 2 ^ S := add_le_add h1 hp'
    _ = _ := by ring

/-! ## Reciprocal from a supplied witness -/

theorem recip_err_real {a b ε sR : ℝ} (hab : |1 - a * b| ≤ ε) (hε : ε < 1 / 2) (ha : |a| ≤ sR) :
    b ≠ 0 ∧ |b⁻¹ - a| ≤ ε * sR / (1 - ε) := by
  have h0 : 0 ≤ ε := (abs_nonneg _).trans hab
  have h1 : 1 - ε ≤ |a * b| := by
    have := abs_sub_abs_le_abs_sub 1 (a * b)
    rw [abs_one] at this
    linarith
  have hab0 : 0 < |a * b| := by linarith
  have hb : b ≠ 0 := by
    intro hb; rw [hb, mul_zero, abs_zero] at hab0; exact lt_irrefl _ hab0
  have hb0 : 0 < |b| := abs_pos.mpr hb
  refine ⟨hb, ?_⟩
  have e : b⁻¹ - a = (1 - a * b) / b := by field_simp
  rw [e, abs_div, div_le_div_iff₀ hb0 (by linarith)]
  rw [abs_mul] at h1
  calc |1 - a * b| * (1 - ε) ≤ ε * (1 - ε) := mul_le_mul_of_nonneg_right hab (by linarith)
    _ ≤ ε * (|a| * |b|) := mul_le_mul_of_nonneg_left h1 h0
    _ ≤ ε * (sR * |b|) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ha hb0.le) h0
    _ = ε * sR * |b| := by ring

/-- `recip` certifies `q ≠ 0` on `[-1,1]` and encloses `1/q` by the witness polynomial. -/
theorem recip_sound (hg : Good N S B W) {Q R : TM} {q : ℝ → ℝ} (hQ : Encl (mkCtx N S B W) Q q)
    {csR : List ℤ} {alR : List ℕ} (hR : Rep (mkCtx N S B W) R csR alR)
    (hok : (recip (mkCtx N S B W) Q R).ok = true) :
    (∀ t ∈ Set.Icc (-1 : ℝ) 1, q t ≠ 0) ∧
      Encl (mkCtx N S B W) (recip (mkCtx N S B W) Q R) (fun t => (q t)⁻¹) := by
  set c := mkCtx N S B W with hc
  set D := addC c false c.twoS 0 (neg c (mul c R Q)) with hDdef
  have hokE : (recip c Q R).ok = (R.ok && D.ok && Nat.blt (2 * rangeX c D) c.twoS) := rfl
  rw [hokE] at hok
  simp only [Bool.and_eq_true, Nat.blt_eq] at hok
  obtain ⟨⟨_, hDok⟩, heps⟩ := hok
  have hDokE : D.ok = ((neg c (mul c R Q)).ok && Nat.blt ((neg c (mul c R Q)).s + c.twoS) c.twoB) := rfl
  have hmulok : (mul c R Q).ok = true := by
    rw [hDokE] at hDok
    simp only [Bool.and_eq_true] at hDok
    exact hDok.1
  have hM := mul_sound hg (Encl.self hR) hQ hmulok
  have hN := neg_sound hM
  have hDc := addC_sound hN false (2 ^ S) 0 1 (by simp) hDok hg
  have hrange := rangeX_sound hg hDc
  replace heps : 2 * rangeX c D < 2 ^ S := heps
  have hD : (0 : ℝ) < 2 ^ S := by positivity
  set eps := rangeX c D with heps_def
  have hepsR : (eps : ℝ) / 2 ^ S < 1 / 2 := by
    rw [div_lt_iff₀ hD]
    have : ((2 * eps : ℕ) : ℝ) < ((2 ^ S : ℕ) : ℝ) := by exact_mod_cast heps
    push_cast at this
    linarith
  have hpt : ∀ t ∈ Set.Icc (-1 : ℝ) 1, q t ≠ 0 ∧
      |(q t)⁻¹ - evalZ csR t / 2 ^ S| ≤ (eps : ℝ) / 2 ^ S * ((R.s : ℝ) / 2 ^ S) / (1 - (eps : ℝ) / 2 ^ S) := by
    intro t ht
    have hta : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
    have h1 := hrange t ht
    have h2 : |1 - evalZ csR t / 2 ^ S * q t| ≤ (eps : ℝ) / 2 ^ S := by
      rw [show 1 - evalZ csR t / 2 ^ S * q t = -(evalZ csR t / 2 ^ S * q t) + 1 by ring]; exact h1
    have h3 : |evalZ csR t / 2 ^ S| ≤ (R.s : ℝ) / 2 ^ S := by
      rw [abs_div, abs_of_pos hD]
      exact div_le_div_of_nonneg_right (abs_evalZ_le_s hR t hta) hD.le
    exact recip_err_real h2 hepsR h3
  refine ⟨fun t ht => (hpt t ht).1, csR, alR, ⟨hR.lcs, hR.lal, hR.hv, hR.ha, hR.dom, hR.hs, hR.sB⟩, ?_⟩
  intro t ht
  have h := (hpt t ht).2
  have hden : 0 < 2 ^ S - eps := by omega
  have hceil := le_ceil_div (R.s * eps) (2 ^ S - eps) hden
  show |(q t)⁻¹ - evalZ csR t / 2 ^ S| ≤
    ((R.e + (R.s * eps + (2 ^ S - eps - 1)) / (2 ^ S - eps) : ℕ) : ℝ) / 2 ^ S
  have hepsle : eps ≤ 2 ^ S := by omega
  have hcastden : ((2 ^ S - eps : ℕ) : ℝ) = 2 ^ S - eps := by push_cast [Nat.cast_sub hepsle]; ring
  rw [hcastden] at hceil
  push_cast at hceil
  have hRe : (0 : ℝ) ≤ R.e := by positivity
  have hdpos : (0 : ℝ) < 2 ^ S - eps := by
    have : ((eps : ℕ) : ℝ) < ((2 ^ S : ℕ) : ℝ) := by exact_mod_cast (by omega : eps < 2 ^ S)
    push_cast at this; linarith
  have hfrac : (eps : ℝ) / 2 ^ S * ((R.s : ℝ) / 2 ^ S) / (1 - (eps : ℝ) / 2 ^ S) =
      ((R.s : ℝ) * eps / (2 ^ S - eps)) / 2 ^ S := by
    field_simp
  rw [hfrac] at h
  push_cast
  calc |(q t)⁻¹ - evalZ csR t / 2 ^ S| ≤ ((R.s : ℝ) * eps / (2 ^ S - eps)) / 2 ^ S := h
    _ ≤ ((((R.s * eps + (2 ^ S - eps - 1)) / (2 ^ S - eps) : ℕ) : ℝ)) / 2 ^ S :=
        div_le_div_of_nonneg_right (by exact_mod_cast hceil) hD.le
    _ ≤ ((R.e : ℝ) + (((R.s * eps + (2 ^ S - eps - 1)) / (2 ^ S - eps) : ℕ) : ℝ)) / 2 ^ S := by
        gcongr; linarith

/-! ## Data inputs -/

/-- coefficients encoded by sign-split data `P` (positive parts), `Q` (negative parts) -/
def pqCoeffs (W m P Q : ℕ) : List ℤ :=
  List.zipWith (fun (p q : ℕ) => (p : ℤ) - (q : ℤ)) (digitsN W m P) (digitsN W m Q)

theorem horner_zipWith_sub (x : ℤ) : ∀ (a b : List ℕ), a.length = b.length →
    horner x (List.zipWith (fun (p q : ℕ) => (p : ℤ) - (q : ℤ)) a b) = (Nat.ofDigits x a) - Nat.ofDigits x b
  | [], [], _ => by simp
  | p :: a, q :: b, h => by
    simp only [List.zipWith_cons_cons, horner_cons]
    rw [horner_zipWith_sub x a b (by simpa using h),
      show Nat.ofDigits x (p :: a) = (p : ℤ) + x * Nat.ofDigits x a from rfl,
      show Nat.ofDigits x (q :: b) = (q : ℤ) + x * Nat.ofDigits x b from rfl]
    ring
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem dom_zipWith_sub : ∀ (a b : List ℕ), a.length = b.length →
    Dom (List.zipWith (fun (p q : ℕ) => (p : ℤ) - (q : ℤ)) a b) (addL a b)
  | [], [], _ => by intro k; simp [addL]
  | p :: a, q :: b, h => by
    have ih := dom_zipWith_sub a b (by simpa using h)
    intro k
    cases k with
    | zero =>
      simp only [List.zipWith_cons_cons, addL, List.getD_cons_zero]
      push_cast
      rw [abs_le]; constructor <;> linarith [(Nat.cast_nonneg p : (0 : ℤ) ≤ p), (Nat.cast_nonneg q : (0 : ℤ) ≤ q)]
    | succ k =>
      simp only [List.zipWith_cons_cons, addL, List.getD_cons_succ]
      exact ih k
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem sum_le_of_lt {L : List ℕ} {b : ℕ} (h : ∀ d ∈ L, d < b) : L.sum ≤ L.length * b := by
  induction L with
  | nil => simp
  | cons d L ih =>
    simp only [List.sum_cons, List.length_cons]
    have h1 := h d (by simp)
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    nlinarith

theorem digits_lt_of_hiPat (hg : Good N S B W) {P : ℕ} (hP : P ≤ 2 ^ (W * (N + 1)) - 1)
    (hhi : P &&& (2 ^ W - 2 ^ B) * ones W (N + 1) = 0) : ∀ d ∈ digitsN W (N + 1) P, d < 2 ^ B := by
  have hW0 : 0 < W := by have := hg.BW; omega
  have hPlt : P < 2 ^ (W * (N + 1)) := by have := Nat.two_pow_pos (W * (N + 1)); omega
  have hBW : B ≤ W := by have := hg.BW; omega
  have hpat : ∀ d ∈ List.replicate (N + 1) (2 ^ W - 2 ^ B), d < 2 ^ W := by
    intro d hd; rw [List.eq_of_mem_replicate hd]; have := Nat.two_pow_pos B; have := Nat.two_pow_pos W; omega
  rw [← ofDigits_replicate hW0, ← ofDigits_digitsN (N + 1) P hPlt,
    ofDigits_land _ _ (digitsN_lt W (N + 1) P) hpat, zipWith_replicate_right',
    List.take_of_length_le (by rw [length_digitsN])] at hhi
  have hz := eq_zero_of_ofDigits_eq_zero (Nat.two_pow_pos W) _ hhi
  intro d hd
  exact lt_of_land_hi hBW (digitsN_lt W (N + 1) P d hd) (hz _ (List.mem_map_of_mem hd))

/-- A data TM built from sign-split digits encloses its own polynomial. -/
theorem ofPQ_sound (hg : Good N S B W) (P Q e : ℕ) (hok : (ofPQ (mkCtx N S B W) P Q e).ok = true) :
    Encl (mkCtx N S B W) (ofPQ (mkCtx N S B W) P Q e) (fun t => evalZ (pqCoeffs W (N + 1) P Q) t / 2 ^ S) := by
  have hW0 : 0 < W := by have := hg.BW; omega
  have hokE : (ofPQ (mkCtx N S B W) P Q e).ok =
      (Nat.beq (P &&& (mkCtx N S B W).hiPat) 0 && Nat.beq (Q &&& (mkCtx N S B W).hiPat) 0 &&
        Nat.ble P (mkCtx N S B W).maskWm && Nat.ble Q (mkCtx N S B W).maskWm &&
        Nat.blt ((P + Q) % (mkCtx N S B W).modW) (mkCtx N S B W).twoB) := rfl
  rw [hokE] at hok
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq, Nat.blt_eq, mk_hiPat, mk_maskWm, mk_modW, mk_twoB] at hok
  obtain ⟨⟨⟨⟨hPh, hQh⟩, hPm⟩, hQm⟩, hs⟩ := hok
  have hPlt : P < 2 ^ (W * (N + 1)) := by have := Nat.two_pow_pos (W * (N + 1)); omega
  have hQlt : Q < 2 ^ (W * (N + 1)) := by have := Nat.two_pow_pos (W * (N + 1)); omega
  have hPb := digits_lt_of_hiPat hg hPm hPh
  have hQb := digits_lt_of_hiPat hg hQm hQh
  set Pd := digitsN W (N + 1) P with hPdef
  set Qd := digitsN W (N + 1) Q with hQdef
  have hPd : Nat.ofDigits (2 ^ W) Pd = P := ofDigits_digitsN (N + 1) P hPlt
  have hQd : Nat.ofDigits (2 ^ W) Qd = Q := ofDigits_digitsN (N + 1) Q hQlt
  have hlP : Pd.length = N + 1 := length_digitsN W (N + 1) P
  have hlQ : Qd.length = N + 1 := length_digitsN W (N + 1) Q
  have hsum : (addL Pd Qd).sum < 2 ^ W - 1 := by
    rw [sum_addL_nat]
    have h1 := sum_le_of_lt hPb
    have h2 := sum_le_of_lt hQb
    rw [hlP] at h1
    rw [hlQ] at h2
    have h3 : N + 1 ≤ 2 ^ B := hg.NB
    have h4 : (N + 1) * 2 ^ B ≤ 2 ^ (2 * B) := by rw [two_mul, pow_add]; exact Nat.mul_le_mul_right _ h3
    have h6 : 2 ^ (2 * B) ≤ 2 ^ (W - 2) := Nat.pow_le_pow_right (by norm_num) (by have := hg.BW; omega)
    have h7 : 2 ^ W = 4 * 2 ^ (W - 2) := by
      conv_lhs => rw [show W = (W - 2) + 2 by have := hg.BW; omega]
      rw [pow_add]; ring
    have h8 : 1 ≤ 2 ^ (W - 2) := Nat.one_le_two_pow
    omega
  have hK : W * (N + 1) ≤ W * (2 * N + 1) := Nat.mul_le_mul_left _ (by omega)
  have hQK : Q ≤ 2 ^ (W * (2 * N + 1)) := hQlt.le.trans (Nat.pow_le_pow_right (by norm_num) hK)
  have hsE : (ofPQ (mkCtx N S B W) P Q e).s = (addL Pd Qd).sum := by
    show (P + Q) % (2 ^ W - 1) = _
    rw [← hPd, ← hQd, ← ofDigits_addL, ofDigits_mod_pred (by have := hg.BW; omega) _ hsum]
  refine ⟨pqCoeffs W (N + 1) P Q, addL Pd Qd, ⟨?_, ?_, ?_, ?_, dom_zipWith_sub Pd Qd (by rw [hlP, hlQ]),
    hsE, ?_⟩, ?_⟩
  · simp [pqCoeffs, length_digitsN]
  · rw [length_addL, hlP, hlQ]; simp
  · show (((P + (2 ^ (W * (2 * N + 1)) - Q)) &&& (2 ^ (W * (2 * N + 1)) - 1) : ℕ) : ℤ) = _
    simp only [mk_W, mk_K]
    rw [toZ_mod_mask, pqCoeffs, horner_zipWith_sub _ Pd Qd (by rw [hlP, hlQ])]
    have e1 : ((Nat.ofDigits ((2 : ℤ) ^ W) Pd : ℤ)) = (P : ℤ) := by rw [← hPd]; push_cast; rfl
    have e2 : ((Nat.ofDigits ((2 : ℤ) ^ W) Qd : ℤ)) = (Q : ℤ) := by rw [← hQd]; push_cast; rfl
    rw [e1, e2, Nat.cast_add, Nat.cast_sub hQK]
    push_cast
    rw [show (P : ℤ) + (2 ^ (W * (2 * N + 1)) - (Q : ℤ)) = ((P : ℤ) - Q) + 2 ^ (W * (2 * N + 1)) * 1 by ring,
      Int.add_mul_emod_self_left]
  · show P + Q = Nat.ofDigits (2 ^ W) (addL Pd Qd)
    rw [ofDigits_addL, hPd, hQd]
  · rw [hsE]; simp only [mk_B]; rw [← hsE]
    show (P + Q) % (2 ^ W - 1) < 2 ^ B
    exact hs
  · intro t _
    simp only [mk_S, sub_self, abs_zero]
    positivity

end ThomsonCompact.Packed
