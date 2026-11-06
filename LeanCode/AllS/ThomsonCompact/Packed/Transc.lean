import ThomsonCompact.Packed.Comp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Soundness of `exp`, `log` and real powers on packed TMs

* `expSeries_sound`, `expTM_sound` (series with the remainder of `Real.exp_bound`, squaring);
* `log1pSeries_sound` (remainder of `Real.abs_log_sub_add_sum_range_le`), `logConst_sound` (a constant
  `log c₀` verified through `exp`), `logTMc_sound`, `logTM_sound`;
* `powL_sound`, `powTM_sound` (`d^(-s/2) = exp(-(s/2)·log d)`, `Real.rpow`).
-/

namespace ThomsonCompact.Packed
open Finset

variable {N S B W : ℕ}

/-! ## Coefficient lists -/

theorem evalQ_append (x : ℝ) : ∀ (l1 l2 : List (Bool × ℕ × ℕ)),
    evalQ (l1 ++ l2) x = evalQ l1 x + x ^ l1.length * evalQ l2 x
  | [], l2 => by simp [evalQ]
  | a :: l1, l2 => by
    rw [List.cons_append, evalQ, evalQ, evalQ_append x l1 l2, List.length_cons, pow_succ]; ring

theorem evalQ_map_range (g : ℕ → Bool × ℕ × ℕ) (x : ℝ) :
    ∀ n, evalQ ((List.range n).map g) x = ∑ i ∈ Finset.range n, qval (g i) * x ^ i
  | 0 => by simp [evalQ]
  | n + 1 => by
    rw [List.range_succ, List.map_append, evalQ_append, evalQ_map_range g x n, Finset.sum_range_succ,
      List.length_map, List.length_range]
    simp only [List.map_cons, List.map_nil, evalQ, mul_zero, add_zero]
    ring

theorem fact_eq : ∀ n, fact n = n.factorial
  | 0 => rfl
  | n + 1 => by
    show (n + 1) * fact n = (n + 1).factorial
    rw [fact_eq n, Nat.factorial_succ]

theorem evalQ_expCoeffs (n : ℕ) (x : ℝ) :
    evalQ (expCoeffs n) x = ∑ i ∈ Finset.range n, x ^ i / (i.factorial : ℝ) := by
  rw [expCoeffs, evalQ_map_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [qval, Bool.false_eq_true, if_false, fact_eq, Nat.cast_one]
  ring

theorem qval_log1p (i : ℕ) : qval (Nat.beq (Nat.mod i 2) 1, 1, i + 1) = (-1 : ℝ) ^ i / (i + 1) := by
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · have hb : Nat.beq (Nat.mod i 2) 1 = false := by rw [show Nat.mod i 2 = i % 2 from rfl, h]; rfl
    have he : Even i := Nat.even_iff.mpr h
    simp only [qval, hb, Bool.false_eq_true, if_false, he.neg_one_pow]
    push_cast; ring
  · have hb : Nat.beq (Nat.mod i 2) 1 = true := by rw [show Nat.mod i 2 = i % 2 from rfl, h]; rfl
    have ho : Odd i := Nat.odd_iff.mpr h
    simp only [qval, hb, if_true, ho.neg_one_pow]
    push_cast; ring

theorem evalQ_log1pCoeffs (n : ℕ) (x : ℝ) :
    x * evalQ (log1pCoeffs n) x = -∑ i ∈ Finset.range n, (-x) ^ (i + 1) / (i + 1) := by
  rw [log1pCoeffs, evalQ_map_range, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [qval_log1p]
  rw [neg_pow]
  ring

/-! ## exp -/

theorem expSeries_ok_arg {c : Ctx} {n : ℕ} {G0 : TM} (h : (expSeries c n G0).ok = true) : G0.ok = true := by
  have e : (expSeries c n G0).ok = ((hornerQ c (refresh c G0) (expCoeffs n)).ok && G0.ok &&
      Nat.ble (Nat.add (refresh c G0).s (refresh c G0).e) c.twoS && Nat.blt 0 n) := rfl
  rw [e] at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.2

theorem expSeries_sound (hg : Good N S B W) {G0 : TM} {g : ℝ → ℝ} (hG : Encl (mkCtx N S B W) G0 g) (n : ℕ)
    (hok : (expSeries (mkCtx N S B W) n G0).ok = true) :
    Encl (mkCtx N S B W) (expSeries (mkCtx N S B W) n G0) (fun t => Real.exp (g t)) := by
  have hG' := refresh_sound hg hG
  have hokE : (expSeries (mkCtx N S B W) n G0).ok =
      ((hornerQ (mkCtx N S B W) (refresh (mkCtx N S B W) G0) (expCoeffs n)).ok && G0.ok &&
        Nat.ble ((refresh (mkCtx N S B W) G0).s + (refresh (mkCtx N S B W) G0).e) (2 ^ S) &&
        Nat.blt 0 n) := rfl
  rw [hokE] at hok
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hok
  obtain ⟨⟨⟨hP, _⟩, hr⟩, hn⟩ := hok
  have hPE := hornerQ_sound hg hG' (expCoeffs n) hP
  set G := refresh (mkCtx N S B W) G0 with hGdef
  set r := G.s + G.e with hrdef
  have hfact : 0 < fact n := by rw [fact_eq]; exact Nat.factorial_pos n
  have hD : 0 < (2 ^ S) ^ (n - 1) * fact n * n := by positivity
  have h2S : (0 : ℝ) < 2 ^ S := by positivity
  have hrem : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |Real.exp (g t) - evalQ (expCoeffs n) (g t)| ≤
      ((((r ^ n * (n + 1)) + ((2 ^ S) ^ (n - 1) * fact n * n - 1)) /
        ((2 ^ S) ^ (n - 1) * fact n * n) : ℕ) : ℝ) / 2 ^ (mkCtx N S B W).S := by
    intro t ht
    have hx : |g t| ≤ (r : ℝ) / 2 ^ S := range_sound hG' t ht
    have hr1 : (r : ℝ) / 2 ^ S ≤ 1 := by rw [div_le_one h2S]; exact_mod_cast hr
    have hx1 : |g t| ≤ 1 := hx.trans hr1
    have hb := Real.exp_bound hx1 hn
    rw [evalQ_expCoeffs]
    refine hb.trans ?_
    have hpow : |g t| ^ n ≤ ((r : ℝ) / 2 ^ S) ^ n := pow_le_pow_left₀ (abs_nonneg _) hx n
    have hceil := le_ceil_div (r ^ n * (n + 1)) ((2 ^ S) ^ (n - 1) * fact n * n) hD
    have hpowS : ((2 : ℝ) ^ S) ^ n = ((2 : ℝ) ^ S) ^ (n - 1) * 2 ^ S := by
      rw [← pow_succ]; congr 1; omega
    have hnf : (0 : ℝ) < (n.factorial : ℝ) * n := by
      have := Nat.factorial_pos n
      have : (0 : ℝ) < n := by exact_mod_cast hn
      positivity
    calc |g t| ^ n * ((n.succ : ℝ) / (n.factorial * n))
        ≤ ((r : ℝ) / 2 ^ S) ^ n * ((n.succ : ℝ) / (n.factorial * n)) :=
          mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = (((r ^ n * (n + 1) : ℕ) : ℝ) / (((2 ^ S) ^ (n - 1) * fact n * n : ℕ) : ℝ)) / 2 ^ S := by
          rw [fact_eq, div_pow, hpowS]
          push_cast
          field_simp
      _ ≤ _ := by
          simp only [mk_S]
          exact div_le_div_of_nonneg_right hceil h2S.le
  have hw := widen_sound _ hPE hrem
  exact hw.of_fields rfl rfl rfl rfl

theorem sqIter_ok {c : Ctx} : ∀ (j : ℕ) (H : TM), (sqIter c j H).ok = true → H.ok = true
  | 0, _, h => h
  | j + 1, H, h => (mul_ok (sqIter_ok j (mul c H H) h)).1

theorem sqIter_sound (hg : Good N S B W) : ∀ (j : ℕ) {H : TM} {h : ℝ → ℝ}, Encl (mkCtx N S B W) H h →
    (sqIter (mkCtx N S B W) j H).ok = true →
      Encl (mkCtx N S B W) (sqIter (mkCtx N S B W) j H) (fun t => h t ^ (2 ^ j))
  | 0, _, _, hH, _ => hH.congr (fun t _ => by simp)
  | j + 1, H, h, hH, hok => by
    have hm := mul_sound hg hH hH (sqIter_ok j _ hok)
    have ih := sqIter_sound hg j hm hok
    exact ih.congr (fun t _ => by rw [← sq, ← pow_mul, ← pow_succ'])

theorem expTM_ok {c : Ctx} {n j : ℕ} {F : TM} (h : (expTM c n j F).ok = true) :
    (smul c false (Nat.pow 2 (Nat.sub c.S j)) 0 F).ok = true ∧ F.ok = true ∧ j ≤ c.S := by
  have e : (expTM c n j F).ok = ((sqIter c j (expSeries c n (smul c false (Nat.pow 2 (Nat.sub c.S j)) 0 F))).ok &&
      Nat.ble j c.S) := rfl
  rw [e] at h
  simp only [Bool.and_eq_true, Nat.ble_eq] at h
  have h1 := expSeries_ok_arg (sqIter_ok j _ h.1)
  exact ⟨h1, smul_ok h1, h.2⟩

/-- `exp F = (exp (F/2^j))^(2^j)` -/
theorem expTM_sound (hg : Good N S B W) {F : TM} {f : ℝ → ℝ} (hF : Encl (mkCtx N S B W) F f) (n j : ℕ)
    (hok : (expTM (mkCtx N S B W) n j F).ok = true) :
    Encl (mkCtx N S B W) (expTM (mkCtx N S B W) n j F) (fun t => Real.exp (f t)) := by
  obtain ⟨hSm, _, hjS⟩ := expTM_ok hok
  simp only [mk_S] at hjS
  have e : (expTM (mkCtx N S B W) n j F).ok = ((sqIter (mkCtx N S B W) j (expSeries (mkCtx N S B W) n
      (smul (mkCtx N S B W) false (2 ^ (S - j)) 0 F))).ok && Nat.ble j S) := rfl
  rw [e] at hok
  simp only [Bool.and_eq_true] at hok
  have hq : (((2 ^ (S - j) : ℕ) : ℝ)) / 2 ^ S = ((2 : ℝ) ^ j)⁻¹ := by
    rw [show (2 : ℝ) ^ S = 2 ^ (S - j) * 2 ^ j by rw [← pow_add, Nat.sub_add_cancel hjS]]
    push_cast
    field_simp
  have hG0 := smul_sound hg hF false (2 ^ (S - j)) 0 ((2 : ℝ) ^ j)⁻¹
    (by simp only [Bool.false_eq_true, if_false, hq, sub_self, abs_zero]; positivity) hSm
  have hE := expSeries_sound hg hG0 n (sqIter_ok j _ hok.1)
  have hQ := sqIter_sound hg j hE hok.1
  have hQ' : Encl (mkCtx N S B W) (expTM (mkCtx N S B W) n j F)
      (fun t => Real.exp (((2 : ℝ) ^ j)⁻¹ * f t) ^ (2 ^ j)) := hQ.of_fields rfl rfl rfl rfl
  refine hQ'.congr (fun t _ => ?_)
  show Real.exp (((2 : ℝ) ^ j)⁻¹ * f t) ^ (2 ^ j) = Real.exp (f t)
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/-! ## log -/

theorem log1pSeries_sound (hg : Good N S B W) {U0 : TM} {u : ℝ → ℝ} (hU : Encl (mkCtx N S B W) U0 u)
    (n : ℕ) (hok : (log1pSeries (mkCtx N S B W) n U0).ok = true) :
    (∀ t ∈ Set.Icc (-1 : ℝ) 1, |u t| < 1) ∧
      Encl (mkCtx N S B W) (log1pSeries (mkCtx N S B W) n U0) (fun t => Real.log (1 + u t)) := by
  have hU' := refresh_sound hg hU
  have hokE : (log1pSeries (mkCtx N S B W) n U0).ok =
      ((mul (mkCtx N S B W) (refresh (mkCtx N S B W) U0)
        (hornerQ (mkCtx N S B W) (refresh (mkCtx N S B W) U0) (log1pCoeffs n))).ok &&
        Nat.blt ((refresh (mkCtx N S B W) U0).s + (refresh (mkCtx N S B W) U0).e) (2 ^ S) &&
        Nat.blt 0 n) := rfl
  rw [hokE] at hok
  simp only [Bool.and_eq_true, Nat.blt_eq] at hok
  obtain ⟨⟨hP, hr⟩, hn⟩ := hok
  have hH := hornerQ_sound hg hU' (log1pCoeffs n) (mul_ok hP).2
  have hPE := mul_sound hg hU' hH hP
  set U := refresh (mkCtx N S B W) U0 with hUdef
  set r := U.s + U.e with hrdef
  have h2S : (0 : ℝ) < 2 ^ S := by positivity
  have hρ : (r : ℝ) / 2 ^ S < 1 := by rw [div_lt_one h2S]; exact_mod_cast hr
  have hx : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |u t| ≤ (r : ℝ) / 2 ^ S := fun t ht => range_sound hU' t ht
  have hu1 : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |u t| < 1 := fun t ht => (hx t ht).trans_lt hρ
  refine ⟨hu1, ?_⟩
  have hD : 0 < (2 ^ S) ^ (n - 1) * (2 ^ S - r) := by
    have : 0 < 2 ^ S - r := by omega
    positivity
  have hrem : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |Real.log (1 + u t) - u t * evalQ (log1pCoeffs n) (u t)| ≤
      ((((r ^ (n + 1)) + ((2 ^ S) ^ (n - 1) * (2 ^ S - r) - 1)) /
        ((2 ^ S) ^ (n - 1) * (2 ^ S - r)) : ℕ) : ℝ) / 2 ^ (mkCtx N S B W).S := by
    intro t ht
    have hneg : |-u t| < 1 := by rw [abs_neg]; exact hu1 t ht
    have hb := Real.abs_log_sub_add_sum_range_le hneg n
    rw [sub_neg_eq_add, abs_neg] at hb
    rw [evalQ_log1pCoeffs, sub_neg_eq_add, add_comm]
    refine hb.trans ?_
    have hut := hx t ht
    have h1 : |u t| ^ (n + 1) / (1 - |u t|) ≤ ((r : ℝ) / 2 ^ S) ^ (n + 1) / (1 - |u t|) :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hut _) (by linarith [hu1 t ht])
    have h2 : ((r : ℝ) / 2 ^ S) ^ (n + 1) / (1 - |u t|) ≤ ((r : ℝ) / 2 ^ S) ^ (n + 1) / (1 - (r : ℝ) / 2 ^ S) :=
      div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
    have hceil := le_ceil_div (r ^ (n + 1)) ((2 ^ S) ^ (n - 1) * (2 ^ S - r)) hD
    have hpowS : ((2 : ℝ) ^ S) ^ (n + 1) = ((2 : ℝ) ^ S) ^ (n - 1) * 2 ^ S * 2 ^ S := by
      rw [mul_assoc, ← sq, ← pow_add]; congr 1; omega
    have hsub : (((2 ^ S - r : ℕ)) : ℝ) = 2 ^ S - r := by
      rw [Nat.cast_sub hr.le]; push_cast; ring
    have h3 : ((r : ℝ) / 2 ^ S) ^ (n + 1) / (1 - (r : ℝ) / 2 ^ S) =
        (((r ^ (n + 1) : ℕ) : ℝ) / (((2 ^ S) ^ (n - 1) * (2 ^ S - r) : ℕ) : ℝ)) / 2 ^ S := by
      have hne : (2 : ℝ) ^ S - r ≠ 0 := by
        have : (r : ℝ) < 2 ^ S := by exact_mod_cast hr
        linarith
      rw [Nat.cast_mul, hsub, div_pow, hpowS]
      push_cast
      field_simp
    calc |u t| ^ (n + 1) / (1 - |u t|) ≤ _ := h1.trans h2
      _ = _ := h3
      _ ≤ _ := by
          simp only [mk_S]
          exact div_le_div_of_nonneg_right hceil h2S.le
  have hw := widen_sound _ hPE hrem
  exact hw.of_fields rfl rfl rfl rfl

/-- `|log a - log b| ≤ |a - b| / min a b` -/
theorem abs_log_sub_log_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |Real.log a - Real.log b| ≤ |a - b| / min a b := by
  have hm : 0 < min a b := lt_min ha hb
  have h1 : Real.log a - Real.log b ≤ (a - b) / b := by
    rw [← Real.log_div ha.ne' hb.ne']
    have := Real.log_le_sub_one_of_pos (div_pos ha hb)
    rw [sub_div, div_self hb.ne']; exact this
  have h2 : Real.log b - Real.log a ≤ (b - a) / a := by
    rw [← Real.log_div hb.ne' ha.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hb ha)
    rw [sub_div, div_self ha.ne']; exact this
  have h3 : (a - b) / b ≤ |a - b| / min a b :=
    (div_le_div_of_nonneg_right (le_abs_self _) hb.le).trans
      (div_le_div_of_nonneg_left (abs_nonneg _) hm (min_le_right a b))
  have h4 : (b - a) / a ≤ |a - b| / min a b := by
    rw [abs_sub_comm]
    exact (div_le_div_of_nonneg_right (le_abs_self _) ha.le).trans
      (div_le_div_of_nonneg_left (abs_nonneg _) hm (min_le_left a b))
  rw [abs_le]
  constructor <;> linarith

/-- signed dyadic constant `±mag·2^-S` -/
noncomputable def sdy (S : ℕ) (ng : Bool) (mag : ℕ) : ℝ := (if ng then -(mag : ℝ) else mag) / 2 ^ S

/-- **verified constant**: `logConst` certifies `|log c₀ - L| ≤ δ·2^-S` -/
theorem logConst_sound (hg : Good N S B W) (nE jE cmag : ℕ) (Lng : Bool) (Lmag : ℕ)
    (hok : (logConst (mkCtx N S B W) nE jE cmag Lng Lmag).1 = true) :
    |Real.log ((cmag : ℝ) / 2 ^ S) - sdy S Lng Lmag| ≤
      ((logConst (mkCtx N S B W) nE jE cmag Lng Lmag).2 : ℝ) / 2 ^ S := by
  set E := expTM (mkCtx N S B W) nE jE (constTM (mkCtx N S B W) Lng Lmag 0) with hEdef
  set A := addC (mkCtx N S B W) true cmag 0 E with hAdef
  set η := rangeX (mkCtx N S B W) A with hηdef
  have hokE : (logConst (mkCtx N S B W) nE jE cmag Lng Lmag).1 = (A.ok && Nat.blt η cmag) := rfl
  have hδ : (logConst (mkCtx N S B W) nE jE cmag Lng Lmag).2 =
      (η * 2 ^ S + (cmag - η - 1)) / (cmag - η) := rfl
  rw [hokE] at hok
  simp only [Bool.and_eq_true, Nat.blt_eq] at hok
  obtain ⟨hAok, hηc⟩ := hok
  have hEok : E.ok = true := addC_ok hAok
  have hCok := (expTM_ok hEok).2.1
  have hC := constTM_sound hg Lng Lmag 0 (sdy S Lng Lmag) (by simp [sdy]) hCok
  have hE := expTM_sound hg hC nE jE hEok
  have h2S : (0 : ℝ) < 2 ^ S := by positivity
  set c0 : ℝ := (cmag : ℝ) / 2 ^ S with hc0
  have hA := addC_sound hE true cmag 0 (-c0) (by simp [hc0, neg_div]) hAok hg
  have hb := rangeX_sound hg hA 0 ⟨by norm_num, by norm_num⟩
  set L := sdy S Lng Lmag with hLdef
  have hηr : (η : ℝ) < cmag := by exact_mod_cast hηc
  have hη0 : (0 : ℝ) ≤ (η : ℝ) / 2 ^ S := by positivity
  have hpos : 0 < c0 - (η : ℝ) / 2 ^ S := by
    rw [hc0, ← sub_div]; exact div_pos (by linarith) h2S
  have hexp : |Real.exp L - c0| ≤ (η : ℝ) / 2 ^ S := by
    have : Real.exp L + -c0 = Real.exp L - c0 := by ring
    rw [← this]; exact hb
  have hc0pos : 0 < c0 := by linarith
  have hmin : c0 - (η : ℝ) / 2 ^ S ≤ min c0 (Real.exp L) := by
    apply le_min
    · linarith
    · linarith [(abs_le.mp hexp).1]
  have hlog := abs_log_sub_log_le hc0pos (Real.exp_pos L)
  rw [Real.log_exp] at hlog
  have hm0 : 0 < min c0 (Real.exp L) := lt_min hc0pos (Real.exp_pos L)
  have hne : (cmag : ℝ) - η ≠ 0 := (sub_pos.mpr hηr).ne'
  calc |Real.log c0 - L| ≤ |c0 - Real.exp L| / min c0 (Real.exp L) := hlog
    _ ≤ ((η : ℝ) / 2 ^ S) / min c0 (Real.exp L) := by
        rw [abs_sub_comm]; exact div_le_div_of_nonneg_right hexp hm0.le
    _ ≤ ((η : ℝ) / 2 ^ S) / (c0 - (η : ℝ) / 2 ^ S) := div_le_div_of_nonneg_left hη0 hpos hmin
    _ = (((η * 2 ^ S : ℕ) : ℝ) / ((cmag - η : ℕ) : ℝ)) / 2 ^ S := by
        rw [Nat.cast_sub hηc.le, hc0]
        push_cast
        field_simp
    _ ≤ _ := by
        rw [hδ]
        exact div_le_div_of_nonneg_right (le_ceil_div _ _ (by omega)) h2S.le

/-- a verified table of log constants (checked once by `decide +kernel`, then used by `logTMc_sound`) -/
theorem logTable_sound (hg : Good N S B W) (nE jE : ℕ) :
    ∀ (T : List (ℕ × Bool × ℕ × ℕ)), logTableOk (mkCtx N S B W) nE jE T = true →
      ∀ x ∈ T, |Real.log ((x.1 : ℝ) / 2 ^ S) - sdy S x.2.1 x.2.2.1| ≤ (x.2.2.2 : ℝ) / 2 ^ S
  | [], _, x, hx => by simp at hx
  | y :: T, h, x, hx => by
    have e : logTableOk (mkCtx N S B W) nE jE (y :: T) =
        ((logConst (mkCtx N S B W) nE jE y.1 y.2.1 y.2.2.1).1 &&
          Nat.ble (logConst (mkCtx N S B W) nE jE y.1 y.2.1 y.2.2.1).2 y.2.2.2 &&
          logTableOk (mkCtx N S B W) nE jE T) := rfl
    rw [e] at h
    simp only [Bool.and_eq_true, Nat.ble_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rcases List.mem_cons.mp hx with rfl | hx
    · refine (logConst_sound hg nE jE x.1 x.2.1 x.2.2.1 h1).trans ?_
      have : ((logConst (mkCtx N S B W) nE jE x.1 x.2.1 x.2.2.1).2 : ℝ) ≤ (x.2.2.2 : ℝ) := by exact_mod_cast h2
      exact div_le_div_of_nonneg_right this (by positivity)
    · exact logTable_sound hg nE jE T h3 x hx

/-- `log F` from a center `c₀` and a constant `L` with `|log c₀ - L| ≤ δ·2^-S` -/
theorem logTMc_sound (hg : Good N S B W) {F : TM} {f : ℝ → ℝ} (hF : Encl (mkCtx N S B W) F f)
    (n cmag : ℕ) (Lng : Bool) (Lmag δ : ℕ)
    (hL : |Real.log ((cmag : ℝ) / 2 ^ S) - sdy S Lng Lmag| ≤ (δ : ℝ) / 2 ^ S)
    (hok : (logTMc (mkCtx N S B W) n cmag Lng Lmag δ F).ok = true) :
    (∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 < f t) ∧
      Encl (mkCtx N S B W) (logTMc (mkCtx N S B W) n cmag Lng Lmag δ F) (fun t => Real.log (f t)) := by
  set q := (2 ^ S * 2 ^ S) / cmag with hqdef
  set Sm := smul (mkCtx N S B W) false q 1 F with hSmdef
  set U := addC (mkCtx N S B W) true (2 ^ S) 0 Sm with hUdef
  set LP := log1pSeries (mkCtx N S B W) n U with hLPdef
  set R := addC (mkCtx N S B W) Lng Lmag δ LP with hRdef
  have hokE : (logTMc (mkCtx N S B W) n cmag Lng Lmag δ F).ok = (R.ok && Nat.blt 0 cmag) := rfl
  rw [hokE] at hok
  simp only [Bool.and_eq_true, Nat.blt_eq] at hok
  obtain ⟨hRok, hcm⟩ := hok
  have hLPok : LP.ok = true := addC_ok hRok
  have hUok : U.ok = true := by
    have e : LP.ok = ((mul (mkCtx N S B W) (refresh (mkCtx N S B W) U)
        (hornerQ (mkCtx N S B W) (refresh (mkCtx N S B W) U) (log1pCoeffs n))).ok &&
        Nat.blt (Nat.add (refresh (mkCtx N S B W) U).s (refresh (mkCtx N S B W) U).e) (2 ^ S) &&
        Nat.blt 0 n) := rfl
    have h := hLPok
    rw [e] at h
    simp only [Bool.and_eq_true] at h
    exact (mul_ok h.1.1).1
  have hSmok : Sm.ok = true := addC_ok hUok
  have h2S : (0 : ℝ) < 2 ^ S := by positivity
  have hcpos : (0 : ℝ) < cmag := by exact_mod_cast hcm
  set c0 : ℝ := (cmag : ℝ) / 2 ^ S with hc0
  have hc0pos : 0 < c0 := div_pos hcpos h2S
  have hσ : |c0⁻¹ - (if false = true then -(q : ℝ) else q) / 2 ^ S| ≤ ((1 : ℕ) : ℝ) / 2 ^ S := by
    have h := ratMag_err (N := N) (B := B) (W := W) (S := S) (false, 2 ^ S, cmag)
    have hqv : qval (false, 2 ^ S, cmag) = c0⁻¹ := by
      simp only [qval, Bool.false_eq_true, if_false, hc0]
      push_cast
      field_simp
    rw [hqv] at h
    exact h
  have hSm := smul_sound hg hF false q 1 c0⁻¹ hσ hSmok
  have hU := addC_sound hSm true (2 ^ S) 0 (-1) (by simp) hUok hg
  obtain ⟨hu1, hLP⟩ := log1pSeries_sound hg hU n hLPok
  have hR := addC_sound hLP Lng Lmag δ (Real.log c0) hL hRok hg
  have hfpos : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 < f t := by
    intro t ht
    have h1 := hu1 t ht
    have h2 : 0 < c0⁻¹ * f t := by have := (abs_lt.mp h1).1; linarith
    exact pos_of_mul_pos_right h2 (inv_pos.mpr hc0pos).le
  have hR' : Encl (mkCtx N S B W) (logTMc (mkCtx N S B W) n cmag Lng Lmag δ F)
      (fun t => Real.log (1 + (c0⁻¹ * f t + -1)) + Real.log c0) := hR.of_fields rfl rfl rfl rfl
  refine ⟨hfpos, hR'.congr (fun t ht => ?_)⟩
  show Real.log (1 + (c0⁻¹ * f t + -1)) + Real.log c0 = Real.log (f t)
  have hft := hfpos t ht
  rw [show 1 + (c0⁻¹ * f t + -1) = f t / c0 by field_simp; ring, Real.log_div hft.ne' hc0pos.ne']
  ring

/-- `log F` with the constant verified in place -/
theorem logTM_sound (hg : Good N S B W) {F : TM} {f : ℝ → ℝ} (hF : Encl (mkCtx N S B W) F f)
    (n nE jE cmag : ℕ) (Lng : Bool) (Lmag : ℕ)
    (hok : (logTM (mkCtx N S B W) n nE jE cmag Lng Lmag F).ok = true) :
    (∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 < f t) ∧
      Encl (mkCtx N S B W) (logTM (mkCtx N S B W) n nE jE cmag Lng Lmag F) (fun t => Real.log (f t)) := by
  have hokE : (logTM (mkCtx N S B W) n nE jE cmag Lng Lmag F).ok =
      ((logTMc (mkCtx N S B W) n cmag Lng Lmag (logConst (mkCtx N S B W) nE jE cmag Lng Lmag).2 F).ok &&
        (logConst (mkCtx N S B W) nE jE cmag Lng Lmag).1) := rfl
  rw [hokE] at hok
  simp only [Bool.and_eq_true] at hok
  have hL := logConst_sound hg nE jE cmag Lng Lmag hok.2
  obtain ⟨hpos, hE⟩ := logTMc_sound hg hF n cmag Lng Lmag _ hL hok.1
  exact ⟨hpos, hE.of_fields rfl rfl rfl rfl⟩

/-! ## Powers -/

theorem powL_ok {c : Ctx} {nX jX : ℕ} {Lg Sv : TM} (h : (powL c nX jX Lg Sv).ok = true) :
    Lg.ok = true ∧ Sv.ok = true := by
  have e : (powL c nX jX Lg Sv).ok = ((expTM c nX jX (neg c (mul c (smul c false (Nat.pow 2 (Nat.sub c.S 1)) 0 Sv)
      Lg))).ok && Nat.ble 1 c.S) := rfl
  rw [e] at h
  simp only [Bool.and_eq_true] at h
  have h1 := (expTM_ok h.1).2.1
  have h2 : (mul c (smul c false (Nat.pow 2 (Nat.sub c.S 1)) 0 Sv) Lg).ok = true := h1
  exact ⟨(mul_ok h2).2, smul_ok (mul_ok h2).1⟩

theorem half_eq {S : ℕ} (hS1 : 1 ≤ S) : (((2 ^ (S - 1) : ℕ)) : ℝ) / 2 ^ S = 1 / 2 := by
  rw [show (2 : ℝ) ^ S = 2 ^ (S - 1) * 2 by rw [← pow_succ, Nat.sub_add_cancel hS1]]
  push_cast
  field_simp

/-- `exp(-(s/2)·l)` -/
theorem powL_sound (hg : Good N S B W) {Lg Sv : TM} {l s : ℝ → ℝ} (hL : Encl (mkCtx N S B W) Lg l)
    (hS : Encl (mkCtx N S B W) Sv s) (nX jX : ℕ) (hok : (powL (mkCtx N S B W) nX jX Lg Sv).ok = true) :
    Encl (mkCtx N S B W) (powL (mkCtx N S B W) nX jX Lg Sv) (fun t => Real.exp (-(s t / 2) * l t)) := by
  have hokE : (powL (mkCtx N S B W) nX jX Lg Sv).ok = ((expTM (mkCtx N S B W) nX jX (neg (mkCtx N S B W)
      (mul (mkCtx N S B W) (smul (mkCtx N S B W) false (2 ^ (S - 1)) 0 Sv) Lg))).ok && Nat.ble 1 S) := rfl
  rw [hokE] at hok
  simp only [Bool.and_eq_true, Nat.ble_eq] at hok
  obtain ⟨hX, hS1⟩ := hok
  have h1 := (expTM_ok hX).2.1
  have h2 : (mul (mkCtx N S B W) (smul (mkCtx N S B W) false (2 ^ (S - 1)) 0 Sv) Lg).ok = true := h1
  have hsm := smul_sound hg hS false (2 ^ (S - 1)) 0 (1 / 2)
    (by simp only [Bool.false_eq_true, if_false, half_eq hS1, sub_self, abs_zero]; positivity) (mul_ok h2).1
  have hm := mul_sound hg hsm hL h2
  have hn := neg_sound hm
  have hx := expTM_sound hg hn nX jX hX
  have hx' : Encl (mkCtx N S B W) (powL (mkCtx N S B W) nX jX Lg Sv)
      (fun t => Real.exp (-(1 / 2 * s t * l t))) := hx.of_fields rfl rfl rfl rfl
  refine hx'.congr (fun t _ => ?_)
  show Real.exp (-(1 / 2 * s t * l t)) = Real.exp (-(s t / 2) * l t)
  congr 1
  ring

/-- **`d^(-s/2)`** for a positive TM `D ≈ d` and `Sv ≈ s` (real power `Real.rpow`) -/
theorem powTM_sound (hg : Good N S B W) {D Sv : TM} {d s : ℝ → ℝ} (hD : Encl (mkCtx N S B W) D d)
    (hS : Encl (mkCtx N S B W) Sv s) (n nE jE cmag : ℕ) (Lng : Bool) (Lmag nX jX : ℕ)
    (hok : (powTM (mkCtx N S B W) n nE jE cmag Lng Lmag nX jX D Sv).ok = true) :
    (∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 < d t) ∧
      Encl (mkCtx N S B W) (powTM (mkCtx N S B W) n nE jE cmag Lng Lmag nX jX D Sv)
        (fun t => d t ^ (-(s t) / 2)) := by
  have hok' : (powL (mkCtx N S B W) nX jX (logTM (mkCtx N S B W) n nE jE cmag Lng Lmag D) Sv).ok = true := hok
  obtain ⟨hpos, hlog⟩ := logTM_sound hg hD n nE jE cmag Lng Lmag (powL_ok hok').1
  have hp := powL_sound hg hlog hS nX jX hok'
  refine ⟨hpos, hp.congr (fun t ht => ?_)⟩
  show Real.exp (-(s t / 2) * Real.log (d t)) = d t ^ (-(s t) / 2)
  rw [Real.rpow_def_of_pos (hpos t ht), neg_div]
  congr 1
  ring

#print axioms expTM_sound
#print axioms logConst_sound
#print axioms logTable_sound
#print axioms logTMc_sound
#print axioms logTM_sound
#print axioms powTM_sound

end ThomsonCompact.Packed
