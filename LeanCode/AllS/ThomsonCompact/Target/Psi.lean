import ThomsonCompact.Packed.Transc
import ThomsonCompact.Target.Core

/-!
# `Ψ(z) = (e^z - 1)/z` on packed TMs, and the node values `phi`, `E = d^(-s/2)`
-/

namespace ThomsonCompact.Target
open ThomsonCompact.Packed Finset

variable {N S B W : ℕ}

/-- `Ψ(z) = (e^z - 1)/z`, `Ψ(0) = 1` (entire) -/
noncomputable def Psi (z : ℝ) : ℝ := if z = 0 then 1 else (Real.exp z - 1) / z

theorem exp_eq_Psi (z : ℝ) : Real.exp z = 1 + z * Psi z := by
  unfold Psi
  split_ifs with h
  · subst h; simp
  · field_simp; ring

theorem Psi_two_mul (w : ℝ) : Psi (2 * w) = Psi w * (1 + w * Psi w / 2) := by
  by_cases hw : w = 0
  · subst hw; simp [Psi]
  · have h2 : 2 * w ≠ 0 := mul_ne_zero two_ne_zero hw
    have e2 : Real.exp (2 * w) = Real.exp w * Real.exp w := by rw [← Real.exp_add]; ring_nf
    unfold Psi
    rw [if_neg h2, if_neg hw, e2]
    field_simp
    ring

theorem sum_range_succ_div_factorial (x : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), x ^ k / (k.factorial : ℝ) =
      1 + x * ∑ k ∈ Finset.range n, x ^ k / ((k + 1).factorial : ℝ) := by
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [pow_succ]
  ring

/-- the series remainder of `Ψ` -/
theorem Psi_series_bound {x : ℝ} (hx : |x| ≤ 1) {n : ℕ} (hn : 0 < n) :
    |Psi x - ∑ k ∈ Finset.range n, x ^ k / ((k + 1).factorial : ℝ)| ≤
      |x| ^ n * (((n + 2 : ℕ) : ℝ) / ((n + 1).factorial * (n + 1 : ℕ))) := by
  by_cases h0 : x = 0
  · subst h0
    have : ∑ k ∈ Finset.range n, (0 : ℝ) ^ k / ((k + 1).factorial : ℝ) = 1 := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro b _ hb; simp [zero_pow hb]
      · intro h; exact absurd (Finset.mem_range.mpr hn) h
    rw [this]
    simp [Psi, zero_pow (Nat.pos_iff_ne_zero.mp hn)]
  · have hb := Real.exp_bound hx (Nat.succ_pos n)
    rw [sum_range_succ_div_factorial] at hb
    have hxa : 0 < |x| := abs_pos.mpr h0
    have e : Psi x - ∑ k ∈ Finset.range n, x ^ k / ((k + 1).factorial : ℝ) =
        (Real.exp x - (1 + x * ∑ k ∈ Finset.range n, x ^ k / ((k + 1).factorial : ℝ))) / x := by
      unfold Psi
      rw [if_neg h0]
      field_simp
      ring
    rw [e, abs_div, div_le_iff₀ hxa]
    calc |Real.exp x - (1 + x * ∑ k ∈ Finset.range n, x ^ k / ((k + 1).factorial : ℝ))|
        ≤ |x| ^ (n + 1) * ((n + 1).succ / ((n + 1).factorial * (n + 1 : ℕ))) := hb
      _ = |x| ^ n * (((n + 2 : ℕ) : ℝ) / ((n + 1).factorial * (n + 1 : ℕ))) * |x| := by
          rw [pow_succ]; push_cast; ring

theorem evalQ_psiCoeffs (n : ℕ) (x : ℝ) :
    evalQ (psiCoeffs n) x = ∑ i ∈ Finset.range n, x ^ i / ((i + 1).factorial : ℝ) := by
  rw [psiCoeffs, evalQ_map_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [qval, Bool.false_eq_true, if_false, fact_eq, Nat.cast_one]
  ring

/-! ## Packed `Ψ` -/

theorem psiSeries_ok_arg {c : Ctx} {n : ℕ} {G0 : TM} (h : (psiSeries c n G0).ok = true) : G0.ok = true := by
  have e : (psiSeries c n G0).ok = ((hornerQ c (refresh c G0) (psiCoeffs n)).ok && G0.ok &&
      Nat.ble (Nat.add (refresh c G0).s (refresh c G0).e) c.twoS && Nat.blt 0 n) := rfl
  rw [e] at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.2

theorem psiSeries_sound (hg : Good N S B W) {G0 : TM} {g : ℝ → ℝ} (hG : Encl (mkCtx N S B W) G0 g) (n : ℕ)
    (hok : (psiSeries (mkCtx N S B W) n G0).ok = true) :
    Encl (mkCtx N S B W) (psiSeries (mkCtx N S B W) n G0) (fun t => Psi (g t)) := by
  have hG' := refresh_sound hg hG
  have hokE : (psiSeries (mkCtx N S B W) n G0).ok =
      ((hornerQ (mkCtx N S B W) (refresh (mkCtx N S B W) G0) (psiCoeffs n)).ok && G0.ok &&
        Nat.ble ((refresh (mkCtx N S B W) G0).s + (refresh (mkCtx N S B W) G0).e) (2 ^ S) &&
        Nat.blt 0 n) := rfl
  rw [hokE] at hok
  simp only [Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hok
  obtain ⟨⟨⟨hP, _⟩, hr⟩, hn⟩ := hok
  have hPE := hornerQ_sound hg hG' (psiCoeffs n) hP
  set G := refresh (mkCtx N S B W) G0 with hGdef
  set r := G.s + G.e with hrdef
  have hfact : 0 < fact (n + 1) := by rw [fact_eq]; exact Nat.factorial_pos _
  have hD : 0 < (2 ^ S) ^ (n - 1) * fact (n + 1) * (n + 1) := by positivity
  have h2S : (0 : ℝ) < 2 ^ S := by positivity
  have hrem : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |Psi (g t) - evalQ (psiCoeffs n) (g t)| ≤
      ((((r ^ n * (n + 2)) + ((2 ^ S) ^ (n - 1) * fact (n + 1) * (n + 1) - 1)) /
        ((2 ^ S) ^ (n - 1) * fact (n + 1) * (n + 1)) : ℕ) : ℝ) / 2 ^ (mkCtx N S B W).S := by
    intro t ht
    have hx : |g t| ≤ (r : ℝ) / 2 ^ S := range_sound hG' t ht
    have hr1 : (r : ℝ) / 2 ^ S ≤ 1 := by rw [div_le_one h2S]; exact_mod_cast hr
    have hb := Psi_series_bound (hx.trans hr1) hn
    rw [evalQ_psiCoeffs]
    refine hb.trans ?_
    have hpow : |g t| ^ n ≤ ((r : ℝ) / 2 ^ S) ^ n := pow_le_pow_left₀ (abs_nonneg _) hx n
    have hceil := le_ceil_div (r ^ n * (n + 2)) ((2 ^ S) ^ (n - 1) * fact (n + 1) * (n + 1)) hD
    have hpowS : ((2 : ℝ) ^ S) ^ n = ((2 : ℝ) ^ S) ^ (n - 1) * 2 ^ S := by
      rw [← pow_succ]; congr 1; omega
    have hf : (0 : ℝ) < ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) := by
      have := Nat.factorial_pos (n + 1)
      positivity
    calc |g t| ^ n * (((n + 2 : ℕ) : ℝ) / ((n + 1).factorial * (n + 1 : ℕ)))
        ≤ ((r : ℝ) / 2 ^ S) ^ n * (((n + 2 : ℕ) : ℝ) / ((n + 1).factorial * (n + 1 : ℕ))) :=
          mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = (((r ^ n * (n + 2) : ℕ) : ℝ) / (((2 ^ S) ^ (n - 1) * fact (n + 1) * (n + 1) : ℕ) : ℝ)) / 2 ^ S := by
          rw [fact_eq, div_pow, hpowS]
          push_cast
          field_simp
      _ ≤ _ := by
          simp only [mk_S]
          exact div_le_div_of_nonneg_right hceil h2S.le
  have hw := widen_sound _ hPE hrem
  exact hw.of_fields rfl rfl rfl rfl

theorem psiDouble_ok_arg {c : Ctx} : ∀ (k : ℕ) {w P : TM}, (psiDouble c k w P).ok = true → P.ok = true
  | 0, _, _, h => h
  | k + 1, w, P, h => by
    have h1 := psiDouble_ok_arg k h
    have h2 : (mul c P (addC c false c.twoS 0 (smul c false (Nat.pow 2 (Nat.sub c.S 1)) 0 (mul c w P)))).ok = true := h1
    exact (mul_ok h2).1

theorem psiDouble_sound (hg : Good N S B W) (hS : 1 ≤ S) :
    ∀ (k : ℕ) {w P : TM} {fw : ℝ → ℝ}, (w.ok = true → Encl (mkCtx N S B W) w fw) →
      Encl (mkCtx N S B W) P (fun t => Psi (fw t)) → (psiDouble (mkCtx N S B W) k w P).ok = true →
      Encl (mkCtx N S B W) (psiDouble (mkCtx N S B W) k w P) (fun t => Psi (2 ^ k * fw t))
  | 0, w, P, fw, _, hP, _ => hP.congr (fun t _ => by simp)
  | k + 1, w, P, fw, hw, hP, hok => by
    have hok' : (psiDouble (mkCtx N S B W) k (add (mkCtx N S B W) w w)
        (refresh (mkCtx N S B W) (mul (mkCtx N S B W) P (addC (mkCtx N S B W) false (mkCtx N S B W).twoS 0
          (smul (mkCtx N S B W) false (2 ^ (S - 1)) 0 (mul (mkCtx N S B W) w P)))))).ok = true := hok
    have hP'ok := psiDouble_ok_arg k hok'
    have hm : (mul (mkCtx N S B W) P (addC (mkCtx N S B W) false (mkCtx N S B W).twoS 0
        (smul (mkCtx N S B W) false (2 ^ (S - 1)) 0 (mul (mkCtx N S B W) w P)))).ok = true := hP'ok
    have hA : (addC (mkCtx N S B W) false (mkCtx N S B W).twoS 0
        (smul (mkCtx N S B W) false (2 ^ (S - 1)) 0 (mul (mkCtx N S B W) w P))).ok = true := (mul_ok hm).2
    have hSm : (smul (mkCtx N S B W) false (2 ^ (S - 1)) 0 (mul (mkCtx N S B W) w P)).ok = true := addC_ok hA
    have hwP : (mul (mkCtx N S B W) w P).ok = true := smul_ok hSm
    have hwE := hw (mul_ok hwP).1
    have e1 := mul_sound hg hwE hP hwP
    have e2 := smul_sound hg e1 false (2 ^ (S - 1)) 0 (1 / 2)
      (by simp only [Bool.false_eq_true, if_false, half_eq hS, sub_self, abs_zero]; positivity) hSm
    have e3 := addC_sound e2 false (2 ^ S) 0 1 (by simp) hA hg
    have e4 := refresh_sound hg (mul_sound hg hP e3 hm)
    have hP2 : Encl (mkCtx N S B W) (refresh (mkCtx N S B W) (mul (mkCtx N S B W) P
        (addC (mkCtx N S B W) false (mkCtx N S B W).twoS 0 (smul (mkCtx N S B W) false (2 ^ (S - 1)) 0
          (mul (mkCtx N S B W) w P))))) (fun t => Psi (2 * fw t)) :=
      e4.congr (fun t _ => by rw [Psi_two_mul]; ring)
    have hw2 : (add (mkCtx N S B W) w w).ok = true → Encl (mkCtx N S B W) (add (mkCtx N S B W) w w) (fun t => 2 * fw t) :=
      fun h => (add_sound hwE hwE h).congr (fun t _ => by ring)
    have IH := psiDouble_sound hg hS k hw2 hP2 hok'
    exact IH.congr (fun t _ => by rw [pow_succ]; ring_nf)

theorem psiTM_sound (hg : Good N S B W) {Z : TM} {z : ℝ → ℝ} (hZ : Encl (mkCtx N S B W) Z z) (n j : ℕ)
    (hok : (psiTM (mkCtx N S B W) n j Z).ok = true) :
    Encl (mkCtx N S B W) (psiTM (mkCtx N S B W) n j Z) (fun t => Psi (z t)) := by
  have hokE : (psiTM (mkCtx N S B W) n j Z).ok = ((psiDouble (mkCtx N S B W) j
      (smul (mkCtx N S B W) false (2 ^ (S - j)) 0 Z)
      (psiSeries (mkCtx N S B W) n (smul (mkCtx N S B W) false (2 ^ (S - j)) 0 Z))).ok &&
      Nat.ble j S && Nat.ble 1 S) := rfl
  rw [hokE] at hok
  simp only [Bool.and_eq_true, Nat.ble_eq] at hok
  obtain ⟨⟨hR, hjS⟩, hS⟩ := hok
  have hser := psiDouble_ok_arg j hR
  have hw := psiSeries_ok_arg hser
  have hq : (((2 ^ (S - j) : ℕ) : ℝ)) / 2 ^ S = ((2 : ℝ) ^ j)⁻¹ := by
    rw [show (2 : ℝ) ^ S = 2 ^ (S - j) * 2 ^ j by rw [← pow_add, Nat.sub_add_cancel hjS]]
    push_cast
    field_simp
  have hwE := smul_sound hg hZ false (2 ^ (S - j)) 0 ((2 : ℝ) ^ j)⁻¹
    (by simp only [Bool.false_eq_true, if_false, hq, sub_self, abs_zero]; positivity)
  have hP := psiSeries_sound hg (hwE hw) n hser
  have hD := psiDouble_sound hg hS j hwE hP hR
  have hD' : Encl (mkCtx N S B W) (psiTM (mkCtx N S B W) n j Z)
      (fun t => Psi (2 ^ j * (((2 : ℝ) ^ j)⁻¹ * z t))) := hD.of_fields rfl rfl rfl rfl
  refine hD'.congr (fun t _ => ?_)
  congr 1
  field_simp

/-! ## `exp` with refreshed squarings -/

theorem sqIterR_ok {c : Ctx} : ∀ (j : ℕ) (H : TM), (sqIterR c j H).ok = true → H.ok = true
  | 0, _, h => h
  | j + 1, H, h => (mul_ok (show (mul c H H).ok = true from sqIterR_ok j (refresh c (mul c H H)) h)).1

theorem sqIterR_sound (hg : Good N S B W) : ∀ (j : ℕ) {H : TM} {h : ℝ → ℝ}, Encl (mkCtx N S B W) H h →
    (sqIterR (mkCtx N S B W) j H).ok = true →
      Encl (mkCtx N S B W) (sqIterR (mkCtx N S B W) j H) (fun t => h t ^ (2 ^ j))
  | 0, _, _, hH, _ => hH.congr (fun t _ => by simp)
  | j + 1, H, h, hH, hok => by
    have hm : (mul (mkCtx N S B W) H H).ok = true :=
      sqIterR_ok j (refresh (mkCtx N S B W) (mul (mkCtx N S B W) H H)) hok
    have hr := refresh_sound hg (mul_sound hg hH hH hm)
    have ih := sqIterR_sound hg j hr hok
    exact ih.congr (fun t _ => by rw [← sq, ← pow_mul, ← pow_succ'])

theorem expR_sound (hg : Good N S B W) {F : TM} {f : ℝ → ℝ} (hF : Encl (mkCtx N S B W) F f) (n j : ℕ)
    (hok : (expR (mkCtx N S B W) n j F).ok = true) :
    Encl (mkCtx N S B W) (expR (mkCtx N S B W) n j F) (fun t => Real.exp (f t)) := by
  have hokE : (expR (mkCtx N S B W) n j F).ok = ((sqIterR (mkCtx N S B W) j (refresh (mkCtx N S B W)
      (expSeries (mkCtx N S B W) n (smul (mkCtx N S B W) false (2 ^ (S - j)) 0 F)))).ok && Nat.ble j S) := rfl
  rw [hokE] at hok
  simp only [Bool.and_eq_true, Nat.ble_eq] at hok
  obtain ⟨h1, hjS⟩ := hok
  have hser0 := sqIterR_ok j _ h1
  have hser : (expSeries (mkCtx N S B W) n (smul (mkCtx N S B W) false (2 ^ (S - j)) 0 F)).ok = true := hser0
  have hSm := expSeries_ok_arg hser
  have hq : (((2 ^ (S - j) : ℕ) : ℝ)) / 2 ^ S = ((2 : ℝ) ^ j)⁻¹ := by
    rw [show (2 : ℝ) ^ S = 2 ^ (S - j) * 2 ^ j by rw [← pow_add, Nat.sub_add_cancel hjS]]
    push_cast
    field_simp
  have hG0 := smul_sound hg hF false (2 ^ (S - j)) 0 ((2 : ℝ) ^ j)⁻¹
    (by simp only [Bool.false_eq_true, if_false, hq, sub_self, abs_zero]; positivity) hSm
  have hE := refresh_sound hg (expSeries_sound hg hG0 n hser)
  have hQ := sqIterR_sound hg j hE h1
  have hQ' : Encl (mkCtx N S B W) (expR (mkCtx N S B W) n j F)
      (fun t => Real.exp (((2 : ℝ) ^ j)⁻¹ * f t) ^ (2 ^ j)) := hQ.of_fields rfl rfl rfl rfl
  refine hQ'.congr (fun t _ => ?_)
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  field_simp

theorem expR_ok_arg {c : Ctx} {n j : ℕ} {F : TM} (h : (expR c n j F).ok = true) : F.ok = true := by
  have e : (expR c n j F).ok = ((sqIterR c j (refresh c (expSeries c n (smul c false (Nat.pow 2 (Nat.sub c.S j)) 0 F)))).ok &&
      Nat.ble j c.S) := rfl
  rw [e] at h
  simp only [Bool.and_eq_true] at h
  have h1 := sqIterR_ok j _ h.1
  have h2 : (expSeries c n (smul c false (Nat.pow 2 (Nat.sub c.S j)) 0 F)).ok = true := h1
  exact smul_ok (expSeries_ok_arg h2)

#print axioms psiTM_sound
#print axioms expR_sound

end ThomsonCompact.Target
