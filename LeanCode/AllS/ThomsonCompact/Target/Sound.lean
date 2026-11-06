import ThomsonCompact.Target.Table
import ThomsonCompact.Target.Lift
import AllS.Units.N_F.N_height_upper
import AllS.Units.N_AI.N_scalar_models.BalancedPotentialSupport

/-!
# Soundness of the H target models (milestones T1, T2)

`targetCoeffs_gen`: for the exponent model `sTM ≈ s` (`s ≥ 0` on the cell) and the height model `A ≈ aS ∘ s`,
output coefficient `j ≤ D` of `targetCoeffs` encloses `(C α + C β · hermitePolynomial (s t) (aS (s t)) m).coeff j`
for every profile with `Profile.Valid D m` and every jet mode (`α = alphaF`, `β = betaF`). Wrappers:
`targetU_sound` (unit balance, `targetCoeffsU`, `H_j`), `targetR_sound` (Riesz, `balancedMultiplier cR s · H_j`),
`Fin` forms `targetTMs_sound` (D12), `targetTMs14_sound` (D14), `targetTMsR_sound` (`hfunR`).
-/

namespace ThomsonCompact.Target
open ThomsonCompact.Packed Blueprint.Thomson.Finite

variable {N S B W : ℕ}

/-! ## Constants -/

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

theorem ln2TM_sound (hg : Good N S B W) (P : Par) (hok : (ln2TM (mkCtx N S B W) P).ok = true) :
    Encl (mkCtx N S B W) (ln2TM (mkCtx N S B W) P) (fun _ => Real.log 2) := by
  have hokE : (ln2TM (mkCtx N S B W) P).ok =
      ((constTM (mkCtx N S B W) false P.l2 (logConst (mkCtx N S B W) P.nE P.jE (2 * 2 ^ S) false P.l2).2).ok &&
        (logConst (mkCtx N S B W) P.nE P.jE (2 * 2 ^ S) false P.l2).1) := rfl
  rw [hokE] at hok
  simp only [Bool.and_eq_true] at hok
  have hL := logConst_sound hg P.nE P.jE (2 * 2 ^ S) false P.l2 hok.2
  have h2 : ((2 * 2 ^ S : ℕ) : ℝ) / 2 ^ S = 2 := by push_cast; field_simp
  rw [h2] at hL
  refine (constTM_sound hg false P.l2 _ (Real.log 2) ?_ hok.1).of_fields rfl rfl rfl rfl
  simpa [sdy] using hL

/-! ## Nodes -/

/-- node of label `l` (source order `[c0, c2, c1, c3, -1]`) -/
noncomputable def nodeF (a : ℝ) (l : ℕ) : ℝ := if h : l < 5 then sourceNodes a ⟨l, h⟩ else 0

theorem nodeF_0 (a : ℝ) : nodeF a 0 = a := by simp [nodeF, sourceNodes, contacts]
theorem nodeF_1 (a : ℝ) : nodeF a 1 = -a + (1 - a) / Real.sqrt 2 := by simp [nodeF, sourceNodes, contacts]
theorem nodeF_2 (a : ℝ) : nodeF a 2 = 2 * a - 1 := by simp [nodeF, sourceNodes, contacts]
theorem nodeF_3 (a : ℝ) : nodeF a 3 = -a - (1 - a) / Real.sqrt 2 := by simp [nodeF, sourceNodes, contacts]
theorem nodeF_4 (a : ℝ) : nodeF a 4 = -1 := by simp [nodeF, sourceNodes]

theorem sourceNodes_injective {a : ℝ} (ha : physical a) : Function.Injective (sourceNodes a) := by
  rw [sourceNodes_eq_canonical]
  exact (canonicalNodes_strictMono a ha).injective.comp sourceNodeOrder.injective

theorem nodeF_lt_one {a : ℝ} (ha : physical a) (l : ℕ) (hl : l < 5) : nodeF a l < 1 := by
  simp only [nodeF, dif_pos hl]
  rw [sourceNodes_eq_canonical]
  exact (canonicalNodes_bounds a ha _).2

theorem nodeF_inj {a : ℝ} (ha : physical a) (h l : ℕ) (hh : h < 5) (hl : l < 5) (he : nodeF a h = nodeF a l) :
    h = l := by
  simp only [nodeF, dif_pos hh, dif_pos hl] at he
  have := sourceNodes_injective ha he
  simpa using this

/-! ## EOK helpers and flag propagation -/

theorem addC_eok (hg : Good N S B W) {A : TM} {f : ℝ → ℝ} (hA : EOK (mkCtx N S B W) A f) (ng : Bool)
    (mag dq : ℕ) (κ : ℝ) (hκ : |κ - (if ng then -(mag : ℝ) else mag) / 2 ^ S| ≤ (dq : ℝ) / 2 ^ S) :
    EOK (mkCtx N S B W) (addC (mkCtx N S B W) ng mag dq A) (fun t => f t + κ) :=
  fun hok => addC_sound (hA (addC_ok hok)) ng mag dq κ hκ hok hg

theorem smul_eok (hg : Good N S B W) {A : TM} {f : ℝ → ℝ} (hA : EOK (mkCtx N S B W) A f) (ng : Bool)
    (q dq : ℕ) (σ : ℝ) (hσ : |σ - (if ng then -(q : ℝ) else q) / 2 ^ S| ≤ (dq : ℝ) / 2 ^ S) :
    EOK (mkCtx N S B W) (smul (mkCtx N S B W) ng q dq A) (fun t => σ * f t) :=
  fun hok => smul_sound hg (hA (smul_ok hok)) ng q dq σ hσ hok

theorem const_eok (hg : Good N S B W) (ng : Bool) (mag dq : ℕ) (κ : ℝ)
    (hκ : |κ - (if ng then -(mag : ℝ) else mag) / 2 ^ S| ≤ (dq : ℝ) / 2 ^ S) :
    EOK (mkCtx N S B W) (constTM (mkCtx N S B W) ng mag dq) (fun _ => κ) :=
  fun hok => constTM_sound hg ng mag dq κ hκ hok

theorem invN_ok_arg {c : Ctx} {k tol : ℕ} {D : TM} (h : (invN c k tol D).ok = true) : D.ok = true :=
  (mul_ok (recip_ok h).2).2

theorem invN_eok (hg : Good N S B W) {D : TM} {d : ℝ → ℝ} (hD : EOK (mkCtx N S B W) D d) (k tol : ℕ)
    (hok : (invN (mkCtx N S B W) k tol D).ok = true) :
    (∀ t ∈ Set.Icc (-1 : ℝ) 1, d t ≠ 0) ∧ Encl (mkCtx N S B W) (invN (mkCtx N S B W) k tol D) (fun t => (d t)⁻¹) :=
  invN_sound hg (hD (invN_ok_arg hok)) k tol hok

theorem logTM_ok_arg {c : Ctx} {n nE jE cmag : ℕ} {Lng : Bool} {Lmag : ℕ} {F : TM}
    (h : (logTM c n nE jE cmag Lng Lmag F).ok = true) : F.ok = true := by
  have e1 : (logTM c n nE jE cmag Lng Lmag F).ok = ((logTMc c n cmag Lng Lmag (logConst c nE jE cmag Lng Lmag).2 F).ok &&
      (logConst c nE jE cmag Lng Lmag).1) := rfl
  rw [e1] at h
  simp only [Bool.and_eq_true] at h
  have e2 : (logTMc c n cmag Lng Lmag (logConst c nE jE cmag Lng Lmag).2 F).ok =
      ((addC c Lng Lmag (logConst c nE jE cmag Lng Lmag).2 (log1pSeries c n (addC c true c.twoS 0
        (smul c false (Nat.div (Nat.mul c.twoS c.twoS) cmag) 1 F)))).ok && Nat.blt 0 cmag) := rfl
  have h1 := h.1
  rw [e2] at h1
  simp only [Bool.and_eq_true] at h1
  have h2 := addC_ok h1.1
  have e3 : (log1pSeries c n (addC c true c.twoS 0 (smul c false (Nat.div (Nat.mul c.twoS c.twoS) cmag) 1 F))).ok =
      ((mul c (refresh c (addC c true c.twoS 0 (smul c false (Nat.div (Nat.mul c.twoS c.twoS) cmag) 1 F)))
        (hornerQ c (refresh c (addC c true c.twoS 0 (smul c false (Nat.div (Nat.mul c.twoS c.twoS) cmag) 1 F)))
          (log1pCoeffs n))).ok &&
        Nat.blt (Nat.add (refresh c (addC c true c.twoS 0 (smul c false (Nat.div (Nat.mul c.twoS c.twoS) cmag) 1 F))).s
          (refresh c (addC c true c.twoS 0 (smul c false (Nat.div (Nat.mul c.twoS c.twoS) cmag) 1 F))).e) c.twoS &&
        Nat.blt 0 n) := rfl
  rw [e3] at h2
  simp only [Bool.and_eq_true] at h2
  have h3 : (addC c true c.twoS 0 (smul c false (Nat.div (Nat.mul c.twoS c.twoS) cmag) 1 F)).ok = true :=
    (mul_ok h2.1.1).1
  exact smul_ok (addC_ok h3)

theorem logTM_eok (hg : Good N S B W) {F : TM} {f : ℝ → ℝ} (hF : EOK (mkCtx N S B W) F f)
    (n nE jE cmag : ℕ) (Lng : Bool) (Lmag : ℕ) :
    EOK (mkCtx N S B W) (logTM (mkCtx N S B W) n nE jE cmag Lng Lmag F) (fun t => Real.log (f t)) :=
  fun hok => (logTM_sound hg (hF (logTM_ok_arg hok)) n nE jE cmag Lng Lmag hok).2

theorem psiTM_ok_arg {c : Ctx} {n j : ℕ} {Z : TM} (h : (psiTM c n j Z).ok = true) : Z.ok = true := by
  have e : (psiTM c n j Z).ok = ((psiDouble c j (smul c false (Nat.pow 2 (Nat.sub c.S j)) 0 Z)
      (psiSeries c n (smul c false (Nat.pow 2 (Nat.sub c.S j)) 0 Z))).ok && Nat.ble j c.S && Nat.ble 1 c.S) := rfl
  rw [e] at h
  simp only [Bool.and_eq_true] at h
  exact smul_ok (psiSeries_ok_arg (psiDouble_ok_arg j h.1.1))

/-! ## Node values `phi`, `E = d^(-s/2)` -/

theorem phi_eq_Psi (s x : ℝ) (hd : 0 < 2 - 2 * x) :
    phi s x = (-(1 / 2) * Real.log (2 - 2 * x)) * Psi (s * (-(1 / 2) * Real.log (2 - 2 * x))) := by
  unfold phi
  split_ifs with hs
  · subst hs; simp [Psi]
  · have hE : (2 - 2 * x) ^ (-s / 2) = Real.exp (s * (-(1 / 2) * Real.log (2 - 2 * x))) := by
      rw [Real.rpow_def_of_pos hd]; congr 1; ring
    rw [hE, exp_eq_Psi]
    field_simp
    ring

theorem phiE_eok (hg : Good N S B W) (hS : 1 ≤ S) (P : Par) {sTM Ld : TM} {s x : ℝ → ℝ}
    (hs : Encl (mkCtx N S B W) sTM s) (hL : EOK (mkCtx N S B W) Ld (fun t => Real.log (2 - 2 * x t)))
    (hd : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 < 2 - 2 * x t) :
    EOK (mkCtx N S B W) (phiE (mkCtx N S B W) P sTM Ld).1 (fun t => phi (s t) (x t)) ∧
    EOK (mkCtx N S B W) (phiE (mkCtx N S B W) P sTM Ld).2 (fun t => (2 - 2 * x t) ^ (-(s t) / 2)) := by
  have hl := smul_eok hg hL true (2 ^ (S - 1)) 0 (-(1 / 2))
    (by
      simp only [if_true]
      rw [neg_div, half_eq hS, sub_self, abs_zero]; positivity)
  have hz := mul_eok hg (EOK.of_encl hs) hl
  have hpsi : EOK (mkCtx N S B W) (psiTM (mkCtx N S B W) P.nP P.jP (mul (mkCtx N S B W) sTM
      (smul (mkCtx N S B W) true (2 ^ (S - 1)) 0 Ld)))
      (fun t => Psi (s t * (-(1 / 2) * Real.log (2 - 2 * x t)))) :=
    fun hok => psiTM_sound hg (hz (psiTM_ok_arg hok)) P.nP P.jP hok
  have hphi := mul_eok hg hl hpsi
  have hphi' : EOK (mkCtx N S B W) (phiE (mkCtx N S B W) P sTM Ld).1 (fun t => phi (s t) (x t)) :=
    hphi.congr (fun t ht => (phi_eq_Psi (s t) (x t) (hd t ht)).symm)
  refine ⟨hphi', ?_⟩
  cases hx : P.expE
  · have e : (phiE (mkCtx N S B W) P sTM Ld).2 = refresh (mkCtx N S B W) (addC (mkCtx N S B W) false
        (mkCtx N S B W).twoS 0 (mul (mkCtx N S B W) sTM (phiE (mkCtx N S B W) P sTM Ld).1)) := by
      show cond P.expE _ _ = _; rw [hx]; rfl
    rw [e]
    have hE := refresh_eok hg (addC_eok hg (mul_eok hg (EOK.of_encl hs) hphi') false (2 ^ S) 0 1 (by simp))
    refine hE.congr (fun t _ => ?_)
    rw [← potential_value_factor]
    ring
  · have e : (phiE (mkCtx N S B W) P sTM Ld).2 = powLR (mkCtx N S B W) P.nX P.jX Ld sTM := by
      show cond P.expE _ _ = _; rw [hx]; rfl
    rw [e]
    intro hok
    have hokE : (powLR (mkCtx N S B W) P.nX P.jX Ld sTM).ok = ((expR (mkCtx N S B W) P.nX P.jX
        (neg (mkCtx N S B W) (mul (mkCtx N S B W) (smul (mkCtx N S B W) false (2 ^ (S - 1)) 0 sTM) Ld))).ok &&
        Nat.ble 1 S) := rfl
    have hok1 := hok
    rw [hokE] at hok1
    simp only [Bool.and_eq_true] at hok1
    have hm0 := expR_ok_arg hok1.1
    have hm : (mul (mkCtx N S B W) (smul (mkCtx N S B W) false (2 ^ (S - 1)) 0 sTM) Ld).ok = true := hm0
    have hsm := smul_eok hg (EOK.of_encl hs) false (2 ^ (S - 1)) 0 (1 / 2)
      (by simp only [Bool.false_eq_true, if_false, half_eq hS, sub_self, abs_zero]; positivity)
    have hx2 := expR_sound hg (neg_sound (mul_eok hg hsm hL hm)) P.nX P.jX hok1.1
    have hx3 : Encl (mkCtx N S B W) (powLR (mkCtx N S B W) P.nX P.jX Ld sTM)
        (fun t => Real.exp (-(1 / 2 * s t * Real.log (2 - 2 * x t)))) := hx2.of_fields rfl rfl rfl rfl
    refine hx3.congr (fun t ht => ?_)
    rw [Real.rpow_def_of_pos (hd t ht)]
    congr 1
    ring

/-! ## Jets -/

theorem jet_one (s x : ℝ) (hd : 0 < 2 - 2 * x) :
    potentialJet s (0 + 1) x / ((0 + 1).factorial : ℝ) = (2 - 2 * x) ^ (-s / 2) * (2 - 2 * x)⁻¹ := by
  rw [Nat.zero_add, potentialJet_one, Nat.factorial_one, Nat.cast_one, div_one,
    show -1 - s / 2 = -s / 2 + (-1) by ring, Real.rpow_add hd, Real.rpow_neg_one]

theorem jet_succ (s x : ℝ) (hd : 0 < 2 - 2 * x) (k : ℕ) :
    potentialJet s (k + 1 + 1) x / ((k + 1 + 1).factorial : ℝ) =
      (1 / ((k + 1 : ℕ) + 1 : ℝ)) * ((potentialJet s (k + 1) x / ((k + 1).factorial : ℝ)) *
        (s + ((2 * (k + 1) : ℕ) : ℝ))) * (2 - 2 * x)⁻¹ := by
  simp only [potentialJet, jetCoeff_succ]
  have hr : (2 - 2 * x) ^ (-1 - ((k + 1 : ℕ) : ℝ) - s / 2) =
      (2 - 2 * x) ^ (-1 - (k : ℝ) - s / 2) * (2 - 2 * x)⁻¹ := by
    rw [show -1 - ((k + 1 : ℕ) : ℝ) - s / 2 = (-1 - (k : ℝ) - s / 2) + (-1) by push_cast; ring,
      Real.rpow_add hd, Real.rpow_neg_one]
  rw [hr, Nat.factorial_succ (k + 1)]
  push_cast
  field_simp

theorem jetTail_eok (hg : Good N S B W) {sTM Rd : TM} {s x κ : ℝ → ℝ} (hs : Encl (mkCtx N S B W) sTM s)
    (hR : EOK (mkCtx N S B W) Rd (fun t => (2 - 2 * x t)⁻¹)) (hd : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 < 2 - 2 * x t) :
    ∀ (r k : ℕ) (V : TM), EOK (mkCtx N S B W) V
        (fun t => κ t * (potentialJet (s t) (k + 1) (x t) / ((k + 1).factorial : ℝ))) →
      ∀ i < r, EOK (mkCtx N S B W) ((jetTail (mkCtx N S B W) sTM Rd (k + 1) r V).getD i zeroTM)
        (fun t => κ t * (potentialJet (s t) (k + 1 + i) (x t) / ((k + 1 + i).factorial : ℝ)))
  | 0, _, _, _, i, hi => absurd hi (Nat.not_lt_zero _)
  | r + 1, k, V, hV, i, hi => by
    have e : jetTail (mkCtx N S B W) sTM Rd (k + 1) (r + 1) V = V :: jetTail (mkCtx N S B W) sTM Rd (k + 1 + 1) r
        (refresh (mkCtx N S B W) (smul (mkCtx N S B W) false (ratMag (mkCtx N S B W) 1 (k + 1 + 1)) 1
          (mul (mkCtx N S B W) (mul (mkCtx N S B W) V (addC (mkCtx N S B W) false (2 * (k + 1) * 2 ^ S) 0 sTM)) Rd))) := rfl
    rw [e]
    cases i with
    | zero => exact hV
    | succ i =>
      rw [List.getD_cons_succ]
      have hsk := addC_eok hg (EOK.of_encl hs) false (2 * (k + 1) * 2 ^ S) 0 ((2 * (k + 1) : ℕ) : ℝ)
        (by simp only [Bool.false_eq_true, if_false]; push_cast; rw [mul_div_assoc, div_self (by positivity)]; simp)
      have hm := mul_eok hg (mul_eok hg hV hsk) hR
      have hq := refresh_eok hg (smul_eok hg hm false (ratMag (mkCtx N S B W) 1 (k + 1 + 1)) 1 (1 / ((k + 1 : ℕ) + 1 : ℝ))
        (by
          have := ratMag_err (N := N) (S := S) (B := B) (W := W) (false, 1, k + 1 + 1)
          simpa [qval] using this))
      have hV' : EOK (mkCtx N S B W) (refresh (mkCtx N S B W) (smul (mkCtx N S B W) false (ratMag (mkCtx N S B W) 1 (k + 1 + 1)) 1
          (mul (mkCtx N S B W) (mul (mkCtx N S B W) V (addC (mkCtx N S B W) false (2 * (k + 1) * 2 ^ S) 0 sTM)) Rd)))
          (fun t => κ t * (potentialJet (s t) (k + 1 + 1) (x t) / ((k + 1 + 1).factorial : ℝ))) :=
        hq.congr (fun t ht => by rw [jet_succ (s t) (x t) (hd t ht) k]; ring)
      have IH := jetTail_eok hg hs hR hd r (k + 1) _ hV' i (by omega)
      exact IH.congr (fun t _ => by rw [show k + 1 + 1 + i = k + 1 + (i + 1) by omega])

theorem jetsTM_eok (hg : Good N S B W) {sTM phiT E Rd : TM} {s x : ℝ → ℝ} (hs : Encl (mkCtx N S B W) sTM s)
    (hphi : EOK (mkCtx N S B W) phiT (fun t => phi (s t) (x t)))
    (hE : EOK (mkCtx N S B W) E (fun t => (2 - 2 * x t) ^ (-(s t) / 2)))
    (hR : EOK (mkCtx N S B W) Rd (fun t => (2 - 2 * x t)⁻¹)) (hd : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 < 2 - 2 * x t) :
    ∀ μ k, k < μ → EOK (mkCtx N S B W) ((jetsTM (mkCtx N S B W) sTM phiT E Rd μ).getD k zeroTM)
      (fun t => potentialJet (s t) k (x t) / (k.factorial : ℝ))
  | 0, k, hk => absurd hk (Nat.not_lt_zero _)
  | μ + 1, k, hk => by
    have e : jetsTM (mkCtx N S B W) sTM phiT E Rd (μ + 1) =
        phiT :: jetTail (mkCtx N S B W) sTM Rd (0 + 1) μ (mul (mkCtx N S B W) E Rd) := rfl
    rw [e]
    cases k with
    | zero =>
      rw [List.getD_cons_zero]
      exact hphi.congr (fun t _ => by simp)
    | succ k =>
      rw [List.getD_cons_succ]
      have h1 : EOK (mkCtx N S B W) (mul (mkCtx N S B W) E Rd)
          (fun t => (fun _ => (1 : ℝ)) t * (potentialJet (s t) (0 + 1) (x t) / ((0 + 1).factorial : ℝ))) :=
        (mul_eok hg hE hR).congr (fun t ht => by rw [jet_one (s t) (x t) (hd t ht)]; ring)
      exact (jetTail_eok hg hs hR hd μ 0 _ h1 k (by omega)).congr (fun t _ => by
        rw [Nat.zero_add, Nat.add_comm]; ring)

/-- jets of `W = α·E`: `[W, s W/d, …]` enclose `α·(1 + s·phi), α·s·J_k/k!` -/
theorem jetsW_eok (hg : Good N S B W) {sTM Wv Rd : TM} {s x α : ℝ → ℝ} (hs : Encl (mkCtx N S B W) sTM s)
    (hW : EOK (mkCtx N S B W) Wv (fun t => α t * (2 - 2 * x t) ^ (-(s t) / 2)))
    (hR : EOK (mkCtx N S B W) Rd (fun t => (2 - 2 * x t)⁻¹)) (hd : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 < 2 - 2 * x t) :
    ∀ μ k, k < μ → EOK (mkCtx N S B W) ((jetsW (mkCtx N S B W) sTM Wv Rd μ).getD k zeroTM)
      (fun t => ((if k = 0 then α t else 0) + α t * s t * potentialJet (s t) k (x t)) / (k.factorial : ℝ))
  | 0, k, hk => absurd hk (Nat.not_lt_zero _)
  | μ + 1, k, hk => by
    have e : jetsW (mkCtx N S B W) sTM Wv Rd (μ + 1) =
        Wv :: jetTail (mkCtx N S B W) sTM Rd (0 + 1) μ
          (refresh (mkCtx N S B W) (mul (mkCtx N S B W) (mul (mkCtx N S B W) sTM Wv) Rd)) := rfl
    rw [e]
    cases k with
    | zero =>
      rw [List.getD_cons_zero]
      refine hW.congr (fun t _ => ?_)
      simp only [if_true, potentialJet_zero, Nat.factorial_zero, Nat.cast_one, div_one]
      rw [← potential_value_factor]
      ring
    | succ k =>
      rw [List.getD_cons_succ]
      have h1 : EOK (mkCtx N S B W) (refresh (mkCtx N S B W) (mul (mkCtx N S B W) (mul (mkCtx N S B W) sTM Wv) Rd))
          (fun t => (α t * s t) * (potentialJet (s t) (0 + 1) (x t) / ((0 + 1).factorial : ℝ))) :=
        (refresh_eok hg (mul_eok hg (mul_eok hg (EOK.of_encl hs) hW) hR)).congr (fun t ht => by
          rw [jet_one (s t) (x t) (hd t ht)]; ring)
      refine (jetTail_eok hg hs hR hd μ 0 _ h1 k (by omega)).congr (fun t _ => ?_)
      rw [Nat.zero_add, Nat.add_comm, if_neg (Nat.succ_ne_zero k)]
      ring

/-! ## Labels (= `profileLabel` of the source multiplicities) -/

/-- label of position `k` for block lengths `μ0 … μ4` -/
def lab5 (μ0 μ1 μ2 μ3 μ4 k : ℕ) : ℕ :=
  if k < μ0 then 0 else if k < μ0 + μ1 then 1 else if k < μ0 + μ1 + μ2 then 2 else
  if k < μ0 + μ1 + μ2 + μ3 then 3 else if k < μ0 + μ1 + μ2 + μ3 + μ4 then 4 else 0

theorem getD_rep_append (a : ℕ) (L : List ℕ) : ∀ (n k : ℕ),
    (List.replicate n a ++ L).getD k 0 = if k < n then a else L.getD (k - n) 0
  | 0, k => by simp
  | n + 1, 0 => by simp [List.replicate_succ]
  | n + 1, k + 1 => by
    rw [List.replicate_succ, List.cons_append, List.getD_cons_succ, getD_rep_append a L n k]
    by_cases h : k < n
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega), show k + 1 - (n + 1) = k - n by omega]

theorem labelsOf_eq (μ0 μ1 μ2 μ3 μ4 : ℕ) : labelsOf [μ0, μ1, μ2, μ3, μ4] =
    List.replicate μ0 0 ++ (List.replicate μ1 1 ++ (List.replicate μ2 2 ++
      (List.replicate μ3 3 ++ (List.replicate μ4 4 ++ [])))) := by
  simp [labelsOf, List.append_assoc]

theorem labelsOf_getD (μ0 μ1 μ2 μ3 μ4 k : ℕ) :
    (labelsOf [μ0, μ1, μ2, μ3, μ4]).getD k 0 = lab5 μ0 μ1 μ2 μ3 μ4 k := by
  rw [labelsOf_eq]
  simp only [getD_rep_append, List.getD_nil]
  unfold lab5
  split_ifs <;> omega

theorem labelsOf_length (μ0 μ1 μ2 μ3 μ4 : ℕ) :
    (labelsOf [μ0, μ1, μ2, μ3, μ4]).length = μ0 + μ1 + μ2 + μ3 + μ4 := by
  simp [labelsOf]
  omega

theorem lab5_spec (μ0 μ1 μ2 μ3 μ4 k : ℕ) (hk : k < μ0 + μ1 + μ2 + μ3 + μ4) :
    (lab5 μ0 μ1 μ2 μ3 μ4 k = 0 ∧ k < μ0) ∨
    (lab5 μ0 μ1 μ2 μ3 μ4 k = 1 ∧ μ0 ≤ k ∧ k < μ0 + μ1) ∨
    (lab5 μ0 μ1 μ2 μ3 μ4 k = 2 ∧ μ0 + μ1 ≤ k ∧ k < μ0 + μ1 + μ2) ∨
    (lab5 μ0 μ1 μ2 μ3 μ4 k = 3 ∧ μ0 + μ1 + μ2 ≤ k ∧ k < μ0 + μ1 + μ2 + μ3) ∨
    (lab5 μ0 μ1 μ2 μ3 μ4 k = 4 ∧ μ0 + μ1 + μ2 + μ3 ≤ k) := by
  unfold lab5
  split_ifs <;> omega

/-! ## Assembly -/

theorem newtonCoeffs_length (c : Ctx) (Vs Hs Gs : List (List TM)) (labels : List ℕ) :
    ∀ (r k : ℕ) (col : List TM), (newtonCoeffs c Vs Hs Gs labels r k col).length = r
  | 0, _, _ => rfl
  | r + 1, k, col => by
    show (_ :: newtonCoeffs c Vs Hs Gs labels r (k + 1) _).length = _
    rw [List.length_cons, newtonCoeffs_length c Vs Hs Gs labels r]

theorem allOkL_getD : ∀ (L : List TM), allOkL L = true → ∀ j < L.length, (L.getD j zeroTM).ok = true
  | [], _, j, hj => absurd hj (by simp)
  | T :: L, h, j, hj => by
    have e : allOkL (T :: L) = (T.ok && allOkL L) := rfl
    rw [e] at h
    simp only [Bool.and_eq_true] at h
    cases j with
    | zero => exact h.1
    | succ j => exact allOkL_getD L h.2 j (by simp at hj; omega)

theorem getD_map_lt {α β : Type*} (f : α → β) (L : List α) (i : ℕ) (d : α) (d' : β) (h : i < L.length) :
    (L.map f).getD i d' = f (L.getD i d) := by
  rw [getD_eq_get _ _ _ (by simpa using h), getD_eq_get _ _ _ h, List.getElem_map]

theorem profileLabel_lab5 (m : Fin 5 → ℕ) (k : ℕ) :
    ((profileLabel (m ∘ sourceNodeOrder) k : Fin 5) : ℕ) =
      if k < m 4 then 0 else if k < m 4 + m 3 then 1 else if k < m 4 + m 3 + m 2 then 2 else
      if k < m 4 + m 3 + m 2 + m 1 then 3 else 4 := by
  rw [profileLabel_val]
  rfl

theorem lab5_eq_profileLabel (m : Fin 5 → ℕ) (k : ℕ) (hk : k < m 4 + m 3 + m 2 + m 1 + m 0) :
    lab5 (m 4) (m 3) (m 2) (m 1) (m 0) k = ((profileLabel (m ∘ sourceNodeOrder) k : Fin 5) : ℕ) := by
  rw [profileLabel_lab5]
  unfold lab5
  split_ifs <;> omega

theorem ln32TM_sound (hg : Good N S B W) (hS : 1 ≤ S) (P : Par) (hok : (ln32TM (mkCtx N S B W) P).ok = true) :
    Encl (mkCtx N S B W) (ln32TM (mkCtx N S B W) P) (fun _ => Real.log (3 / 2)) := by
  have hokE : (ln32TM (mkCtx N S B W) P).ok =
      ((constTM (mkCtx N S B W) false P.l32 (logConst (mkCtx N S B W) P.nE P.jE (3 * 2 ^ (S - 1)) false P.l32).2).ok &&
        (logConst (mkCtx N S B W) P.nE P.jE (3 * 2 ^ (S - 1)) false P.l32).1) := rfl
  rw [hokE] at hok
  simp only [Bool.and_eq_true] at hok
  have hL := logConst_sound hg P.nE P.jE (3 * 2 ^ (S - 1)) false P.l32 hok.2
  have h2 : ((3 * 2 ^ (S - 1) : ℕ) : ℝ) / 2 ^ S = 3 / 2 := by
    rw [show (2 : ℝ) ^ S = 2 ^ (S - 1) * 2 by rw [← pow_succ, Nat.sub_add_cancel hS]]
    push_cast; field_simp
  rw [h2] at hL
  refine (constTM_sound hg false P.l32 _ (Real.log (3 / 2)) ?_ hok.1).of_fields rfl rfl rfl rfl
  simpa [sdy] using hL

/-- the semantic weight `α` of the jets of mode `P.mode` (`0`; `2^-ek`; Riesz `exp(((s - c)/2) log(3/2))/c`) -/
noncomputable def alphaF (P : Par) (S : ℕ) (s : ℝ) : ℝ :=
  if P.mode = 0 then 0 else if P.mode = 1 then ((2 ^ (S - P.ek) : ℕ) : ℝ) / 2 ^ S
  else Real.exp (((s - P.cR) / 2) * Real.log (3 / 2)) / P.cR

/-- the semantic weight `β` (`1`, or `α·s`) -/
noncomputable def betaF (P : Par) (S : ℕ) (s : ℝ) : ℝ := if P.mode = 0 then 1 else alphaF P S s * s

theorem headW_eok (hg : Good N S B W) (hS : 1 ≤ S) (P : Par) (hP : P.mode ≠ 0) {sTM Ld E : TM} {s x : ℝ → ℝ}
    (hs : Encl (mkCtx N S B W) sTM s) (hL : EOK (mkCtx N S B W) Ld (fun t => Real.log (2 - 2 * x t)))
    (hE : EOK (mkCtx N S B W) E (fun t => (2 - 2 * x t) ^ (-(s t) / 2)))
    (hd : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 < 2 - 2 * x t) :
    EOK (mkCtx N S B W) (headW (mkCtx N S B W) P sTM Ld (ln32TM (mkCtx N S B W) P) E)
      (fun t => alphaF P S (s t) * (2 - 2 * x t) ^ (-(s t) / 2)) := by
  by_cases h1 : P.mode = 1
  · have e : headW (mkCtx N S B W) P sTM Ld (ln32TM (mkCtx N S B W) P) E =
        smul (mkCtx N S B W) false (2 ^ (S - P.ek)) 0 E := by
      show cond (Nat.beq P.mode 1) _ _ = _
      rw [h1]; rfl
    rw [e]
    refine (smul_eok hg hE false (2 ^ (S - P.ek)) 0 (((2 ^ (S - P.ek) : ℕ) : ℝ) / 2 ^ S)
      (by simp)).congr (fun t _ => ?_)
    simp [alphaF, h1]
  · have hb : Nat.beq P.mode 1 = false := by
      cases h : Nat.beq P.mode 1
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) h1
    have e : headW (mkCtx N S B W) P sTM Ld (ln32TM (mkCtx N S B W) P) E =
        smul (mkCtx N S B W) false (ratMag (mkCtx N S B W) 1 P.cR) 1 (expR (mkCtx N S B W) P.nB P.jB
          (add (mkCtx N S B W) (neg (mkCtx N S B W) (mul (mkCtx N S B W)
            (smul (mkCtx N S B W) false (2 ^ (S - 1)) 0 sTM) Ld))
            (mul (mkCtx N S B W) (smul (mkCtx N S B W) false (2 ^ (S - 1)) 0
              (addC (mkCtx N S B W) true (P.cR * 2 ^ S) 0 sTM)) (ln32TM (mkCtx N S B W) P)))) := by
      show cond (Nat.beq P.mode 1) _ _ = _
      rw [hb]; rfl
    rw [e]
    have hhalf : ∀ {A : TM} {f : ℝ → ℝ}, EOK (mkCtx N S B W) A f →
        EOK (mkCtx N S B W) (smul (mkCtx N S B W) false (2 ^ (S - 1)) 0 A) (fun t => 1 / 2 * f t) :=
      fun hA => smul_eok hg hA false (2 ^ (S - 1)) 0 (1 / 2)
        (by simp only [Bool.false_eq_true, if_false, half_eq hS, sub_self, abs_zero]; positivity)
    have hc : EOK (mkCtx N S B W) (addC (mkCtx N S B W) true (P.cR * 2 ^ S) 0 sTM) (fun t => s t + -(P.cR : ℝ)) :=
      addC_eok hg (EOK.of_encl hs) true (P.cR * 2 ^ S) 0 (-(P.cR : ℝ))
        (by simp only [if_true]; push_cast; rw [neg_div, mul_div_assoc, div_self (by positivity)]; simp)
    have hL32 : EOK (mkCtx N S B W) (ln32TM (mkCtx N S B W) P) (fun _ => Real.log (3 / 2)) :=
      fun h => ln32TM_sound hg hS P h
    have harg := add_eok (neg_eok (mul_eok hg (hhalf (EOK.of_encl hs)) hL) rfl) (mul_eok hg (hhalf hc) hL32) rfl
    have hex : EOK (mkCtx N S B W) (expR (mkCtx N S B W) P.nB P.jB
        (add (mkCtx N S B W) (neg (mkCtx N S B W) (mul (mkCtx N S B W)
          (smul (mkCtx N S B W) false (2 ^ (S - 1)) 0 sTM) Ld))
          (mul (mkCtx N S B W) (smul (mkCtx N S B W) false (2 ^ (S - 1)) 0
            (addC (mkCtx N S B W) true (P.cR * 2 ^ S) 0 sTM)) (ln32TM (mkCtx N S B W) P))))
        (fun t => Real.exp (-(1 / 2 * s t * Real.log (2 - 2 * x t)) +
          1 / 2 * (s t + -(P.cR : ℝ)) * Real.log (3 / 2))) :=
      fun h => expR_sound hg (harg (expR_ok_arg h)) P.nB P.jB h
    refine (smul_eok hg hex false (ratMag (mkCtx N S B W) 1 P.cR) 1 (1 / (P.cR : ℝ)) ?_).congr (fun t ht => ?_)
    · have := ratMag_err (N := N) (S := S) (B := B) (W := W) (false, 1, P.cR)
      simpa [qval] using this
    · simp only [alphaF, hP, h1, if_false]
      rw [Real.rpow_def_of_pos (hd t ht), Real.exp_add, div_eq_mul_inv, div_eq_mul_inv]
      ring_nf

theorem iter_deriv_add (k : ℕ) (f g : Polynomial ℝ) :
    Polynomial.derivative^[k] (f + g) = Polynomial.derivative^[k] f + Polynomial.derivative^[k] g := by
  induction k generalizing f g with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
      Polynomial.derivative_add, ih]

/-- Hermite interpolation is affine in the jets: `(α, 0, 0, …) + β·J ↦ α + β·H_J` -/
theorem profileHermite_affine (z : Fin 5 → ℝ) (m : Fin 5 → ℕ) (J : ℕ → ℝ → ℝ) (hz : Function.Injective z)
    (hm1 : 0 < ∑ i, m i) (α β : ℝ) :
    profileHermite z m (fun k x => (if k = 0 then α else 0) + β * J k x) =
      Polynomial.C α + Polynomial.C β * profileHermite z m J := by
  symm
  apply profileHermite_unique z m _ hz
  · have h1 := profileHermite_degree z m J
    have h0 : (Polynomial.C α).degree < ((∑ i, m i : ℕ) : WithBot ℕ) :=
      lt_of_le_of_lt Polynomial.degree_C_le (by exact_mod_cast hm1)
    have h2 : (Polynomial.C β * profileHermite z m J).degree < ((∑ i, m i : ℕ) : WithBot ℕ) := by
      by_cases hβ : β = 0
      · rw [hβ, Polynomial.C_0, zero_mul, Polynomial.degree_zero]; exact WithBot.bot_lt_coe _
      · rw [Polynomial.degree_C_mul hβ]; exact h1
    exact lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt h0 h2)
  · intro i j hj
    have hJ := profileHermite_jets z m J hz i j hj
    unfold polynomialJets at hJ ⊢
    show _ = (if j = 0 then α else 0) + β * J j (z i)
    rw [iter_deriv_add, Polynomial.iterate_derivative_C_mul, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, hJ]
    cases j with
    | zero => simp
    | succ j => rw [Polynomial.iterate_derivative_C (Nat.succ_pos j), Polynomial.eval_zero, if_neg (by omega : j + 1 ≠ 0)]

theorem beq_true_of {a b : ℕ} (h : a = b) : Nat.beq a b = true := by rw [h]; exact Nat.beq_refl b

theorem beq_false_of {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem allOkL_drop1 (L : List TM) (h : allOkL (L.drop 1) = true) (j : ℕ) (hj1 : 1 ≤ j) (hj : j < L.length) :
    (L.getD j zeroTM).ok = true := by
  cases L with
  | nil => simp at hj
  | cons T L =>
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [List.getD_cons_succ]
    exact allOkL_getD L h i (by simp at hj; omega)

/-- **Soundness of the H target models** (all jet modes): the packed target has `D + 1` entries and
coefficient `j ≤ D` encloses `(C α + C β · hermitePolynomial (s t) (aS (s t)) m).coeff j` with the mode weights
`α = alphaF`, `β = betaF` (mode 0: `α = 0, β = 1`; mode 1: `α = 2^-ek, β = α s`; mode 2 (Riesz):
`α = exp(((s - cR)/2) log(3/2))/cR`, `β = α s = balancedMultiplier cR s`). -/
theorem targetCoeffs_gen (hg : Good N S B W) (hS2 : 2 ≤ S) {sTM A : TM} {s : ℝ → ℝ}
    (hs : Encl (mkCtx N S B W) sTM s) (hs0 : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ s t)
    (hA : Encl (mkCtx N S B W) A (fun t => aS (s t))) (P : Par) {D : ℕ} (m : Fin 5 → ℕ)
    (hm : Profile.Valid D m) :
    (targetCoeffs0 (mkCtx N S B W) P [m 0, m 1, m 2, m 3, m 4] sTM A).length = D + 1 ∧
    ∀ j ≤ D, EOK (mkCtx N S B W) ((targetCoeffs0 (mkCtx N S B W) P [m 0, m 1, m 2, m 3, m 4] sTM A).getD j zeroTM)
      (fun t => (Polynomial.C (alphaF P S (s t)) + Polynomial.C (betaF P S (s t)) *
        hermitePolynomial (s t) (aS (s t)) m).coeff j) := by
  have hS1 : 1 ≤ S := by omega
  have hD2 : (0 : ℝ) < 2 ^ S := by positivity
  -- names for the pipeline
  set μ := srcMult [m 0, m 1, m 2, m 3, m 4] with hμdef
  have hμ : μ = [m 4, m 3, m 2, m 1, m 0] := rfl
  set labels := labelsOf μ with hlabels
  set Xs := nodeTMs (mkCtx N S B W) (ir2TM (mkCtx N S B W) P.r2) A with hXs
  set Ds := Xs.map (distTM (mkCtx N S B W)) with hDs
  set L2 := ln2TM (mkCtx N S B W) P with hL2def
  set Lds := ldsOf (mkCtx N S B W) P L2 Ds with hLds
  set Rds := rdsOf (mkCtx N S B W) P Ds with hRds
  set Vs := vsOf (mkCtx N S B W) P sTM Lds Rds μ with hVs
  set Hs := hsOf (mkCtx N S B W) Xs with hHs
  set Gs := gsOf (mkCtx N S B W) P Hs with hGs
  set col0 := labels.map (fun l => (Vs.getD l []).getD 0 zeroTM) with hcol0def
  set cs := newtonCoeffs (mkCtx N S B W) Vs Hs Gs labels labels.length 0 col0 with hcs
  have hT : targetCoeffs0 (mkCtx N S B W) P [m 0, m 1, m 2, m 3, m 4] sTM A = hornerN (mkCtx N S B W) Xs labels cs := rfl
  rw [hT]
  -- semantic objects
  set a : ℝ → ℝ := fun t => aS (s t) with ha_def
  have hphys : ∀ t ∈ Set.Icc (-1 : ℝ) 1, physical (a t) := fun t ht => aS_physical (s t) (hs0 t ht)
  set xs : ℝ → ℕ → ℝ := fun t l => nodeF (a t) l with hxs
  have hd : ∀ l < 5, ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 < 2 - 2 * xs t l := by
    intro l hl t ht
    have := nodeF_lt_one (hphys t ht) l hl
    show 0 < 2 - 2 * nodeF (a t) l
    linarith
  have hlen5 : Xs.length = 5 := rfl
  -- constants
  have hI : EOK (mkCtx N S B W) (ir2TM (mkCtx N S B W) P.r2) (fun _ => (Real.sqrt 2)⁻¹) :=
    fun h => ir2TM_sound hg P.r2 h
  have hL2 : EOK (mkCtx N S B W) L2 (fun _ => Real.log 2) := fun h => ln2TM_sound hg P h
  have hAE : EOK (mkCtx N S B W) A a := EOK.of_encl hA
  -- nodes
  have hW : EOK (mkCtx N S B W) (mul (mkCtx N S B W) (ir2TM (mkCtx N S B W) P.r2) (oneSub (mkCtx N S B W) A))
      (fun t => (Real.sqrt 2)⁻¹ * (-(a t) + 1)) :=
    mul_eok hg hI (addC_eok hg (neg_eok hAE rfl) false (2 ^ S) 0 1 (by simp))
  have hX : ∀ l < 5, EOK (mkCtx N S B W) (Xs.getD l zeroTM) (fun t => xs t l) := by
    intro l hl
    interval_cases l
    · exact (refresh_eok hg hAE).congr (fun t _ => by simp [hxs, nodeF_0])
    · exact (refresh_eok hg (add_eok (neg_eok hAE rfl) hW rfl)).congr (fun t _ => by
        simp only [hxs, nodeF_1]; field_simp; ring)
    · exact (refresh_eok hg (addC_eok hg (add_eok hAE hAE rfl) true (2 ^ S) 0 (-1) (by simp))).congr
        (fun t _ => by simp only [hxs, nodeF_2]; ring)
    · exact (refresh_eok hg (neg_eok (add_eok hAE hW rfl) rfl)).congr (fun t _ => by
        simp only [hxs, nodeF_3]; field_simp; ring)
    · exact (refresh_eok hg (const_eok hg true (2 ^ S) 0 (-1) (by simp))).congr
        (fun t _ => by simp [hxs, nodeF_4])
  have h4 : ∀ t ∈ Set.Icc (-1 : ℝ) 1, xs t 4 = -1 := fun t _ => nodeF_4 _
  -- distances
  have hDd : ∀ l < 5, EOK (mkCtx N S B W) (Ds.getD l zeroTM) (fun t => 2 - 2 * xs t l) := by
    intro l hl
    rw [getD_map_lt _ _ _ zeroTM _ (by rw [hlen5]; exact hl)]
    exact (refresh_eok hg (addC_eok hg (neg_eok (add_eok (hX l hl) (hX l hl) rfl) rfl) false (2 * 2 ^ S) 0 2
      (by simp))).congr (fun t _ => by ring)
  -- logs
  have hLd : ∀ l < 5, EOK (mkCtx N S B W) (Lds.getD l zeroTM) (fun t => Real.log (2 - 2 * xs t l)) := by
    intro l hl
    have hLA : EOK (mkCtx N S B W) (logTM (mkCtx N S B W) P.nL P.nE P.jE P.cA P.gA P.lA (Ds.getD 0 zeroTM))
        (fun t => Real.log (2 - 2 * xs t 0)) := logTM_eok hg (hDd 0 (by norm_num)) _ _ _ _ _ _
    interval_cases l
    · exact hLA
    · exact logTM_eok hg (hDd 1 (by norm_num)) _ _ _ _ _ _
    · refine (add_eok hLA hL2 rfl).congr (fun t ht => ?_)
      have h0 := hd 0 (by norm_num) t ht
      simp only [hxs, nodeF_0, nodeF_2] at h0 ⊢
      rw [← Real.log_mul h0.ne' two_ne_zero]
      congr 1; ring
    · exact logTM_eok hg (hDd 3 (by norm_num)) _ _ _ _ _ _
    · refine (add_eok hL2 hL2 rfl).congr (fun t _ => ?_)
      simp only [hxs, nodeF_4]
      rw [← Real.log_mul two_ne_zero two_ne_zero]
      norm_num
  -- reciprocal distances
  have hRd : ∀ l < 5, EOK (mkCtx N S B W) (Rds.getD l zeroTM) (fun t => (2 - 2 * xs t l)⁻¹) := by
    intro l hl
    have hRA : EOK (mkCtx N S B W) (invN (mkCtx N S B W) P.kN P.tol (Ds.getD 0 zeroTM))
        (fun t => (2 - 2 * xs t 0)⁻¹) := fun h => (invN_eok hg (hDd 0 (by norm_num)) _ _ h).2
    interval_cases l
    · exact hRA
    · exact fun h => (invN_eok hg (hDd 1 (by norm_num)) _ _ h).2
    · refine (smul_eok hg hRA false (2 ^ (S - 1)) 0 (1 / 2)
        (by simp only [Bool.false_eq_true, if_false, half_eq hS1, sub_self, abs_zero]; positivity)).congr
        (fun t _ => ?_)
      simp only [hxs, nodeF_0, nodeF_2]
      rw [show 2 - 2 * (2 * a t - 1) = 2 * (2 - 2 * a t) by ring, mul_inv]
      ring
    · exact fun h => (invN_eok hg (hDd 3 (by norm_num)) _ _ h).2
    · refine (const_eok hg false (2 ^ (S - 2)) 0 (1 / 4) ?_).congr (fun t _ => ?_)
      · simp only [Bool.false_eq_true, if_false]
        rw [show (2 : ℝ) ^ S = 2 ^ (S - 2) * 4 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add, Nat.sub_add_cancel hS2]]
        push_cast
        rw [show ((2 : ℝ) ^ (S - 2)) / (2 ^ (S - 2) * 4) = 1 / 4 by field_simp]
        simp
      · simp only [hxs, nodeF_4]; norm_num
  -- jets
  set J : ℝ → ℕ → ℝ → ℝ := fun t k x => (if k = 0 then alphaF P S (s t) else 0) +
    betaF P S (s t) * potentialJet (s t) k x with hJ
  have hVs : ∀ l < 5, Vs.getD l [] = cond (Nat.beq P.mode 0)
      (jetsTM (mkCtx N S B W) sTM (phiE (mkCtx N S B W) P sTM (Lds.getD l zeroTM)).1
        (phiE (mkCtx N S B W) P sTM (Lds.getD l zeroTM)).2 (Rds.getD l zeroTM) (μ.getD l 0))
      (jetsW (mkCtx N S B W) sTM (headW (mkCtx N S B W) P sTM (Lds.getD l zeroTM) (ln32TM (mkCtx N S B W) P)
        (phiE (mkCtx N S B W) P sTM (Lds.getD l zeroTM)).2) (Rds.getD l zeroTM) (μ.getD l 0)) := by
    intro l hl
    show ((List.range 5).map _).getD l [] = _
    rw [getD_map_lt _ _ _ 0 _ (by simpa using hl)]
    rw [getD_eq_get (List.range 5) l 0 (by simpa using hl), List.getElem_range]
  have hV : ∀ l k, l < 5 → k < μ.getD l 0 → EOK (mkCtx N S B W) ((Vs.getD l []).getD k zeroTM)
      (fun t => J t k (xs t l) / (k.factorial : ℝ)) := by
    intro l k hl hk
    rw [hVs l hl]
    obtain ⟨hphi, hE⟩ := phiE_eok hg hS1 P hs (hLd l hl) (hd l hl)
    by_cases h0 : P.mode = 0
    · rw [beq_true_of h0]
      refine (jetsTM_eok hg hs hphi hE (hRd l hl) (hd l hl) _ k hk).congr (fun t _ => ?_)
      simp only [hJ, alphaF, betaF, if_pos h0, ite_self, zero_add, one_mul]
    · rw [beq_false_of h0]
      refine (jetsW_eok hg hs (headW_eok hg hS1 P h0 hs (hLd l hl) hE (hd l hl)) (hRd l hl) (hd l hl) _ k hk).congr
        (fun t _ => ?_)
      simp only [hJ, betaF, if_neg h0]
  -- gaps
  have hrow : ∀ h < 5, (Hs.getD h []).length = 5 := by
    intro h hh
    show ((Xs.map (fun Xh => Xs.map (fun Xl => refresh (mkCtx N S B W) (add (mkCtx N S B W) Xh
      (neg (mkCtx N S B W) Xl))))).getD h []).length = 5
    rw [getD_map_lt _ _ _ zeroTM _ (by rw [hlen5]; exact hh), List.length_map, hlen5]
  have hHs : ∀ h l, h < 5 → l < 5 → (Hs.getD h []).getD l zeroTM =
      refresh (mkCtx N S B W) (add (mkCtx N S B W) (Xs.getD h zeroTM) (neg (mkCtx N S B W) (Xs.getD l zeroTM))) := by
    intro h l hh hl
    show ((Xs.map (fun Xh => Xs.map (fun Xl => refresh (mkCtx N S B W) (add (mkCtx N S B W) Xh
      (neg (mkCtx N S B W) Xl))))).getD h []).getD l zeroTM = _
    rw [getD_map_lt _ _ _ zeroTM _ (by rw [hlen5]; exact hh), getD_map_lt _ _ _ zeroTM _ (by rw [hlen5]; exact hl)]
  have hH : ∀ h l, h < 5 → l < 5 → h ≠ l →
      EOK (mkCtx N S B W) ((Hs.getD h []).getD l zeroTM) (fun t => xs t h - xs t l) := by
    intro h l hh hl _
    rw [hHs h l hh hl]
    exact (refresh_eok hg (add_eok (hX h hh) (neg_eok (hX l hl) rfl) rfl)).congr (fun t _ => by ring)
  have hGs : ∀ h l, h < 5 → l < 5 → (Gs.getD h []).getD l zeroTM =
      invN (mkCtx N S B W) P.kN P.tol ((Hs.getD h []).getD l zeroTM) := by
    intro h l hh hl
    show ((Hs.map (fun row => row.map (invN (mkCtx N S B W) P.kN P.tol))).getD h []).getD l zeroTM = _
    rw [getD_map_lt _ _ _ [] _ (by show h < (hsOf (mkCtx N S B W) Xs).length; simp [hsOf, hlen5, hh]),
      getD_map_lt _ _ _ zeroTM _ (by rw [hrow h hh]; exact hl)]
  have hG : ∀ h l, h < 5 → l < 5 → h ≠ l → ((Gs.getD h []).getD l zeroTM).ok = true →
      (∀ t ∈ Set.Icc (-1 : ℝ) 1, xs t h - xs t l ≠ 0) ∧
        Encl (mkCtx N S B W) ((Gs.getD h []).getD l zeroTM) (fun t => (xs t h - xs t l)⁻¹) := by
    intro h l hh hl hne hok'
    rw [hGs h l hh hl] at hok' ⊢
    exact invN_eok hg (hH h l hh hl hne) _ _ hok'
  -- labels
  have hlabD : ∀ k, labels.getD k 0 = lab5 (m 4) (m 3) (m 2) (m 1) (m 0) k :=
    fun k => labelsOf_getD (m 4) (m 3) (m 2) (m 1) (m 0) k
  have hn : labels.length = m 4 + m 3 + m 2 + m 1 + m 0 := labelsOf_length (m 4) (m 3) (m 2) (m 1) (m 0)
  have hμg : ∀ l, μ.getD l 0 = [m 4, m 3, m 2, m 1, m 0].getD l 0 := fun l => rfl
  set zE : ℝ → ℕ → ℝ := fun t k => expandedProfileNode (sourceNodes (a t)) (m ∘ sourceNodeOrder) k with hzE
  have H : TabCtx (mkCtx N S B W) Vs Hs Gs labels zE xs J (fun l => μ.getD l 0) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, hV, hH, hG⟩
    · intro k _
      rw [hlabD]; unfold lab5; split_ifs <;> omega
    · intro t _ k hk
      rw [hn] at hk
      rw [hlabD, lab5_eq_profileLabel m k hk]
      show sourceNodes (a t) (profileLabel (m ∘ sourceNodeOrder) k) = nodeF (a t) _
      simp only [nodeF, dif_pos (profileLabel (m ∘ sourceNodeOrder) k).isLt, Fin.eta]
    · intro t ht h l hh hl he
      exact nodeF_inj (hphys t ht) h l hh hl he
    · intro i j hij hj he
      rw [hn] at hj
      rw [hlabD, hlabD] at he
      rw [hlabD, hμg]
      rcases lab5_spec (m 4) (m 3) (m 2) (m 1) (m 0) i (by omega) with ⟨hi1, hi2⟩ | ⟨hi1, hi2⟩ | ⟨hi1, hi2⟩ |
        ⟨hi1, hi2⟩ | ⟨hi1, hi2⟩ <;>
      rcases lab5_spec (m 4) (m 3) (m 2) (m 1) (m 0) j hj with ⟨hj1, hj2⟩ | ⟨hj1, hj2⟩ | ⟨hj1, hj2⟩ |
        ⟨hj1, hj2⟩ | ⟨hj1, hj2⟩ <;>
      rw [hi1] at he ⊢ <;> rw [hj1] at he <;> simp at he ⊢ <;> omega
    · intro k hk
      rw [hn] at hk
      rw [hlabD, hμg]
      rcases lab5_spec (m 4) (m 3) (m 2) (m 1) (m 0) k hk with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
        ⟨h1, h2⟩ <;> rw [h1] <;> simp <;> omega
  -- the first column
  have hcol0 : ∀ i < col0.length, EOK (mkCtx N S B W) (col0.getD i zeroTM)
      (fun t => confluentTable (zE t) (J t) 0 i) := by
    intro i hi
    have hil : i < labels.length := by simpa [hcol0def] using hi
    rw [getD_map_lt _ _ _ 0 _ hil]
    have hl5 := H.lab_lt i hil
    have hpos := H.mu_pos i hil
    refine (hV _ 0 hl5 hpos).congr (fun t ht => ?_)
    show J t 0 (xs t (labels.getD i 0)) / ((0 : ℕ).factorial : ℝ) = confluentTable (zE t) (J t) 0 i
    rw [confluentTable, H.hz t ht i hil, Nat.factorial_zero, Nat.cast_one, div_one]
  have hc0len : col0.length = labels.length := by simp [hcol0def]
  have hcsE := newtonCoeffs_sound hg H labels.length 0 col0 (by rw [hc0len, Nat.add_zero]) (by omega) hcol0
  have hcsl : cs.length = labels.length := newtonCoeffs_length _ _ _ _ _ _ _ _
  have HN := hornerN_sound hg H hX h4 cs hcsl (fun i hi => (hcsE i hi).congr (fun t _ => by rw [Nat.zero_add]))
    labels.length le_rfl
  rw [Nat.sub_self, List.drop_zero, List.drop_zero] at HN
  -- the old Hermite polynomial
  have hsum : ∑ i, m i = D + 1 := hm.1
  rw [profile_total] at hsum
  have hbridge : ∀ t ∈ Set.Icc (-1 : ℝ) 1, snh zE J t labels.length 0 =
      Polynomial.C (alphaF P S (s t)) + Polynomial.C (betaF P S (s t)) * hermitePolynomial (s t) (aS (s t)) m := by
    intro t ht
    have hinj := sourceNodes_injective (hphys t ht)
    have hc := (hermite_constructor (sourceNodes (a t)) (m ∘ sourceNodeOrder) (J t) hinj).2.2.2.2
    have hs' : (∑ i, (m ∘ sourceNodeOrder) i) = labels.length := by
      rw [profile_total, hn]; rfl
    have hpos : 0 < ∑ i, (m ∘ sourceNodeOrder) i := by rw [hs']; omega
    have haff : profileHermite (sourceNodes (a t)) (m ∘ sourceNodeOrder) (J t) =
        Polynomial.C (alphaF P S (s t)) + Polynomial.C (betaF P S (s t)) *
          profileHermite (sourceNodes (a t)) (m ∘ sourceNodeOrder) (potentialJet (s t)) :=
      profileHermite_affine (sourceNodes (a t)) (m ∘ sourceNodeOrder) (potentialJet (s t)) hinj hpos _ _
    rw [hs'] at hc
    rw [← hermitePolynomial_source_order (s t) (a t) m (hphys t ht), ← haff, ← hc]
    rfl
  refine ⟨by rw [HN.1, hn]; omega, fun j hj => ?_⟩
  have hjn : j < labels.length := by rw [hn]; omega
  exact (HN.2.1 j hjn).congr (fun t ht => by rw [hbridge t ht])

theorem hrest_length (c : Ctx) (x : TM) (neg1 : Bool) : ∀ L : List TM, (hrest c x neg1 L).length = L.length
  | [] => rfl
  | [_] => rfl
  | p :: q :: rest => by
    show (_ :: hrest c x neg1 (q :: rest)).length = _
    rw [List.length_cons, hrest_length c x neg1 (q :: rest)]
    rfl

theorem hstep_length (c : Ctx) (x : TM) (neg1 : Bool) (ci : TM) :
    ∀ L : List TM, (hstep c x neg1 ci L).length = L.length + 1
  | [] => rfl
  | p :: ps => by
    show (_ :: hrest c x neg1 (p :: ps)).length = _
    rw [List.length_cons, hrest_length]

theorem hornerN_length (c : Ctx) (Xs : List TM) :
    ∀ (ls : List ℕ) (cs : List TM), cs.length = ls.length → (hornerN c Xs ls cs).length = ls.length
  | [], _, _ => rfl
  | _ :: _, [], h => absurd h (by simp)
  | l :: ls, ci :: cs, h => by
    show (hstep c (Xs.getD l zeroTM) (Nat.beq l 4) ci (hornerN c Xs ls cs)).length = _
    rw [hstep_length, hornerN_length c Xs ls cs (by simpa using h), List.length_cons]

/-- the pipeline has one entry per Hermite condition (no hypotheses) -/
theorem targetCoeffs0_length (c : Ctx) (P : Par) (m : Fin 5 → ℕ) (sTM A : TM) :
    (targetCoeffs0 c P [m 0, m 1, m 2, m 3, m 4] sTM A).length = m 4 + m 3 + m 2 + m 1 + m 0 := by
  show (hornerN c _ (labelsOf (srcMult [m 0, m 1, m 2, m 3, m 4])) (newtonCoeffs c _ _ _ _ _ 0 _)).length = _
  rw [hornerN_length _ _ _ _ (newtonCoeffs_length _ _ _ _ _ _ _ _)]
  exact labelsOf_length (m 4) (m 3) (m 2) (m 1) (m 0)

theorem targetCoeffsU0_length (c : Ctx) (P : Par) (m : Fin 5 → ℕ) (sTM A : TM) :
    (targetCoeffsU0 c P [m 0, m 1, m 2, m 3, m 4] sTM A).length = m 4 + m 3 + m 2 + m 1 + m 0 := by
  unfold targetCoeffsU0
  cases Nat.beq P.mode 1
  · simp only [cond_false]; exact targetCoeffs0_length c P m sTM A
  · simp only [cond_true, List.length_map]; exact targetCoeffs0_length c P m sTM A

/-- unit balance at a fixed order (modes 0, 1): coefficient `j ∈ [1, D]` of `targetCoeffsU0` encloses `H_j` -/
theorem targetU0_eok (hg : Good N S B W) (hS2 : 2 ≤ S) {sTM A : TM} {s : ℝ → ℝ}
    (hs : Encl (mkCtx N S B W) sTM s) (hs0 : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ s t)
    (hA : Encl (mkCtx N S B W) A (fun t => aS (s t))) (P : Par) (hP : P.mode ≤ 1) {D : ℕ} (m : Fin 5 → ℕ)
    (hm : Profile.Valid D m) (j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ D) :
    EOK (mkCtx N S B W) ((targetCoeffsU0 (mkCtx N S B W) P [m 0, m 1, m 2, m 3, m 4] sTM A).getD j zeroTM)
      (fun t => (hermitePolynomial (s t) (aS (s t)) m).coeff j) := by
  obtain ⟨hlen, hgen⟩ := targetCoeffs_gen hg hS2 hs hs0 hA P m hm
  intro hokj
  by_cases h1 : P.mode = 1
  · have e : targetCoeffsU0 (mkCtx N S B W) P [m 0, m 1, m 2, m 3, m 4] sTM A =
        (targetCoeffs0 (mkCtx N S B W) P [m 0, m 1, m 2, m 3, m 4] sTM A).map (fun X => divR (mkCtx N S B W) X
          (smul (mkCtx N S B W) false (2 ^ (S - P.ek)) 0 sTM)
          (invN (mkCtx N S B W) P.kN P.tol (smul (mkCtx N S B W) false (2 ^ (S - P.ek)) 0 sTM))) := by
      show cond (Nat.beq P.mode 1) _ _ = _
      rw [beq_true_of h1]; rfl
    rw [e] at hokj ⊢
    have hjl : j < (targetCoeffs0 (mkCtx N S B W) P [m 0, m 1, m 2, m 3, m 4] sTM A).length := by omega
    rw [getD_map_lt _ _ _ zeroTM _ hjl] at hokj ⊢
    obtain ⟨hFok, hGok, hRok⟩ := divR_ok hokj
    have hsS : EOK (mkCtx N S B W) (smul (mkCtx N S B W) false (2 ^ (S - P.ek)) 0 sTM)
        (fun t => (((2 ^ (S - P.ek) : ℕ) : ℝ) / 2 ^ S) * s t) :=
      smul_eok hg (EOK.of_encl hs) false _ 0 _ (by simp)
    have hIS := invN_eok hg hsS P.kN P.tol hRok
    refine (divR_sound hg (hgen j hj hFok) (hsS hGok) hIS.2 hIS.1 hokj).congr (fun t ht => ?_)
    have hst := hIS.1 t ht
    simp only [alphaF, betaF, if_neg (show P.mode ≠ 0 by omega), if_pos h1]
    rw [Polynomial.coeff_add, Polynomial.coeff_C, if_neg (show j ≠ 0 by omega), zero_add, Polynomial.coeff_C_mul]
    exact mul_div_cancel_left₀ _ hst
  · have h0 : P.mode = 0 := by omega
    have e : targetCoeffsU0 (mkCtx N S B W) P [m 0, m 1, m 2, m 3, m 4] sTM A =
        targetCoeffs0 (mkCtx N S B W) P [m 0, m 1, m 2, m 3, m 4] sTM A := by
      show cond (Nat.beq P.mode 1) _ _ = _
      rw [beq_false_of h1]; rfl
    rw [e] at hokj ⊢
    refine (hgen j hj hokj).congr (fun t _ => ?_)
    simp only [alphaF, betaF, if_pos h0, Polynomial.C_0, Polynomial.C_1, zero_add, one_mul]

/-- Riesz balance at a fixed order (mode ≥ 2): coefficient `j ∈ [1, D]` of `targetCoeffs0` encloses
`balancedMultiplier cR (s t) · H_j` -/
theorem targetR0_eok (hg : Good N S B W) (hS2 : 2 ≤ S) {sTM A : TM} {s : ℝ → ℝ}
    (hs : Encl (mkCtx N S B W) sTM s) (hs0 : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ s t)
    (hA : Encl (mkCtx N S B W) A (fun t => aS (s t))) (P : Par) (hP : 2 ≤ P.mode) {D : ℕ} (m : Fin 5 → ℕ)
    (hm : Profile.Valid D m) (j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ D) :
    EOK (mkCtx N S B W) ((targetCoeffs0 (mkCtx N S B W) P [m 0, m 1, m 2, m 3, m 4] sTM A).getD j zeroTM)
      (fun t => Blueprint.CAP.balancedMultiplier (P.cR : ℝ) (s t) * (hermitePolynomial (s t) (aS (s t)) m).coeff j) := by
  obtain ⟨hlen, hgen⟩ := targetCoeffs_gen hg hS2 hs hs0 hA P m hm
  intro hokj
  refine (hgen j hj hokj).congr (fun t _ => ?_)
  simp only [alphaF, betaF, if_neg (show P.mode ≠ 0 by omega), if_neg (show P.mode ≠ 1 by omega),
    Blueprint.CAP.balancedMultiplier]
  rw [Polynomial.coeff_add, Polynomial.coeff_C, if_neg (show j ≠ 0 by omega), zero_add, Polynomial.coeff_C_mul]
  ring

/-- the internal order `N + dN` (T3): an enclosure at the inner order, truncated, is an enclosure at order `N`
(the flag `innerOk` certifies `Good (N + dN)`) -/
theorem inner_trunc (hg : Good N S B W) (dN : ℕ) {T : TM} {f : ℝ → ℝ}
    (hin : Good (N + dN) S B W → EOK (mkCtx (N + dN) S B W) T f) :
    EOK (mkCtx N S B W) (truncTo (mkCtx (N + dN) S B W) (mkCtx N S B W) (innerOk (mkCtx N S B W) dN) T) f := by
  intro hok
  have hok' : (T.ok && innerOk (mkCtx N S B W) dN) = true := hok
  simp only [Bool.and_eq_true] at hok'
  have hb : N + dN + 1 ≤ 2 ^ B := Nat.le_of_ble_eq_true hok'.2
  have hg2 : Good (N + dN) S B W := ⟨hg.B1, hg.BW, hg.SW, hb⟩
  exact truncTo_sound hg2 (Nat.le_add_right N dN) _ (hin hg2 hok'.1)

/-- **Unit-balance targets** (modes 0, 1; `targetCoeffsU` runs at order `N + P.dN` and divides mode-1 coefficients
by `2^-ek s`): for `1 ≤ j ≤ D`, coefficient `j` encloses `(hermitePolynomial (s t) (aS (s t)) m).coeff j`. -/
theorem targetU_sound (hg : Good N S B W) (hS2 : 2 ≤ S) {sTM A : TM} {s : ℝ → ℝ}
    (hs : Encl (mkCtx N S B W) sTM s) (hs0 : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ s t)
    (hA : Encl (mkCtx N S B W) A (fun t => aS (s t))) (P : Par) (hP : P.mode ≤ 1) {D : ℕ} (m : Fin 5 → ℕ)
    (hm : Profile.Valid D m)
    (hok : allOkL ((targetCoeffsU (mkCtx N S B W) P [m 0, m 1, m 2, m 3, m 4] sTM A).drop 1) = true)
    (j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ D) :
    Encl (mkCtx N S B W) ((targetCoeffsU (mkCtx N S B W) P [m 0, m 1, m 2, m 3, m 4] sTM A).getD j zeroTM)
      (fun t => (hermitePolynomial (s t) (aS (s t)) m).coeff j) := by
  have e : targetCoeffsU (mkCtx N S B W) P [m 0, m 1, m 2, m 3, m 4] sTM A =
      (targetCoeffsU0 (mkCtx (N + P.dN) S B W) P [m 0, m 1, m 2, m 3, m 4]
        (liftTo (mkCtx N S B W) (mkCtx (N + P.dN) S B W) sTM) (liftTo (mkCtx N S B W) (mkCtx (N + P.dN) S B W) A)).map
        (truncTo (mkCtx (N + P.dN) S B W) (mkCtx N S B W) (innerOk (mkCtx N S B W) P.dN)) := rfl
  rw [e] at hok ⊢
  have hsum : ∑ i, m i = D + 1 := hm.1
  rw [profile_total] at hsum
  have hjl : j < (targetCoeffsU0 (mkCtx (N + P.dN) S B W) P [m 0, m 1, m 2, m 3, m 4]
      (liftTo (mkCtx N S B W) (mkCtx (N + P.dN) S B W) sTM)
      (liftTo (mkCtx N S B W) (mkCtx (N + P.dN) S B W) A)).length := by
    rw [targetCoeffsU0_length]; omega
  have hokj := allOkL_drop1 _ hok j hj1 (by rw [List.length_map]; exact hjl)
  rw [getD_map_lt _ _ _ zeroTM _ hjl] at hokj ⊢
  refine inner_trunc hg P.dN (fun hg2 => ?_) hokj
  have hN : N ≤ N + P.dN := Nat.le_add_right N P.dN
  exact targetU0_eok hg2 hS2 (liftTo_sound hg hN hs) hs0 (liftTo_sound hg hN hA) P hP m hm j hj1 hj

/-- **Riesz-balanced targets** (mode 2, `targetCoeffs` at order `N + P.dN`): for `1 ≤ j ≤ D`, coefficient `j`
encloses `balancedMultiplier cR (s t) · (hermitePolynomial (s t) (aS (s t)) m).coeff j`. -/
theorem targetR_sound (hg : Good N S B W) (hS2 : 2 ≤ S) {sTM A : TM} {s : ℝ → ℝ}
    (hs : Encl (mkCtx N S B W) sTM s) (hs0 : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ s t)
    (hA : Encl (mkCtx N S B W) A (fun t => aS (s t))) (P : Par) (hP : 2 ≤ P.mode) {D : ℕ} (m : Fin 5 → ℕ)
    (hm : Profile.Valid D m)
    (hok : allOkL ((targetCoeffs (mkCtx N S B W) P [m 0, m 1, m 2, m 3, m 4] sTM A).drop 1) = true)
    (j : ℕ) (hj1 : 1 ≤ j) (hj : j ≤ D) :
    Encl (mkCtx N S B W) ((targetCoeffs (mkCtx N S B W) P [m 0, m 1, m 2, m 3, m 4] sTM A).getD j zeroTM)
      (fun t => Blueprint.CAP.balancedMultiplier (P.cR : ℝ) (s t) * (hermitePolynomial (s t) (aS (s t)) m).coeff j) := by
  have e : targetCoeffs (mkCtx N S B W) P [m 0, m 1, m 2, m 3, m 4] sTM A =
      (targetCoeffs0 (mkCtx (N + P.dN) S B W) P [m 0, m 1, m 2, m 3, m 4]
        (liftTo (mkCtx N S B W) (mkCtx (N + P.dN) S B W) sTM) (liftTo (mkCtx N S B W) (mkCtx (N + P.dN) S B W) A)).map
        (truncTo (mkCtx (N + P.dN) S B W) (mkCtx N S B W) (innerOk (mkCtx N S B W) P.dN)) := rfl
  rw [e] at hok ⊢
  have hsum : ∑ i, m i = D + 1 := hm.1
  rw [profile_total] at hsum
  have hjl : j < (targetCoeffs0 (mkCtx (N + P.dN) S B W) P [m 0, m 1, m 2, m 3, m 4]
      (liftTo (mkCtx N S B W) (mkCtx (N + P.dN) S B W) sTM)
      (liftTo (mkCtx N S B W) (mkCtx (N + P.dN) S B W) A)).length := by
    rw [targetCoeffs0_length]; omega
  have hokj := allOkL_drop1 _ hok j hj1 (by rw [List.length_map]; exact hjl)
  rw [getD_map_lt _ _ _ zeroTM _ hjl] at hokj ⊢
  refine inner_trunc hg P.dN (fun hg2 => ?_) hokj
  have hN : N ≤ N + P.dN := Nat.le_add_right N P.dN
  exact targetR0_eok hg2 hS2 (liftTo_sound hg hN hs) hs0 (liftTo_sound hg hN hA) P hP m hm j hj1 hj

/-- **D12 form** (F2a statement): with `D12.hfun s m j x = (hermitePolynomial (s x) (aS (s x)) m).coeff (j+1)`,
`∀ j : Fin 12, Encl c (targetCoeffsU … |>.getD (j+1) zeroTM) (D12.hfun s m j)`. -/
theorem targetTMs_sound (hg : Good N S B W) (hS2 : 2 ≤ S) {sTM A : TM} {s : ℝ → ℝ}
    (hs : Encl (mkCtx N S B W) sTM s) (hs0 : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ s t)
    (hA : Encl (mkCtx N S B W) A (fun t => aS (s t))) (P : Par) (hP : P.mode ≤ 1) (m : Fin 5 → ℕ)
    (hm : Profile.Valid 12 m)
    (hok : allOkL ((targetCoeffsU (mkCtx N S B W) P [m 0, m 1, m 2, m 3, m 4] sTM A).drop 1) = true) (j : Fin 12) :
    Encl (mkCtx N S B W) ((targetCoeffsU (mkCtx N S B W) P [m 0, m 1, m 2, m 3, m 4] sTM A).getD (j.val + 1) zeroTM)
      (fun x => (hermitePolynomial (s x) (aS (s x)) m).coeff (j.val + 1)) :=
  targetU_sound hg hS2 hs hs0 hA P hP m hm hok (j.val + 1) (by omega) (by omega)

/-- **D14 form** (unit balance, `D = 14`). -/
theorem targetTMs14_sound (hg : Good N S B W) (hS2 : 2 ≤ S) {sTM A : TM} {s : ℝ → ℝ}
    (hs : Encl (mkCtx N S B W) sTM s) (hs0 : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ s t)
    (hA : Encl (mkCtx N S B W) A (fun t => aS (s t))) (P : Par) (hP : P.mode ≤ 1) (m : Fin 5 → ℕ)
    (hm : Profile.Valid 14 m)
    (hok : allOkL ((targetCoeffsU (mkCtx N S B W) P [m 0, m 1, m 2, m 3, m 4] sTM A).drop 1) = true) (j : Fin 14) :
    Encl (mkCtx N S B W) ((targetCoeffsU (mkCtx N S B W) P [m 0, m 1, m 2, m 3, m 4] sTM A).getD (j.val + 1) zeroTM)
      (fun x => (hermitePolynomial (s x) (aS (s x)) m).coeff (j.val + 1)) :=
  targetU_sound hg hS2 hs hs0 hA P hP m hm hok (j.val + 1) (by omega) (by omega)

/-- Riesz-balanced Hermite coefficient `j + 1` at exponent `s x`, normalization `β x = balancedMultiplier c (s x)`:
the D16/D18 analogue of `CoeffMap.D12.hfun` (`= β x · (hermitePolynomial (s x) (aS (s x)) m).coeff (j+1)`, the
summand of `CoeffMap.retained_target_sum` with this `β`). -/
noncomputable def hfunR (c : ℝ) (s : ℝ → ℝ) (m : Fin 5 → ℕ) {D : ℕ} (j : Fin D) (x : ℝ) : ℝ :=
  Blueprint.CAP.balancedMultiplier c (s x) * (hermitePolynomial (s x) (aS (s x)) m).coeff (j.val + 1)

/-- **Riesz form** (`D = 16, 18`): `∀ j : Fin D, Encl c (targetCoeffs … |>.getD (j+1) zeroTM) (hfunR P.cR s m j)`. -/
theorem targetTMsR_sound (hg : Good N S B W) (hS2 : 2 ≤ S) {sTM A : TM} {s : ℝ → ℝ}
    (hs : Encl (mkCtx N S B W) sTM s) (hs0 : ∀ t ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ s t)
    (hA : Encl (mkCtx N S B W) A (fun t => aS (s t))) (P : Par) (hP : 2 ≤ P.mode) {D : ℕ} (m : Fin 5 → ℕ)
    (hm : Profile.Valid D m)
    (hok : allOkL ((targetCoeffs (mkCtx N S B W) P [m 0, m 1, m 2, m 3, m 4] sTM A).drop 1) = true) (j : Fin D) :
    Encl (mkCtx N S B W) ((targetCoeffs (mkCtx N S B W) P [m 0, m 1, m 2, m 3, m 4] sTM A).getD (j.val + 1) zeroTM)
      (hfunR (P.cR : ℝ) s m j) :=
  targetR_sound hg hS2 hs hs0 hA P hP m hm hok (j.val + 1) (by omega) (by omega)

#print axioms targetCoeffs_gen
#print axioms targetU0_eok
#print axioms targetU_sound
#print axioms targetR_sound
#print axioms targetTMs_sound
#print axioms targetTMs14_sound
#print axioms targetTMsR_sound

end ThomsonCompact.Target
