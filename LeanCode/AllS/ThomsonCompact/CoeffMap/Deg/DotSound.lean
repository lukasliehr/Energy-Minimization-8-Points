import ThomsonCompact.CoeffMap.Deg.Dot
import ThomsonCompact.Packed.SoundMul
import ThomsonCompact.Packed.Comp
import ThomsonCompact.CoeffMap.Contract

/-!
# Soundness of the packed dot product (F2f)

`dotTM_sound`: if every factor `Aᵢ`, `Bᵢ` encloses `fᵢ`, `gᵢ` (once its `ok` flag is set) and `dotTM c L` is `ok`,
then `dotTM c L` encloses `Σᵢ fᵢ gᵢ`. The proof is `Packed.mul_sound` with the product polynomial `convL csA csB`
replaced by the pointwise sum `Σᵢ convL csAᵢ csBᵢ` (`dot_rep`: residues, magnitude digits, domination, digit sum and
the real product errors are additive), then the same truncation and rounding lemmas (`round_signed`, `round_abs`,
`eval_round`).
-/

namespace ThomsonCompact.CoeffMap.Deg

open ThomsonCompact.Packed ThomsonCompact.CoeffMap
open scoped BigOperators

variable {N S B W : ℕ}

theorem dotAcc_nil : dotAcc [] = (0, 0, 0, 0, true) := rfl

theorem dotAcc_cons (A B : TM) (L : List (TM × TM)) : dotAcc ((A, B) :: L) =
    (A.v * B.v + (dotAcc L).1, A.a * B.a + (dotAcc L).2.1, A.s * B.e + B.s * A.e + A.e * B.e + (dotAcc L).2.2.1,
      A.s * B.s + (dotAcc L).2.2.2.1, A.ok && B.ok && (dotAcc L).2.2.2.2) := rfl

theorem dotAcc_ok : ∀ {L : List (TM × TM)}, (dotAcc L).2.2.2.2 = true → ∀ p ∈ L, p.1.ok = true ∧ p.2.ok = true
  | [], _, _, hp => absurd hp List.not_mem_nil
  | (A, B) :: L, h, p, hp => by
    rw [dotAcc_cons] at h
    simp only [Bool.and_eq_true] at h
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨h.1.1, h.1.2⟩
    · exact dotAcc_ok h.2 p hp

theorem replicate_zero_dom (n : ℕ) : Dom (List.replicate n (0 : ℤ)) (List.replicate n 0) := by
  intro k
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split_ifs <;> simp

theorem horner_rep0 (t : ℤ) : ∀ n, horner t (List.replicate n (0 : ℤ)) = 0
  | 0 => rfl
  | n + 1 => by rw [List.replicate_succ, horner_cons, horner_rep0 t n]; ring

theorem evalZ_rep0 (t : ℝ) (n : ℕ) : evalZ (List.replicate n (0 : ℤ)) t = 0 := by
  unfold evalZ
  rw [List.map_replicate, Int.cast_zero]
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, horner_cons, ih]; ring

/-- **Representation of the dot-product accumulators.** -/
theorem dot_rep (hg : Good N S B W) : ∀ (L : List (TM × TM)) (F : List ((ℝ → ℝ) × (ℝ → ℝ))),
    List.Forall₂ (fun p q => Encl (mkCtx N S B W) p.1 q.1 ∧ Encl (mkCtx N S B W) p.2 q.2) L F →
    ∃ z γ, z.length = 2 * N + 1 ∧ γ.length = 2 * N + 1 ∧
      ((dotAcc L).1 : ℤ) % 2 ^ (W * (2 * N + 1)) = horner (2 ^ W : ℤ) z % 2 ^ (W * (2 * N + 1)) ∧
      (dotAcc L).2.1 = Nat.ofDigits (2 ^ W) γ ∧ Dom z γ ∧ γ.sum = (dotAcc L).2.2.2.1 ∧
      ∀ t ∈ Set.Icc (-1 : ℝ) 1, |(F.map fun q => q.1 t * q.2 t).sum - evalZ z t / (2 ^ S * 2 ^ S)| ≤
        ((dotAcc L).2.2.1 : ℝ) / (2 ^ S * 2 ^ S)
  | [], [], List.Forall₂.nil => by
    refine ⟨List.replicate (2 * N + 1) 0, List.replicate (2 * N + 1) 0, by simp, by simp, ?_, ?_,
      replicate_zero_dom _, by simp [dotAcc_nil], fun t _ => ?_⟩
    · rw [dotAcc_nil, horner_rep0]; rfl
    · rw [dotAcc_nil, Nat.ofDigits_replicate_zero]
    · rw [dotAcc_nil, evalZ_rep0]; simp
  | (A, B') :: L, (f, g) :: F, List.Forall₂.cons ⟨hA, hB⟩ hL => by
    obtain ⟨z, γ, hzl, hγl, hv, ha, hdom, hsum, hreal⟩ := dot_rep hg L F hL
    obtain ⟨csA, alA, hRA, hfA⟩ := hA
    obtain ⟨csB, alB, hRB, hfB⟩ := hB
    have hlA : csA.length = N + 1 := hRA.lcs
    have hlB : csB.length = N + 1 := hRB.lcs
    have hlaA : alA.length = N + 1 := hRA.lal
    have hlaB : alB.length = N + 1 := hRB.lal
    have hcl : (convL csA csB).length = 2 * N + 1 := by
      rw [length_convL csB (List.ne_nil_of_length_pos (by omega)) csA (List.ne_nil_of_length_pos (by omega)), hlA, hlB]
      omega
    have hal : (convL alA alB).length = 2 * N + 1 := by
      rw [length_convL alB (List.ne_nil_of_length_pos (by omega)) alA (List.ne_nil_of_length_pos (by omega)), hlaA,
        hlaB]
      omega
    have hA' := hRA.hv
    have hB' := hRB.hv
    simp only [mk_W, mk_K] at hA' hB'
    refine ⟨addL (convL csA csB) z, addL (convL alA alB) γ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [length_addL, hcl, hzl, max_self]
    · rw [length_addL, hal, hγl, max_self]
    · rw [dotAcc_cons]
      push_cast
      rw [Int.add_emod, Int.mul_emod, hA', hB', Int.emod_emod, Int.emod_emod, ← Int.mul_emod, hv, ← Int.add_emod,
        horner_addL, horner_convL]
    · rw [dotAcc_cons, ofDigits_addL, ofDigits_convL, ← ha]
      have h1 := hRA.ha
      have h2 := hRB.ha
      simp only [mk_W] at h1 h2
      rw [h1, h2]
    · exact Dom.addL (Dom.convL hRB.dom csA alA (by rw [hlA, hlaA]) hRA.dom) hdom
    · rw [sum_addL_nat, sum_convL, hsum, dotAcc_cons, ← hRA.hs, ← hRB.hs]
    · intro t ht
      have hta : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
      have hD : (0 : ℝ) < 2 ^ S := by positivity
      have h1 := hfA t ht
      have h2 := hfB t ht
      simp only [mk_S] at h1 h2
      have hpA := abs_evalZ_le_s hRA t hta
      have hpB := abs_evalZ_le_s hRB t hta
      have hprod := prod_err hD h1 h2 hpA hpB (by positivity) (by positivity)
      have hr := hreal t ht
      rw [dotAcc_cons, evalZ_addL, evalZ_convL, List.map_cons, List.sum_cons]
      push_cast
      have key : f t * g t + (F.map fun q => q.1 t * q.2 t).sum -
          (evalZ csA t * evalZ csB t + evalZ z t) / (2 ^ S * 2 ^ S) =
          (f t * g t - evalZ csA t * evalZ csB t / (2 ^ S * 2 ^ S)) +
            ((F.map fun q => q.1 t * q.2 t).sum - evalZ z t / (2 ^ S * 2 ^ S)) := by ring
      rw [key]
      refine (abs_add_le _ _).trans ?_
      have e : ((A.s : ℝ) * B'.e + B'.s * A.e + A.e * B'.e + ((dotAcc L).2.2.1 : ℝ)) / (2 ^ S * 2 ^ S) =
          ((A.s : ℝ) * B'.e + B'.s * A.e + A.e * B'.e) / (2 ^ S * 2 ^ S) + ((dotAcc L).2.2.1 : ℝ) / (2 ^ S * 2 ^ S) := by
        ring
      rw [e]
      exact add_le_add hprod hr

/-- The real error bookkeeping of the truncated, rounded dot product. -/
theorem dot_err_real {D F X X0 Zc Tl tl c1 c2 m eS : ℝ} (hD : 0 < D)
    (hprod : |F - X / (D * D)| ≤ eS / (D * D))
    (hzt : X = X0 + Tl) (htl : |Tl| ≤ tl) (hround : |X0 - D * Zc| ≤ m * D)
    (hc1 : eS / D ≤ c1) (hc2 : tl / D ≤ c2) :
    |F - Zc / D| ≤ (c1 + c2 + m) / D := by
  have hDD : 0 < D * D := by positivity
  have key : F - Zc / D = (F - X / (D * D)) + (X0 - D * Zc) / (D * D) + Tl / (D * D) := by
    rw [hzt]; field_simp; ring
  have b1 : |(X0 - D * Zc) / (D * D)| ≤ m / D := by
    rw [abs_div, abs_of_pos hDD, div_le_div_iff₀ hDD hD]
    nlinarith [abs_nonneg (X0 - D * Zc)]
  have b2 : |Tl / (D * D)| ≤ tl / (D * D) := by
    rw [abs_div, abs_of_pos hDD]; exact div_le_div_of_nonneg_right htl hDD.le
  have b3 : eS / (D * D) ≤ c1 / D := by
    rw [← div_div]; exact div_le_div_of_nonneg_right hc1 hD.le
  have b4 : tl / (D * D) ≤ c2 / D := by
    rw [← div_div]; exact div_le_div_of_nonneg_right hc2 hD.le
  rw [key]
  calc |(F - X / (D * D)) + (X0 - D * Zc) / (D * D) + Tl / (D * D)|
      ≤ |F - X / (D * D)| + |(X0 - D * Zc) / (D * D)| + |Tl / (D * D)| := abs_add_three _ _ _
    _ ≤ c1 / D + m / D + c2 / D := by linarith
    _ = (c1 + c2 + m) / D := by ring

/-- **Soundness of the packed dot product.** -/
theorem dotTM_sound (hg : Good N S B W) {L : List (TM × TM)} {F : List ((ℝ → ℝ) × (ℝ → ℝ))}
    (hL : List.Forall₂ (fun p q => EnclOk (mkCtx N S B W) p.1 q.1 ∧ EnclOk (mkCtx N S B W) p.2 q.2) L F) :
    EnclOk (mkCtx N S B W) (dotTM (mkCtx N S B W) L) (fun t => (F.map fun q => q.1 t * q.2 t).sum) := by
  intro hok
  have hokE : (dotTM (mkCtx N S B W) L).ok = ((dotAcc L).2.2.2.2 &&
      Nat.blt (dotAcc L).2.2.2.1 (Nat.mul (mkCtx N S B W).twoB (mkCtx N S B W).twoB) &&
      Nat.blt (dotTM (mkCtx N S B W) L).s (mkCtx N S B W).twoB) := rfl
  rw [hokE] at hok
  simp only [Bool.and_eq_true, Nat.blt_eq] at hok
  obtain ⟨⟨hall, hS2⟩, hs⟩ := hok
  have hL' : List.Forall₂ (fun p q => Encl (mkCtx N S B W) p.1 q.1 ∧ Encl (mkCtx N S B W) p.2 q.2) L F := by
    have hok' := dotAcc_ok hall
    clear hokE hs hS2 hall
    induction hL with
    | nil => exact List.Forall₂.nil
    | cons h _ ih =>
      exact List.Forall₂.cons ⟨h.1 (hok' _ (List.mem_cons_self ..)).1, h.2 (hok' _ (List.mem_cons_self ..)).2⟩
        (ih (fun p hp => hok' p (List.mem_cons_of_mem _ hp)))
  obtain ⟨z, γ, hzlen, hγlen, hV, hG, hdom, hγsum, hreal⟩ := dot_rep hg L F hL'
  have hW1 := hg.W1
  have hW0 : 0 < W := by omega
  have hS2' : (dotAcc L).2.2.2.1 < 2 ^ (2 * B) := by
    have : Nat.mul (mkCtx N S B W).twoB (mkCtx N S B W).twoB = 2 ^ (2 * B) := by
      show 2 ^ B * 2 ^ B = 2 ^ (2 * B); rw [two_mul, pow_add]
    rw [← this]; exact hS2
  have hzb : ∀ x ∈ z, |x| < 2 ^ (2 * B) := by
    intro x hx
    have h1 := hdom.abs_le_sum hx
    have h2 : ((γ.sum : ℕ) : ℤ) < 2 ^ (2 * B) := by rw [hγsum]; exact_mod_cast hS2'
    linarith
  have hγb : ∀ d ∈ γ, d < 2 ^ (2 * B) := fun d hd => (mem_le_sum hd).trans_lt (hγsum ▸ hS2')
  have hγW : ∀ d ∈ γ, d < 2 ^ W := fun d hd =>
    (hγb d hd).trans_le (Nat.pow_le_pow_right (by norm_num) (by have := hg.BW; omega))
  -- signed coefficients
  have hv := round_signed hg z hzlen hzb (dotAcc L).1 hV
  -- magnitude bounds
  have hsplit := ofDigits_take_drop hW0 γ hγW (N + 1)
  have hGm : (dotAcc L).2.1 &&& (mkCtx N S B W).maskWm = Nat.ofDigits (2 ^ W) (γ.take (N + 1)) := by
    rw [mk_maskWm, Nat.and_two_pow_sub_one_eq_mod, hG]; exact hsplit.1
  have hlt : (γ.take (N + 1)).length = N + 1 := by simp [hγlen]; omega
  have ha := round_abs hg (γ.take (N + 1)) hlt (fun d hd => hγb d (List.mem_of_mem_take hd))
  set alC := (γ.take (N + 1)).map (fun g => (g + (2 ^ S - 1)) / 2 ^ S) with halC
  have hsumC : alC.sum ≤ (dotAcc L).2.2.2.1 :=
    calc alC.sum ≤ (γ.take (N + 1)).sum := sum_map_ceil_le S _
      _ ≤ γ.sum := sum_take_le _ _
      _ = (dotAcc L).2.2.2.1 := hγsum
  have hmodC : Nat.ofDigits (2 ^ W) alC % (2 ^ W - 1) = alC.sum :=
    ofDigits_mod_pred (by have := hg.BW; omega) alC
      (lt_of_lt_of_le (lt_of_le_of_lt hsumC hS2') ((Nat.le_add_right _ _).trans hg.pow_lt.le))
  have haC : (dotTM (mkCtx N S B W) L).a = Nat.ofDigits (2 ^ W) alC := by
    show (((dotAcc L).2.1 &&& (mkCtx N S B W).maskWm) + (mkCtx N S B W).ceilAdd &&& (mkCtx N S B W).rmask) >>>
      (mkCtx N S B W).S = _
    rw [hGm]; exact ha
  have hsC : (dotTM (mkCtx N S B W) L).s = alC.sum := by
    show (dotTM (mkCtx N S B W) L).a % (mkCtx N S B W).modW = _
    rw [haC, mk_modW, hmodC]
  -- tail mass
  have htail : ((dotAcc L).2.1 >>> (W * (N + 1))) % (2 ^ W - 1) = (γ.drop (N + 1)).sum := by
    rw [Nat.shiftRight_eq_div_pow, hG, hsplit.2]
    apply ofDigits_mod_pred (by have := hg.BW; omega)
    have hdr : (γ.drop (N + 1)).sum ≤ γ.sum := by
      conv_rhs => rw [← List.take_append_drop (N + 1) γ]
      rw [List.sum_append]; omega
    have hg2 : γ.sum < 2 ^ (2 * B) := by rw [hγsum]; exact hS2'
    exact lt_of_le_of_lt hdr (lt_of_lt_of_le hg2 ((Nat.le_add_right _ _).trans hg.pow_lt.le))
  refine ⟨(z.take (N + 1)).map (fun x => x / 2 ^ S), alC, ⟨?_, ?_, ?_, haC, dom_round S hdom (N + 1), hsC, hs⟩, ?_⟩
  · simp [hzlen]; omega
  · show alC.length = N + 1
    rw [halC, List.length_map, hlt]
  · exact hv
  · intro t ht
    have hta : |t| ≤ 1 := abs_le.mpr ⟨ht.1, ht.2⟩
    have hD : (0 : ℝ) < 2 ^ S := by positivity
    have hprod := hreal t ht
    have hzt : evalZ z t = evalZ (z.take (N + 1)) t + t ^ (N + 1) * evalZ (z.drop (N + 1)) t :=
      evalZ_take_drop z (N + 1) t
    have htl : |t ^ (N + 1) * evalZ (z.drop (N + 1)) t| ≤ ((γ.drop (N + 1)).sum : ℝ) := by
      rw [abs_mul, abs_pow]
      have h3 := abs_evalZ_le (hdom.drop (N + 1)) t hta
      have h4 : |t| ^ (N + 1) ≤ 1 := pow_le_one₀ (abs_nonneg t) hta
      calc |t| ^ (N + 1) * |evalZ (z.drop (N + 1)) t| ≤ 1 * ((γ.drop (N + 1)).sum : ℝ) :=
            mul_le_mul h4 h3 (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
    have hround := eval_round S t hta (z.take (N + 1))
    rw [show (z.take (N + 1)).length = N + 1 by simp [hzlen]; omega] at hround
    have hcd1 := le_cdiv S (dotAcc L).2.2.1
    have hcd2 := le_cdiv S ((γ.drop (N + 1)).sum)
    push_cast at hround
    show |(F.map fun q => q.1 t * q.2 t).sum - evalZ ((z.take (N + 1)).map (fun x => x / 2 ^ S)) t / 2 ^ S| ≤
      ((cdiv S (dotAcc L).2.2.1 + cdiv S (((dotAcc L).2.1 >>> (W * (N + 1))) % (2 ^ W - 1)) + (N + 1) : ℕ) : ℝ) /
        2 ^ S
    rw [htail]
    push_cast
    exact dot_err_real hD hprod hzt htl hround hcd1 hcd2

#print axioms dotTM_sound

/-! ## Constants -/

theorem constQ_sound (hg : Good N S B W) (ng : Bool) (n d : ℕ) :
    EnclOk (mkCtx N S B W) (constQ (mkCtx N S B W) ng n d) (fun _ => qval (ng, n, d)) :=
  fun hok => constTM_sound hg ng _ 1 _ (ratMag_err (ng, n, d)) hok

theorem constI_sound (hg : Good N S B W) (m : ℕ) :
    EnclOk (mkCtx N S B W) (constI (mkCtx N S B W) m) (fun _ => (m : ℝ)) := by
  intro hok
  refine constTM_sound hg false _ 0 _ ?_ hok
  show |(m : ℝ) - (if false = true then -((Nat.mul m (2 ^ S) : ℕ) : ℝ) else ((Nat.mul m (2 ^ S) : ℕ) : ℝ)) / 2 ^ S| ≤
    ((0 : ℕ) : ℝ) / 2 ^ S
  simp only [Bool.false_eq_true, if_false, Nat.mul_eq]
  push_cast
  rw [mul_div_assoc, div_self (by positivity), mul_one, sub_self, abs_zero]
  simp

theorem powA_sound (hg : Good N S B W) {A : TM} {a : ℝ → ℝ} (hA : Encl (mkCtx N S B W) A a) :
    ∀ j, EnclOk (mkCtx N S B W) (powA (mkCtx N S B W) A j) (fun t => a t ^ j)
  | 0 => (constI_sound hg 1).congr (fun t _ => by simp)
  | j + 1 => by
    intro hok
    have hok' : (mul (mkCtx N S B W) (powA (mkCtx N S B W) A j) A).ok = true := hok
    have h := mul_sound hg (powA_sound hg hA j (mul_ok hok').1) hA hok'
    exact h.congr (fun t _ => by rw [pow_succ])

theorem zipPow_range (c : Ctx) (A : TM) : ∀ (L : List (Bool × ℕ × ℕ)) (k : ℕ),
    zipPow c L ((List.range' k L.length).map (powA c A)) =
      (L.zip (List.range' k L.length)).map fun x => (constQ c x.1.1 x.1.2.1 x.1.2.2, powA c A x.2)
  | [], _ => rfl
  | q :: L, k => by
    rw [List.length_cons, List.range'_succ, List.map_cons, List.zip_cons_cons, List.map_cons, ← zipPow_range c A L (k + 1)]
    rfl

theorem evalQ_zip (y : ℝ) : ∀ (L : List (Bool × ℕ × ℕ)) (k : ℕ),
    ((L.zip (List.range' k L.length)).map fun x => qval x.1 * y ^ x.2).sum = y ^ k * evalQ L y
  | [], _ => by simp [evalQ]
  | q :: L, k => by
    rw [List.length_cons, List.range'_succ, List.zip_cons_cons, List.map_cons, List.sum_cons, evalQ_zip y L (k + 1)]
    simp only [evalQ, pow_succ]
    ring

/-- **A polynomial at a TM by one dot product with the powers.** -/
theorem polyD_sound (hg : Good N S B W) {A : TM} {a : ℝ → ℝ} (hA : Encl (mkCtx N S B W) A a)
    (L : List (Bool × ℕ × ℕ)) :
    EnclOk (mkCtx N S B W) (polyD (mkCtx N S B W) A L) (fun t => evalQ L (a t)) := by
  unfold polyD powTab
  rw [mkList_eq, List.range_eq_range', zipPow_range]
  have h := dotTM_sound hg (forall₂_map_same (R := fun x y => EnclOk (mkCtx N S B W) x.1 y.1 ∧
      EnclOk (mkCtx N S B W) x.2 y.2)
    (f := fun x => (constQ (mkCtx N S B W) x.1.1 x.1.2.1 x.1.2.2, powA (mkCtx N S B W) A x.2))
    (g := fun x => ((fun _ => qval x.1), (fun t => a t ^ x.2)))
    (L.zip (List.range' 0 L.length)) (fun x _ => ⟨constQ_sound hg _ _ _, powA_sound hg hA x.2⟩))
  refine h.congr (fun t _ => ?_)
  have := evalQ_zip (a t) L 0
  rw [pow_zero, one_mul] at this
  rw [← this, List.map_map]
  rfl

theorem entTM_sound (hg : Good N S B W) {e : Option TM} {κ : ℝ → ℝ} (he : EntryOk (mkCtx N S B W) e κ) :
    EnclOk (mkCtx N S B W) (entTM (mkCtx N S B W) e) κ := by
  cases e with
  | none => exact (constI_sound hg 1).congr (fun t ht => by rw [he t ht]; norm_num)
  | some K => exact he

end ThomsonCompact.CoeffMap.Deg
