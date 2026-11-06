import ThomsonCompact.Packed.Round

/-!
# Packed exact magnitudes (`pabs`): correctness

`pabs c A` computes, with a constant number of bignum operations, the packed vector of the exact
magnitudes `|cₖ|` of a represented TM. Consequences: `rangeX c A = Σ|cₖ| + e` (`Rep.rangeX_eq`) and the
exact magnitude reset `refresh` (in `Comp.lean`).
-/

namespace ThomsonCompact.Packed
open Nat

/-! ## Digitwise operations on lists that are images of one digit list -/

theorem ofDigits_map_add (b : ℕ) (f g : ℕ → ℕ) : ∀ L : List ℕ,
    Nat.ofDigits b (L.map f) + Nat.ofDigits b (L.map g) = Nat.ofDigits b (L.map (fun x => f x + g x))
  | [] => by simp
  | d :: L => by
    simp only [List.map_cons, Nat.ofDigits_cons]
    rw [← ofDigits_map_add b f g L]; ring

theorem ofDigits_map_sub (b : ℕ) (f g : ℕ → ℕ) (L : List ℕ) (h : ∀ x ∈ L, g x ≤ f x) :
    Nat.ofDigits b (L.map f) - Nat.ofDigits b (L.map g) = Nat.ofDigits b (L.map (fun x => f x - g x)) := by
  have e : L.map f = L.map (fun x => (f x - g x) + g x) :=
    List.map_congr_left (fun x hx => (Nat.sub_add_cancel (h x hx)).symm)
  rw [e, ← ofDigits_map_add, Nat.add_sub_cancel]

theorem ofDigits_land_map {W : ℕ} (g : ℕ → ℕ) : ∀ L : List ℕ, (∀ x ∈ L, x < 2 ^ W) →
    (∀ x ∈ L, g x < 2 ^ W) →
    Nat.ofDigits (2 ^ W) L &&& Nat.ofDigits (2 ^ W) (L.map g) =
      Nat.ofDigits (2 ^ W) (L.map (fun x => x &&& g x))
  | [], _, _ => by simp
  | d :: L, hf, hg => by
    have ih := ofDigits_land_map g L (fun x hx => hf x (List.mem_cons_of_mem _ hx))
      (fun x hx => hg x (List.mem_cons_of_mem _ hx))
    simp only [List.map_cons, Nat.ofDigits_cons]
    rw [add_comm d, add_comm (g d), land_two_pow_mul_add (hf d (by simp)) (hg d (by simp)), ih, add_comm]

theorem ofDigits_map_const (b c : ℕ) (L : List ℕ) :
    Nat.ofDigits b (L.map (fun _ => c)) = Nat.ofDigits b (List.replicate L.length c) := by
  rw [List.map_const']

/-! ## Per-digit facts -/

theorem digit_cases {W d : ℕ} (hW : 1 ≤ W) (hd : d < 2 ^ W) :
    (d / 2 ^ (W - 1) = 0 ∧ d < 2 ^ (W - 1)) ∨ (d / 2 ^ (W - 1) = 1 ∧ 2 ^ (W - 1) ≤ d) := by
  have hH : 2 ^ W = 2 * 2 ^ (W - 1) := by
    conv_lhs => rw [show W = (W - 1) + 1 by omega]
    rw [pow_succ]; ring
  have hp : 0 < 2 ^ (W - 1) := Nat.two_pow_pos _
  rcases Nat.lt_or_ge d (2 ^ (W - 1)) with h | h
  · exact Or.inl ⟨Nat.div_eq_of_lt h, h⟩
  · refine Or.inr ⟨?_, h⟩
    apply Nat.div_eq_of_lt_le
    · omega
    · omega

theorem land_full {W d : ℕ} (hd : d < 2 ^ W) : d &&& (2 ^ W - 1) = d := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hd]

theorem land_half {W d : ℕ} (hW : 1 ≤ W) (hd : d < 2 ^ W) :
    d &&& 2 ^ (W - 1) = 2 ^ (W - 1) * (d / 2 ^ (W - 1)) := by
  have e : 2 ^ (W - 1) = 2 ^ W - 2 ^ (W - 1) := by
    have : 2 ^ W = 2 * 2 ^ (W - 1) := by
      conv_lhs => rw [show W = (W - 1) + 1 by omega]
      rw [pow_succ]; ring
    omega
  conv_lhs => rw [e]
  exact land_round (by omega) hd

/-! ## The packed computation on digit lists -/

theorem pabs_ofDigits {W : ℕ} (hW : 1 ≤ W) (m : ℕ) (ds : List ℕ) (hl : ds.length = m)
    (hd : ∀ d ∈ ds, d < 2 ^ W) :
    ((Nat.ofDigits (2 ^ W) ds &&&
        (((Nat.ofDigits (2 ^ W) ds &&& (2 ^ (W - 1) * ones W m)) >>> (W - 1)) * (2 ^ W - 1))) -
      (Nat.ofDigits (2 ^ W) ds &&& (2 ^ (W - 1) * ones W m))) +
    (((2 ^ (W - 1) * ones W m) - (Nat.ofDigits (2 ^ W) ds &&& (2 ^ (W - 1) * ones W m))) -
      (Nat.ofDigits (2 ^ W) ds &&& ((2 ^ (W * m) - 1) -
        ((Nat.ofDigits (2 ^ W) ds &&& (2 ^ (W - 1) * ones W m)) >>> (W - 1)) * (2 ^ W - 1)))) =
    Nat.ofDigits (2 ^ W) (ds.map (fun d => (d - 2 ^ (W - 1)) + (2 ^ (W - 1) - d))) := by
  have hW0 : 0 < W := by omega
  set H := 2 ^ (W - 1) with hHdef
  have hHW : H < 2 ^ W := by
    rw [hHdef]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hM1 : 2 ^ W - 1 < 2 ^ W := by have := Nat.two_pow_pos W; omega
  -- the constant vectors as images of `ds`
  have hhb : H * ones W m = Nat.ofDigits (2 ^ W) (ds.map (fun _ => H)) := by
    rw [ofDigits_map_const, hl, ofDigits_replicate hW0]
  have hmask : 2 ^ (W * m) - 1 = Nat.ofDigits (2 ^ W) (ds.map (fun _ => 2 ^ W - 1)) := by
    rw [ofDigits_map_const, hl, ← ofDigits_replicate_one_mul m, ← ones_eq hW0, ofDigits_replicate hW0]
  -- h = X &&& hb
  have hh : Nat.ofDigits (2 ^ W) ds &&& H * ones W m = Nat.ofDigits (2 ^ W) (ds.map (fun d => H * (d / H))) := by
    rw [hhb, ofDigits_land_map _ ds hd (fun _ _ => hHW)]
    congr 1
    apply List.map_congr_left
    intro d hd'
    exact land_half hW (hd d hd')
  -- sign vector
  have hsg : (Nat.ofDigits (2 ^ W) ds &&& H * ones W m) >>> (W - 1) = Nat.ofDigits (2 ^ W) (ds.map (fun d => d / H)) := by
    rw [hh, ofDigits_map_mul (2 ^ W) H (fun d => d / H), Nat.shiftRight_eq_div_pow, ← hHdef,
      Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
  have hpm : ((Nat.ofDigits (2 ^ W) ds &&& H * ones W m) >>> (W - 1)) * (2 ^ W - 1) =
      Nat.ofDigits (2 ^ W) (ds.map (fun d => (2 ^ W - 1) * (d / H))) := by
    rw [hsg, mul_comm, ofDigits_map_mul (2 ^ W) (2 ^ W - 1) (fun d => d / H)]
  have hpmlt : ∀ d ∈ ds, (2 ^ W - 1) * (d / H) < 2 ^ W := by
    intro d hd'
    rcases digit_cases hW (hd d hd') with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [← hHdef] at h1 <;> simp [h1]
  -- X &&& pm
  have hXpm : Nat.ofDigits (2 ^ W) ds &&& Nat.ofDigits (2 ^ W) (ds.map (fun d => (2 ^ W - 1) * (d / H))) =
      Nat.ofDigits (2 ^ W) (ds.map (fun d => d &&& ((2 ^ W - 1) * (d / H)))) := by
    rw [ofDigits_land_map _ ds hd hpmlt]
  -- negative mask
  have hneg : 2 ^ (W * m) - 1 - Nat.ofDigits (2 ^ W) (ds.map (fun d => (2 ^ W - 1) * (d / H))) =
      Nat.ofDigits (2 ^ W) (ds.map (fun d => (2 ^ W - 1) - (2 ^ W - 1) * (d / H))) := by
    rw [hmask, ofDigits_map_sub]
    intro d hd'
    rcases digit_cases hW (hd d hd') with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [← hHdef] at h1 <;> simp [h1]
  have hXneg : Nat.ofDigits (2 ^ W) ds &&& Nat.ofDigits (2 ^ W) (ds.map (fun d => (2 ^ W - 1) - (2 ^ W - 1) * (d / H))) =
      Nat.ofDigits (2 ^ W) (ds.map (fun d => d &&& ((2 ^ W - 1) - (2 ^ W - 1) * (d / H)))) := by
    rw [ofDigits_land_map _ ds hd (fun x _ => lt_of_le_of_lt (Nat.sub_le _ _) hM1)]
  rw [hpm, hXpm, hneg, hXneg, hh, hhb]
  -- first difference
  have hd1 : Nat.ofDigits (2 ^ W) (ds.map (fun d => d &&& ((2 ^ W - 1) * (d / H)))) -
      Nat.ofDigits (2 ^ W) (ds.map (fun d => H * (d / H))) =
      Nat.ofDigits (2 ^ W) (ds.map (fun d => (d &&& ((2 ^ W - 1) * (d / H))) - H * (d / H))) := by
    rw [ofDigits_map_sub]
    intro d hd'
    rcases digit_cases hW (hd d hd') with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [← hHdef] at h1 h2
    · simp [h1]
    · simp only [h1, mul_one]; rw [land_full (hd d hd')]; exact h2
  have hd2 : Nat.ofDigits (2 ^ W) (ds.map (fun _ => H)) - Nat.ofDigits (2 ^ W) (ds.map (fun d => H * (d / H))) =
      Nat.ofDigits (2 ^ W) (ds.map (fun d => H - H * (d / H))) := by
    rw [ofDigits_map_sub]
    intro d hd'
    rcases digit_cases hW (hd d hd') with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [← hHdef] at h1 <;> simp [h1]
  rw [hd1, hd2]
  have hd3 : Nat.ofDigits (2 ^ W) (ds.map (fun d => H - H * (d / H))) -
      Nat.ofDigits (2 ^ W) (ds.map (fun d => d &&& ((2 ^ W - 1) - (2 ^ W - 1) * (d / H)))) =
      Nat.ofDigits (2 ^ W) (ds.map (fun d => (H - H * (d / H)) - (d &&& ((2 ^ W - 1) - (2 ^ W - 1) * (d / H))))) := by
    rw [ofDigits_map_sub]
    intro d hd'
    rcases digit_cases hW (hd d hd') with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [← hHdef] at h1 h2
    · simp only [h1, mul_zero, Nat.sub_zero]; rw [land_full (hd d hd')]; exact h2.le
    · simp [h1]
  rw [hd3, ofDigits_map_add]
  congr 1
  apply List.map_congr_left
  intro d hd'
  rcases digit_cases hW (hd d hd') with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [← hHdef] at h1 h2
  · simp only [h1, mul_zero, Nat.sub_zero, Nat.and_zero, zero_add]
    rw [land_full (hd d hd')]; omega
  · simp only [h1, mul_one, Nat.sub_self, Nat.and_zero, add_zero]
    rw [land_full (hd d hd')]; omega

/-! ## Represented TMs -/

/-- the biased digits of a represented TM -/
theorem Rep.biased {N S B W : ℕ} (hg : Good N S B W) {T : TM} {cs : List ℤ} {al : List ℕ}
    (hR : Rep (mkCtx N S B W) T cs al) :
    (T.v + 2 ^ (W - 1) * ones W (N + 1)) &&& (2 ^ (W * (2 * N + 1)) - 1) =
      Nat.ofDigits (2 ^ W) (cs.map (fun x => (x + 2 ^ (W - 1)).toNat)) ∧
    ∀ x ∈ cs, 0 ≤ x + 2 ^ (W - 1) ∧ x + 2 ^ (W - 1) < 2 ^ W := by
  have hW1 := hg.W1
  have hlen : cs.length = N + 1 := hR.lcs
  have hb : ∀ x ∈ cs, |x| < 2 ^ (W - 1) := by
    intro x hx
    have h1 := hR.coeff_lt x hx
    simp only [mk_B] at h1
    have h2 : (2 : ℤ) ^ B ≤ 2 ^ (W - 1) := pow_le_pow_right₀ (by norm_num) (by have := hg.BW; omega)
    linarith
  have hV : (T.v : ℤ) % 2 ^ (W * (2 * N + 1)) = horner (2 ^ W : ℤ) cs % 2 ^ (W * (2 * N + 1)) := by
    have := hR.hv
    simp only [mk_W, mk_K] at this
    rw [this, Int.emod_emod]
  have hnn : ∀ x ∈ cs, 0 ≤ x + 2 ^ (W - 1) ∧ x + 2 ^ (W - 1) < 2 ^ W := by
    have hH2 : (2 : ℤ) ^ W = 2 * 2 ^ (W - 1) := by
      conv_lhs => rw [show W = (W - 1) + 1 by omega]
      exact pow_succ' 2 (W - 1)
    intro x hx
    have := abs_lt.mp (hb x hx)
    constructor <;> [linarith; (rw [hH2]; linarith)]
  refine ⟨?_, hnn⟩
  rw [Nat.and_two_pow_sub_one_eq_mod]
  exact mod_biased hW1 (Nat.mul_le_mul_left W (by omega : N + 1 ≤ 2 * N + 1)) cs hlen hb T.v hV

theorem absDigit_offset (x : ℤ) (H : ℕ) (hx : 0 ≤ x + (H : ℤ)) :
    ((x + (H : ℤ)).toNat - H) + (H - (x + (H : ℤ)).toNat) = x.natAbs := by
  omega

/-- `pabs` of a represented TM is the packed vector of the exact magnitudes -/
theorem Rep.pabs_eq {N S B W : ℕ} (hg : Good N S B W) {T : TM} {cs : List ℤ} {al : List ℕ}
    (hR : Rep (mkCtx N S B W) T cs al) :
    pabs (mkCtx N S B W) T = Nat.ofDigits (2 ^ W) (cs.map Int.natAbs) := by
  obtain ⟨hbias, hnn⟩ := hR.biased hg
  have hdig := offset_digits_lt (2 ^ (W - 1)) hnn
  have hlen : cs.length = N + 1 := hR.lcs
  have hl2 : (cs.map (fun x => (x + 2 ^ (W - 1)).toNat)).length = N + 1 := by simp [hlen]
  have hmap : (cs.map (fun x => (x + 2 ^ (W - 1)).toNat)).map (fun d => (d - 2 ^ (W - 1)) + (2 ^ (W - 1) - d)) =
      cs.map Int.natAbs := by
    rw [List.map_map]
    apply List.map_congr_left
    intro x hx
    have hc : ((2 ^ (W - 1) : ℕ) : ℤ) = 2 ^ (W - 1) := by push_cast; rfl
    have := absDigit_offset x (2 ^ (W - 1)) (by rw [hc]; exact (hnn x hx).1)
    rw [hc] at this
    exact this
  have key := pabs_ofDigits hg.W1 (N + 1) _ hl2 hdig
  rw [hmap, ← hbias] at key
  rw [← key]
  rfl

theorem Rep.sum_natAbs_le {c : Ctx} {T : TM} {cs : List ℤ} {al : List ℕ} (hR : Rep c T cs al) :
    (cs.map Int.natAbs).sum ≤ T.s := by
  have h1 := Dom.sum_abs_le cs al hR.dom
  have h2 : ∀ l : List ℤ, (((l.map Int.natAbs).sum : ℕ) : ℤ) = (l.map abs).sum := by
    intro l
    induction l with
    | nil => simp
    | cons z zs ih => simp only [List.map_cons, List.sum_cons, Nat.cast_add, ih, Int.abs_eq_natAbs]
  have : ((cs.map Int.natAbs).sum : ℤ) ≤ (al.sum : ℤ) := by rw [h2]; exact h1
  rw [hR.hs]
  exact_mod_cast this

/-- the slot sum of `pabs` is the exact `Σ|cₖ|` -/
theorem Rep.ssum_pabs {N S B W : ℕ} (hg : Good N S B W) {T : TM} {cs : List ℤ} {al : List ℕ}
    (hR : Rep (mkCtx N S B W) T cs al) :
    ssum (mkCtx N S B W) (pabs (mkCtx N S B W) T) = (cs.map Int.natAbs).sum := by
  rw [hR.pabs_eq hg]
  show Nat.ofDigits (2 ^ W) (cs.map Int.natAbs) % (2 ^ W - 1) = _
  have hBW := hg.BW
  have h1 := hR.sum_natAbs_le
  have h2 : T.s < 2 ^ B := by have := hR.sB; simpa using this
  have h3 : 2 ^ B < 2 ^ W - 1 := by
    have h4 : 2 ^ (B + 2) ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h5 : 2 ^ (B + 2) = 4 * 2 ^ B := by rw [pow_add]; ring
    have h6 : 1 ≤ 2 ^ B := Nat.one_le_two_pow
    have h7 : 4 * 2 ^ B ≤ 2 ^ W := h5 ▸ h4
    generalize 2 ^ B = x at h6 h7 ⊢
    generalize 2 ^ W = y at h7 ⊢
    omega
  exact ofDigits_mod_pred (by omega) _ (by omega)

theorem Rep.rangeX_eq {N S B W : ℕ} (hg : Good N S B W) {T : TM} {cs : List ℤ} {al : List ℕ}
    (hR : Rep (mkCtx N S B W) T cs al) :
    rangeX (mkCtx N S B W) T = (cs.map Int.natAbs).sum + T.e := by
  show ssum (mkCtx N S B W) (pabs (mkCtx N S B W) T) + T.e = _
  rw [hR.ssum_pabs hg]

end ThomsonCompact.Packed
