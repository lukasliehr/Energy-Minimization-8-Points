import ThomsonCompact.Packed.Rep
import Mathlib.Tactic.FieldSimp

/-!
# Slot-wise rounding: integer and real facts

`round_signed`: from a residue of `Σ zₖ Xᵏ` (`2N+1` coefficients, `|zₖ| < 2^(2B)`), the kernel expression
`((((V + biasP) &&& maskK) &&& rmask) >>> S + unb) &&& maskK` is the residue of `Σ_{k≤N} ⌊zₖ/2^S⌋ Xᵏ`.
`round_abs`: `((Σ δₖ Xᵏ + ceilAdd) &&& rmask) >>> S = Σ ⌈δₖ/2^S⌉ Xᵏ`.
`dom_round`, `eval_round`: domination of the rounded coefficients and the real rounding error.
-/

namespace ThomsonCompact.Packed
open Nat

theorem Good.W1 {N S B W : ℕ} (hg : Good N S B W) : 1 ≤ W := by have := hg.BW; omega
theorem Good.SleW {N S B W : ℕ} (hg : Good N S B W) : S ≤ W := by have := hg.SW; omega

theorem pow2B_le_H {N S B W : ℕ} (hg : Good N S B W) : (2 : ℤ) ^ (2 * B) ≤ 2 ^ (W - 1) :=
  pow_le_pow_right₀ (by norm_num) (by have := hg.BW; omega)

theorem addL_replicate (c : ℕ) : ∀ (δ : List ℕ), addL δ (List.replicate δ.length c) = δ.map (· + c)
  | [] => by simp [addL]
  | d :: δ => by
    rw [List.length_cons, List.replicate_succ, addL, addL_replicate c δ, List.map_cons]

/-- ceiling rounding of nonnegative digits (`< 2^(2B)`) by one add, one mask and one shift -/
theorem round_abs {N S B W : ℕ} (hg : Good N S B W) (δ : List ℕ) (hδ : δ.length = N + 1)
    (hb : ∀ d ∈ δ, d < 2 ^ (2 * B)) :
    ((Nat.ofDigits (2 ^ W) δ + (mkCtx N S B W).ceilAdd) &&& (mkCtx N S B W).rmask) >>> (mkCtx N S B W).S =
      Nat.ofDigits (2 ^ W) (δ.map (fun g => (g + (2 ^ S - 1)) / 2 ^ S)) := by
  have hW1 := hg.W1
  simp only [mk_ceilAdd, mk_rmask, mk_S]
  rw [← ofDigits_replicate (by omega), ← ofDigits_replicate (by omega), ← hδ, ← ofDigits_addL,
    addL_replicate]
  have hdig : ∀ d ∈ δ.map (· + (2 ^ S - 1)), d < 2 ^ W := by
    intro d hd
    simp only [List.mem_map] at hd
    obtain ⟨g, hg', rfl⟩ := hd
    have h1 := hb g hg'
    have h2 : 2 ^ (2 * B) + 2 ^ S ≤ 2 ^ W := by
      have e1 : 2 ^ (2 * B) ≤ 2 ^ (W - 1) := Nat.pow_le_pow_right (by norm_num) (by have := hg.BW; omega)
      have e2 : 2 ^ S ≤ 2 ^ (W - 1) := Nat.pow_le_pow_right (by norm_num) (by have := hg.SW; omega)
      have e3 : 2 ^ W = 2 * 2 ^ (W - 1) := by
        conv_lhs => rw [show W = (W - 1) + 1 by omega]
        exact pow_succ' 2 (W - 1)
      omega
    have := Nat.two_pow_pos S
    omega
  rw [ofDigits_round hg.SleW _ hdig, List.take_of_length_le (by simp), List.map_map]
  rfl

theorem take_map' {α β : Type*} (f : α → β) :
    ∀ (L : List α) (n : ℕ), (L.map f).take n = (L.take n).map f
  | [], n => by simp
  | x :: L, 0 => by simp
  | x :: L, n + 1 => by
    rw [List.map_cons, List.take_succ_cons, List.take_succ_cons, List.map_cons, take_map' f L n]

theorem toNat_div_offset {S W : ℕ} (hSW : S + 1 ≤ W) (x : ℤ) (hx : 0 ≤ x + 2 ^ (W - 1)) :
    (x + 2 ^ (W - 1)).toNat / 2 ^ S = (x / 2 ^ S + 2 ^ (W - 1 - S)).toNat := by
  have hdvd : (2 : ℤ) ^ S ∣ 2 ^ (W - 1) := pow_dvd_pow 2 (by omega)
  have hsplit : (2 : ℤ) ^ (W - 1) / 2 ^ S = 2 ^ (W - 1 - S) := by
    rw [show W - 1 = S + (W - 1 - S) by omega, pow_add, Int.mul_ediv_cancel_left _ (by positivity)]
    congr 1
    omega
  have h1 : (x + 2 ^ (W - 1)) / 2 ^ S = x / 2 ^ S + 2 ^ (W - 1 - S) := by
    rw [Int.add_ediv_of_dvd_right hdvd, hsplit]
  have h2 : 0 ≤ x / 2 ^ S + 2 ^ (W - 1 - S) := by
    rw [← h1]; exact Int.ediv_nonneg hx (by positivity)
  apply Int.ofNat_inj.mp
  rw [Int.toNat_of_nonneg h2, ← h1, ← Int.ofNat_ediv_ofNat, Int.toNat_of_nonneg hx]
  push_cast
  rfl

/-- floor rounding of signed coefficients through the biased representation -/
theorem round_signed {N S B W : ℕ} (hg : Good N S B W) (z : List ℤ) (hz : z.length = 2 * N + 1)
    (hb : ∀ x ∈ z, |x| < 2 ^ (2 * B)) (V : ℕ)
    (hV : (V : ℤ) % 2 ^ (W * (2 * N + 1)) = horner (2 ^ W : ℤ) z % 2 ^ (W * (2 * N + 1))) :
    ((((((V + (mkCtx N S B W).biasP) &&& (mkCtx N S B W).maskK) &&& (mkCtx N S B W).rmask) >>>
        (mkCtx N S B W).S) + (mkCtx N S B W).unb) &&& (mkCtx N S B W).maskK : ℕ) =
      (horner (2 ^ W : ℤ) ((z.take (N + 1)).map (fun x => x / 2 ^ S)) % 2 ^ (W * (2 * N + 1)) : ℤ) := by
  have hW1 := hg.W1
  have hH := pow2B_le_H hg
  have hbH : ∀ x ∈ z, |x| < 2 ^ (W - 1) := fun x hx => (hb x hx).trans_le hH
  simp only [mk_biasP, mk_maskK, mk_rmask, mk_S, mk_unb]
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod,
    mod_biased hW1 (le_refl _) z hz hbH V hV]
  -- the biased digits
  have hz2 : ∀ x ∈ z, 0 ≤ x + 2 ^ (W - 1) ∧ x + 2 ^ (W - 1) < 2 ^ W := by
    have hH2 : (2 : ℤ) ^ W = 2 * 2 ^ (W - 1) := by
      conv_lhs => rw [show W = (W - 1) + 1 by omega]
      exact pow_succ' 2 (W - 1)
    intro x hx
    have := abs_lt.mp (hbH x hx)
    constructor <;> [linarith; (rw [hH2]; linarith)]
  have hdig := offset_digits_lt (2 ^ (W - 1)) hz2
  rw [← ofDigits_replicate (by omega), ofDigits_round hg.SleW _ hdig]
  -- rewrite digits as offsets of the rounded coefficients
  have hcongr : (List.take (N + 1) (z.map (fun x => (x + 2 ^ (W - 1)).toNat))).map (fun d => d / 2 ^ S) =
      ((z.take (N + 1)).map (fun x => x / 2 ^ S)).map (fun y => (y + 2 ^ (W - 1 - S)).toNat) := by
    rw [take_map', List.map_map, List.map_map]
    apply List.map_congr_left
    intro x hx
    exact toNat_div_offset hg.SW x (hz2 x (List.mem_of_mem_take hx)).1
  rw [hcongr]
  have hlenC : ((z.take (N + 1)).map (fun x => x / 2 ^ S)).length = N + 1 := by
    simp [hz]; omega
  have hnonneg : ∀ y ∈ (z.take (N + 1)).map (fun x => x / 2 ^ S), 0 ≤ y + 2 ^ (W - 1 - S) := by
    intro y hy
    simp only [List.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have h1 : (x + 2 ^ (W - 1)) / 2 ^ S = x / 2 ^ S + 2 ^ (W - 1 - S) := by
      have hdvd : (2 : ℤ) ^ S ∣ 2 ^ (W - 1) := pow_dvd_pow 2 (by have := hg.SW; omega)
      rw [Int.add_ediv_of_dvd_right hdvd]
      congr 1
      rw [show W - 1 = S + (W - 1 - S) by have := hg.SW; omega, pow_add, Int.mul_ediv_cancel_left _ (by positivity)]
      congr 1
      have := hg.SW
      omega
    rw [← h1]
    exact Int.ediv_nonneg (hz2 x (List.mem_of_mem_take hx)).1 (by positivity)
  have hcast := cast_ofDigits_offset (W := W) (by omega) (2 ^ (W - 1 - S)) _ hnonneg
  rw [hlenC] at hcast
  -- the unbias constant
  have hones_lt : 2 ^ (W - 1 - S) * ones W (N + 1) ≤ 2 ^ (W * (2 * N + 1)) := by
    rw [← ofDigits_replicate (by omega)]
    have hd : ∀ d ∈ List.replicate (N + 1) (2 ^ (W - 1 - S)), d < 2 ^ W := by
      intro d hd
      rw [List.eq_of_mem_replicate hd]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    have := ofDigits_lt_pow (by omega) _ hd
    rw [List.length_replicate] at this
    exact this.le.trans (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
  rw [Int.natCast_emod, Nat.cast_add, hcast, Nat.cast_sub hones_lt]
  push_cast
  rw [show horner (2 ^ W : ℤ) ((z.take (N + 1)).map (fun x => x / 2 ^ S)) +
        2 ^ (W - 1 - S) * (ones W (N + 1) : ℤ) + (2 ^ (W * (2 * N + 1)) - 2 ^ (W - 1 - S) * (ones W (N + 1) : ℤ)) =
      horner (2 ^ W : ℤ) ((z.take (N + 1)).map (fun x => x / 2 ^ S)) + 2 ^ (W * (2 * N + 1)) * 1 by ring,
    Int.add_mul_emod_self_left]

/-- `|⌊x/d⌋| ≤ ⌈g/d⌉` whenever `|x| ≤ g` -/
theorem abs_ediv_le_ceil (x : ℤ) (d : ℕ) (hd : 0 < d) (g : ℕ) (hx : |x| ≤ g) :
    |x / (d : ℤ)| ≤ (((g + (d - 1)) / d : ℕ) : ℤ) := by
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℤ) ≤ d := by exact_mod_cast hd
  have h1 : 0 ≤ x % d := Int.emod_nonneg x hd'.ne'
  have h2 : x % d < d := Int.emod_lt_of_pos x hd'
  have h2' : x % (d : ℤ) ≤ d - 1 := by omega
  have h3 : (d : ℤ) * (x / d) + x % d = x := Int.mul_ediv_add_emod x d
  have hx' := abs_le.mp hx
  rw [← Int.ofNat_ediv_ofNat, Int.le_ediv_iff_mul_le hd']
  push_cast [Nat.cast_sub (show 1 ≤ d from hd)]
  rcases abs_cases (x / (d : ℤ)) with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h, mul_comm]; linarith
  · rw [h, neg_mul, mul_comm]; linarith

theorem getD_map_of_zero {α β : Type*} (f : α → β) (a0 : α) (b0 : β) (h : f a0 = b0) :
    ∀ (L : List α) (k : ℕ), (L.map f).getD k b0 = f (L.getD k a0)
  | [], k => by simp [h]
  | x :: L, 0 => by simp
  | x :: L, k + 1 => by simp only [List.map_cons, List.getD_cons_succ]; exact getD_map_of_zero f a0 b0 h L k

theorem dom_round (S : ℕ) {z : List ℤ} {γ : List ℕ} (h : Dom z γ) (m : ℕ) :
    Dom ((z.take m).map (fun x => x / 2 ^ S)) ((γ.take m).map (fun g => (g + (2 ^ S - 1)) / 2 ^ S)) := by
  intro k
  have ht := (h.take m) k
  have hz0 : ((z.take m).map (fun x => x / 2 ^ S)).getD k 0 = (z.take m).getD k 0 / 2 ^ S :=
    getD_map_of_zero (fun x : ℤ => x / 2 ^ S) 0 0 (by simp) _ k
  have hg0 : ((γ.take m).map (fun g => (g + (2 ^ S - 1)) / 2 ^ S)).getD k 0 =
      ((γ.take m).getD k 0 + (2 ^ S - 1)) / 2 ^ S := by
    have e : (0 + (2 ^ S - 1)) / 2 ^ S = 0 := by
      apply Nat.div_eq_of_lt; have := Nat.two_pow_pos S; omega
    exact getD_map_of_zero (fun g : ℕ => (g + (2 ^ S - 1)) / 2 ^ S) 0 0 e _ k
  rw [hz0, hg0]
  have := abs_ediv_le_ceil ((z.take m).getD k 0) (2 ^ S) (Nat.two_pow_pos S) _ ht
  push_cast at this ⊢
  exact this

/-- real rounding error of `⌊·/2^S⌋` on a coefficient list, for `|t| ≤ 1` -/
theorem eval_round (S : ℕ) (t : ℝ) (ht : |t| ≤ 1) : ∀ L : List ℤ,
    |evalZ L t - 2 ^ S * evalZ (L.map (fun x => x / 2 ^ S)) t| ≤ L.length * 2 ^ S
  | [] => by simp [evalZ]
  | x :: L => by
    have ih := eval_round S t ht L
    have hr : ((x : ℝ) - 2 ^ S * ((x / 2 ^ S : ℤ) : ℝ)) = ((x % 2 ^ S : ℤ) : ℝ) := by
      have := Int.mul_ediv_add_emod x (2 ^ S)
      have hc : ((2 ^ S * (x / 2 ^ S) + x % 2 ^ S : ℤ) : ℝ) = (x : ℝ) := by rw [this]
      push_cast at hc
      linarith
    have h0 : (0 : ℝ) ≤ ((x % 2 ^ S : ℤ) : ℝ) := by exact_mod_cast Int.emod_nonneg x (by positivity)
    have h1 : ((x % 2 ^ S : ℤ) : ℝ) ≤ 2 ^ S := by
      have := (Int.emod_lt_of_pos x (show (0 : ℤ) < 2 ^ S by positivity)).le
      exact_mod_cast this
    simp only [evalZ, List.map_cons, horner_cons] at ih ⊢
    set P := horner t (List.map (Int.cast : ℤ → ℝ) L)
    set Q := horner t (List.map (Int.cast : ℤ → ℝ) (List.map (fun x => x / 2 ^ S) L))
    have e : (x : ℝ) + t * P - 2 ^ S * (((x / 2 ^ S : ℤ) : ℝ) + t * Q) =
        ((x % 2 ^ S : ℤ) : ℝ) + t * (P - 2 ^ S * Q) := by rw [← hr]; ring
    rw [e]
    calc |((x % 2 ^ S : ℤ) : ℝ) + t * (P - 2 ^ S * Q)|
        ≤ |((x % 2 ^ S : ℤ) : ℝ)| + |t| * |P - 2 ^ S * Q| := by rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ 2 ^ S + 1 * (L.length * 2 ^ S) := by
          rw [abs_of_nonneg h0]
          gcongr
      _ = ((x :: L).length : ℝ) * 2 ^ S := by simp; ring

/-- product error: `|f g - (pA pB)/D²| ≤ (sA eB + sB eA + eA eB)/D²` for enclosures at scale `1/D` -/
theorem prod_err {D f g pA pB sA sB eA eB : ℝ} (hD : 0 < D)
    (hf : |f - pA / D| ≤ eA / D) (hg : |g - pB / D| ≤ eB / D) (hpA : |pA| ≤ sA) (hpB : |pB| ≤ sB)
    (heA : 0 ≤ eA) (heB : 0 ≤ eB) :
    |f * g - pA * pB / (D * D)| ≤ (sA * eB + sB * eA + eA * eB) / (D * D) := by
  set dA := f - pA / D
  set dB := g - pB / D
  have e : f * g - pA * pB / (D * D) = pA / D * dB + pB / D * dA + dA * dB := by
    simp only [dA, dB]; field_simp; ring
  rw [e]
  have h1 : |pA / D * dB| ≤ sA / D * (eB / D) := by
    rw [abs_mul, abs_div, abs_of_pos hD]
    exact mul_le_mul (div_le_div_of_nonneg_right hpA hD.le) hg (abs_nonneg _) (by
      have := abs_nonneg pA; exact div_nonneg (this.trans hpA) hD.le)
  have h2 : |pB / D * dA| ≤ sB / D * (eA / D) := by
    rw [abs_mul, abs_div, abs_of_pos hD]
    exact mul_le_mul (div_le_div_of_nonneg_right hpB hD.le) hf (abs_nonneg _) (by
      have := abs_nonneg pB; exact div_nonneg (this.trans hpB) hD.le)
  have h3 : |dA * dB| ≤ eA / D * (eB / D) := by
    rw [abs_mul]; exact mul_le_mul hf hg (abs_nonneg _) (div_nonneg heA hD.le)
  calc |pA / D * dB + pB / D * dA + dA * dB| ≤ |pA / D * dB| + |pB / D * dA| + |dA * dB| := abs_add_three _ _ _
    _ ≤ sA / D * (eB / D) + sB / D * (eA / D) + eA / D * (eB / D) := by linarith
    _ = (sA * eB + sB * eA + eA * eB) / (D * D) := by field_simp

/-- `x / 2^S ≤ ⌈x / 2^S⌉` as reals -/
theorem le_cdiv (S x : ℕ) : (x : ℝ) / 2 ^ S ≤ (cdiv S x : ℝ) := by
  have hc : cdiv S x = (x + (2 ^ S - 1)) / 2 ^ S := by
    show (x + (2 ^ S - 1)) >>> S = _
    rw [Nat.shiftRight_eq_div_pow]
  have hpos : 0 < 2 ^ S := Nat.two_pow_pos S
  have key : x ≤ 2 ^ S * cdiv S x := by
    rw [hc]
    have := Nat.div_add_mod (x + (2 ^ S - 1)) (2 ^ S)
    have := Nat.mod_lt (x + (2 ^ S - 1)) hpos
    omega
  rw [div_le_iff₀ (by positivity)]
  have : (x : ℝ) ≤ ((2 ^ S * cdiv S x : ℕ) : ℝ) := by exact_mod_cast key
  push_cast at this
  linarith

/-- `x / d ≤ ⌈x / d⌉` with the Nat ceiling `(x + d - 1) / d` -/
theorem le_ceil_div (x d : ℕ) (hd : 0 < d) : (x : ℝ) / d ≤ (((x + (d - 1)) / d : ℕ) : ℝ) := by
  have key : x ≤ d * ((x + (d - 1)) / d) := by
    have := Nat.div_add_mod (x + (d - 1)) d
    have := Nat.mod_lt (x + (d - 1)) hd
    omega
  rw [div_le_iff₀ (by exact_mod_cast hd)]
  have : (x : ℝ) ≤ ((d * ((x + (d - 1)) / d) : ℕ) : ℝ) := by exact_mod_cast key
  push_cast at this
  linarith

end ThomsonCompact.Packed
