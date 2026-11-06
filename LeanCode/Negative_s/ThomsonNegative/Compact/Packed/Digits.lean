import ThomsonNegative.Compact.Packed.Core
import ThomsonNegative.Compact.Packed.ListPoly
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Digit sums in base `2^W`

Facts about `Nat.ofDigits (2^W) L` used by the packed checker: splitting by `take`/`drop` (masks and shifts),
digit-wise `&&&` (via `testBit`), slot-wise floor rounding by one mask and one shift, digit sums by casting out
`2^W - 1`, and the `ones` pattern.
-/

namespace ThomsonNegative.Compact.Packed
open Nat

theorem ofDigits_eq_horner (b : ℕ) : ∀ L : List ℕ, Nat.ofDigits b L = horner b L
  | [] => rfl
  | d :: L => by simp [Nat.ofDigits_cons, ofDigits_eq_horner b L]

theorem ofDigits_addL (b : ℕ) (L M : List ℕ) :
    Nat.ofDigits b (addL L M) = Nat.ofDigits b L + Nat.ofDigits b M := by
  simp only [ofDigits_eq_horner, horner_addL]

theorem ofDigits_convL (b : ℕ) (L M : List ℕ) :
    Nat.ofDigits b (convL L M) = Nat.ofDigits b L * Nat.ofDigits b M := by
  simp only [ofDigits_eq_horner, horner_convL]

theorem ofDigits_map_mul (b k : ℕ) (f : ℕ → ℕ) :
    ∀ L : List ℕ, Nat.ofDigits b (L.map (fun x => k * f x)) = k * Nat.ofDigits b (L.map f)
  | [] => by simp
  | d :: L => by simp only [List.map_cons, Nat.ofDigits_cons, ofDigits_map_mul b k f L]; ring

theorem two_pow_gt_one {W : ℕ} (hW : 0 < W) : 1 < 2 ^ W := by
  simpa using Nat.pow_lt_pow_right (by norm_num : 1 < 2) hW

theorem ofDigits_lt_pow {W : ℕ} (hW : 0 < W) (L : List ℕ) (h : ∀ d ∈ L, d < 2 ^ W) :
    Nat.ofDigits (2 ^ W) L < 2 ^ (W * L.length) := by
  rw [pow_mul]; exact Nat.ofDigits_lt_base_pow_length (two_pow_gt_one hW) h

theorem ofDigits_take_drop {W : ℕ} (hW : 0 < W) (L : List ℕ) (h : ∀ d ∈ L, d < 2 ^ W) (n : ℕ) :
    Nat.ofDigits (2 ^ W) L % 2 ^ (W * n) = Nat.ofDigits (2 ^ W) (L.take n) ∧
    Nat.ofDigits (2 ^ W) L / 2 ^ (W * n) = Nat.ofDigits (2 ^ W) (L.drop n) := by
  have hsplit : Nat.ofDigits (2 ^ W) L = Nat.ofDigits (2 ^ W) (L.take n) +
      2 ^ (W * (L.take n).length) * Nat.ofDigits (2 ^ W) (L.drop n) := by
    conv_lhs => rw [← List.take_append_drop n L]
    rw [Nat.ofDigits_append, pow_mul]
  have hlt := ofDigits_lt_pow hW (L.take n) (fun d hd => h d (List.mem_of_mem_take hd))
  by_cases hn : n ≤ L.length
  · have hl : (L.take n).length = n := List.length_take_of_le hn
    rw [hl] at hsplit hlt
    constructor
    · rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
    · rw [hsplit, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlt, zero_add]
  · push Not at hn
    have ht : L.take n = L := List.take_of_length_le hn.le
    have hd : L.drop n = [] := List.drop_eq_nil_of_le hn.le
    have hL := ofDigits_lt_pow hW L h
    have hle : 2 ^ (W * L.length) ≤ 2 ^ (W * n) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hn.le)
    rw [ht, hd, Nat.ofDigits_nil]
    exact ⟨Nat.mod_eq_of_lt (hL.trans_le hle), Nat.div_eq_of_lt (hL.trans_le hle)⟩

/-! ## Digit-wise `&&&` -/

theorem land_two_pow_mul_add {W d e : ℕ} (hd : d < 2 ^ W) (he : e < 2 ^ W) (a b : ℕ) :
    (2 ^ W * a + d) &&& (2 ^ W * b + e) = 2 ^ W * (a &&& b) + (d &&& e) := by
  have hde : d &&& e < 2 ^ W := Nat.and_lt_two_pow d he
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add a hd, Nat.testBit_two_pow_mul_add b he,
    Nat.testBit_two_pow_mul_add (a &&& b) hde]
  split_ifs <;> simp [Nat.testBit_and]

theorem ofDigits_land {W : ℕ} : ∀ (L M : List ℕ), (∀ d ∈ L, d < 2 ^ W) → (∀ d ∈ M, d < 2 ^ W) →
    Nat.ofDigits (2 ^ W) L &&& Nat.ofDigits (2 ^ W) M = Nat.ofDigits (2 ^ W) (List.zipWith (· &&& ·) L M)
  | [], M, _, _ => by simp
  | d :: L, [], _, _ => by simp
  | d :: L, e :: M, hL, hM => by
    have ih := ofDigits_land L M (fun x hx => hL x (List.mem_cons_of_mem _ hx))
      (fun x hx => hM x (List.mem_cons_of_mem _ hx))
    simp only [Nat.ofDigits_cons, List.zipWith_cons_cons]
    rw [Nat.add_comm d, Nat.add_comm e, land_two_pow_mul_add (hL d (by simp)) (hM e (by simp)), ih,
      Nat.add_comm]

theorem land_round {W S u : ℕ} (hSW : S ≤ W) (hu : u < 2 ^ W) :
    u &&& (2 ^ W - 2 ^ S) = 2 ^ S * (u / 2 ^ S) := by
  have hpat : 2 ^ W - 2 ^ S = 2 ^ S * (2 ^ (W - S) - 1) := by
    rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hSW]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, hpat, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_sub_one,
    Nat.testBit_div_two_pow]
  by_cases h1 : S ≤ i
  · rw [Nat.sub_add_cancel h1]
    by_cases h2 : i < W
    · simp [h1, show i - S < W - S by omega]
    · have hb : u.testBit i = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hu (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [hb]
  · simp [h1]

theorem zipWith_replicate_right' {α β γ : Type*} (f : α → β → γ) (c : β) :
    ∀ (L : List α) (n : ℕ), List.zipWith f L (List.replicate n c) = (L.take n).map (fun x => f x c)
  | [], n => by simp
  | x :: L, 0 => by simp
  | x :: L, n + 1 => by simp [List.replicate_succ, zipWith_replicate_right' f c L n]

/-- Slot-wise floor division by `2^S` of the first `n` digits: one mask, one shift. -/
theorem ofDigits_round {W S : ℕ} (hSW : S ≤ W) (L : List ℕ) (hL : ∀ d ∈ L, d < 2 ^ W) (n : ℕ) :
    (Nat.ofDigits (2 ^ W) L &&& Nat.ofDigits (2 ^ W) (List.replicate n (2 ^ W - 2 ^ S))) >>> S =
      Nat.ofDigits (2 ^ W) ((L.take n).map (· / 2 ^ S)) := by
  have hpat : ∀ d ∈ List.replicate n (2 ^ W - 2 ^ S), d < 2 ^ W := by
    intro d hd
    rw [List.eq_of_mem_replicate hd]
    have := Nat.two_pow_pos S
    have := Nat.two_pow_pos W
    omega
  rw [ofDigits_land L _ hL hpat, zipWith_replicate_right', Nat.shiftRight_eq_div_pow]
  have hmap : (L.take n).map (fun x => x &&& (2 ^ W - 2 ^ S)) =
      (L.take n).map (fun x => 2 ^ S * (x / 2 ^ S)) := by
    apply List.map_congr_left
    intro x hx
    exact land_round hSW (hL x (List.mem_of_mem_take hx))
  rw [hmap, ofDigits_map_mul, Nat.mul_div_cancel_left _ (Nat.two_pow_pos S)]

/-! ## Digit sums by casting out `2^W - 1` -/

theorem ofDigits_mod_pred {W : ℕ} (hW : 2 ≤ W) (L : List ℕ) (h : L.sum < 2 ^ W - 1) :
    Nat.ofDigits (2 ^ W) L % (2 ^ W - 1) = L.sum := by
  have h4 : 4 ≤ 2 ^ W := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ W := Nat.pow_le_pow_right (by norm_num) hW
  have hmod : 2 ^ W ≡ 1 [MOD 2 ^ W - 1] := by
    unfold Nat.ModEq
    generalize hX : 2 ^ W = X at h4 ⊢
    calc X % (X - 1) = ((X - 1) + 1) % (X - 1) := by rw [Nat.sub_add_cancel (by omega : 1 ≤ X)]
      _ = 1 % (X - 1) := Nat.add_mod_left _ _
  have := Nat.ofDigits_modEq' (2 ^ W) 1 (2 ^ W - 1) hmod L
  rw [Nat.ofDigits_one] at this
  unfold Nat.ModEq at this
  rw [this]
  exact Nat.mod_eq_of_lt h

/-! ## The `ones` pattern -/

theorem ofDigits_replicate_one_mul {W : ℕ} :
    ∀ n : ℕ, (2 ^ W - 1) * Nat.ofDigits (2 ^ W) (List.replicate n 1) = 2 ^ (W * n) - 1
  | 0 => by simp
  | n + 1 => by
    have ih := ofDigits_replicate_one_mul (W := W) n
    rw [List.replicate_succ, Nat.ofDigits_cons, Nat.mul_add, mul_one]
    have h1 : 1 ≤ 2 ^ W := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ (W * n) := Nat.one_le_two_pow
    have e : (2 ^ W - 1) * (2 ^ W * Nat.ofDigits (2 ^ W) (List.replicate n 1)) =
        2 ^ W * (2 ^ (W * n) - 1) := by rw [← ih]; ring
    rw [e, Nat.mul_sub, mul_one, ← pow_add, show W + W * n = W * (n + 1) by ring]
    have h3 : 2 ^ W ≤ 2 ^ (W * (n + 1)) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    omega

theorem ones_eq {W : ℕ} (hW : 0 < W) (n : ℕ) : ones W n = Nat.ofDigits (2 ^ W) (List.replicate n 1) := by
  have hpos : 0 < 2 ^ W - 1 := by have := two_pow_gt_one hW; omega
  show (2 ^ (W * n) - 1) / (2 ^ W - 1) = _
  rw [← ofDigits_replicate_one_mul n, Nat.mul_div_cancel_left _ hpos]

theorem ofDigits_replicate {W : ℕ} (hW : 0 < W) (n d : ℕ) :
    Nat.ofDigits (2 ^ W) (List.replicate n d) = d * ones W n := by
  rw [ones_eq hW]
  have : List.replicate n d = (List.replicate n 1).map (fun x => d * id x) := by simp
  rw [this, ofDigits_map_mul]
  simp

/-! ## Fixed-length digit extraction -/

/-- the first `n` base-`2^W` digits of `x` -/
def digitsN (W n x : ℕ) : List ℕ := (List.range n).map (fun k => x / 2 ^ (W * k) % 2 ^ W)

theorem digitsN_succ (W n x : ℕ) : digitsN W (n + 1) x = x % 2 ^ W :: digitsN W n (x / 2 ^ W) := by
  simp only [digitsN, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · simp
  · apply List.map_congr_left
    intro k _
    simp only [Function.comp_apply, Nat.div_div_eq_div_mul, ← pow_add]
    rw [show W * k.succ = W + W * k by rw [Nat.succ_eq_add_one]; ring]

theorem digitsN_lt (W n x : ℕ) : ∀ d ∈ digitsN W n x, d < 2 ^ W := by
  intro d hd
  simp only [digitsN, List.mem_map] at hd
  obtain ⟨k, _, rfl⟩ := hd
  exact Nat.mod_lt _ (Nat.two_pow_pos W)

theorem length_digitsN (W n x : ℕ) : (digitsN W n x).length = n := by simp [digitsN]

theorem ofDigits_digitsN {W : ℕ} : ∀ (n x : ℕ), x < 2 ^ (W * n) → Nat.ofDigits (2 ^ W) (digitsN W n x) = x
  | 0, x, h => by simp at h; simp [digitsN, h]
  | n + 1, x, h => by
    rw [digitsN_succ, Nat.ofDigits_cons, ofDigits_digitsN n (x / 2 ^ W)]
    · exact Nat.mod_add_div x (2 ^ W)
    · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos W), ← pow_add]
      calc x < 2 ^ (W * (n + 1)) := h
        _ = 2 ^ (W * n + W) := by ring_nf

theorem eq_zero_of_ofDigits_eq_zero {b : ℕ} (hb : 0 < b) :
    ∀ L : List ℕ, Nat.ofDigits b L = 0 → ∀ d ∈ L, d = 0
  | [], _, d, hd => by simp at hd
  | x :: L, h, d, hd => by
    rw [Nat.ofDigits_cons] at h
    have hx : x = 0 := by omega
    have hL : Nat.ofDigits b L = 0 := by
      have : b * Nat.ofDigits b L = 0 := by omega
      rcases Nat.mul_eq_zero.mp this with h1 | h1
      · omega
      · exact h1
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hx
    · exact eq_zero_of_ofDigits_eq_zero hb L hL d hd

/-- `x &&& (2^W - 2^B) = 0` for `x < 2^W` means `x < 2^B`. -/
theorem lt_of_land_hi {W B x : ℕ} (hBW : B ≤ W) (hx : x < 2 ^ W) (h : x &&& (2 ^ W - 2 ^ B) = 0) :
    x < 2 ^ B := by
  rw [land_round hBW hx] at h
  have h1 : x / 2 ^ B = 0 := by
    rcases Nat.mul_eq_zero.mp h with h2 | h2
    · exact absurd h2 (Nat.two_pow_pos B).ne'
    · exact h2
  exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos B)).mp h1

end ThomsonNegative.Compact.Packed
