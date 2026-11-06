import ThomsonNegative.Compact.Packed.SoundMore
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Semantic export

`decode c v` recovers the coefficient list of a packed TM from `v` alone; `poly c T` and `err c T` are the real
polynomial and error radius, and `Encl.export` states the enclosure in these terms:
`Encl c T f → ∀ t ∈ [-1,1], |f t - poly c T t| ≤ err c T`.
-/

namespace ThomsonNegative.Compact.Packed
open Nat

variable {N S B W : ℕ}

/-- decoded signed coefficients: biased digits of `(v + H·ONES) mod 2^K`, minus `H` -/
def decode (c : Ctx) (v : ℕ) : List ℤ :=
  (digitsN c.W c.m ((v + c.hb) % 2 ^ c.K)).map (fun (d : ℕ) => (d : ℤ) - 2 ^ (c.W - 1))

/-- the real polynomial of a TM -/
noncomputable def poly (c : Ctx) (T : TM) (t : ℝ) : ℝ := evalZ (decode c T.v) t / 2 ^ c.S

/-- the real error radius of a TM -/
noncomputable def err (c : Ctx) (T : TM) : ℝ := (T.e : ℝ) / 2 ^ c.S

theorem digitsN_ofDigits {W : ℕ} : ∀ (L : List ℕ), (∀ d ∈ L, d < 2 ^ W) →
    digitsN W L.length (Nat.ofDigits (2 ^ W) L) = L
  | [], _ => by simp [digitsN]
  | d :: L, h => by
    have hd := h d (by simp)
    have h1 : (d + 2 ^ W * Nat.ofDigits (2 ^ W) L) % 2 ^ W = d := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
    have h2 : (d + 2 ^ W * Nat.ofDigits (2 ^ W) L) / 2 ^ W = Nat.ofDigits (2 ^ W) L := by
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos W), Nat.div_eq_of_lt hd, zero_add]
    rw [List.length_cons, digitsN_succ, Nat.ofDigits_cons, h1, h2,
      digitsN_ofDigits L (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- The coefficients of a represented TM are determined by `v`. -/
theorem Rep.decode_eq (hg : Good N S B W) {T : TM} {cs : List ℤ} {al : List ℕ}
    (h : Rep (mkCtx N S B W) T cs al) : decode (mkCtx N S B W) T.v = cs := by
  have hW1 := hg.W1
  have hlen : cs.length = N + 1 := h.lcs
  have hb : ∀ x ∈ cs, |x| < 2 ^ (W - 1) := by
    intro x hx
    have h1 := h.coeff_lt x hx
    simp only [mk_B] at h1
    have h2 : (2 : ℤ) ^ B ≤ 2 ^ (W - 1) := pow_le_pow_right₀ (by norm_num) (by have := hg.BW; omega)
    linarith
  have hV : (T.v : ℤ) % 2 ^ (W * (2 * N + 1)) = horner (2 ^ W : ℤ) cs % 2 ^ (W * (2 * N + 1)) := by
    have := h.hv
    simp only [mk_W, mk_K] at this
    rw [this, Int.emod_emod]
  have hmod := mod_biased hW1 (Nat.mul_le_mul_left W (by omega : N + 1 ≤ 2 * N + 1)) cs hlen hb T.v hV
  have hnn : ∀ x ∈ cs, 0 ≤ x + 2 ^ (W - 1) ∧ x + 2 ^ (W - 1) < 2 ^ W := by
    have hH2 : (2 : ℤ) ^ W = 2 * 2 ^ (W - 1) := by
      conv_lhs => rw [show W = (W - 1) + 1 by omega]
      exact pow_succ' 2 (W - 1)
    intro x hx
    have := abs_lt.mp (hb x hx)
    constructor <;> [linarith; (rw [hH2]; linarith)]
  have hdig := offset_digits_lt (2 ^ (W - 1)) hnn
  show (digitsN W (N + 1) ((T.v + 2 ^ (W - 1) * ones W (N + 1)) % 2 ^ (W * (2 * N + 1)))).map
    (fun (d : ℕ) => (d : ℤ) - 2 ^ (W - 1)) = cs
  rw [hmod]
  have hl2 : (cs.map (fun x => (x + 2 ^ (W - 1)).toNat)).length = N + 1 := by simp [hlen]
  rw [← hl2, digitsN_ofDigits _ hdig, List.map_map]
  conv_rhs => rw [← List.map_id cs]
  apply List.map_congr_left
  intro x hx
  simp only [Function.comp_apply, id]
  rw [Int.toNat_of_nonneg (hnn x hx).1]
  ring

/-- **Export.** An enclosure yields `|f t - poly(T) t| ≤ err(T)` on `[-1,1]`, with `poly`, `err` computed from `T`. -/
theorem Encl.export (hg : Good N S B W) {T : TM} {f : ℝ → ℝ} (h : Encl (mkCtx N S B W) T f) :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1, |f t - poly (mkCtx N S B W) T t| ≤ err (mkCtx N S B W) T := by
  obtain ⟨cs, al, hR, hf⟩ := h
  intro t ht
  simp only [poly, err, hR.decode_eq hg]
  exact hf t ht

theorem length_decode (c : Ctx) (v : ℕ) : (decode c v).length = c.m := by
  simp [decode, length_digitsN]

theorem horner_eq_sum (t : ℝ) : ∀ (L : List ℝ) (n : ℕ), L.length ≤ n →
    horner t L = ∑ k ∈ Finset.range n, L.getD k 0 * t ^ k
  | [], n, _ => by simp
  | c :: L, 0, h => by simp at h
  | c :: L, n + 1, h => by
    rw [Finset.sum_range_succ', horner_cons, horner_eq_sum t L n (by simp at h; omega), Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring

/-- `poly` as an explicit sum over the coefficient indices -/
theorem poly_eq_sum (c : Ctx) (T : TM) (t : ℝ) :
    poly c T t = ∑ k ∈ Finset.range c.m, (((decode c T.v).getD k 0 : ℤ) : ℝ) / 2 ^ c.S * t ^ k := by
  rw [poly, evalZ, horner_eq_sum t _ c.m (by simp [length_decode]), div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [getD_map_of_zero (Int.cast : ℤ → ℝ) 0 0 (by simp)]
  ring

#print axioms Encl.export
#print axioms mul_sound
#print axioms smul_sound
#print axioms recip_sound
#print axioms ofPQ_sound
#print axioms add_sound
#print axioms neg_sound
#print axioms addC_sound
#print axioms range_sound
#print axioms rangeX_sound

end ThomsonNegative.Compact.Packed
