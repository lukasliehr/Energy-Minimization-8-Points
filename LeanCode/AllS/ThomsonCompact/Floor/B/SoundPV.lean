import ThomsonCompact.Floor.B.SoundZ

/-!
# Packed integer vectors (channels) and the table contraction (F3b)

A packed integer vector of `n` slots of width `W`: `(V : ℤ) ≡ Σ zᵢ 2^(W i) (mod 2^(W n))` with `|zᵢ| < 2^(W-1)`.
* `slot_ofDigits`: slot extraction from digit lists;
* `pb_decode`, `pb_abs`: the biased form `(V + bias) mod 2^(W n)` gives the signed slots (`pbGet`) and the
  packed magnitudes (`pbAbs`);
* `dotOff_eq`, `contractK_mod`: the transposed-table contraction is the exact `Σ_idx ê_idx z_idx`.
-/

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Packed
open ThomsonCompact.Floor (mask slot)

/-! ## Digits -/

theorem mask_eq (w : ℕ) : mask w = 2 ^ w - 1 := by
  show 1 <<< w - 1 = _
  rw [Nat.shiftLeft_eq, one_mul]

theorem slot_eq (w x i : ℕ) : slot w x i = x / 2 ^ (w * i) % 2 ^ w := by
  show (x >>> (w * i)) &&& mask w = _
  rw [mask_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem ofDigits_div_pow {W : ℕ} (hW : 0 < W) : ∀ (ds : List ℕ) (i : ℕ), (∀ d ∈ ds, d < 2 ^ W) →
    Nat.ofDigits (2 ^ W) ds / 2 ^ (W * i) = Nat.ofDigits (2 ^ W) (ds.drop i)
  | ds, i, h => (ofDigits_take_drop hW ds h i).2

theorem slot_ofDigits {W : ℕ} (hW : 0 < W) (ds : List ℕ) (hd : ∀ d ∈ ds, d < 2 ^ W) (i : ℕ) :
    slot W (Nat.ofDigits (2 ^ W) ds) i = ds.getD i 0 := by
  rw [slot_eq, ofDigits_div_pow hW ds i hd]
  have hd' : ∀ d ∈ ds.drop i, d < 2 ^ W := fun d h => hd d (List.mem_of_mem_drop h)
  rcases hds : ds.drop i with _ | ⟨d, rest⟩
  · have : ds.length ≤ i := List.drop_eq_nil_iff.mp hds
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr this]
  · have h1 : ds.getD i 0 = d := by
      have : ds[i]? = some d := by
        have := (List.getElem?_drop (xs := ds) (i := i) (j := 0)).symm
        rw [hds] at this
        simpa using this
      simp [List.getD_eq_getElem?_getD, this]
    rw [h1, Nat.ofDigits_cons, Nat.add_mul_mod_self_left]
    rw [hds] at hd'
    exact Nat.mod_eq_of_lt (hd' d (by simp))

/-! ## Biased packed vectors -/

theorem pvBias_eq (W n : ℕ) : pvBias W n = 2 ^ (W - 1) * ones W n := by
  show Nat.pow 2 (Nat.sub W 1) * ones W n = _; rfl

/-- the biased digits of a packed integer vector -/
theorem pb_digits {W n : ℕ} (hW : 1 ≤ W) (z : List ℤ) (hz : z.length = n) (hb : ∀ x ∈ z, |x| < 2 ^ (W - 1))
    (V : ℕ) (hV : (V : ℤ) % 2 ^ (W * n) = horner (2 ^ W : ℤ) z % 2 ^ (W * n)) :
    Nat.land (Nat.add V (pvBias W n)) (mask (Nat.mul W n)) =
      Nat.ofDigits (2 ^ W) (z.map fun x => (x + 2 ^ (W - 1)).toNat) := by
  show (V + pvBias W n) &&& mask (W * n) = _
  rw [pvBias_eq, mask_eq, Nat.and_two_pow_sub_one_eq_mod]
  exact mod_biased hW le_rfl z hz hb V hV

theorem biased_lt {W : ℕ} (hW : 1 ≤ W) {x : ℤ} (hx : |x| < 2 ^ (W - 1)) :
    0 ≤ x + 2 ^ (W - 1) ∧ x + 2 ^ (W - 1) < 2 ^ W := by
  have hH2 : (2 : ℤ) ^ W = 2 * 2 ^ (W - 1) := by
    conv_lhs => rw [show W = (W - 1) + 1 by omega]
    exact pow_succ' 2 (W - 1)
  have := abs_lt.mp hx
  constructor <;> [linarith; (rw [hH2]; linarith)]

/-- decoding a slot of a biased packed vector -/
theorem pbGet_ofDigits {W : ℕ} (hW : 1 ≤ W) (z : List ℤ) (hb : ∀ x ∈ z, |x| < 2 ^ (W - 1)) (i : ℕ)
    (hi : i < z.length) :
    pbGet W (Nat.ofDigits (2 ^ W) (z.map fun x => (x + 2 ^ (W - 1)).toNat)) i =
      (decide (z[i] < 0), z[i].natAbs) := by
  have hnn : ∀ x ∈ z, 0 ≤ x + 2 ^ (W - 1) ∧ x + 2 ^ (W - 1) < 2 ^ W := fun x hx => biased_lt hW (hb x hx)
  have hdig := offset_digits_lt (2 ^ (W - 1)) hnn
  have hs := slot_ofDigits (by omega) _ hdig i
  have hg : (z.map fun x => (x + 2 ^ (W - 1)).toNat).getD i 0 = (z[i] + 2 ^ (W - 1)).toNat := by
    simp [List.getD_eq_getElem?_getD, hi]
  rw [hg] at hs
  have hx := hnn z[i] (List.getElem_mem hi)
  have hc : ((2 ^ (W - 1) : ℕ) : ℤ) = 2 ^ (W - 1) := by push_cast; rfl
  show (Nat.blt (slot W _ i) (Nat.pow 2 (Nat.sub W 1)),
    Nat.add (Nat.sub (slot W _ i) (Nat.pow 2 (Nat.sub W 1))) (Nat.sub (Nat.pow 2 (Nat.sub W 1)) (slot W _ i))) = _
  rw [hs]
  have e1 : ((z[i] + 2 ^ (W - 1)).toNat : ℤ) = z[i] + 2 ^ (W - 1) := Int.toNat_of_nonneg hx.1
  refine Prod.ext ?_ ?_
  · rw [Bool.eq_iff_iff, Nat.blt_eq, decide_eq_true_iff]
    show (z[i] + 2 ^ (W - 1)).toNat < 2 ^ (W - 1) ↔ z[i] < 0
    constructor
    · intro h
      have : ((z[i] + 2 ^ (W - 1)).toNat : ℤ) < ((2 ^ (W - 1) : ℕ) : ℤ) := by exact_mod_cast h
      rw [e1, hc] at this; linarith
    · intro h
      have : ((z[i] + 2 ^ (W - 1)).toNat : ℤ) < ((2 ^ (W - 1) : ℕ) : ℤ) := by rw [e1, hc]; linarith
      exact_mod_cast this
  · show (z[i] + 2 ^ (W - 1)).toNat - 2 ^ (W - 1) + (2 ^ (W - 1) - (z[i] + 2 ^ (W - 1)).toNat) = z[i].natAbs
    have := absDigit_offset z[i] (2 ^ (W - 1)) (by rw [hc]; exact hx.1)
    rw [hc] at this
    exact this

/-- the packed magnitudes of a biased packed vector -/
theorem pbAbs_ofDigits {W n : ℕ} (hW : 1 ≤ W) (z : List ℤ) (hz : z.length = n) (hb : ∀ x ∈ z, |x| < 2 ^ (W - 1)) :
    pbAbs W n (Nat.ofDigits (2 ^ W) (z.map fun x => (x + 2 ^ (W - 1)).toNat)) =
      Nat.ofDigits (2 ^ W) (z.map Int.natAbs) := by
  have hnn : ∀ x ∈ z, 0 ≤ x + 2 ^ (W - 1) ∧ x + 2 ^ (W - 1) < 2 ^ W := fun x hx => biased_lt hW (hb x hx)
  have hdig := offset_digits_lt (2 ^ (W - 1)) hnn
  have hl2 : (z.map fun x => (x + 2 ^ (W - 1)).toNat).length = n := by simp [hz]
  have key := pabs_ofDigits hW n _ hl2 hdig
  have hmap : (z.map fun x => (x + 2 ^ (W - 1)).toNat).map (fun d => (d - 2 ^ (W - 1)) + (2 ^ (W - 1) - d)) =
      z.map Int.natAbs := by
    rw [List.map_map]
    apply List.map_congr_left
    intro x hx
    have hc : ((2 ^ (W - 1) : ℕ) : ℤ) = 2 ^ (W - 1) := by push_cast; rfl
    have := absDigit_offset x (2 ^ (W - 1)) (by rw [hc]; exact (hnn x hx).1)
    rw [hc] at this
    exact this
  rw [hmap] at key
  rw [← key]
  simp only [pbAbs, pvBias_eq, mask_eq]
  rfl

/-! ## The contraction -/

/-- the first `n` slots of `t` (width `w`) -/
def slotsL (w : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | n + 1, t => (t &&& mask w) :: slotsL w n (t >>> w)

theorem slotsL_length (w : ℕ) : ∀ n t, (slotsL w n t).length = n
  | 0, _ => rfl
  | n + 1, t => by simp [slotsL, slotsL_length w n]

theorem slotsL_getD (w : ℕ) : ∀ n t i, i < n → (slotsL w n t).getD i 0 = slot w t i
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, t, 0, _ => by
    show t &&& mask w = (t >>> (w * 0)) &&& mask w; simp
  | n + 1, t, i + 1, h => by
    show (slotsL w n (t >>> w)).getD i 0 = _
    rw [slotsL_getD w n (t >>> w) i (by omega)]
    show ((t >>> w) >>> (w * i)) &&& mask w = (t >>> (w * (i + 1))) &&& mask w
    rw [← Nat.shiftRight_add, show w + w * i = w * (i + 1) by ring]

theorem slotsL_lt (w : ℕ) : ∀ n t, ∀ x ∈ slotsL w n t, x < 2 ^ w
  | 0, _ => by simp [slotsL]
  | n + 1, t => by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [mask_eq, Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_lt _ (Nat.two_pow_pos w)
    · exact slotsL_lt w n _ x hx

/-- `dotOff` is the dot product of the slots with the vectors -/
theorem dotOff_eq (w : ℕ) : ∀ (cvs : List ℕ) (t acc : ℕ),
    dotOff w (mask w) cvs t acc = acc + (List.zipWith (· * ·) (slotsL w cvs.length t) cvs).sum
  | [], t, acc => by simp [dotOff, slotsL]
  | cv :: cvs, t, acc => by
    show dotOff w (mask w) cvs (t >>> w) (acc + (t &&& mask w) * cv) = _
    rw [dotOff_eq w cvs (t >>> w) (acc + (t &&& mask w) * cv)]
    simp only [List.length_cons, slotsL, List.zipWith_cons_cons, List.sum_cons]
    ring

/-- exact linear combinations of coefficient lists -/
def lcomb : List (ℤ × List ℤ) → List ℤ
  | [] => []
  | x :: L => addL (scaleL x.1 x.2) (lcomb L)

theorem horner_lcomb {R : Type*} [CommRing R] (X : R) : ∀ L : List (ℤ × List ℤ),
    horner X ((lcomb L).map (Int.cast : ℤ → R)) = (L.map fun x => (x.1 : R) * horner X (x.2.map (Int.cast : ℤ → R))).sum
  | [] => by simp [lcomb]
  | x :: L => by
    have h := map_addL (Int.castRingHom R) (scaleL x.1 x.2) (lcomb L)
    have h2 := map_scaleL (Int.castRingHom R) x.1 x.2
    simp only [lcomb, List.map_cons, List.sum_cons]
    rw [show (Int.cast : ℤ → R) = (Int.castRingHom R : ℤ → R) from rfl, h, horner_addL, h2, horner_scaleL]
    rw [show (Int.castRingHom R : ℤ → R) = (Int.cast : ℤ → R) from rfl, horner_lcomb X L]

theorem lcomb_getD : ∀ (L : List (ℤ × List ℤ)) (k : ℕ),
    (lcomb L).getD k 0 = (L.map fun x => x.1 * x.2.getD k 0).sum
  | [], k => by simp [lcomb]
  | x :: L, k => by
    simp only [lcomb, List.map_cons, List.sum_cons]
    rw [getD_addL, getD_scaleL, lcomb_getD L k]

theorem lcomb_length_le {n : ℕ} : ∀ (L : List (ℤ × List ℤ)), (∀ x ∈ L, x.2.length ≤ n) → (lcomb L).length ≤ n
  | [], _ => by simp [lcomb]
  | x :: L, h => by
    simp only [lcomb]
    rw [length_addL, length_scaleL]
    have := h x (by simp)
    have := lcomb_length_le L (fun y hy => h y (List.mem_cons_of_mem _ hy))
    omega

theorem horner_lcombZ (X : ℤ) : ∀ L : List (ℤ × List ℤ),
    horner X (lcomb L) = (L.map fun x => x.1 * horner X x.2).sum
  | [] => by simp [lcomb]
  | x :: L => by
    simp only [lcomb, List.map_cons, List.sum_cons, horner_addL, horner_scaleL, horner_lcombZ X L]

/-- the congruence of a linear combination of packed vectors -/
theorem lcomb_mod {M : ℤ} {W : ℕ} : ∀ (L : List (ℤ × ℕ × List ℤ)),
    (∀ x ∈ L, (x.2.1 : ℤ) % M = horner (2 ^ W : ℤ) x.2.2 % M) →
    (L.map fun x => x.1 * (x.2.1 : ℤ)).sum % M = horner (2 ^ W : ℤ) (lcomb (L.map fun x => (x.1, x.2.2))) % M
  | [], _ => by simp [lcomb]
  | x :: L, h => by
    have h1 : Int.ModEq M (x.2.1 : ℤ) (horner (2 ^ W : ℤ) x.2.2) := h x (by simp)
    have h2 : Int.ModEq M (L.map fun x => x.1 * (x.2.1 : ℤ)).sum
        (horner (2 ^ W : ℤ) (lcomb (L.map fun x => (x.1, x.2.2)))) :=
      lcomb_mod L (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have := (h1.mul_left x.1).add h2
    simp only [List.map_cons, List.sum_cons, lcomb, horner_addL, horner_scaleL]
    exact this

end ThomsonCompact.Floor.B
