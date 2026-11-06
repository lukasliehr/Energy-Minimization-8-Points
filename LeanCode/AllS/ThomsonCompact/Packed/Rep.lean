import ThomsonCompact.Packed.Digits

/-!
# Representation invariant and the generic packed lemmas

`Rep c T cs al`: the packed TM `T` encodes the signed coefficient list `cs` (scale `2^-S`) with magnitude bounds
`al`. `Encl c T f` adds the analytic enclosure on `[-1,1]`. The generic lemmas here are shared by all
operations: the biased decoding of a product modulo `2^K` (no carries), slot-wise floor rounding of signed
coefficients, slot-wise ceiling rounding of magnitude bounds, and the real rounding error.
-/

namespace ThomsonCompact.Packed
open Nat

/-- Admissible parameters for `mkCtx N S B W`. -/
structure Good (N S B W : ℕ) : Prop where
  B1 : 1 ≤ B
  BW : 2 * B + 2 ≤ W
  SW : S + 1 ≤ W
  NB : N + 1 ≤ 2 ^ B

section Fields
variable (N S B W : ℕ)
@[simp] theorem mk_N : (mkCtx N S B W).N = N := rfl
@[simp] theorem mk_S : (mkCtx N S B W).S = S := rfl
@[simp] theorem mk_B : (mkCtx N S B W).B = B := rfl
@[simp] theorem mk_W : (mkCtx N S B W).W = W := rfl
@[simp] theorem mk_m : (mkCtx N S B W).m = N + 1 := rfl
@[simp] theorem mk_K : (mkCtx N S B W).K = W * (2 * N + 1) := rfl
@[simp] theorem mk_wm : (mkCtx N S B W).wm = W * (N + 1) := rfl
@[simp] theorem mk_maskK : (mkCtx N S B W).maskK = 2 ^ (W * (2 * N + 1)) - 1 := rfl
@[simp] theorem mk_modW : (mkCtx N S B W).modW = 2 ^ W - 1 := rfl
@[simp] theorem mk_maskWm : (mkCtx N S B W).maskWm = 2 ^ (W * (N + 1)) - 1 := rfl
@[simp] theorem mk_biasP : (mkCtx N S B W).biasP = 2 ^ (W - 1) * ones W (2 * N + 1) := rfl
@[simp] theorem mk_hb : (mkCtx N S B W).hb = 2 ^ (W - 1) * ones W (N + 1) := rfl
@[simp] theorem mk_rmask : (mkCtx N S B W).rmask = (2 ^ W - 2 ^ S) * ones W (N + 1) := rfl
@[simp] theorem mk_ceilAdd : (mkCtx N S B W).ceilAdd = (2 ^ S - 1) * ones W (N + 1) := rfl
@[simp] theorem mk_unb :
    (mkCtx N S B W).unb = 2 ^ (W * (2 * N + 1)) - 2 ^ (W - 1 - S) * ones W (N + 1) := rfl
@[simp] theorem mk_hiPat : (mkCtx N S B W).hiPat = (2 ^ W - 2 ^ B) * ones W (N + 1) := rfl
@[simp] theorem mk_twoK : (mkCtx N S B W).twoK = 2 ^ (W * (2 * N + 1)) := rfl
@[simp] theorem mk_twoB : (mkCtx N S B W).twoB = 2 ^ B := rfl
@[simp] theorem mk_twoS : (mkCtx N S B W).twoS = 2 ^ S := rfl
end Fields

/-! ## Small list facts -/

theorem getD_le_sum : ∀ (L : List ℕ) (k : ℕ), L.getD k 0 ≤ L.sum
  | [], k => by simp
  | d :: L, 0 => by simp
  | d :: L, k + 1 => by
    simp only [List.getD_cons_succ, List.sum_cons]
    have := getD_le_sum L k
    omega

theorem exists_getD_of_mem {z : List ℤ} {x : ℤ} (h : x ∈ z) : ∃ k, z.getD k 0 = x := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp h
  exact ⟨i, by simp [List.getD_eq_getElem?_getD, hi]⟩

theorem exists_getD_of_mem' {z : List ℕ} {x : ℕ} (h : x ∈ z) : ∃ k, z.getD k 0 = x := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp h
  exact ⟨i, by simp [List.getD_eq_getElem?_getD, hi]⟩

theorem mem_le_sum {L : List ℕ} {d : ℕ} (h : d ∈ L) : d ≤ L.sum := by
  obtain ⟨k, rfl⟩ := exists_getD_of_mem' h
  exact getD_le_sum L k

theorem Dom.abs_le_sum {a : List ℤ} {α : List ℕ} (h : Dom a α) {x : ℤ} (hx : x ∈ a) :
    |x| ≤ (α.sum : ℤ) := by
  obtain ⟨k, rfl⟩ := exists_getD_of_mem hx
  exact (h k).trans (by exact_mod_cast getD_le_sum α k)

theorem sum_addL_nat (L M : List ℕ) : (addL L M).sum = L.sum + M.sum := by
  rw [← horner_one, horner_addL, horner_one, horner_one]

theorem horner_append_zeros {R : Type*} [CommSemiring R] (t : R) :
    ∀ (L : List R) (n : ℕ), horner t (L ++ List.replicate n 0) = horner t L
  | [], n => by
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [List.nil_append, horner_nil] at ih
      simp only [List.nil_append, List.replicate_succ, horner_cons, ih, mul_zero, add_zero, horner_nil]
  | c :: L, n => by simp [horner_append_zeros t L n]

/-! ## Biased digits and reduction modulo `2^K` -/

theorem cast_ofDigits_offset {W : ℕ} (hW : 0 < W) (h : ℤ) :
    ∀ z : List ℤ, (∀ x ∈ z, 0 ≤ x + h) →
      ((Nat.ofDigits (2 ^ W) (z.map (fun x => (x + h).toNat)) : ℕ) : ℤ) =
        horner (2 ^ W : ℤ) z + h * (ones W z.length : ℤ)
  | [], _ => by simp [ones_eq hW]
  | x :: z, hz => by
    have ih := cast_ofDigits_offset hW h z (fun y hy => hz y (List.mem_cons_of_mem _ hy))
    have hx : 0 ≤ x + h := hz x (by simp)
    have hones : (ones W (z.length + 1) : ℤ) = 1 + 2 ^ W * (ones W z.length : ℤ) := by
      rw [ones_eq hW, ones_eq hW, List.replicate_succ, Nat.ofDigits_cons]
      push_cast
      ring
    simp only [List.map_cons, Nat.ofDigits_cons, List.length_cons, Nat.cast_add, Nat.cast_mul,
      Nat.cast_pow, Nat.cast_ofNat]
    rw [ih, Int.toNat_of_nonneg hx, hones, horner_cons]
    ring

theorem offset_digits_lt {W : ℕ} (h : ℤ) {z : List ℤ} (hz : ∀ x ∈ z, 0 ≤ x + h ∧ x + h < 2 ^ W) :
    ∀ d ∈ z.map (fun x => (x + h).toNat), d < 2 ^ W := by
  intro d hd
  simp only [List.mem_map] at hd
  obtain ⟨x, hx, rfl⟩ := hd
  have h1 := hz x hx
  have e := Int.toNat_of_nonneg h1.1
  have : (((x + h).toNat : ℕ) : ℤ) < ((2 ^ W : ℕ) : ℤ) := by rw [e]; push_cast; exact h1.2
  exact_mod_cast this

/-- A residue `V` of `Σ zₖ Xᵏ` plus the bias `H·Σ_{k<n} Xᵏ`, reduced modulo `2^K ≥ X^n`, is the digit sum of the
biased digits `zₖ + H` (no carries), provided `|zₖ| < H = 2^(W-1)`. -/
theorem mod_biased {W K n : ℕ} (hW : 1 ≤ W) (hK : W * n ≤ K) (z : List ℤ) (hz : z.length = n)
    (hb : ∀ x ∈ z, |x| < 2 ^ (W - 1)) (V : ℕ) (hV : (V : ℤ) % 2 ^ K = horner (2 ^ W : ℤ) z % 2 ^ K) :
    (V + 2 ^ (W - 1) * ones W n) % 2 ^ K =
      Nat.ofDigits (2 ^ W) (z.map (fun x => (x + 2 ^ (W - 1)).toNat)) := by
  have hH : (2 : ℤ) ^ W = 2 * 2 ^ (W - 1) := by
    conv_lhs => rw [show W = (W - 1) + 1 by omega]
    exact pow_succ' 2 (W - 1)
  have hz2 : ∀ x ∈ z, 0 ≤ x + 2 ^ (W - 1) ∧ x + 2 ^ (W - 1) < 2 ^ W := by
    intro x hx
    have := abs_lt.mp (hb x hx)
    constructor <;> [linarith; (rw [hH]; linarith)]
  have hdig := offset_digits_lt (2 ^ (W - 1)) hz2
  have hlt : Nat.ofDigits (2 ^ W) (z.map (fun x => (x + 2 ^ (W - 1)).toNat)) < 2 ^ K := by
    have := ofDigits_lt_pow (by omega) _ hdig
    rw [List.length_map, hz] at this
    exact this.trans_le (Nat.pow_le_pow_right (by norm_num) hK)
  have hcast := cast_ofDigits_offset (W := W) (by omega) (2 ^ (W - 1)) z (fun x hx => (hz2 x hx).1)
  rw [hz] at hcast
  apply Int.ofNat_inj.mp
  have hV' : ((V + 2 ^ (W - 1) * ones W n : ℕ) : ℤ) % 2 ^ K =
      (horner (2 ^ W : ℤ) z + 2 ^ (W - 1) * (ones W n : ℤ)) % 2 ^ K := by
    push_cast
    rw [Int.add_emod, hV, ← Int.add_emod]
  have hlt' : ((Nat.ofDigits (2 ^ W) (z.map (fun x => (x + 2 ^ (W - 1)).toNat)) : ℕ) : ℤ) < 2 ^ K := by
    exact_mod_cast hlt
  calc (((V + 2 ^ (W - 1) * ones W n) % 2 ^ K : ℕ) : ℤ)
      = ((V + 2 ^ (W - 1) * ones W n : ℕ) : ℤ) % 2 ^ K := by push_cast; rfl
    _ = (horner (2 ^ W : ℤ) z + 2 ^ (W - 1) * (ones W n : ℤ)) % 2 ^ K := hV'
    _ = ((Nat.ofDigits (2 ^ W) (z.map (fun x => (x + 2 ^ (W - 1)).toNat)) : ℕ) : ℤ) % 2 ^ K := by
        rw [hcast]
    _ = _ := Int.emod_eq_of_lt (by positivity) hlt'

/-! ## The representation invariant -/

/-- `T` encodes the signed coefficients `cs` (scale `2^-S`, slot width `W`) with magnitude bounds `al`. -/
structure Rep (c : Ctx) (T : TM) (cs : List ℤ) (al : List ℕ) : Prop where
  lcs : cs.length = c.m
  lal : al.length = c.m
  hv : (T.v : ℤ) = horner (2 ^ c.W : ℤ) cs % 2 ^ c.K
  ha : T.a = Nat.ofDigits (2 ^ c.W) al
  dom : Dom cs al
  hs : T.s = al.sum
  sB : T.s < 2 ^ c.B

/-- Semantic enclosure: `|f t - Σ csₖ 2^-S tᵏ| ≤ e·2^-S` on `[-1,1]`. -/
def Encl (c : Ctx) (T : TM) (f : ℝ → ℝ) : Prop :=
  ∃ cs al, Rep c T cs al ∧
    ∀ t ∈ Set.Icc (-1 : ℝ) 1, |f t - evalZ cs t / 2 ^ c.S| ≤ (T.e : ℝ) / 2 ^ c.S

theorem Rep.v_lt {c : Ctx} {T : TM} {cs al} (h : Rep c T cs al) : T.v < 2 ^ c.K := by
  have h1 := h.hv
  have h2 : horner (2 ^ c.W : ℤ) cs % 2 ^ c.K < 2 ^ c.K := Int.emod_lt_of_pos _ (by positivity)
  have : (T.v : ℤ) < ((2 ^ c.K : ℕ) : ℤ) := by rw [h1]; push_cast; exact h2
  exact_mod_cast this

/-- every magnitude bound and every coefficient is below `2^B` -/
theorem Rep.coeff_lt {c : Ctx} {T : TM} {cs al} (h : Rep c T cs al) : ∀ x ∈ cs, |x| < 2 ^ c.B := by
  intro x hx
  have h1 := h.dom.abs_le_sum hx
  have h2 : (al.sum : ℤ) < 2 ^ c.B := by rw [← h.hs]; exact_mod_cast h.sB
  linarith

theorem abs_evalZ_le_s {c : Ctx} {T : TM} {cs al} (h : Rep c T cs al) (t : ℝ) (ht : |t| ≤ 1) :
    |evalZ cs t| ≤ (T.s : ℝ) := by
  rw [h.hs]; exact abs_evalZ_le h.dom t ht

end ThomsonCompact.Packed
