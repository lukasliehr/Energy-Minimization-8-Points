import ThomsonNegative.Structure.Packed.PolyKernel
import ThomsonNegative.Structure.Packed.Digits
import Mathlib.Algebra.BigOperators.Fin

/-!
# Soundness of the fixed-table kernel, part 1: decoding (workstream F4)

* `sv`: integer value of a sign-magnitude pair; `sv_sm : sv (sm p q) = p - q`.
* `recCoeffs x`: the coefficient list (lowest first) of the polynomial record at the bottom of `x`;
  `sv_polyVal : sv (polyVal R x) = horner (2^R) (recCoeffs x)` (for `1 ≤ R`).
* `decPolysC`, `decPolyVecC`: coefficient-list decoders mirroring `decPolys`, `decPolyVec`;
  `decPolyVec_sv`: the kernel values are the radix evaluations of the decoded coefficient lists.
-/

namespace ThomsonNegative.Structure.Exact

open ThomsonNegative.Structure.Packed

/-! ## Kernel primitives in standard notation -/

theorem nat_add (a b : Nat) : Nat.add a b = a + b := rfl
theorem nat_sub (a b : Nat) : Nat.sub a b = a - b := rfl
theorem nat_mul (a b : Nat) : Nat.mul a b = a * b := rfl
theorem nat_land (a b : Nat) : Nat.land a b = a &&& b := rfl
theorem nat_shiftLeft (a b : Nat) : Nat.shiftLeft a b = a * 2 ^ b := Nat.shiftLeft_eq a b
theorem nat_shiftRight (a b : Nat) : Nat.shiftRight a b = a / 2 ^ b := Nat.shiftRight_eq_div_pow a b

/-! ## Signed values -/

/-- Integer value of a sign-magnitude pair. -/
def sv (e : Bool × Nat) : ℤ := if e.1 then -(e.2 : ℤ) else (e.2 : ℤ)

theorem sv_sm (p q : Nat) : sv (sm p q) = (p : ℤ) - q := by
  unfold sm sv
  cases h : Nat.blt p q
  · have : ¬ p < q := by
      intro hlt
      have : Nat.blt p q = true := Nat.blt_eq.mpr hlt
      rw [h] at this; exact Bool.false_ne_true this
    simp only [Bool.false_eq_true, ↓reduceIte, nat_sub]
    push_cast [Nat.cast_sub (by omega : q ≤ p)]
    ring
  · have : p < q := Nat.blt_eq.mp h
    simp only [↓reduceIte, nat_sub]
    push_cast [Nat.cast_sub this.le]
    ring

theorem sv_xor (s t : Bool) (m n : Nat) : sv (xor s t, m * n) = sv (s, m) * sv (t, n) := by
  cases s <;> cases t <;> simp [sv] <;> ring

theorem mask_eq (w : Nat) : Nat.sub (Nat.shiftLeft 1 w) 1 = 2 ^ w - 1 := by
  show 1 <<< w - 1 = 2 ^ w - 1
  rw [Nat.one_shiftLeft]

theorem land_mask (x w : Nat) : Nat.land x (Nat.sub (Nat.shiftLeft 1 w) 1) = x % 2 ^ w := by
  rw [mask_eq]; exact Nat.and_two_pow_sub_one_eq_mod x w

theorem land_lit (x : Nat) (w c : Nat) (hc : c = 2 ^ w - 1) : Nat.land x c = x % 2 ^ w := by
  subst hc; exact Nat.and_two_pow_sub_one_eq_mod x w

theorem shiftRight_eq (x n : Nat) : Nat.shiftRight x n = x / 2 ^ n := Nat.shiftRight_eq_div_pow x n

theorem shiftLeft_eq (x n : Nat) : Nat.shiftLeft x n = x * 2 ^ n := Nat.shiftLeft_eq x n

/-! ## Horner over slots -/

theorem hornerU_eq (R w : Nat) : ∀ (L x acc : Nat),
    hornerU R w (2 ^ w - 1) L x acc = (digitsN w L x).foldl (fun a s => a * 2 ^ R + s) acc
  | 0, x, acc => by simp [hornerU, digitsN]
  | L + 1, x, acc => by
    rw [digitsN_succ, List.foldl_cons, ← hornerU_eq R w L (x / 2 ^ w)]
    show hornerU R w (2 ^ w - 1) L (Nat.shiftRight x w) (Nat.add (Nat.shiftLeft acc R) (Nat.land x (2 ^ w - 1))) = _
    rw [nat_shiftRight, nat_add, nat_shiftLeft, nat_land, Nat.and_two_pow_sub_one_eq_mod]

theorem foldl_horner {R : Type*} [CommSemiring R] (B : R) : ∀ (l : List R) (acc : R),
    l.foldl (fun a s => a * B + s) acc = acc * B ^ l.length + horner B l.reverse
  | [], acc => by simp
  | s :: l, acc => by
    rw [List.foldl_cons, foldl_horner B l, List.reverse_cons, List.length_cons]
    have h : ∀ (u : List R) (c : R), horner B (u ++ [c]) = horner B u + B ^ u.length * c := by
      intro u c
      induction u with
      | nil => simp
      | cons d u ih => simp only [List.cons_append, horner_cons, ih, List.length_cons, pow_succ]; ring
    rw [h, List.length_reverse]
    ring

theorem horner_map_sub (B c : ℤ) : ∀ l : List ℕ,
    horner B (List.map (fun s : ℕ => (s : ℤ) - c) l) =
      horner B (List.map (Nat.cast : ℕ → ℤ) l) - c * horner B (List.replicate l.length 1)
  | [] => by simp
  | s :: l => by
    simp only [List.map_cons, horner_cons, List.length_cons, List.replicate_succ]
    rw [horner_map_sub B c l]
    ring

theorem horner_natCast (B : ℕ) : ∀ l : List ℕ, ((horner B l : ℕ) : ℤ) = horner (B : ℤ) (l.map (Nat.cast : ℕ → ℤ))
  | [] => by simp
  | s :: l => by simp [horner_natCast B l]

/-! ## Polynomial records -/

/-- Header fields as computed by the kernel. -/
def hdrL (x : Nat) : Nat := Nat.land (Nat.shiftRight x 12) 255
def hdrW (x : Nat) : Nat := Nat.land (Nat.shiftRight x 20) 4095

/-- Coefficients (lowest first) of the polynomial record at the bottom of `x`. -/
def recCoeffs (x : Nat) : List ℤ :=
  List.map (fun s : ℕ => (s : ℤ) - 2 ^ (hdrW x - 1)) (digitsN (hdrW x) (hdrL x) (Nat.shiftRight x 32)).reverse

theorem length_recCoeffs (x : Nat) : (recCoeffs x).length = hdrL x := by
  simp [recCoeffs, length_digitsN]

theorem onesR_eq (R L : Nat) (hR : 0 < R) : onesR R L = horner (2 ^ R) (List.replicate L 1) := by
  unfold onesR mask
  rw [← ofDigits_eq_horner, ← ones_eq hR L]
  show (1 <<< (R * L) - 1) / (1 <<< R - 1) = (2 ^ (R * L) - 1) / (2 ^ R - 1)
  rw [Nat.one_shiftLeft, Nat.one_shiftLeft]

theorem sv_polyVal (R x : Nat) (hR : 0 < R) : sv (polyVal R x) = horner ((2 : ℤ) ^ R) (recCoeffs x) := by
  unfold polyVal
  rw [sv_sm]
  have e1 : Nat.sub (Nat.shiftLeft 1 (Nat.land (Nat.shiftRight x 20) 4095)) 1 = 2 ^ hdrW x - 1 := mask_eq _
  rw [e1, show Nat.land (Nat.shiftRight x 20) 4095 = hdrW x from rfl,
    show Nat.land (Nat.shiftRight x 12) 255 = hdrL x from rfl, hornerU_eq, foldl_horner, zero_mul, zero_add,
    onesR_eq R _ hR, recCoeffs]
  rw [horner_map_sub, List.length_reverse, length_digitsN]
  rw [show Nat.shiftLeft 1 (Nat.sub (hdrW x) 1) = 2 ^ (hdrW x - 1) from Nat.one_shiftLeft _]
  rw [show Nat.mul (2 ^ (hdrW x - 1)) (horner (2 ^ R) (List.replicate (hdrL x) 1)) =
    2 ^ (hdrW x - 1) * horner (2 ^ R) (List.replicate (hdrL x) 1) from rfl]
  push_cast
  rw [horner_natCast, horner_natCast]
  simp only [List.map_replicate, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]

/-- Coefficient decoder mirroring `decPolys`. -/
def decPolysC : Nat → Nat → List (Nat × List ℤ)
  | 0, _ => []
  | n + 1, x => (Nat.land x 4095, recCoeffs x) :: decPolysC n (Nat.shiftRight x (polyLen x))

theorem decPolys_sv (R : Nat) (hR : 0 < R) : ∀ n x,
    (decPolys R n x).map (fun e => (e.1, sv e.2)) = (decPolysC n x).map (fun e => (e.1, horner ((2 : ℤ) ^ R) e.2))
  | 0, x => rfl
  | n + 1, x => by
    show (Nat.land x 4095, sv (polyVal R x)) :: (decPolys R n (Nat.shiftRight x (polyLen x))).map _ =
      (Nat.land x 4095, horner _ (recCoeffs x)) :: (decPolysC n (Nat.shiftRight x (polyLen x))).map _
    rw [sv_polyVal R x hR, decPolys_sv R hR n]

/-- Coefficient decoder mirroring `decPolyVec`. -/
def decPolyVecC (ch : Nat → Nat) : Nat → Nat → List (Nat × List ℤ)
  | 0, _ => []
  | n + 1, c => decPolysC (Nat.land (ch c) 255) (Nat.shiftRight (ch c) 8) ++ decPolyVecC ch n (c + 1)

theorem decPolyVec_sv (R : Nat) (hR : 0 < R) (ch : Nat → Nat) : ∀ n c,
    (decPolyVec R ch n c).map (fun e => (e.1, sv e.2)) =
      (decPolyVecC ch n c).map (fun e => (e.1, horner ((2 : ℤ) ^ R) e.2))
  | 0, c => rfl
  | n + 1, c => by
    show (decPolys R (Nat.land (ch c) 255) (Nat.shiftRight (ch c) 8) ++ decPolyVec R ch n (Nat.add c 1)).map _ =
      (decPolysC (Nat.land (ch c) 255) (Nat.shiftRight (ch c) 8) ++ decPolyVecC ch n (c + 1)).map _
    rw [List.map_append, List.map_append, decPolys_sv R hR, decPolyVec_sv R hR ch n]

#print axioms sv_polyVal
#print axioms decPolyVec_sv

end ThomsonNegative.Structure.Exact
