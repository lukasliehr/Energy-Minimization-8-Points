import ThomsonNegative.Analytic.RootLower
import ThomsonNegative.Analytic.RootMargin

/-! Global sign proofs for every factor occurring in the hybrid correction,
contact kernels and moment pivots. All identities are checked by `ring`.
The interval is analytic, so these are not per-cell numerical gates. -/

noncomputable section
namespace ThomsonNegative.Reduction
set_option maxHeartbeats 1200000

def denominatorFactor0 (a : ℝ) : ℝ :=
  (-1:ℝ)*a^0 + (1:ℝ)*a^1

theorem denominatorFactor0_sign (a : ℝ) (ha : (5:ℝ)/16 ≤ a) (hb : a < 1/3) :
    0 < (-1:ℝ)*denominatorFactor0 a := by
  let t : ℝ := 48*a-15
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hu : 0 < 1-t := by dsimp [t]; linarith
  have he : (-1:ℝ)*denominatorFactor0 a =
      (11/16:ℝ)*t^0*(1-t)^1 +
      (2/3:ℝ)*t^1*(1-t)^0 := by
    dsimp [denominatorFactor0,t]
    ring
  rw [he]
  positivity

def denominatorFactor1 (a : ℝ) : ℝ :=
  (-1:ℝ)*a^0 + (3:ℝ)*a^1

theorem denominatorFactor1_sign (a : ℝ) (ha : (5:ℝ)/16 ≤ a) (hb : a < 1/3) :
    0 < (-1:ℝ)*denominatorFactor1 a := by
  let t : ℝ := 48*a-15
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hu : 0 < 1-t := by dsimp [t]; linarith
  have he : (-1:ℝ)*denominatorFactor1 a =
      (1/16:ℝ)*t^0*(1-t)^1 := by
    dsimp [denominatorFactor1,t]
    ring
  rw [he]
  positivity

def denominatorFactor2 (a : ℝ) : ℝ :=
  (-1:ℝ)*a^0 + (5:ℝ)*a^1

theorem denominatorFactor2_sign (a : ℝ) (ha : (5:ℝ)/16 ≤ a) (hb : a < 1/3) :
    0 < (1:ℝ)*denominatorFactor2 a := by
  let t : ℝ := 48*a-15
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hu : 0 < 1-t := by dsimp [t]; linarith
  have he : (1:ℝ)*denominatorFactor2 a =
      (9/16:ℝ)*t^0*(1-t)^1 +
      (2/3:ℝ)*t^1*(1-t)^0 := by
    dsimp [denominatorFactor2,t]
    ring
  rw [he]
  positivity

def denominatorFactor3 (a : ℝ) : ℝ :=
  (1:ℝ)*a^1

theorem denominatorFactor3_sign (a : ℝ) (ha : (5:ℝ)/16 ≤ a) (hb : a < 1/3) :
    0 < (1:ℝ)*denominatorFactor3 a := by
  let t : ℝ := 48*a-15
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hu : 0 < 1-t := by dsimp [t]; linarith
  have he : (1:ℝ)*denominatorFactor3 a =
      (5/16:ℝ)*t^0*(1-t)^1 +
      (1/3:ℝ)*t^1*(1-t)^0 := by
    dsimp [denominatorFactor3,t]
    ring
  rw [he]
  positivity

def denominatorFactor4 (a : ℝ) : ℝ :=
  (-1:ℝ)*a^0 + (-6:ℝ)*a^1 + (23:ℝ)*a^2

theorem denominatorFactor4_sign (a : ℝ) (ha : (5:ℝ)/16 ≤ a) (hb : a < 1/3) :
    0 < (-1:ℝ)*denominatorFactor4 a := by
  let t : ℝ := 48*a-15
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hu : 0 < 1-t := by dsimp [t]; linarith
  have he : (-1:ℝ)*denominatorFactor4 a =
      (161/256:ℝ)*t^0*(1-t)^2 +
      (13/12:ℝ)*t^1*(1-t)^1 +
      (4/9:ℝ)*t^2*(1-t)^0 := by
    dsimp [denominatorFactor4,t]
    ring
  rw [he]
  positivity

def denominatorFactor5 (a : ℝ) : ℝ :=
  (-1:ℝ)*a^0 + (2:ℝ)*a^1 + (7:ℝ)*a^2

theorem denominatorFactor5_sign (a : ℝ) (ha : (5:ℝ)/16 ≤ a) (hb : a < 1/3) :
    0 < (1:ℝ)*denominatorFactor5 a := by
  let t : ℝ := 48*a-15
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hu : 0 < 1-t := by dsimp [t]; linarith
  have he : (1:ℝ)*denominatorFactor5 a =
      (79/256:ℝ)*t^0*(1-t)^2 +
      (3/4:ℝ)*t^1*(1-t)^1 +
      (4/9:ℝ)*t^2*(1-t)^0 := by
    dsimp [denominatorFactor5,t]
    ring
  rw [he]
  positivity

def denominatorFactor6 (a : ℝ) : ℝ :=
  (1:ℝ)*a^0 + (-10:ℝ)*a^1 + (17:ℝ)*a^2

theorem denominatorFactor6_sign (a : ℝ) (ha : (5:ℝ)/16 ≤ a) (hb : a < 1/3) :
    0 < (-1:ℝ)*denominatorFactor6 a := by
  let t : ℝ := 48*a-15
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hu : 0 < 1-t := by dsimp [t]; linarith
  have he : (-1:ℝ)*denominatorFactor6 a =
      (119/256:ℝ)*t^0*(1-t)^2 +
      (11/12:ℝ)*t^1*(1-t)^1 +
      (4/9:ℝ)*t^2*(1-t)^0 := by
    dsimp [denominatorFactor6,t]
    ring
  rw [he]
  positivity

def denominatorFactor7 (a : ℝ) : ℝ :=
  (1:ℝ)*a^0 + (6:ℝ)*a^1 + (1:ℝ)*a^2

theorem denominatorFactor7_sign (a : ℝ) (ha : (5:ℝ)/16 ≤ a) (hb : a < 1/3) :
    0 < (1:ℝ)*denominatorFactor7 a := by
  let t : ℝ := 48*a-15
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hu : 0 < 1-t := by dsimp [t]; linarith
  have he : (1:ℝ)*denominatorFactor7 a =
      (761/256:ℝ)*t^0*(1-t)^2 +
      (73/12:ℝ)*t^1*(1-t)^1 +
      (28/9:ℝ)*t^2*(1-t)^0 := by
    dsimp [denominatorFactor7,t]
    ring
  rw [he]
  positivity

def denominatorFactor8 (a : ℝ) : ℝ :=
  (3:ℝ)*a^0 + (-30:ℝ)*a^1 + (35:ℝ)*a^2

theorem denominatorFactor8_sign (a : ℝ) (ha : (5:ℝ)/16 ≤ a) (hb : a < 1/3) :
    0 < (-1:ℝ)*denominatorFactor8 a := by
  let t : ℝ := 48*a-15
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hu : 0 < 1-t := by dsimp [t]; linarith
  have he : (-1:ℝ)*denominatorFactor8 a =
      (757/256:ℝ)*t^0*(1-t)^2 +
      (73/12:ℝ)*t^1*(1-t)^1 +
      (28/9:ℝ)*t^2*(1-t)^0 := by
    dsimp [denominatorFactor8,t]
    ring
  rw [he]
  positivity

def denominatorFactor9 (a : ℝ) : ℝ :=
  (-3:ℝ)*a^0 + (21:ℝ)*a^1 + (-45:ℝ)*a^2 + (35:ℝ)*a^3

theorem denominatorFactor9_sign (a : ℝ) (ha : (5:ℝ)/16 ≤ a) (hb : a < 1/3) :
    0 < (1:ℝ)*denominatorFactor9 a := by
  let t : ℝ := 48*a-15
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hu : 0 < 1-t := by dsimp [t]; linarith
  have he : (1:ℝ)*denominatorFactor9 a =
      (967/4096:ℝ)*t^0*(1-t)^3 +
      (99/128:ℝ)*t^1*(1-t)^2 +
      (5/6:ℝ)*t^2*(1-t)^1 +
      (8/27:ℝ)*t^3*(1-t)^0 := by
    dsimp [denominatorFactor9,t]
    ring
  rw [he]
  positivity

def denominatorFactor10 (a : ℝ) : ℝ :=
  (-1:ℝ)*a^0 + (9:ℝ)*a^1 + (-35:ℝ)*a^2 + (35:ℝ)*a^3

theorem denominatorFactor10_sign (a : ℝ) (ha : (5:ℝ)/16 ≤ a) (hb : a < 1/3) :
    0 < (-1:ℝ)*denominatorFactor10 a := by
  let t : ℝ := 48*a-15
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hu : 0 < 1-t := by dsimp [t]; linarith
  have he : (-1:ℝ)*denominatorFactor10 a =
      (2201/4096:ℝ)*t^0*(1-t)^3 +
      (5/3:ℝ)*t^1*(1-t)^2 +
      (31/18:ℝ)*t^2*(1-t)^1 +
      (16/27:ℝ)*t^3*(1-t)^0 := by
    dsimp [denominatorFactor10,t]
    ring
  rw [he]
  positivity

def denominatorFactor11 (a : ℝ) : ℝ :=
  (-1:ℝ)*a^0 + (78:ℝ)*a^2 + (-408:ℝ)*a^3 + (587:ℝ)*a^4

theorem denominatorFactor11_sign (a : ℝ) (ha : (5:ℝ)/16 ≤ a) (hb : a < 1/3) :
    0 < (-1:ℝ)*denominatorFactor11 a := by
  let t : ℝ := 48*a-15
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hu : 0 < 1-t := by dsimp [t]; linarith
  have he : (-1:ℝ)*denominatorFactor11 a =
      (15461/65536:ℝ)*t^0*(1-t)^4 +
      (2843/3072:ℝ)*t^1*(1-t)^3 +
      (43/32:ℝ)*t^2*(1-t)^2 +
      (23/27:ℝ)*t^3*(1-t)^1 +
      (16/81:ℝ)*t^4*(1-t)^0 := by
    dsimp [denominatorFactor11,t]
    ring
  rw [he]
  positivity

def denominatorFactor12 (a : ℝ) : ℝ :=
  (1:ℝ)*a^0 + (-84:ℝ)*a^1 + (1794:ℝ)*a^2 + (-19684:ℝ)*a^3 + (141983:ℝ)*a^4 + (-783016:ℝ)*a^5 + (3545180:ℝ)*a^6 + (-12904040:ℝ)*a^7 + (35253007:ℝ)*a^8 + (-67080708:ℝ)*a^9 + (81406786:ℝ)*a^10 + (-54042548:ℝ)*a^11 + (13170609:ℝ)*a^12

theorem denominatorFactor12_sign (a : ℝ) (ha : (5:ℝ)/16 ≤ a) (hb : a < 1/3) :
    0 < (1:ℝ)*denominatorFactor12 a := by
  let t : ℝ := 48*a-15
  have ht : 0 ≤ t := by dsimp [t]; linarith
  have hu : 0 < 1-t := by dsimp [t]; linarith
  have he : (1:ℝ)*denominatorFactor12 a =
      (4595562452161/281474976710656:ℝ)*t^0*(1-t)^12 +
      (672655385207/3298534883328:ℝ)*t^1*(1-t)^11 +
      (180312061579/154618822656:ℝ)*t^2*(1-t)^10 +
      (234053553803/57982058496:ℝ)*t^3*(1-t)^9 +
      (22752170065/2415919104:ℝ)*t^4*(1-t)^8 +
      (220788157/14155776:ℝ)*t^5*(1-t)^7 +
      (449020315/23887872:ℝ)*t^6*(1-t)^6 +
      (37184351/2239488:ℝ)*t^7*(1-t)^5 +
      (17912995/1679616:ℝ)*t^8*(1-t)^4 +
      (10619/2187:ℝ)*t^9*(1-t)^3 +
      (87776/59049:ℝ)*t^10*(1-t)^2 +
      (48640/177147:ℝ)*t^11*(1-t)^1 +
      (4096/177147:ℝ)*t^12*(1-t)^0 := by
    dsimp [denominatorFactor12,t]
    ring
  rw [he]
  positivity

def denominatorFactor : Fin 13 → ℝ → ℝ :=
  ![denominatorFactor0, denominatorFactor1, denominatorFactor2, denominatorFactor3, denominatorFactor4, denominatorFactor5, denominatorFactor6, denominatorFactor7, denominatorFactor8, denominatorFactor9, denominatorFactor10, denominatorFactor11, denominatorFactor12]

theorem denominatorFactor_ne_zero (a : ℝ) (ha : (5:ℝ)/16 ≤ a) (hb : a < 1/3)
    (i : Fin 13) : denominatorFactor i a ≠ 0 := by
  fin_cases i
  · change denominatorFactor0 a ≠ 0
    intro hz
    have h := denominatorFactor0_sign a ha hb
    simp only [hz,mul_zero,lt_self_iff_false] at h
  · change denominatorFactor1 a ≠ 0
    intro hz
    have h := denominatorFactor1_sign a ha hb
    simp only [hz,mul_zero,lt_self_iff_false] at h
  · change denominatorFactor2 a ≠ 0
    intro hz
    have h := denominatorFactor2_sign a ha hb
    simp only [hz,mul_zero,lt_self_iff_false] at h
  · change denominatorFactor3 a ≠ 0
    intro hz
    have h := denominatorFactor3_sign a ha hb
    simp only [hz,mul_zero,lt_self_iff_false] at h
  · change denominatorFactor4 a ≠ 0
    intro hz
    have h := denominatorFactor4_sign a ha hb
    simp only [hz,mul_zero,lt_self_iff_false] at h
  · change denominatorFactor5 a ≠ 0
    intro hz
    have h := denominatorFactor5_sign a ha hb
    simp only [hz,mul_zero,lt_self_iff_false] at h
  · change denominatorFactor6 a ≠ 0
    intro hz
    have h := denominatorFactor6_sign a ha hb
    simp only [hz,mul_zero,lt_self_iff_false] at h
  · change denominatorFactor7 a ≠ 0
    intro hz
    have h := denominatorFactor7_sign a ha hb
    simp only [hz,mul_zero,lt_self_iff_false] at h
  · change denominatorFactor8 a ≠ 0
    intro hz
    have h := denominatorFactor8_sign a ha hb
    simp only [hz,mul_zero,lt_self_iff_false] at h
  · change denominatorFactor9 a ≠ 0
    intro hz
    have h := denominatorFactor9_sign a ha hb
    simp only [hz,mul_zero,lt_self_iff_false] at h
  · change denominatorFactor10 a ≠ 0
    intro hz
    have h := denominatorFactor10_sign a ha hb
    simp only [hz,mul_zero,lt_self_iff_false] at h
  · change denominatorFactor11 a ≠ 0
    intro hz
    have h := denominatorFactor11_sign a ha hb
    simp only [hz,mul_zero,lt_self_iff_false] at h
  · change denominatorFactor12 a ≠ 0
    intro hz
    have h := denominatorFactor12_sign a ha hb
    simp only [hz,mul_zero,lt_self_iff_false] at h

theorem denominatorFactor_at_negative_root (q : ℝ) (hq : q ∈ Set.Ioc (0:ℝ) 1)
    (i : Fin 13) : denominatorFactor i (aStar (2*q-2)) ≠ 0 := by
  have h := aStar_negative_range q hq
  exact denominatorFactor_ne_zero _ h.1.le h.2 i

/-- A uniform gap from the only upper-endpoint zero factor. -/
theorem root_upper_denominator_gap (q : ℝ) (hq : q ∈ Set.Ioc (0:ℝ) 1) :
    (3:ℝ)/512 ≤ 1-3*aStar (2*q-2) := by
  have h := aStar_upper_margin q hq
  linarith

#print axioms denominatorFactor_at_negative_root
#print axioms root_upper_denominator_gap
end ThomsonNegative.Reduction
