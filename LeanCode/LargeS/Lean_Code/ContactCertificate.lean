import Lean_Code.Parameter

open Real
noncomputable section
namespace SquareAntiprismVerification

def azimuth : Fin 8 → ℝ :=
  ![0, π / 2, π, 3 * π / 2, π / 4, 3 * π / 4, 5 * π / 4, 7 * π / 4]

def layerSign : Fin 8 → ℝ := ![1, 1, 1, 1, -1, -1, -1, -1]

@[simp] lemma azimuth_0 : azimuth 0 = 0 := rfl
@[simp] lemma azimuth_1 : azimuth 1 = π / 2 := rfl
@[simp] lemma azimuth_2 : azimuth 2 = π := rfl
@[simp] lemma azimuth_3 : azimuth 3 = 3 * π / 2 := rfl
@[simp] lemma azimuth_4 : azimuth 4 = π / 4 := rfl
@[simp] lemma azimuth_5 : azimuth 5 = 3 * π / 4 := rfl
@[simp] lemma azimuth_6 : azimuth 6 = 5 * π / 4 := rfl
@[simp] lemma azimuth_7 : azimuth 7 = 7 * π / 4 := rfl
@[simp] lemma layerSign_0 : layerSign 0 = 1 := rfl
@[simp] lemma layerSign_1 : layerSign 1 = 1 := rfl
@[simp] lemma layerSign_2 : layerSign 2 = 1 := rfl
@[simp] lemma layerSign_3 : layerSign 3 = 1 := rfl
@[simp] lemma layerSign_4 : layerSign 4 = -1 := rfl
@[simp] lemma layerSign_5 : layerSign 5 = -1 := rfl
@[simp] lemma layerSign_6 : layerSign 6 = -1 := rfl
@[simp] lemma layerSign_7 : layerSign 7 = -1 := rfl

def rigidityRow (i j : Fin 8) (α β : Fin 8 → ℝ) : ℝ :=
  (1 - aInf) * sin (azimuth j - azimuth i) * (α i - α j) +
    aInf * (layerSign i * layerSign j - cos (azimuth j - azimuth i)) *
      (β i + β j)

abbrev InfinitesimalCoordinates := (Fin 8 → ℝ) × (Fin 8 → ℝ)

def InContactGauge (q : InfinitesimalCoordinates) : Prop :=
  q.1 0 = 0 ∧ q.2 0 = 0 ∧ q.2 1 = 0

/-- The thirteen rows of the nonsingular minor, in exactly the order printed
in the paper. -/
def selectedContactRows (q : InfinitesimalCoordinates) : Fin 13 → ℝ :=
  ![rigidityRow 2 3 q.1 q.2,
    rigidityRow 4 5 q.1 q.2,
    rigidityRow 6 7 q.1 q.2,
    rigidityRow 1 2 q.1 q.2,
    rigidityRow 4 7 q.1 q.2,
    rigidityRow 3 6 q.1 q.2,
    rigidityRow 5 6 q.1 q.2,
    rigidityRow 2 6 q.1 q.2,
    rigidityRow 2 5 q.1 q.2,
    rigidityRow 3 7 q.1 q.2,
    rigidityRow 0 3 q.1 q.2,
    rigidityRow 0 7 q.1 q.2,
    rigidityRow 1 5 q.1 q.2]

/-- The 13-by-13 minor specified in the paper is nonsingular.  The proof is
an exact inverse certificate over `ℚ(√2)`; each `linear_combination` line is
checked by Lean's ring normalizer. -/
theorem contact_minor_injective (α β : Fin 8 → ℝ)
    (ha0 : α 0 = 0) (hb0 : β 0 = 0) (hb1 : β 1 = 0)
    (h1 : rigidityRow 2 3 α β = 0)
    (h2 : rigidityRow 4 5 α β = 0)
    (h3 : rigidityRow 6 7 α β = 0)
    (h4 : rigidityRow 1 2 α β = 0)
    (h5 : rigidityRow 4 7 α β = 0)
    (h6 : rigidityRow 3 6 α β = 0)
    (h7 : rigidityRow 5 6 α β = 0)
    (h8 : rigidityRow 2 6 α β = 0)
    (h9 : rigidityRow 2 5 α β = 0)
    (h10 : rigidityRow 3 7 α β = 0)
    (h11 : rigidityRow 0 3 α β = 0)
    (h12 : rigidityRow 0 7 α β = 0)
    (h13 : rigidityRow 1 5 α β = 0) : α = 0 ∧ β = 0 := by
  have hs2 : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2cube : √(2 : ℝ) ^ 3 = 2 * √2 := by
    calc
      √(2 : ℝ) ^ 3 = √2 ^ 2 * √2 := by ring
      _ = 2 * √2 := by rw [hs2]
  have hs2four : √(2 : ℝ) ^ 4 = 4 := by
    calc
      √(2 : ℝ) ^ 4 = (√2 ^ 2) ^ 2 := by ring
      _ = 4 := by rw [hs2]; norm_num
  have hs3s : sin (3 * π / 4) = √2 / 2 := by
    rw [show (3 : ℝ) * π / 4 = π / 2 + π / 4 by ring, Real.sin_add]
    simp [Real.sin_pi_div_four, Real.cos_pi_div_four]
  have hs3c : cos (3 * π / 4) = -√2 / 2 := by
    rw [show (3 : ℝ) * π / 4 = π / 2 + π / 4 by ring, Real.cos_add]
    simp [Real.sin_pi_div_four, Real.cos_pi_div_four]
    ring
  have hs5s : sin (5 * π / 4) = -√2 / 2 := by
    rw [show (5 : ℝ) * π / 4 = π + π / 4 by ring, Real.sin_add]
    simp [Real.sin_pi_div_four, Real.cos_pi_div_four]
    ring
  have hs5c : cos (5 * π / 4) = -√2 / 2 := by
    rw [show (5 : ℝ) * π / 4 = π + π / 4 by ring, Real.cos_add]
    simp [Real.sin_pi_div_four, Real.cos_pi_div_four]
    ring
  have hs7s : sin (7 * π / 4) = -√2 / 2 := by
    rw [show (7 : ℝ) * π / 4 = 2 * π - π / 4 by ring, Real.sin_sub]
    simp [Real.sin_pi_div_four, Real.cos_pi_div_four]
    ring
  have hs7c : cos (7 * π / 4) = √2 / 2 := by
    rw [show (7 : ℝ) * π / 4 = 2 * π - π / 4 by ring, Real.cos_sub]
    simp [Real.sin_pi_div_four, Real.cos_pi_div_four]
  have hs32s : sin (3 * π / 2) = -1 := by
    rw [show (3 : ℝ) * π / 2 = π + π / 2 by ring, Real.sin_add]
    simp
  have hs32c : cos (3 * π / 2) = 0 := by
    rw [show (3 : ℝ) * π / 2 = π + π / 2 by ring, Real.cos_add]
    simp
  norm_num [rigidityRow, aInf, Real.sin_sub, Real.cos_sub,
    Real.sin_pi_div_four, Real.cos_pi_div_four, hs3s, hs3c, hs5s, hs5c,
    hs7s, hs7c, hs32s, hs32c] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  simp only [ha0, hb0, hb1, zero_sub, zero_add] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  ring_nf at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  norm_num [hs2, hs2cube, hs2four] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  ring_nf at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
  have ha1 : α 1 = 0 := by
    linear_combination
      ((5*√2 - 8)/4) * h1 + ((3*√2 - 2)/2) * h3 +
      ((3*√2 - 2)/4) * h4 + (4*√2 - 5) * h6 +
      ((3*√2 - 2)/2) * h7 + (4*√2 - 5) * h8 +
      ((5*√2 - 8)/2) * h9 + ((5*√2 - 8)/2) * h10 +
      ((3*√2 - 2)/4) * h11 + ((3*√2 - 2)/2) * h12 +
      ((3*√2 - 2)/2) * h13 +
      ((-9/14) * α 1 + (-5/7) * α 2 + (5/7) * α 3 + (-1/7) * α 5 +
        (1/7) * α 7 + (23/28) * β 2 + (23/28) * β 3 + (3/7) * β 5 +
        (6/7) * β 6 + (3/7) * β 7) * hs2
  have ha2 : α 2 = 0 := by
    linear_combination
      ((4*√2 - 5)/4) * h1 + ((3*√2 - 2)/4) * h3 +
      ((√2 - 3)/2) * h4 + ((11*√2 - 12)/4) * h6 +
      ((3*√2 - 2)/2) * h7 + ((13*√2 - 18)/4) * h8 +
      ((5*√2 - 8)/2) * h9 + ((5*√2 - 8)/4) * h10 +
      ((2*√2 + 1)/4) * h11 + ((3*√2 - 2)/4) * h12 +
      ((3*√2 - 2)/2) * h13 +
      ((-5/7) * α 1 + (-2/7) * α 2 + (5/7) * α 3 + (-1/7) * α 5 +
        (1/14) * α 6 + (1/14) * α 7 + (45/56) * β 2 + (3/7) * β 3 +
        (3/7) * β 5 + (9/14) * β 6 + (3/14) * β 7) * hs2
  have ha3 : α 3 = 0 := by
    linear_combination
      ((√2 - 3)/4) * h1 + ((√2 - 3)/4) * h4 +
      ((3*√2 - 2)/4) * h6 + ((3*√2 - 2)/4) * h7 +
      ((5*√2 - 8)/4) * h8 + ((5*√2 - 8)/4) * h9 +
      ((√2 + 4)/4) * h11 + ((3*√2 - 2)/4) * h13 +
      ((-5/14) * α 1 + (3/7) * α 3 + (-1/14) * α 5 + (1/14) * α 6 +
        (11/28) * β 2 + (1/56) * β 3 + (3/14) * β 5 + (3/14) * β 6) * hs2
  have ha4 : α 4 = 0 := by
    linear_combination
      ((5*√2 - 8)/8) * h1 + ((√2 + 4)/8) * h2 +
      ((5*√2 - 8)/8) * h3 + (-(√2 + 4)/8) * h4 +
      (-(√2 + 4)/8) * h5 + ((10*√2 - 9)/4) * h6 +
      (7*√2/8) * h7 + ((6*√2 - 11)/4) * h8 +
      ((4*√2 - 5)/4) * h9 + ((6*√2 - 11)/4) * h10 +
      (7*√2/8) * h11 + ((4*√2 - 5)/4) * h12 +
      ((2*√2 + 1)/4) * h13 +
      ((-9/28) * α 1 + (-1/14) * α 2 + (9/14) * α 3 + (1/14) * α 4 +
        (-1/14) * α 5 + (-9/14) * α 6 + (1/14) * α 7 + (11/28) * β 2 +
        (3/7) * β 3 + (1/28) * β 5 + (3/7) * β 6 + (11/28) * β 7) * hs2
  have ha5 : α 5 = 0 := by
    linear_combination
      ((11*√2 - 12)/8) * h1 + ((4*√2 - 5)/4) * h3 +
      ((5*√2 - 8)/8) * h4 + ((15*√2 - 17)/4) * h6 +
      ((3*√2 - 2)/2) * h7 + (7*(2*√2 - 3)/4) * h8 +
      (3*(4*√2 - 5)/4) * h9 + ((9*√2 - 13)/4) * h10 +
      (7*√2/8) * h11 + ((4*√2 - 5)/4) * h12 +
      ((4*√2 - 5)/4) * h13 +
      ((-11/28) * α 1 + (-1/14) * α 2 + (5/7) * α 3 + (-5/7) * α 5 +
        (-2/7) * α 6 + (3/7) * α 7 + (23/28) * β 2 + (9/14) * β 3 +
        (3/7) * β 5 + (47/56) * β 6 + (23/56) * β 7) * hs2
  have ha6 : α 6 = 0 := by
    linear_combination
      ((5*√2 - 8)/8) * h1 + ((2*√2 + 1)/4) * h3 +
      ((5*√2 - 8)/8) * h4 + (7*(√2 - 1)/4) * h6 +
      ((4*√2 - 5)/4) * h7 + ((9*√2 - 13)/4) * h8 +
      ((9*√2 - 13)/4) * h9 + ((√2 - 3)/4) * h10 +
      ((√2 + 4)/8) * h11 + ((2*√2 + 1)/4) * h12 +
      ((4*√2 - 5)/4) * h13 +
      ((-11/28) * α 1 + (5/7) * α 3 + (-3/7) * α 5 + (1/7) * α 6 +
        (-2/7) * α 7 + (17/28) * β 2 + (3/14) * β 3 + (23/56) * β 5 +
        (3/7) * β 6 + (1/56) * β 7) * hs2
  have ha7 : α 7 = 0 := by
    linear_combination
      (-(√2 + 4)/8) * h1 + (-(√2 + 4)/8) * h4 +
      ((2*√2 + 1)/4) * h6 + ((2*√2 + 1)/4) * h7 +
      ((√2 - 3)/4) * h8 + ((√2 - 3)/4) * h9 +
      (-(2*√2 + 1)/4) * h10 + ((√2 + 4)/8) * h11 +
      ((2*√2 + 1)/4) * h12 + ((2*√2 + 1)/4) * h13 +
      ((-9/28) * α 1 + (9/14) * α 3 + (2/7) * α 5 + (-2/7) * α 6 +
        (-4/7) * α 7 + (5/28) * β 2 + (1/56) * β 5 + (1/56) * β 6) * hs2
  have hb2 : β 2 = 0 := by
    linear_combination
      ((3*√2 - 2)/2) * h1 + (√2 - 3) * h3 + (4*√2 - 5) * h6 +
      (√2 - 3) * h8 + (4*√2 - 5) * h10 + ((3*√2 - 2)/2) * h11 +
      (√2 - 3) * h12 +
      ((-1/7) * α 2 + (-10/7) * α 6 + (10/7) * α 7 + (-3/14) * β 2 +
        (6/7) * β 3 + (11/14) * β 6 + (11/14) * β 7) * hs2
  have hb3 : β 3 = 0 := by
    linear_combination
      ((3*√2 - 2)/2) * h1 + ((3*√2 - 2)/2) * h4 + (√2 - 3) * h6 +
      (√2 - 3) * h7 + (4*√2 - 5) * h8 + (4*√2 - 5) * h9 +
      (√2 - 3) * h13 +
      ((-1/7) * α 1 + (1/7) * α 3 + (-10/7) * α 5 + (10/7) * α 6 +
        (6/7) * β 2 + (-3/14) * β 3 + (11/14) * β 5 + (11/14) * β 6) * hs2
  have hb4 : β 4 = 0 := by
    linear_combination
      (-3*(√2 - 3)/2) * h1 + ((2*√2 + 1)/2) * h2 +
      (-(4*√2 - 5)/2) * h3 + (-(√2 - 3)/2) * h4 +
      ((2*√2 + 1)/2) * h5 + (-(13*√2 - 18)/2) * h6 +
      (-(4*√2 - 5)/2) * h7 + (-(13*√2 - 18)/2) * h8 +
      (-7*(√2 - 2)/2) * h9 + (-7*(√2 - 2)/2) * h10 +
      (-(√2 - 3)/2) * h11 + (-(3*√2 - 2)/2) * h12 +
      (-(3*√2 - 2)/2) * h13 +
      ((5/7) * α 1 + (10/7) * α 2 + (-10/7) * α 3 + (2/7) * α 5 +
        (-2/7) * α 7 + (-11/7) * β 2 + (-11/7) * β 3 + (-4/7) * β 4 +
        (-11/14) * β 5 + (-23/14) * β 6 + (-11/14) * β 7) * hs2
  have hb5 : β 5 = 0 := by
    linear_combination
      ((√2 - 3)/2) * h1 + ((3*√2 - 2)/2) * h3 +
      (-(√2 - 3)/2) * h4 + ((5*√2 - 8)/2) * h6 +
      ((3*√2 - 2)/2) * h8 + (-(3*√2 - 2)/2) * h9 +
      ((5*√2 - 8)/2) * h10 + ((√2 - 3)/2) * h11 +
      ((3*√2 - 2)/2) * h12 + (-(3*√2 - 2)/2) * h13 +
      ((5/7) * α 1 + (-10/7) * α 2 + (-1/7) * α 6 + (1/7) * α 7 +
        (11/14) * β 3 + (-9/14) * β 5 + (3/7) * β 6 + (3/7) * β 7) * hs2
  have hb6 : β 6 = 0 := by
    linear_combination
      ((√2 - 3)/2) * h1 + ((3*√2 - 2)/2) * h3 +
      ((√2 - 3)/2) * h4 + ((5*√2 - 8)/2) * h6 +
      ((3*√2 - 2)/2) * h7 + ((5*√2 - 8)/2) * h8 +
      ((5*√2 - 8)/2) * h9 + ((5*√2 - 8)/2) * h10 +
      ((√2 - 3)/2) * h11 + ((3*√2 - 2)/2) * h12 +
      ((3*√2 - 2)/2) * h13 +
      ((-5/7) * α 1 + (-1/7) * α 5 + (1/7) * α 7 + (11/14) * β 2 +
        (11/14) * β 3 + (3/7) * β 5 + (3/14) * β 6 + (3/7) * β 7) * hs2
  have hb7 : β 7 = 0 := by
    linear_combination
      ((√2 - 3)/2) * h1 + ((√2 - 3)/2) * h4 +
      ((3*√2 - 2)/2) * h6 + ((3*√2 - 2)/2) * h7 +
      ((5*√2 - 8)/2) * h8 + ((5*√2 - 8)/2) * h9 +
      (-(3*√2 - 2)/2) * h10 + (-(√2 - 3)/2) * h11 +
      (-(3*√2 - 2)/2) * h12 + ((3*√2 - 2)/2) * h13 +
      ((-5/7) * α 1 + (10/7) * α 3 + (-1/7) * α 5 + (1/7) * α 6 +
        (11/14) * β 2 + (3/7) * β 5 + (3/7) * β 6 + (-9/14) * β 7) * hs2
  constructor
  · funext i
    fin_cases i <;> simp [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7]
  · funext i
    fin_cases i <;> simp [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7]

theorem selectedContactRows_eq_zero {q : InfinitesimalCoordinates}
    (hgauge : InContactGauge q) (hrows : selectedContactRows q = 0) : q = 0 := by
  obtain ⟨ha0, hb0, hb1⟩ := hgauge
  have hr (i : Fin 13) : selectedContactRows q i = 0 := by
    rw [hrows]
    rfl
  have h := contact_minor_injective q.1 q.2 ha0 hb0 hb1
    (by simpa [selectedContactRows] using hr 0)
    (by simpa [selectedContactRows] using hr 1)
    (by simpa [selectedContactRows] using hr 2)
    (by simpa [selectedContactRows] using hr 3)
    (by simpa [selectedContactRows] using hr 4)
    (by simpa [selectedContactRows] using hr 5)
    (by simpa [selectedContactRows] using hr 6)
    (by simpa [selectedContactRows] using hr 7)
    (by simpa [selectedContactRows] using hr 8)
    (by simpa [selectedContactRows] using hr 9)
    (by simpa [selectedContactRows] using hr 10)
    (by simpa [selectedContactRows] using hr 11)
    (by simpa [selectedContactRows] using hr 12)
  rcases h with ⟨hα, hβ⟩
  exact Prod.ext hα hβ

end SquareAntiprismVerification
