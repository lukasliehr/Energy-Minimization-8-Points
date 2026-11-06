import AllS.Units.N_A.N_encoding
import AllS.Units.N_A.N_interval_semantics

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def MatrixMidpointRadiusStatement : Prop :=
  ∀ {m n p : ℕ} (X MA RA : Matrix (Fin m) (Fin n) ℝ)
    (Y MB RB : Matrix (Fin n) (Fin p) ℝ) (SA SB : ℝ),
    0 < SA → 0 < SB → (∀ i h, 0 ≤ RA i h) → (∀ h j, 0 ≤ RB h j) →
    (∀ i h, |X i h-MA i h/(2*SA)| ≤ RA i h/(2*SA)) →
    (∀ h j, |Y h j-MB h j/(2*SB)| ≤ RB h j/(2*SB)) →
    ∀ i j, |(X*Y) i j-(MA*MB) i j/(4*SA*SB)|  ≤ 
      (∑ h, (|MA i h| * RB h j + RA i h * |MB h j| + RA i h * RB h j)) / (4 * SA * SB)

theorem product_midpoint_radius (x y a b r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hx : |x-a| ≤ r) (hy : |y-b| ≤ s) :
    |x*y-a*b| ≤ |a| *s+r* |b|+r*s := by
  have hid : x*y-a*b=a*(y-b)+(x-a)*b+(x-a)*(y-b) := by ring
  rw [hid]
  calc
    _  ≤  |a*(y-b)+(x-a)*b|+|(x-a)*(y-b)| := abs_add_le _ _
    _  ≤  (|a*(y-b)|+|(x-a)*b|)+|(x-a)*(y-b)| :=
      add_le_add (abs_add_le _ _) le_rfl
    _  ≤  |a| *s+r* |b|+r*s := by
      simp only [abs_mul]
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hy (abs_nonneg a))
        (mul_le_mul_of_nonneg_right hx (abs_nonneg b)))
        (mul_le_mul hx hy (abs_nonneg _) hr)

theorem scaled_product_midpoint_radius (x y a b r s SA SB : ℝ)
    (hSA : 0 < SA) (hSB : 0 < SB) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hx : |x-a/(2*SA)| ≤ r/(2*SA)) (hy : |y-b/(2*SB)| ≤ s/(2*SB)) :
    |x*y-a*b/(4*SA*SB)| ≤ (|a| *s+r* |b|+r*s)/(4*SA*SB) := by
  have h1 := product_midpoint_radius x y (a/(2*SA)) (b/(2*SB))
    (r/(2*SA)) (s/(2*SB)) (by positivity) (by positivity) hx hy
  have hprod : a/(2*SA)*(b/(2*SB))=a*b/(4*SA*SB) := by ring
  rw [hprod] at h1
  convert h1 using 1
  rw [abs_div, abs_div, abs_of_pos (mul_pos (by norm_num) hSA),
    abs_of_pos (mul_pos (by norm_num) hSB)]
  ring

theorem matrix_polynomials_midpoint_radius : MatrixMidpointRadiusStatement := by
  intro m n p X MA RA Y MB RB SA SB hSA hSB hRA hRB hX hY i j
  simp only [Matrix.mul_apply, Finset.sum_div, ←Finset.sum_sub_distrib]
  calc
    _  ≤  ∑ h : Fin n, |X i h*Y h j-MA i h*MB h j/(4*SA*SB)| :=
      Finset.abs_sum_le_sum_abs _ _
    _  ≤  _ := Finset.sum_le_sum fun h _ =>
      scaled_product_midpoint_radius _ _ _ _ _ _ SA SB hSA hSB
        (hRA i h) (hRB h j) (hX i h) (hY h j)

#check matrix_polynomials_midpoint_radius
#print MatrixMidpointRadiusStatement
#print axioms matrix_polynomials_midpoint_radius
end Blueprint.CAP
