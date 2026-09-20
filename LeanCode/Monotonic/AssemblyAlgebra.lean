import LeanCode.Monotonic.ScalarDefinitions
import LeanCode.Monotonic.Operators

noncomputable section
open Real
namespace SquareAntiprismCounterexample

lemma coefficient_positive
    (hg : L aStar g1 < 0) (hh : 0 < L aStar h1)
    (he : lambda = -L aStar g1 / L aStar h1) : 0 < lambda := by
  rw [he]
  exact div_pos (neg_pos.mpr hg) hh

lemma mixture_stationary
    (hh : L aStar h1 ≠ 0)
    (he : lambda = -L aStar g1 / L aStar h1) : L aStar f1 = 0 := by
  unfold f1
  rw [L_add, L_smul, he]
  field_simp
  ring

lemma mixture_variation_identity
    (hh : L aStar h1 ≠ 0)
    (he : lambda = -L aStar g1 / L aStar h1) :
    Q aStar f1 f2 = (Q aStar g1 g2 + L aStar g1) -
      L aStar g1 * ((Q aStar h1 h2 + L aStar h1) / L aStar h1) := by
  unfold f1 f2
  rw [Q_add, Q_smul, he]
  field_simp
  ring

lemma mixture_variation_negative
    (hglo : -22 < (n:ℝ)^3 * L aStar g1)
    (hghi : (n:ℝ)^3 * L aStar g1 < -20)
    (hgs : (n:ℝ)^3 * (Q aStar g1 g2 + L aStar g1) < -4)
    (hh : 0 < L aStar h1)
    (hhr : |(Q aStar h1 h2 + L aStar h1) / L aStar h1| < 1/10)
    (he : lambda = -L aStar g1 / L aStar h1) : Q aStar f1 f2 < 0 := by
  let A := (n:ℝ)^3 * L aStar g1
  let R := (Q aStar h1 h2 + L aStar h1) / L aStar h1
  have hA : |A| < 22 := abs_lt.mpr ⟨hglo, by dsimp [A]; linarith⟩
  have hR : |R| < 1/10 := hhr
  have hprod : |A * R| < 22/10 := by
    rw [abs_mul]
    nlinarith [abs_nonneg A, abs_nonneg R,
      mul_nonneg (sub_nonneg.mpr hA.le) (abs_nonneg R)]
  have hbound : -A*R < 22/10 := by
    have := neg_le_abs (A*R)
    nlinarith
  have hidentity := mixture_variation_identity hh.ne' he
  have hscaled : (n:ℝ)^3 * Q aStar f1 f2 < 0 := by
    rw [hidentity]
    dsimp [A, R] at hbound
    nlinarith
  have hn3 : 0 < (n:ℝ)^3 := pow_pos n_pos 3
  by_contra hQ
  have := mul_nonneg hn3.le (le_of_not_gt hQ)
  linarith

end SquareAntiprismCounterexample
