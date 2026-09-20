import LeanCode.Monotonic.Operators
import LeanCode.Monotonic.ScalarDefinitions
import LeanCode.Monotonic.EstimatesSlow
import LeanCode.Monotonic.EstimatesFast
/-! Quantitative estimates at the prescribed height, with all constants
proved using rational inequalities and the exact square-root identity. -/

noncomputable section
open Real Set
namespace SquareAntiprismCounterexample

private lemma abs_linear_three (c₁ c₂ c₃ x₁ x₂ x₃ u : ℝ)
    (h₁ : |x₁| ≤ u) (h₂ : |x₂| ≤ u) (h₃ : |x₃| ≤ u) :
    |c₁*x₁+c₂*x₂+c₃*x₃| ≤ (|c₁|+|c₂|+|c₃|)*u := by
  calc
    _ ≤ |c₁*x₁|+|c₂*x₂|+|c₃*x₃| := abs_add_three _ _ _
    _ ≤ |c₁| *u+|c₂| *u+|c₃| *u := by simp only [abs_mul]; gcongr
    _ = _ := by ring

private lemma abs_linear_four (c₁ c₂ c₃ c₄ x₁ x₂ x₃ x₄ u : ℝ)
    (h₁ : |x₁| ≤ u) (h₂ : |x₂| ≤ u) (h₃ : |x₃| ≤ u) (h₄ : |x₄| ≤ u) :
    |c₁*x₁+c₂*x₂+c₃*x₃+c₄*x₄| ≤ (|c₁|+|c₂|+|c₃|+|c₄|)*u := by
  have h := abs_linear_three c₁ c₂ c₃ x₁ x₂ x₃ u h₁ h₂ h₃
  have h' : |c₄*x₄| ≤ |c₄| *u := by rw [abs_mul]; gcongr
  calc
    _ ≤ |c₁*x₁+c₂*x₂+c₃*x₃|+|c₄*x₄| := abs_add_le _ _
    _ ≤ (|c₁|+|c₂|+|c₃|)*u+|c₄| *u := add_le_add h h'
    _ = _ := by ring

private lemma coeff_first_star : |B aStar| ≤ 1 ∧ |C aStar| ≤ 1 ∧ |D aStar| ≤ 1 := by
  have hs := sqrt_two_bounds
  simp only [B,C,D,aStar,div_eq_mul_inv,inv_sqrt_two]
  constructor
  · norm_num
  constructor <;> rw [abs_le] <;> constructor <;> nlinarith

private lemma coeff_second_star :
    0 ≤ 128*aStar*(1-aStar) ∧ 0 ≤ 32*aStar*(1-aStar)*kPlus^2 ∧
    0 ≤ 32*aStar*(1-aStar)*kMinus^2 ∧
    128*aStar*(1-aStar)+32*aStar*(1-aStar)*kPlus^2+
      32*aStar*(1-aStar)*kMinus^2 ≤ 56 := by
  refine ⟨by norm_num [aStar], by norm_num [aStar]; positivity, by norm_num [aStar]; positivity, ?_⟩
  simp only [aStar,kPlus,kMinus,div_eq_mul_inv,inv_sqrt_two]
  nlinarith [sqrt_two_sq]

lemma L_bound_star (p : ℝ → ℝ) (u : ℝ)
    (hA : |p (dA aStar)| ≤ u) (hB : |p (dB aStar)| ≤ u)
    (hC : |p (dC aStar)| ≤ u) (hD : |p (dD aStar)| ≤ u) :
    |L aStar p| ≤ 64*u := by
  have hh := abs_linear_four (-16) (-16) (8*(2+√2)) (8*(2-√2))
    _ _ _ _ u hA hB hC hD
  have hc : 0 ≤ 8*(2+√(2:ℝ)) := by positivity
  have hd : 0 ≤ 8*(2-√(2:ℝ)) := by linarith [sqrt_two_lt_two]
  norm_num only [abs_of_nonneg hc,abs_of_nonneg hd,abs_neg] at hh
  unfold L
  convert hh using 1 <;> ring_nf

private lemma Q_second_bound_star (q : ℝ → ℝ) (v : ℝ) (hv : 0 ≤ v)
    (hB : |q (dB aStar)| ≤ v) (hC : |q (dC aStar)| ≤ v)
    (hD : |q (dD aStar)| ≤ v) :
    |128*aStar*(1-aStar)*q (dB aStar)+32*aStar*(1-aStar)*
      (kPlus^2*q (dC aStar)+kMinus^2*q (dD aStar))| ≤ 56*v := by
  rcases coeff_second_star with ⟨hb,hc,hd,hs⟩
  have hh := abs_linear_three (128*aStar*(1-aStar)) (32*aStar*(1-aStar)*kPlus^2)
    (32*aStar*(1-aStar)*kMinus^2) _ _ _ v hB hC hD
  rw [abs_of_nonneg hb,abs_of_nonneg hc,abs_of_nonneg hd] at hh
  calc
    _ = |128*aStar*(1-aStar)*q (dB aStar)+(32*aStar*(1-aStar)*kPlus^2)*q (dC aStar)+
      (32*aStar*(1-aStar)*kMinus^2)*q (dD aStar)| := by congr 1; ring
    _ ≤ _ := hh
    _ ≤ _ := mul_le_mul_of_nonneg_right hs hv

lemma Q_bound_star (p q : ℝ → ℝ) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hA : |p (dA aStar)| ≤ u) (hB : |p (dB aStar)| ≤ u)
    (hC : |p (dC aStar)| ≤ u) (hD : |p (dD aStar)| ≤ u)
    (hB' : |q (dB aStar)| ≤ v) (hC' : |q (dC aStar)| ≤ v)
    (hD' : |q (dD aStar)| ≤ v) :
    |Q aStar p q| ≤ 64*u+56*v := by
  rcases coeff_first_star with ⟨hb,hc,hd⟩
  have hp := abs_linear_four 1 (B aStar) (C aStar) (D aStar) _ _ _ _ u hA hB hC hD
  simp only [one_mul,abs_one] at hp
  have hp' : |p (dA aStar)+B aStar*p (dB aStar)+C aStar*p (dC aStar)+D aStar*p (dD aStar)| ≤ 4*u :=
    hp.trans (mul_le_mul_of_nonneg_right (by linarith) hu)
  have hq := Q_second_bound_star q v hv hB' hC' hD'
  unfold Q
  calc
    _ ≤ |16*(p (dA aStar)+B aStar*p (dB aStar)+C aStar*p (dC aStar)+D aStar*p (dD aStar))|+
      |128*aStar*(1-aStar)*q (dB aStar)+32*aStar*(1-aStar)*(kPlus^2*q (dC aStar)+kMinus^2*q (dD aStar))| := by
      simpa only [add_assoc] using abs_add_le
        (16*(p (dA aStar)+B aStar*p (dB aStar)+C aStar*p (dC aStar)+D aStar*p (dD aStar)))
        (128*aStar*(1-aStar)*q (dB aStar)+32*aStar*(1-aStar)*(kPlus^2*q (dC aStar)+kMinus^2*q (dD aStar)))
    _ ≤ 16*(4*u)+56*v := by simp only [abs_mul]; gcongr; norm_num
    _ = _ := by ring

lemma slow_bounds : -22 < (n:ℝ)^3*L aStar g1 ∧ (n:ℝ)^3*L aStar g1 < -20 ∧
    (n:ℝ)^3*(Q aStar g1 g2+L aStar g1) < -4 := by
  let e₁ : ℝ → ℝ := fun t => (n:ℝ)^3*g1 t+(n:ℝ)-2*t
  let e₂ : ℝ → ℝ := fun t => (n:ℝ)^3*g2 t-2
  have he₁ (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 4) : |e₁ t| ≤ 1/200 := by
    simpa [e₁,g1,n] using slow_error_one t ht.1 ht.2.le
  have he₂ (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 4) : |e₂ t| ≤ 1/400 := by
    simpa [e₂,g2,n] using slow_error_two t ht.1 ht.2.le
  rcases distance_domains aStar_mem with ⟨ha,hb,hc,hd⟩
  have hl := L_bound_star e₁ (1/200) (he₁ _ ha) (he₁ _ hb) (he₁ _ hc) (he₁ _ hd)
  have hq := Q_bound_star e₁ e₂ (1/200) (1/400) (by norm_num) (by norm_num)
    (he₁ _ ha) (he₁ _ hb) (he₁ _ hc) (he₁ _ hd) (he₂ _ hb) (he₂ _ hc) (he₂ _ hd)
  have hle : L aStar e₁ = (n:ℝ)^3*L aStar g1+64/3 := by
    have hlin : L aStar e₁ = (n:ℝ)^3*L aStar g1+L aStar (fun _ => (n:ℝ))-L aStar (fun t => 2*t) := by
      dsimp [L,e₁]; ring
    rw [hlin,L_constant,L_quadratic_star]; ring
  have hqe : Q aStar e₁ e₂ + L aStar e₁ =
      (n:ℝ)^3*(Q aStar g1 g2+L aStar g1)+416/81 := by
    have hlin : Q aStar e₁ e₂ + L aStar e₁ =
        (n:ℝ)^3*(Q aStar g1 g2+L aStar g1)+Q aStar (fun _ => (n:ℝ)) (fun _ => 0)+
          L aStar (fun _ => (n:ℝ))-(Q aStar (fun t => 2*t) (fun _ => 2)+L aStar (fun t => 2*t)) := by
      dsimp [Q,L,e₁,e₂]; ring
    rw [hlin,Q_constant,L_constant,QL_quadratic_star]; ring
  have hs : |Q aStar e₁ e₂+L aStar e₁| ≤ 128*(1/200:ℝ)+56*(1/400:ℝ) := by
    have := abs_add_le (Q aStar e₁ e₂) (L aStar e₁)
    linarith
  rw [hle] at hl
  rw [hqe] at hs
  rw [abs_le] at hl hs
  constructor
  · linarith
  constructor <;> linarith

lemma L_tail_bound_star (p : ℝ → ℝ) (u : ℝ)
    (hB : |p (dB aStar)| ≤ u) (hC : |p (dC aStar)| ≤ u)
    (hD : |p (dD aStar)| ≤ u) :
    |L aStar p+16*p (dA aStar)| ≤ 48*u := by
  have hh := abs_linear_three (-16) (8*(2+√2)) (8*(2-√2)) _ _ _ u hB hC hD
  have hc : 0 ≤ 8*(2+√(2:ℝ)) := by positivity
  have hd : 0 ≤ 8*(2-√(2:ℝ)) := by linarith [sqrt_two_lt_two]
  norm_num only [abs_of_nonneg hc,abs_of_nonneg hd,abs_neg] at hh
  unfold L
  convert hh using 1 <;> ring_nf

lemma QL_tail_bound_star (p q : ℝ → ℝ) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hB : |p (dB aStar)| ≤ u) (hC : |p (dC aStar)| ≤ u)
    (hD : |p (dD aStar)| ≤ u) (hB' : |q (dB aStar)| ≤ v)
    (hC' : |q (dC aStar)| ≤ v) (hD' : |q (dD aStar)| ≤ v) :
    |Q aStar p q+L aStar p| ≤ 96*u+56*v := by
  rcases coeff_first_star with ⟨hb,hc,hd⟩
  have hp := abs_linear_three (B aStar) (C aStar) (D aStar) _ _ _ u hB hC hD
  have hp' : |B aStar*p (dB aStar)+C aStar*p (dC aStar)+D aStar*p (dD aStar)| ≤ 3*u :=
    hp.trans (mul_le_mul_of_nonneg_right (by linarith) hu)
  have hp'' : |16*(B aStar*p (dB aStar)+C aStar*p (dC aStar)+D aStar*p (dD aStar))| ≤ 48*u := by
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<16)]
    nlinarith
  have hl := L_tail_bound_star p u hB hC hD
  have hq := Q_second_bound_star q v hv hB' hC' hD'
  have heq : Q aStar p q+L aStar p =
      16*(B aStar*p (dB aStar)+C aStar*p (dC aStar)+D aStar*p (dD aStar))+
      (L aStar p+16*p (dA aStar))+
      (128*aStar*(1-aStar)*q (dB aStar)+32*aStar*(1-aStar)*
        (kPlus^2*q (dC aStar)+kMinus^2*q (dD aStar))) := by unfold Q; ring
  rw [heq]
  have := abs_add_three
    (16*(B aStar*p (dB aStar)+C aStar*p (dC aStar)+D aStar*p (dD aStar)))
    (L aStar p+16*p (dA aStar))
    (128*aStar*(1-aStar)*q (dB aStar)+32*aStar*(1-aStar)*(kPlus^2*q (dC aStar)+kMinus^2*q (dD aStar)))
  linarith

lemma fast_bounds : 8*(n:ℝ)/dStar < L aStar h1 ∧
    |(Q aStar h1 h2+L aStar h1)/(L aStar h1)| < 1/10 := by
  rcases fast_distance_ratios with ⟨hb,hbr,hc,hcr,hd,hdr⟩
  have hB := fast_tail _ hb hbr.le
  have hC := fast_tail _ hc hcr.le
  have hD := fast_tail _ hd hdr.le
  have hT : 0 < (n:ℝ)/dStar := div_pos n_pos dStar_pos
  have hR : 0 < (n:ℝ)*((n:ℝ)+1)/dStar^2 :=
    div_pos (mul_pos n_pos (by linarith [n_pos])) (sq_pos_of_pos dStar_pos)
  have hl := L_tail_bound_star h1 (((n:ℝ)/dStar)*eta) hB.1 hC.1 hD.1
  rw [distances_at_star.1,h1_at_dStar,abs_le] at hl
  have heta := eta_bounds
  have hlower : 8*(n:ℝ)/dStar < L aStar h1 := by
    have hmul := mul_lt_mul_of_pos_left heta.2 hT
    norm_num [n,dStar] at hl hT hmul ⊢
    linarith [hl.1]
  refine ⟨hlower,?_⟩
  have hLpos : 0 < L aStar h1 := lt_trans (div_pos (mul_pos (by norm_num) n_pos) dStar_pos) hlower
  have hs := QL_tail_bound_star h1 h2 (((n:ℝ)/dStar)*eta)
    (((n:ℝ)*((n:ℝ)+1)/dStar^2)*eta)
    (mul_nonneg hT.le heta.1.le) (mul_nonneg hR.le heta.1.le)
    hB.1 hC.1 hD.1 hB.2 hC.2 hD.2
  rw [abs_div,abs_of_pos hLpos,div_lt_iff₀ hLpos]
  have hnum : 96*((n:ℝ)/dStar*eta)+56*((n:ℝ)*((n:ℝ)+1)/dStar^2*eta) <
      (1/10:ℝ)*(8*(n:ℝ)/dStar) := by
    norm_num [n,dStar]
    linarith [heta.2]
  nlinarith

end SquareAntiprismCounterexample
