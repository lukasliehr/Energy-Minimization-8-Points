import ThomsonNegative.Definitions
import ThomsonNegative.SeriesIdentity

noncomputable section
open scoped BigOperators
namespace ThomsonNegative

def pairSum (f : Fin 8 → Fin 8 → ℝ) : ℝ :=
  ∑ i : Fin 8, ∑ j : Fin 8 with i<j, f i j

/-- The normalization is a negative scalar multiple of the original distance sum. -/
theorem energy_negative_scale (s : ℝ) (hs : s < 0) (Y : Fin 8 → Point) :
    E s Y = (pairSum fun i j => ‖Y i-Y j‖^(-s))/s := by
  simp only [E, if_neg (ne_of_lt hs), pairSum, Finset.sum_div]

/-- Minimizing normalized negative energy is maximizing the unnormalized sum. -/
theorem negative_energy_le_iff (s : ℝ) (hs : s < 0) (Y Z : Fin 8 → Point) :
    E s Z ≤ E s Y ↔
      (pairSum fun i j => ‖Y i-Y j‖^(-s)) ≤ (pairSum fun i j => ‖Z i-Z j‖^(-s)) := by
  rw [energy_negative_scale s hs Y,energy_negative_scale s hs Z]
  exact div_le_div_right_of_neg hs

lemma pairSum_const (c : ℝ) : pairSum (fun _ _ => c) = 28*c := by
  have hn : (∑ i : Fin 8, (Finset.univ.filter (fun j : Fin 8 => i<j)).card) = 28 := by
    decide +kernel
  simp only [pairSum,Finset.sum_const,nsmul_eq_mul,← Finset.sum_mul,← Nat.cast_sum,hn,Nat.cast_ofNat]

/-- Exact centroid identity. It does not assume distinctness. -/
theorem pair_inner_centroid (Y : Fin 8 → Point) (hY : ∀ i, ‖Y i‖=1) :
    pairSum (fun i j => inner ℝ (Y i) (Y j)) = (‖∑ i,Y i‖^2-8)/2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp_rw [sum_inner,inner_sum]
  simp [pairSum,Fin.sum_univ_succ,Finset.sum_filter,real_inner_comm,real_inner_self_eq_norm_sq,hY]
  ring

lemma pairSum_add (f g : Fin 8 → Fin 8 → ℝ) :
    pairSum (fun i j => f i j+g i j) = pairSum f+pairSum g := by
  simp [pairSum,Finset.sum_add_distrib]

lemma pairSum_mul (c : ℝ) (f : Fin 8 → Fin 8 → ℝ) :
    pairSum (fun i j => c*f i j) = c*pairSum f := by
  simp [pairSum,Finset.mul_sum]

/-- The auxiliary pair potential in the polynomial-series coordinate. -/
def auxEnergy (q : ℝ) (Y : Fin 8 → Point) : ℝ :=
  pairSum (fun i j => normalizedAux q ((1+inner ℝ (Y i) (Y j))/2))

/-- Remove the constant and centroid terms before constructing a certificate. -/
theorem potential_decomposition (q x : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hx : x ≤ 1) :
    (4*(1-x))^(1-q)/(2*q-2) =
      (4:ℝ)^(1-q)/(2*q-2)+2*(4:ℝ)^(-q)*x+
        2*q*(4:ℝ)^(-q)*normalizedAux q x := by
  have hp : (4:ℝ)^(1-q) = 4*(4:ℝ)^(-q) := by
    rw [show 1-q = 1+(-q) by ring,Real.rpow_add (by norm_num),Real.rpow_one]
  rw [Real.mul_rpow (by norm_num) (by linarith),hp]
  unfold normalizedAux
  rw [show 2*q-2 = -2*(1-q) by ring]
  field_simp [hq.1.ne', (sub_pos.mpr hq.2).ne']
  ring

/-- Squared distance and inner-product powers agree, including zero distance. -/
theorem pair_power (q : ℝ) (y z : Point) (hy : ‖y‖=1) (hz : ‖z‖=1) :
    ‖y-z‖^(-(2*q-2)) = (4*(1-(1+inner ℝ y z)/2))^(1-q) := by
  have hd : ‖y-z‖^2 = 4*(1-(1+inner ℝ y z)/2) := by
    rw [norm_sub_sq_real,hy,hz]
    ring
  calc
    _ = ‖y-z‖^((2:ℝ)*(1-q)) := by congr 1; ring
    _ = (‖y-z‖^(2:ℝ))^(1-q) := Real.rpow_mul (norm_nonneg _) _ _
    _ = _ := by rw [Real.rpow_two,hd]

/-- Exact energy decomposition; this is the bridge back to the showcase. -/
theorem energy_decomposition (q : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (Y : Fin 8 → Point) (hY : ∀ i, ‖Y i‖=1) :
    E (2*q-2) Y = 28*((4:ℝ)^(1-q)/(2*q-2))+
      (4:ℝ)^(-q)*(24+‖∑ i,Y i‖^2/2)+2*q*(4:ℝ)^(-q)*auxEnergy q Y := by
  have hp (i j : Fin 8) :
      ‖Y i-Y j‖^(-(2*q-2))/(2*q-2) =
        (4:ℝ)^(1-q)/(2*q-2)+(4:ℝ)^(-q)*(1+inner ℝ (Y i) (Y j))+
          2*q*(4:ℝ)^(-q)*normalizedAux q ((1+inner ℝ (Y i) (Y j))/2) := by
    rw [pair_power q (Y i) (Y j) (hY i) (hY j)]
    have hd := sq_nonneg ‖Y i-Y j‖
    rw [norm_sub_sq_real,hY i,hY j] at hd
    have hx : (1+inner ℝ (Y i) (Y j))/2 ≤ 1 := by nlinarith
    rw [potential_decomposition q _ hq hx]
    ring
  simp only [E,if_neg (show 2*q-2 ≠ 0 by linarith [hq.2])]
  change pairSum (fun i j => ‖Y i-Y j‖^(-(2*q-2))/(2*q-2)) = _
  simp_rw [hp]
  rw [pairSum_add,pairSum_add,pairSum_const,pairSum_mul,pairSum_mul]
  change 28*((4:ℝ)^(1-q)/(2*q-2))+
    (4:ℝ)^(-q)*pairSum (fun i j => 1+inner ℝ (Y i) (Y j))+
    2*q*(4:ℝ)^(-q)*auxEnergy q Y = _
  rw [pairSum_add,pairSum_const,pair_inner_centroid Y hY]
  ring

/-- Auxiliary optimality suffices: the discarded centroid term is nonnegative. -/
theorem energy_le_of_auxEnergy_le (q : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (Y Z : Fin 8 → Point) (hY : ∀ i, ‖Y i‖=1) (hZ : ∀ i, ‖Z i‖=1)
    (hcentroid : ∑ i,Z i=0) (haux : auxEnergy q Z ≤ auxEnergy q Y) :
    E (2*q-2) Z ≤ E (2*q-2) Y := by
  rw [energy_decomposition q hq Y hY,energy_decomposition q hq Z hZ,hcentroid]
  simp only [norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),zero_div,add_zero]
  have hs : 0 < (4:ℝ)^(-q) := Real.rpow_pos_of_pos (by norm_num) _
  have hm := mul_le_mul_of_nonneg_left haux (show 0 ≤ 2*q*(4:ℝ)^(-q) by positivity [hq.1])
  have hn := mul_nonneg hs.le (sq_nonneg ‖∑ i,Y i‖)
  nlinarith

/-- The endpoint has a completely analytic, nonunique equality criterion. -/
theorem energy_minus_two (Y : Fin 8 → Point) (hY : ∀ i, ‖Y i‖=1) :
    E (-2) Y = -32+‖∑ i,Y i‖^2/2 := by
  rw [energy_negative_scale (-2) (by norm_num)]
  norm_num only [neg_neg,Real.rpow_two]
  have hd (i j : Fin 8) : ‖Y i-Y j‖^2 = 2+(-2)*inner ℝ (Y i) (Y j) := by
    rw [norm_sub_sq_real,hY i,hY j]
    ring
  simp_rw [hd]
  rw [pairSum_add,pairSum_const,pairSum_mul,pair_inner_centroid Y hY]
  ring

theorem energy_minus_two_minimum (Y : Fin 8 → Point) (hY : ∀ i, ‖Y i‖=1) :
    -32 ≤ E (-2) Y ∧ (E (-2) Y = -32 ↔ ∑ i,Y i=0) := by
  rw [energy_minus_two Y hY]
  refine ⟨by nlinarith [sq_nonneg ‖∑ i,Y i‖],?_⟩
  constructor
  · intro he
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (∑ i,Y i)]
  · intro he
    simp [he]

/-- The candidate's centroid vanishes identically, even without height bounds. -/
theorem antiprism_centroid (a : ℝ) : ∑ i : Fin 8, X a i=0 := by
  ext j
  fin_cases j <;> simp [X,Fin.sum_univ_succ] <;> ring

/-- Explicit degree-two Gram identity for the centroid contribution.
These are the `(1,1)` entry of `R_0` and `(0,0)` entry of `R_1`. -/
theorem centroid_gram_identity (u v t : ℝ) :
    (2*(u*v+u*t+v*t)+(u^2+v^2+t^2+2*(u+v+t))/3+1/7 +
      (2*(u+v+t)-2*(u*v+u*t+v*t)+1-(u^2+v^2+t^2)/3))/8 =
        (u+v+t)/3+1/7 := by ring

#print axioms energy_minus_two_minimum
#print axioms antiprism_centroid
#print axioms centroid_gram_identity

#print axioms potential_decomposition
#print axioms energy_decomposition
#print axioms energy_le_of_auxEnergy_le

#print axioms negative_energy_le_iff
#print axioms pair_inner_centroid
end ThomsonNegative
