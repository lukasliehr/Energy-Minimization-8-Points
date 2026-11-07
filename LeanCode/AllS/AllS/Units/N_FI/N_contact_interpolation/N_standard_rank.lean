import AllS.Units.N_FI.N_contact_interpolation.N_orbit_sigma

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

def standardP (x : Fin 3 → ℝ) (i : Fin 3) : ℝ := x i-(∑ j, x j)/3

def standardQ (x : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  standardP x i^2-(∑ j, standardP x j^2)/3

def standardContactPoint (a : ℝ) (r : Fin 5) : Fin 3 → ℝ :=
  contactTripleEval a (contactRepresentative r)

def regularOrbit : Fin 2 → Fin 5 := ![3,4]

def repeatedLambda (a : ℝ) : Fin 3 → ℝ :=
  ![(a-1)/3,a/2-contactSigma a 1/6,a/2-contactSigma a 2/6]

def StandardRankContract : Prop := ∀ a : ℝ, physical a →
  (∀ r : Fin 2, ∀ c d : ℝ,
    (∀ i, c*standardP (standardContactPoint a (regularOrbit r)) i+
      d*standardQ (standardContactPoint a (regularOrbit r)) i = 0) → c=0 ∧ d=0) ∧
  (∀ r : Fin 3, standardQ (standardContactPoint a (Fin.castAdd 2 r)) =
    repeatedLambda a r • standardP (standardContactPoint a (Fin.castAdd 2 r)))

def standardVandermonde (x : Fin 3 → ℝ) : ℝ := (x 0-x 1)*(x 0-x 2)*(x 1-x 2)

theorem standardP_sum (x : Fin 3 → ℝ) : ∑ i, standardP x i = 0 := by
  simp [standardP,Fin.sum_univ_succ]
  ring

theorem standardQ_sum (x : Fin 3 → ℝ) : ∑ i, standardQ x i = 0 := by
  simp [standardQ,Fin.sum_univ_succ]
  ring

theorem standard_gram_det (x : Fin 3 → ℝ) :
    (∑ i, standardP x i^2)*(∑ i, standardQ x i^2) -
      (∑ i, standardP x i*standardQ x i)^2 = standardVandermonde x^2/3 := by
  simp [standardP,standardQ,standardVandermonde,Fin.sum_univ_succ]
  ring

theorem standard_independent (x : Fin 3 → ℝ) (hx : standardVandermonde x ≠ 0)
    (c d : ℝ) (h : ∀ i, c*standardP x i+d*standardQ x i=0) : c=0 ∧ d=0 := by
  have hp : c*(∑ i,standardP x i^2)+d*(∑ i,standardP x i*standardQ x i)=0 := by
    calc
      _ = ∑ i, standardP x i*(c*standardP x i+d*standardQ x i) := by
        simp only [Finset.mul_sum,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by simp [h]
  have hq : c*(∑ i,standardP x i*standardQ x i)+d*(∑ i,standardQ x i^2)=0 := by
    calc
      _ = ∑ i, standardQ x i*(c*standardP x i+d*standardQ x i) := by
        simp only [Finset.mul_sum,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = 0 := by simp [h]
  have hc : c*((∑ i,standardP x i^2)*(∑ i,standardQ x i^2)-
      (∑ i,standardP x i*standardQ x i)^2)=0 := by
    linear_combination (∑ i,standardQ x i^2)*hp-(∑ i,standardP x i*standardQ x i)*hq
  have hd : d*((∑ i,standardP x i^2)*(∑ i,standardQ x i^2)-
      (∑ i,standardP x i*standardQ x i)^2)=0 := by
    linear_combination (∑ i,standardP x i^2)*hq-(∑ i,standardP x i*standardQ x i)*hp
  rw [standard_gram_det] at hc hd
  have hdet : standardVandermonde x^2/3 ≠ 0 := div_ne_zero (pow_ne_zero 2 hx) (by norm_num)
  exact ⟨(mul_eq_zero.mp hc).resolve_right hdet,(mul_eq_zero.mp hd).resolve_right hdet⟩

theorem regular_vandermonde_ne (a : ℝ) (ha : physical a) (r : Fin 2) :
    standardVandermonde (standardContactPoint a (regularOrbit r)) ≠ 0 := by
  have hinj := contacts_injective a ha
  fin_cases r
  · change (contacts a 0-contacts a 2)*(contacts a 0-contacts a 3)*
      (contacts a 2-contacts a 3) ≠ 0
    exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (hinj.ne (by decide)))
      (sub_ne_zero.mpr (hinj.ne (by decide)))) (sub_ne_zero.mpr (hinj.ne (by decide)))
  · change (contacts a 1-contacts a 2)*(contacts a 1-contacts a 3)*
      (contacts a 2-contacts a 3) ≠ 0
    exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (hinj.ne (by decide)))
      (sub_ne_zero.mpr (hinj.ne (by decide)))) (sub_ne_zero.mpr (hinj.ne (by decide)))

theorem standard_repeated_lambda (a : ℝ) (r : Fin 3) :
    standardQ (standardContactPoint a (Fin.castAdd 2 r)) =
      repeatedLambda a r • standardP (standardContactPoint a (Fin.castAdd 2 r)) := by
  funext i
  fin_cases r <;> fin_cases i <;>
    norm_num [standardQ,standardP,standardContactPoint,contactTripleEval,contactRepresentative,
      repeatedLambda,contactSigma,contacts,Fin.sum_univ_succ]
  all_goals try dsimp
  all_goals ring

theorem contact_interpolation_standard_rank : StandardRankContract := by
  intro a ha
  refine ⟨?_,standard_repeated_lambda a⟩
  intro r c d h
  exact standard_independent _ (regular_vandermonde_ne a ha r) c d h

#check contact_interpolation_standard_rank
#print axioms contact_interpolation_standard_rank
#check StandardRankContract
#print axioms StandardRankContract
end Blueprint.Thomson.Finite
