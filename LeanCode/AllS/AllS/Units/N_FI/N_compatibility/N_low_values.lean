import AllS.Units.N_FI.N_compatibility.N_family_functionals

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem finite_sum_fin8 {R : Type*} [AddCommMonoid R] (f : Fin 8 → R) :
    (∑ i,f i)=f 0+(f 1+(f 2+(f 3+(f 4+(f 5+(f 6+f 7)))))) := by
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  rfl

/-- The finite contact label enumeration, with arbitrary values for all four labels. -/
theorem candidate_labels_sigma_square {R : Type*} [CommRing R] (c : Fin 4 → R) :
    (∑ i : Fin 8,∑ j : Fin 8,∑ k : Fin 8,
      if i≠j ∧ j≠k ∧ k≠i then
        (c (candidateContactLabel i j)+c (candidateContactLabel i k)+c (candidateContactLabel j k))^2 else 0)=
      48*(2*c 0+c 1)^2+48*(c 0+2*c 2)^2+48*(c 0+2*c 3)^2+
        96*(c 0+c 2+c 3)^2+96*(c 1+c 2+c 3)^2 := by
  have hr (i : Fin 8) : (∑ j : Fin 8,∑ k : Fin 8,
      if i≠j ∧ j≠k ∧ k≠i then
        (c (candidateContactLabel i j)+c (candidateContactLabel i k)+c (candidateContactLabel j k))^2 else 0)=
      6*(2*c 0+c 1)^2+6*(c 0+2*c 2)^2+6*(c 0+2*c 3)^2+
        12*(c 0+c 2+c 3)^2+12*(c 1+c 2+c 3)^2 := by
    fin_cases i <;> simp only [(show (⟨0,by decide⟩ : Fin 8)=0 from rfl),
      (show (⟨1,by decide⟩ : Fin 8)=1 from rfl),
      (show (⟨2,by decide⟩ : Fin 8)=2 from rfl),
      (show (⟨3,by decide⟩ : Fin 8)=3 from rfl),
      (show (⟨4,by decide⟩ : Fin 8)=4 from rfl),
      (show (⟨5,by decide⟩ : Fin 8)=5 from rfl),
      (show (⟨6,by decide⟩ : Fin 8)=6 from rfl),
      (show (⟨7,by decide⟩ : Fin 8)=7 from rfl),
      finite_sum_fin8,
      (show candidateContactLabel 0 0=0 from by decide),
      (show candidateContactLabel 0 1=0 from by decide),
      (show (¬(0 : Fin 8)=1) from by decide),
      (show candidateContactLabel 0 2=1 from by decide),
      (show (¬(0 : Fin 8)=2) from by decide),
      (show candidateContactLabel 0 3=0 from by decide),
      (show (¬(0 : Fin 8)=3) from by decide),
      (show candidateContactLabel 0 4=2 from by decide),
      (show (¬(0 : Fin 8)=4) from by decide),
      (show candidateContactLabel 0 5=3 from by decide),
      (show (¬(0 : Fin 8)=5) from by decide),
      (show candidateContactLabel 0 6=3 from by decide),
      (show (¬(0 : Fin 8)=6) from by decide),
      (show candidateContactLabel 0 7=2 from by decide),
      (show (¬(0 : Fin 8)=7) from by decide),
      (show candidateContactLabel 1 0=0 from by decide),
      (show (¬(1 : Fin 8)=0) from by decide),
      (show candidateContactLabel 1 1=0 from by decide),
      (show candidateContactLabel 1 2=0 from by decide),
      (show (¬(1 : Fin 8)=2) from by decide),
      (show candidateContactLabel 1 3=1 from by decide),
      (show (¬(1 : Fin 8)=3) from by decide),
      (show candidateContactLabel 1 4=2 from by decide),
      (show (¬(1 : Fin 8)=4) from by decide),
      (show candidateContactLabel 1 5=2 from by decide),
      (show (¬(1 : Fin 8)=5) from by decide),
      (show candidateContactLabel 1 6=3 from by decide),
      (show (¬(1 : Fin 8)=6) from by decide),
      (show candidateContactLabel 1 7=3 from by decide),
      (show (¬(1 : Fin 8)=7) from by decide),
      (show candidateContactLabel 2 0=1 from by decide),
      (show (¬(2 : Fin 8)=0) from by decide),
      (show candidateContactLabel 2 1=0 from by decide),
      (show (¬(2 : Fin 8)=1) from by decide),
      (show candidateContactLabel 2 2=0 from by decide),
      (show candidateContactLabel 2 3=0 from by decide),
      (show (¬(2 : Fin 8)=3) from by decide),
      (show candidateContactLabel 2 4=3 from by decide),
      (show (¬(2 : Fin 8)=4) from by decide),
      (show candidateContactLabel 2 5=2 from by decide),
      (show (¬(2 : Fin 8)=5) from by decide),
      (show candidateContactLabel 2 6=2 from by decide),
      (show (¬(2 : Fin 8)=6) from by decide),
      (show candidateContactLabel 2 7=3 from by decide),
      (show (¬(2 : Fin 8)=7) from by decide),
      (show candidateContactLabel 3 0=0 from by decide),
      (show (¬(3 : Fin 8)=0) from by decide),
      (show candidateContactLabel 3 1=1 from by decide),
      (show (¬(3 : Fin 8)=1) from by decide),
      (show candidateContactLabel 3 2=0 from by decide),
      (show (¬(3 : Fin 8)=2) from by decide),
      (show candidateContactLabel 3 3=0 from by decide),
      (show candidateContactLabel 3 4=3 from by decide),
      (show (¬(3 : Fin 8)=4) from by decide),
      (show candidateContactLabel 3 5=3 from by decide),
      (show (¬(3 : Fin 8)=5) from by decide),
      (show candidateContactLabel 3 6=2 from by decide),
      (show (¬(3 : Fin 8)=6) from by decide),
      (show candidateContactLabel 3 7=2 from by decide),
      (show (¬(3 : Fin 8)=7) from by decide),
      (show candidateContactLabel 4 0=2 from by decide),
      (show (¬(4 : Fin 8)=0) from by decide),
      (show candidateContactLabel 4 1=2 from by decide),
      (show (¬(4 : Fin 8)=1) from by decide),
      (show candidateContactLabel 4 2=3 from by decide),
      (show (¬(4 : Fin 8)=2) from by decide),
      (show candidateContactLabel 4 3=3 from by decide),
      (show (¬(4 : Fin 8)=3) from by decide),
      (show candidateContactLabel 4 4=0 from by decide),
      (show candidateContactLabel 4 5=0 from by decide),
      (show (¬(4 : Fin 8)=5) from by decide),
      (show candidateContactLabel 4 6=1 from by decide),
      (show (¬(4 : Fin 8)=6) from by decide),
      (show candidateContactLabel 4 7=0 from by decide),
      (show (¬(4 : Fin 8)=7) from by decide),
      (show candidateContactLabel 5 0=3 from by decide),
      (show (¬(5 : Fin 8)=0) from by decide),
      (show candidateContactLabel 5 1=2 from by decide),
      (show (¬(5 : Fin 8)=1) from by decide),
      (show candidateContactLabel 5 2=2 from by decide),
      (show (¬(5 : Fin 8)=2) from by decide),
      (show candidateContactLabel 5 3=3 from by decide),
      (show (¬(5 : Fin 8)=3) from by decide),
      (show candidateContactLabel 5 4=0 from by decide),
      (show (¬(5 : Fin 8)=4) from by decide),
      (show candidateContactLabel 5 5=0 from by decide),
      (show candidateContactLabel 5 6=0 from by decide),
      (show (¬(5 : Fin 8)=6) from by decide),
      (show candidateContactLabel 5 7=1 from by decide),
      (show (¬(5 : Fin 8)=7) from by decide),
      (show candidateContactLabel 6 0=3 from by decide),
      (show (¬(6 : Fin 8)=0) from by decide),
      (show candidateContactLabel 6 1=3 from by decide),
      (show (¬(6 : Fin 8)=1) from by decide),
      (show candidateContactLabel 6 2=2 from by decide),
      (show (¬(6 : Fin 8)=2) from by decide),
      (show candidateContactLabel 6 3=2 from by decide),
      (show (¬(6 : Fin 8)=3) from by decide),
      (show candidateContactLabel 6 4=1 from by decide),
      (show (¬(6 : Fin 8)=4) from by decide),
      (show candidateContactLabel 6 5=0 from by decide),
      (show (¬(6 : Fin 8)=5) from by decide),
      (show candidateContactLabel 6 6=0 from by decide),
      (show candidateContactLabel 6 7=0 from by decide),
      (show (¬(6 : Fin 8)=7) from by decide),
      (show candidateContactLabel 7 0=2 from by decide),
      (show (¬(7 : Fin 8)=0) from by decide),
      (show candidateContactLabel 7 1=3 from by decide),
      (show (¬(7 : Fin 8)=1) from by decide),
      (show candidateContactLabel 7 2=3 from by decide),
      (show (¬(7 : Fin 8)=2) from by decide),
      (show candidateContactLabel 7 3=2 from by decide),
      (show (¬(7 : Fin 8)=3) from by decide),
      (show candidateContactLabel 7 4=0 from by decide),
      (show (¬(7 : Fin 8)=4) from by decide),
      (show candidateContactLabel 7 5=1 from by decide),
      (show (¬(7 : Fin 8)=5) from by decide),
      (show candidateContactLabel 7 6=0 from by decide),
      (show (¬(7 : Fin 8)=6) from by decide),
      (show candidateContactLabel 7 7=0 from by decide),
      ne_eq,not_false_eq_true,not_true_eq_false,and_true,and_false,false_and,true_and,ite_true,ite_false,add_zero,zero_add] <;> ring
  simp_rw [hr]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

/-- The finite contact label enumeration, with arbitrary values for all four labels. -/
theorem candidate_labels_coordinate_sum {R : Type*} [CommRing R] (c : Fin 4 → R) :
    (∑ i : Fin 8,∑ j : Fin 8,∑ k : Fin 8,
      if i≠j ∧ j≠k ∧ k≠i then
        (c (candidateContactLabel i j)+c (candidateContactLabel i k)+c (candidateContactLabel j k)) else 0)=
      288*c 0+144*c 1+288*c 2+288*c 3 := by
  have hr (i : Fin 8) : (∑ j : Fin 8,∑ k : Fin 8,
      if i≠j ∧ j≠k ∧ k≠i then
        (c (candidateContactLabel i j)+c (candidateContactLabel i k)+c (candidateContactLabel j k)) else 0)=
      36*c 0+18*c 1+36*c 2+36*c 3 := by
    fin_cases i <;> simp only [(show (⟨0,by decide⟩ : Fin 8)=0 from rfl),
      (show (⟨1,by decide⟩ : Fin 8)=1 from rfl),
      (show (⟨2,by decide⟩ : Fin 8)=2 from rfl),
      (show (⟨3,by decide⟩ : Fin 8)=3 from rfl),
      (show (⟨4,by decide⟩ : Fin 8)=4 from rfl),
      (show (⟨5,by decide⟩ : Fin 8)=5 from rfl),
      (show (⟨6,by decide⟩ : Fin 8)=6 from rfl),
      (show (⟨7,by decide⟩ : Fin 8)=7 from rfl),
      finite_sum_fin8,
      (show candidateContactLabel 0 0=0 from by decide),
      (show candidateContactLabel 0 1=0 from by decide),
      (show (¬(0 : Fin 8)=1) from by decide),
      (show candidateContactLabel 0 2=1 from by decide),
      (show (¬(0 : Fin 8)=2) from by decide),
      (show candidateContactLabel 0 3=0 from by decide),
      (show (¬(0 : Fin 8)=3) from by decide),
      (show candidateContactLabel 0 4=2 from by decide),
      (show (¬(0 : Fin 8)=4) from by decide),
      (show candidateContactLabel 0 5=3 from by decide),
      (show (¬(0 : Fin 8)=5) from by decide),
      (show candidateContactLabel 0 6=3 from by decide),
      (show (¬(0 : Fin 8)=6) from by decide),
      (show candidateContactLabel 0 7=2 from by decide),
      (show (¬(0 : Fin 8)=7) from by decide),
      (show candidateContactLabel 1 0=0 from by decide),
      (show (¬(1 : Fin 8)=0) from by decide),
      (show candidateContactLabel 1 1=0 from by decide),
      (show candidateContactLabel 1 2=0 from by decide),
      (show (¬(1 : Fin 8)=2) from by decide),
      (show candidateContactLabel 1 3=1 from by decide),
      (show (¬(1 : Fin 8)=3) from by decide),
      (show candidateContactLabel 1 4=2 from by decide),
      (show (¬(1 : Fin 8)=4) from by decide),
      (show candidateContactLabel 1 5=2 from by decide),
      (show (¬(1 : Fin 8)=5) from by decide),
      (show candidateContactLabel 1 6=3 from by decide),
      (show (¬(1 : Fin 8)=6) from by decide),
      (show candidateContactLabel 1 7=3 from by decide),
      (show (¬(1 : Fin 8)=7) from by decide),
      (show candidateContactLabel 2 0=1 from by decide),
      (show (¬(2 : Fin 8)=0) from by decide),
      (show candidateContactLabel 2 1=0 from by decide),
      (show (¬(2 : Fin 8)=1) from by decide),
      (show candidateContactLabel 2 2=0 from by decide),
      (show candidateContactLabel 2 3=0 from by decide),
      (show (¬(2 : Fin 8)=3) from by decide),
      (show candidateContactLabel 2 4=3 from by decide),
      (show (¬(2 : Fin 8)=4) from by decide),
      (show candidateContactLabel 2 5=2 from by decide),
      (show (¬(2 : Fin 8)=5) from by decide),
      (show candidateContactLabel 2 6=2 from by decide),
      (show (¬(2 : Fin 8)=6) from by decide),
      (show candidateContactLabel 2 7=3 from by decide),
      (show (¬(2 : Fin 8)=7) from by decide),
      (show candidateContactLabel 3 0=0 from by decide),
      (show (¬(3 : Fin 8)=0) from by decide),
      (show candidateContactLabel 3 1=1 from by decide),
      (show (¬(3 : Fin 8)=1) from by decide),
      (show candidateContactLabel 3 2=0 from by decide),
      (show (¬(3 : Fin 8)=2) from by decide),
      (show candidateContactLabel 3 3=0 from by decide),
      (show candidateContactLabel 3 4=3 from by decide),
      (show (¬(3 : Fin 8)=4) from by decide),
      (show candidateContactLabel 3 5=3 from by decide),
      (show (¬(3 : Fin 8)=5) from by decide),
      (show candidateContactLabel 3 6=2 from by decide),
      (show (¬(3 : Fin 8)=6) from by decide),
      (show candidateContactLabel 3 7=2 from by decide),
      (show (¬(3 : Fin 8)=7) from by decide),
      (show candidateContactLabel 4 0=2 from by decide),
      (show (¬(4 : Fin 8)=0) from by decide),
      (show candidateContactLabel 4 1=2 from by decide),
      (show (¬(4 : Fin 8)=1) from by decide),
      (show candidateContactLabel 4 2=3 from by decide),
      (show (¬(4 : Fin 8)=2) from by decide),
      (show candidateContactLabel 4 3=3 from by decide),
      (show (¬(4 : Fin 8)=3) from by decide),
      (show candidateContactLabel 4 4=0 from by decide),
      (show candidateContactLabel 4 5=0 from by decide),
      (show (¬(4 : Fin 8)=5) from by decide),
      (show candidateContactLabel 4 6=1 from by decide),
      (show (¬(4 : Fin 8)=6) from by decide),
      (show candidateContactLabel 4 7=0 from by decide),
      (show (¬(4 : Fin 8)=7) from by decide),
      (show candidateContactLabel 5 0=3 from by decide),
      (show (¬(5 : Fin 8)=0) from by decide),
      (show candidateContactLabel 5 1=2 from by decide),
      (show (¬(5 : Fin 8)=1) from by decide),
      (show candidateContactLabel 5 2=2 from by decide),
      (show (¬(5 : Fin 8)=2) from by decide),
      (show candidateContactLabel 5 3=3 from by decide),
      (show (¬(5 : Fin 8)=3) from by decide),
      (show candidateContactLabel 5 4=0 from by decide),
      (show (¬(5 : Fin 8)=4) from by decide),
      (show candidateContactLabel 5 5=0 from by decide),
      (show candidateContactLabel 5 6=0 from by decide),
      (show (¬(5 : Fin 8)=6) from by decide),
      (show candidateContactLabel 5 7=1 from by decide),
      (show (¬(5 : Fin 8)=7) from by decide),
      (show candidateContactLabel 6 0=3 from by decide),
      (show (¬(6 : Fin 8)=0) from by decide),
      (show candidateContactLabel 6 1=3 from by decide),
      (show (¬(6 : Fin 8)=1) from by decide),
      (show candidateContactLabel 6 2=2 from by decide),
      (show (¬(6 : Fin 8)=2) from by decide),
      (show candidateContactLabel 6 3=2 from by decide),
      (show (¬(6 : Fin 8)=3) from by decide),
      (show candidateContactLabel 6 4=1 from by decide),
      (show (¬(6 : Fin 8)=4) from by decide),
      (show candidateContactLabel 6 5=0 from by decide),
      (show (¬(6 : Fin 8)=5) from by decide),
      (show candidateContactLabel 6 6=0 from by decide),
      (show candidateContactLabel 6 7=0 from by decide),
      (show (¬(6 : Fin 8)=7) from by decide),
      (show candidateContactLabel 7 0=2 from by decide),
      (show (¬(7 : Fin 8)=0) from by decide),
      (show candidateContactLabel 7 1=3 from by decide),
      (show (¬(7 : Fin 8)=1) from by decide),
      (show candidateContactLabel 7 2=3 from by decide),
      (show (¬(7 : Fin 8)=2) from by decide),
      (show candidateContactLabel 7 3=2 from by decide),
      (show (¬(7 : Fin 8)=3) from by decide),
      (show candidateContactLabel 7 4=0 from by decide),
      (show (¬(7 : Fin 8)=4) from by decide),
      (show candidateContactLabel 7 5=1 from by decide),
      (show (¬(7 : Fin 8)=5) from by decide),
      (show candidateContactLabel 7 6=0 from by decide),
      (show (¬(7 : Fin 8)=6) from by decide),
      (show candidateContactLabel 7 7=0 from by decide),
      ne_eq,not_false_eq_true,not_true_eq_false,and_true,and_false,false_and,true_and,ite_true,ite_false,add_zero,zero_add] <;> ring
  simp_rw [hr]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

theorem candidateFamilyMap_one : candidateFamilyMap (1 : Poly3)=336 := by
  rw [candidateFamilyMap_apply]
  simp only [map_one]
  have h : (∑ i : Fin 8,∑ j : Fin 8,∑ k : Fin 8,
      if i≠j ∧ j≠k ∧ k≠i then (1 : ℕ) else 0)=336 := by decide
  exact_mod_cast h

theorem candidateFamilyMap_sigma_square :
    candidateFamilyMap (sigma^2)=1152*Polynomial.X^2-768*Polynomial.X+336 := by
  rw [candidateFamilyMap_apply]
  have ht (i j k : Fin 8) : candidateTripleSubst i j k (sigma^2)=
      (contactPolynomial (candidateContactLabel i j)+contactPolynomial (candidateContactLabel i k)+
        contactPolynomial (candidateContactLabel j k))^2 := by simp [candidateTripleSubst,sigma]
  simp_rw [ht]
  rw [candidate_labels_sigma_square]
  simp only [contactPolynomial,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_neg,Polynomial.eval_one]
  have hq : (1/Real.sqrt 2)^2=(1/2 : ℝ) := by norm_num [div_pow,Real.sq_sqrt]
  linear_combination (384*x^2-768*x+384)*hq

def coordinateSquareSum : Poly3 :=
  (MvPolynomial.X 0)^2+(MvPolynomial.X 1)^2+(MvPolynomial.X 2)^2

theorem candidateFamilyMap_coordinate_square :
    candidateFamilyMap coordinateSquareSum=1728*Polynomial.X^2-1152*Polynomial.X+432 := by
  rw [candidateFamilyMap_apply]
  have ht (i j k : Fin 8) : candidateTripleSubst i j k coordinateSquareSum=
      (contactPolynomial (candidateContactLabel i j))^2+(contactPolynomial (candidateContactLabel i k))^2+
        (contactPolynomial (candidateContactLabel j k))^2 := by
    simp [candidateTripleSubst,coordinateSquareSum]
  simp_rw [ht]
  rw [candidate_labels_coordinate_sum (fun r => (contactPolynomial r)^2)]
  apply Polynomial.funext
  intro x
  simp only [contactPolynomial,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons,Polynomial.eval_add,Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_neg,Polynomial.eval_one]
  have hq : (1/Real.sqrt 2)^2=(1/2 : ℝ) := by norm_num [div_pow,Real.sq_sqrt]
  linear_combination (576*(1-x)^2)*hq

def LowValuesContract : Prop := ∀ a : ℝ,physical a →
  ell0 a 1=56 ∧ ell1 a 1=0 ∧
  ell0 a (sigma^2)=192*a^2-128*a+56 ∧ ell1 a (sigma^2)=128*(3*a-1) ∧
  ell1 a (sigma^2)≠0 ∧
  L1 a ((MvPolynomial.X 0)^2+(MvPolynomial.X 1)^2+(MvPolynomial.X 2)^2)=1152*(3*a-1)

theorem low_L0_one (a : ℝ) : L0 a 1=336 := by simp [L0,candidateFamilyMap_one]
theorem low_L1_one (a : ℝ) : L1 a 1=0 := by simp [L1,candidateFamilyMap_one]
theorem low_L0_sigma_square (a : ℝ) : L0 a (sigma^2)=1152*a^2-768*a+336 := by
  simp [L0,candidateFamilyMap_sigma_square]
theorem low_L1_sigma_square (a : ℝ) : L1 a (sigma^2)=768*(3*a-1) := by
  simp [L1,candidateFamilyMap_sigma_square]
  ring
theorem low_L1_coordinate_square (a : ℝ) : L1 a coordinateSquareSum=1152*(3*a-1) := by
  simp [L1,candidateFamilyMap_coordinate_square]
  ring

theorem compatibility_low_values : LowValuesContract := by
  intro a ha
  have hne : 128*(3*a-1)≠0 := by nlinarith [ha.2]
  have he0 : ell0 a 1=56 := by simp [ell0,low_L0_one];norm_num
  have he1 : ell1 a 1=0 := by simp [ell1,low_L1_one]
  have hes0 : ell0 a (sigma^2)=192*a^2-128*a+56 := by
    simp only [ell0,LinearMap.smul_apply,smul_eq_mul,low_L0_sigma_square]
    ring
  have hes1 : ell1 a (sigma^2)=128*(3*a-1) := by
    simp only [ell1,LinearMap.smul_apply,smul_eq_mul,low_L1_sigma_square]
    ring
  exact ⟨he0,he1,hes0,hes1,hes1 ▸ hne,low_L1_coordinate_square a⟩

#check compatibility_low_values
#print axioms compatibility_low_values
end Blueprint.Thomson.Finite
