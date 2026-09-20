import Coulomb8.HermiteDegree
import Coulomb8.Potential
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Coprime.Lemmas

namespace Coulomb8

open Polynomial
open scoped BigOperators

noncomputable def squaredGap : Polynomial ℝ := 1-(C 2-C 2*X)*Hpoly^2
noncomputable def contactFactor : Polynomial ℝ :=
  (X+1)^5*∏ i : Fin 4, (X-C (nodes a i))^2

theorem double_root_dvd (p : Polynomial ℝ) (x : ℝ)
    (hp : p.eval x=0) (hd : p.derivative.eval x=0) : (X-C x)^2 ∣ p := by
  obtain ⟨r,hr⟩ := (dvd_iff_isRoot.mpr hp : X-C x ∣ p)
  have hrv : r.eval x=0 := by
    rw [hr] at hd
    simpa [derivative_mul] using hd
  obtain ⟨s,hs⟩ := (dvd_iff_isRoot.mpr hrv : X-C x ∣ r)
  refine ⟨s,?_⟩
  rw [hr,hs]
  ring

theorem contact_square_divides (i : Fin 4) : (X-C (nodes a i))^2 ∣ squaredGap := by
  have hv : Hpoly.eval (nodes a i)=phi (nodes a i) := H_contact i
  have hd : 2-2*nodes a i ≠ 0 := by linarith [(nodes_interior i).2]
  apply double_root_dvd
  · simp [squaredGap,hv,phi_square (nodes_interior i).2]
  · simp [squaredGap,derivative_mul,derivative_pow,hv,H_derivative_contact]
    have hd1 : 1-nodes a i ≠ 0 := by linarith [(nodes_interior i).2]
    field_simp [hd,hd1]
    <;> ring

noncomputable def taylor4Rat : Polynomial ℚ :=
  C (1/2)+C (1/8)*(X+1)+C (3/64)*(X+1)^2+C (5/256)*(X+1)^3+C (35/4096)*(X+1)^4
noncomputable def taylorQuotientRat : Polynomial ℚ :=
  C (63/4096)+C (105/32768)*(X+1)+C (135/131072)*(X+1)^2+
    C (1575/4194304)*(X+1)^3+C (1225/8388608)*(X+1)^4

theorem taylor_squared_identity :
    1-(C 2-C 2*X)*taylor4Rat^2=(X+1)^5*taylorQuotientRat := by
  apply Polynomial.funext
  intro x
  norm_num [taylor4Rat,taylorQuotientRat]
  <;> ring

theorem map_taylor4 : taylor4Rat.map (Rat.castHom ℝ)=taylor4 := by
  norm_num [taylor4Rat,taylor4]

theorem taylor_squared_divides : (X+1 : Polynomial ℝ)^5 ∣ 1-(C 2-C 2*X)*taylor4^2 := by
  refine ⟨taylorQuotientRat.map (Rat.castHom ℝ),?_⟩
  have h := congrArg (Polynomial.map (Rat.castHom ℝ)) taylor_squared_identity
  simpa [map_taylor4] using h

theorem endpoint_squared_divides : (X+1 : Polynomial ℝ)^5 ∣ squaredGap := by
  have hd : (X+1 : Polynomial ℝ)^5 ∣ squaredGap-(1-(C 2-C 2*X)*taylor4^2) := by
    refine ⟨-(C 2-C 2*X)*residualPolynomial*(Hpoly+taylor4),?_⟩
    unfold squaredGap Hpoly
    ring
  simpa using dvd_add hd taylor_squared_divides

theorem contactFactor_divides : contactFactor ∣ squaredGap := by
  have hc (i j : Fin 4) (hij : i ≠ j) :
      IsCoprime ((X-C (nodes a i))^2) ((X-C (nodes a j))^2) :=
    (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero_of_ne (nodes_injective.ne hij)).isUnit).pow
  have hprod : (∏ i : Fin 4, (X-C (nodes a i))^2) ∣ squaredGap :=
    Fintype.prod_dvd_of_coprime hc contact_square_divides
  have he (i : Fin 4) : IsCoprime ((X+1 : Polynomial ℝ)^5) ((X-C (nodes a i))^2) := by
    have hn : (-1 : ℝ)-nodes a i ≠ 0 := by linarith [(nodes_interior i).1]
    have h := (isCoprime_X_sub_C_of_isUnit_sub hn.isUnit).pow (m := 5) (n := 2)
    simpa using h
  exact (IsCoprime.prod_right (fun i _ => he i)).mul_dvd endpoint_squared_divides hprod

theorem contactFactor_monic : contactFactor.Monic := by
  unfold contactFactor
  simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one]
  monicity <;> norm_num

theorem contactFactor_degree : contactFactor.natDegree=13 := by
  unfold contactFactor
  simp only [Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one]
  compute_degree <;> norm_num

theorem squaredGap_degree : squaredGap.natDegree ≤ 25 := by
  have hl : (C 2-C 2*X : Polynomial ℝ).natDegree ≤ 1 := by compute_degree
  have hh : (Hpoly^2).natDegree ≤ 24 := natDegree_pow_le.trans (Nat.mul_le_mul_left 2 Hpoly_degree)
  have hp : ((C 2-C 2*X)*Hpoly^2).natDegree ≤ 25 := natDegree_mul_le.trans (Nat.add_le_add hl hh)
  exact (natDegree_sub_le _ _).trans (max_le (by simp) hp)

theorem squaredGap_ne_zero : squaredGap ≠ 0 := by
  intro h
  have hv := congrArg (Polynomial.eval 1) h
  norm_num [squaredGap] at hv

noncomputable def gapQuotient : Polynomial ℝ := Classical.choose contactFactor_divides
theorem squared_factorization : squaredGap=contactFactor*gapQuotient :=
  Classical.choose_spec contactFactor_divides

theorem gapQuotient_ne_zero : gapQuotient ≠ 0 := by
  intro h
  exact squaredGap_ne_zero (by simp [squared_factorization,h])

theorem gapQuotient_degree : gapQuotient.natDegree ≤ 12 := by
  have hd := natDegree_mul contactFactor_monic.ne_zero gapQuotient_ne_zero
  rw [←squared_factorization,contactFactor_degree] at hd
  have hp := squaredGap_degree
  omega

theorem contactFactor_eval (t : ℝ) :
    contactFactor.eval t=(t+1)^5*∏ i : Fin 4, (t-nodes a i)^2 := by
  simp [contactFactor,eval_prod]

end Coulomb8

#print axioms Coulomb8.squared_factorization
#print axioms Coulomb8.gapQuotient_degree
