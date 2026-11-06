import AllS.Units.N_GI.N_polar_tetrahedra.N_matched_strict

set_option maxHeartbeats 700000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem cube_cross_inner_sum (A B : Fin 4 → Point) (c : ℝ)
    (hcross : ∀i j,i≠j → inner ℝ (A i) (B j)=c) (w : Fin 4 → ℝ) (j : Fin 4) :
    inner ℝ (∑i,w i • A i) (B j)=c*(∑i,w i)+(inner ℝ (A j) (B j)-c)*w j := by
  rw [sum_inner]
  simp only [inner_smul_left,conj_trivial]
  calc
    ∑i,w i*inner ℝ (A i) (B j) =
        ∑i,(c*w i+if i=j then (inner ℝ (A j) (B j)-c)*w j else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hij : i=j
      · subst i;simp only [eq_self_iff_true,ite_true];ring
      · rw [hcross i j hij,if_neg hij];ring
    _ = _ := by simp [Finset.sum_add_distrib,←Finset.mul_sum]

theorem cube_normalized_relation_unique (A B : Fin 4 → Point) (c : ℝ)
    (hcross : ∀i j,i≠j → inner ℝ (A i) (B j)=c)
    (hstrict : ∀i,inner ℝ (A i) (B i)<c) (w : Fin 4 → ℝ)
    (hsum : ∑i,w i=1) (hzero : ∑i,w i • A i=0) :
    ∀i,w i=c/(c-inner ℝ (A i) (B i)) := by
  intro i
  have hh := cube_cross_inner_sum A B c hcross w i
  rw [hzero,inner_zero_left,hsum,mul_one] at hh
  apply (eq_div_iff (sub_pos.mpr (hstrict i)).ne').mpr
  nlinarith

theorem polar_tetrahedra_positive_relation (A B : Fin 4 → Point) (c : ℝ)
    (hunit : ∀i,‖A i‖=1) (hAinj : Function.Injective A) (hBinj : Function.Injective B)
    (hc : 0<c) (hcross : ∀i j,i≠j → inner ℝ (A i) (B j)=c)
    (hmatched : ∀i,inner ℝ (A i) (B i)≤c) :
    ∃w : Fin 4 → ℝ,(∀i,0<w i) ∧ (∑i,w i=1) ∧ (∑i,w i • A i=0) ∧
      ∀i,w i=c/(c-inner ℝ (A i) (B i)) := by
  have hstrict := polar_tetrahedra_matched_strict A B c hunit hAinj hBinj hc hcross hmatched
  have hnot : ¬LinearIndependent ℝ A := by
    intro hLI
    have hh := hLI.fintype_card_le_finrank
    norm_num [Point] at hh
  obtain ⟨u,hu,j,huj⟩ := Fintype.not_linearIndependent_iff.mp hnot
  let S := ∑i,u i
  have hS : S≠0 := by
    intro hzero
    have hh := cube_cross_inner_sum A B c hcross u j
    rw [hu,inner_zero_left] at hh
    change 0=c*S+(inner ℝ (A j) (B j)-c)*u j at hh
    rw [hzero,mul_zero,zero_add] at hh
    have hprod : (inner ℝ (A j) (B j)-c)*u j=0 := hh.symm
    exact huj ((mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr (hstrict j).ne))
  let w : Fin 4 → ℝ := fun i => u i/S
  have hsum : ∑i,w i=1 := by
    change (∑i,u i/S)=1
    rw [←Finset.sum_div]
    exact div_self hS
  have hzero : ∑i,w i • A i=0 := by
    calc
      ∑i,w i • A i = ∑i,S⁻¹ • (u i • A i) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [w,div_eq_mul_inv,smul_smul,mul_comm]
      _ = S⁻¹ • (∑i,u i • A i) := Finset.smul_sum.symm
      _ = 0 := by rw [hu,smul_zero]
  have hformula := cube_normalized_relation_unique A B c hcross hstrict w hsum hzero
  exact ⟨w,fun i => (hformula i).symm ▸ div_pos hc (sub_pos.mpr (hstrict i)),hsum,hzero,hformula⟩

#print axioms cube_cross_inner_sum
#print axioms cube_normalized_relation_unique
#print axioms polar_tetrahedra_positive_relation
end Blueprint.Thomson.Tail.Implementation
