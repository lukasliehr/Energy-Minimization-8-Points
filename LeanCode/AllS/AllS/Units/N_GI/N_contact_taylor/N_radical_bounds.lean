import AllS.Units.N_GI.N_contact_taylor.N_exact_expansion

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem contact_distinct (i j : Fin 8)
    (hc : inner ℝ (packingReference i) (packingReference j)=packingHeight) : i ≠ j := by
  intro he
  subst j
  rw [real_inner_self_eq_norm_sq,packingReference_norm] at hc
  have h := Blueprint.Thomson.Finite.packing_endpoint_bounds.2.1
  change packingHeight < 1/3 at h
  norm_num at hc
  linarith

theorem tangentVector_pair_norm_sq (q : TangentCoordinates) (i j : Fin 8) (hij : i ≠ j) :
    ‖tangentVector q i‖^2+‖tangentVector q j‖^2 ≤ ‖q‖^2 := by
  have hs : ∑ k ∈ ({i,j} : Finset (Fin 8)), ‖tangentVector q k‖^2 ≤
      ∑ k : Fin 8, ‖tangentVector q k‖^2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
  simpa [Finset.sum_pair hij,tangentVector_sum_norm_sq] using hs

theorem chartRoot_bounds (q : TangentCoordinates) (hq : ‖q‖ < 1) (i : Fin 8) :
    0 < √(1-‖q‖^2) ∧ √(1-‖q‖^2) ≤ chartRoot q i ∧ chartRoot q i ≤ 1 := by
  have hn := tangentVector_norm_le q i
  have hq0 := norm_nonneg q
  refine ⟨Real.sqrt_pos.mpr (by nlinarith),?_,?_⟩
  · apply Real.sqrt_le_sqrt
    nlinarith [norm_nonneg (tangentVector q i)]
  · have hs := chartRoot_sq q hq i
    have hp : 0 ≤ chartRoot q i := Real.sqrt_nonneg _
    nlinarith [sq_nonneg ‖tangentVector q i‖]

theorem chartRoot_rationalize (q : TangentCoordinates) (hq : ‖q‖ < 1) (i : Fin 8) :
    1-chartRoot q i=‖tangentVector q i‖^2/(1+chartRoot q i) := by
  have hp : 0 ≤ chartRoot q i := Real.sqrt_nonneg _
  apply (eq_div_iff (by positivity : 1+chartRoot q i ≠ 0)).mpr
  nlinarith [chartRoot_sq q hq i]

theorem chartRoot_difference (q : TangentCoordinates) (hq : ‖q‖ < 1) (i j : Fin 8) :
    |chartRoot q i-chartRoot q j| ≤
      |‖tangentVector q i‖^2-‖tangentVector q j‖^2|/(2*√(1-‖q‖^2)) := by
  obtain ⟨hp,hi,_⟩ := chartRoot_bounds q hq i
  obtain ⟨_,hj,_⟩ := chartRoot_bounds q hq j
  apply (le_div_iff₀ (by positivity)).mpr
  have he : |chartRoot q i-chartRoot q j| *(chartRoot q i+chartRoot q j)=
      |‖tangentVector q i‖^2-‖tangentVector q j‖^2| := by
    rw [← abs_of_nonneg (by linarith : 0 ≤ chartRoot q i+chartRoot q j),← abs_mul]
    have hh : (chartRoot q i-chartRoot q j)*(chartRoot q i+chartRoot q j)=
        -(‖tangentVector q i‖^2-‖tangentVector q j‖^2) := by
      nlinarith [chartRoot_sq q hq i,chartRoot_sq q hq j]
    rw [hh,abs_neg]
  nlinarith [abs_nonneg (chartRoot q i-chartRoot q j)]

theorem contact_inner_bound (q : TangentCoordinates) (i j : Fin 8)
    (hc : inner ℝ (packingReference i) (packingReference j)=packingHeight) :
    |inner ℝ (packingReference i) (tangentVector q j)| ≤
      √(1-packingHeight^2)*‖tangentVector q j‖ := by
  have hz : inner ℝ (packingReference j) (tangentVector q j)=0 := by
    rw [real_inner_comm]; exact tangentVector_orthogonal q j
  have he : inner ℝ (packingReference i-packingHeight • packingReference j) (tangentVector q j)=
      inner ℝ (packingReference i) (tangentVector q j) := by
    simp [inner_sub_left,inner_smul_left,hz]
  have hn : ‖packingReference i-packingHeight • packingReference j‖^2=1-packingHeight^2 := by
    rw [norm_sub_sq_real,norm_smul,packingReference_norm,packingReference_norm,
      real_inner_smul_right,hc,Real.norm_eq_abs,mul_one,sq_abs]
    ring
  have hnorm : ‖packingReference i-packingHeight • packingReference j‖=√(1-packingHeight^2) := by
    rw [← hn,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]
  have h := abs_real_inner_le_norm (packingReference i-packingHeight • packingReference j) (tangentVector q j)
  rwa [he,hnorm] at h

theorem contact_taylor_radical_bounds (q : TangentCoordinates) (hq : ‖q‖ ≤ 3/10)
    (i j : Fin 8) (hc : inner ℝ (packingReference i) (packingReference j)=packingHeight) :
    (1-chartRoot q i=‖tangentVector q i‖^2/(1+chartRoot q i)) ∧
    (|chartRoot q i-chartRoot q j| ≤
      |‖tangentVector q i‖^2-‖tangentVector q j‖^2|/(2*√(1-‖q‖^2))) ∧
    |inner ℝ (packingReference i) (tangentVector q j)| ≤
      √(1-packingHeight^2)*‖tangentVector q j‖ := by
  have hq1 : ‖q‖ < 1 := by linarith
  exact ⟨chartRoot_rationalize q hq1 i,chartRoot_difference q hq1 i j,contact_inner_bound q i j hc⟩

#check contact_taylor_radical_bounds
#print axioms contact_taylor_radical_bounds
end Blueprint.Thomson.Tail.Implementation
