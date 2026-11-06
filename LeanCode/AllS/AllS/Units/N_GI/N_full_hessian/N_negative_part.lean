import AllS.Units.N_GI.N_full_hessian.N_exact_hessian

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem unordered_incident_weight_sum (f : Fin 8→Fin 8→ℝ) (hf : ∀ i j, f i j=f j i) (u : Fin 8→ℝ) :
    (∑ ij∈unorderedPairs, f ij.1 ij.2*(u ij.1+u ij.2))=
      ∑ i : Fin 8, u i*(∑ j∈Finset.univ.erase i, f i j) := by
  have he (i : Fin 8) : (∑ j∈Finset.univ.erase i, f i j)=(∑ j : Fin 8, f i j)-f i i :=
    Finset.sum_erase_eq_sub (Finset.mem_univ i)
  simp_rw [he]
  norm_num [unorderedPairs,Finset.sum_filter,Fintype.sum_prod_type,Fin.sum_univ_succ,Fin.succ,Fin.instOfNat,Fin.ofNat]
  dsimp
  simp only [hf]
  ring

theorem full_hessian_negative_part (p : ℝ) (hp : (97:ℝ)/2≤p) (q ξ : TangentCoordinates)
    (hq : q∈convexTailDomain p) :
    tau*hessianNegativeSum p q ξ≤((248:ℝ)/15)*tau*‖ξ‖^2 := by
  let f : Fin 8→Fin 8→ℝ := fun i j=>(tau/squaredDistance (orthographicChart q) i j)^(p+1)
  have hf : ∀ i j, f i j=f j i := by intro i j;dsimp [f];rw [squaredDistance_symm]
  have hnonneg (i j : Fin 8) : 0≤f i j := Real.rpow_nonneg (div_nonneg tau_pos.le (sq_nonneg _)) _
  have hpair : hessianNegativeSum p q ξ≤
      ((8:ℝ)/3)*(∑ ij∈unorderedPairs, f ij.1 ij.2*(‖tangentVector ξ ij.1‖^2+‖tangentVector ξ ij.2‖^2)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ij hij
    have h := mul_le_mul_of_nonneg_left
      (pair_hessian p hp q ξ hq.2.1 ij.1 ij.2 (ne_of_lt ((mem_unorderedPairs _ _).mp hij))) (hnonneg ij.1 ij.2)
    convert! h using 1 <;> ring
  rw [unordered_incident_weight_sum f hf (fun i=>‖tangentVector ξ i‖^2)] at hpair
  have hsum : (∑ i : Fin 8, ‖tangentVector ξ i‖^2*(∑ j∈Finset.univ.erase i, f i j))≤
      ((31:ℝ)/5)*‖ξ‖^2 := by
    rw [←tangentVector_sum_norm_sq ξ,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have h := mul_le_mul_of_nonneg_left (incident_bound_all_incident p hp q hq i).le (sq_nonneg ‖tangentVector ξ i‖)
    convert! h using 1 <;> ring
  have h : hessianNegativeSum p q ξ≤((248:ℝ)/15)*‖ξ‖^2 := by linarith
  have ht := mul_le_mul_of_nonneg_left h tau_pos.le
  convert! ht using 1 <;> ring

#print axioms full_hessian_negative_part
end Blueprint.Thomson.Tail.Implementation
