import AllS.Units.N_GI.N_signed_mean.N_physical_bounds

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

/-- A dual Gram certificate controls an operator in the positive quadratic metric. -/
theorem tensorMap_bound_of_dual_gram {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : E →ₗ[ℝ] E) (c : ι → E) (B : ℝ)
    (hA : ∀v,0 ≤ inner ℝ v (A v)) (hB : 0 ≤ B)
    (hgram : ∀v,(∑i,(inner ℝ (A v) (c i))^2) ≤ B*inner ℝ v (A v))
    (z : ι → ℝ) :
    inner ℝ (∑i,z i • c i) (A (∑i,z i • c i)) ≤ B*(∑i,(z i)^2) := by
  let u := ∑i,z i • c i
  let v := inner ℝ u (A u)
  have hv : 0 ≤ v := hA u
  have he : (∑i,z i*inner ℝ (A u) (c i))=v := by
    dsimp [v,u]
    rw [sum_inner]
    simp only [real_inner_smul_left,real_inner_comm (A _) (c _)]
  have hc := finite_weighted_cauchy (fun _ : ι=>(1:ℝ)) z
    (fun i=>inner ℝ (A u) (c i)) (fun _=>by norm_num)
  simp only [one_mul,he] at hc
  have hz : 0 ≤ ∑i,(z i)^2 := Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have ht := mul_le_mul_of_nonneg_left (hgram u) hz
  change v ≤ B*(∑i,(z i)^2)
  by_cases hv0 : v=0
  · rw [hv0]
    exact mul_nonneg hB hz
  · have hvp : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
    have hp : v*v ≤ (B*(∑i,(z i)^2))*v := by
      dsimp [v] at ht ⊢
      nlinarith [hc,ht]
    exact (mul_le_mul_iff_left₀ hvp).mp hp

#print axioms tensorMap_bound_of_dual_gram
end Blueprint.Thomson.Tail.Implementation
