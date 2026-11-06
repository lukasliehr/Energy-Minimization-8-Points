import AllS.Units.N_GI.N_disphenoid.N_sign_coordinates

set_option maxHeartbeats 1200000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem orthonormal_sum_norm_sq (e : Fin 3 → Point) (he : Orthonormal ℝ e) (l : Fin 3 → ℝ) :
    ‖∑k,l k • e k‖^2=∑k,(l k)^2 := by
  rw [←real_inner_self_eq_norm_sq,he.inner_sum]
  simp only [conj_trivial,pow_two]

theorem cube_coordinate_normalizations (A B : Fin 4 → Point) (c : ℝ)
    (hAunit : ∀i,‖A i‖=1) (hBunit : ∀i,‖B i‖=1)
    (e : Fin 3 → Point) (he : Orthonormal ℝ e) (x : Fin 3 → ℝ)
    (hA : ∀i,A i=∑k,(cubeSign i k*x k) • e k)
    (hB : ∀i,B i=∑k,(-c*cubeSign i k/x k) • e k) :
    (∑k,(x k)^2)=1 ∧ c^2*(∑k,1/(x k)^2)=1 := by
  have hsign : ∀k,cubeSign 0 k=1 := by intro k;fin_cases k <;> rfl
  have hnormA := congrArg (fun z : Point => ‖z‖^2) (hA 0)
  have hnormB := congrArg (fun z : Point => ‖z‖^2) (hB 0)
  rw [hAunit,one_pow,orthonormal_sum_norm_sq e he] at hnormA
  rw [hBunit,one_pow,orthonormal_sum_norm_sq e he] at hnormB
  simp only [hsign,mul_one,one_mul] at hnormA hnormB
  refine ⟨hnormA.symm,?_⟩
  calc
    c^2*(∑k,1/(x k)^2) = ∑k,(-c/x k)^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp only [div_pow,neg_sq,mul_one_div]
    _ = 1 := hnormB.symm

theorem disphenoid_coordinates (A B : Fin 4 → Point) (c : ℝ) (hc : 0<c)
    (hAunit : ∀i,‖A i‖=1) (hBunit : ∀i,‖B i‖=1)
    (hAinj : Function.Injective A) (hBinj : Function.Injective B)
    (hcross : ∀i j,i≠j → inner ℝ (A i) (B j)=c)
    (hmatched : ∀i,inner ℝ (A i) (B i)≤c) :
    ∃ (e : Fin 3 → Point) (x : Fin 3 → ℝ),Orthonormal ℝ e ∧ (∀k,0<x k) ∧
      (∀i,A i=∑k,(cubeSign i k*x k) • e k) ∧
      (∀i,B i=∑k,(-c*cubeSign i k/x k) • e k) ∧
      (∑k,(x k)^2)=1 ∧ c^2*(∑k,1/(x k)^2)=1 := by
  obtain ⟨hG,huv,huw,hvw,hun,hvn,hwn⟩ := disphenoid_hadamard_frame A B c hc hAunit hBunit hAinj hBinj hcross hmatched
  obtain ⟨hn,ho⟩ := hadamardVectors_nonzero_orthogonal A huv huw hvw hun hvn hwn
  obtain ⟨e,x,he,hx,hA⟩ := hadamard_orthonormal_coordinates A hG hn ho
  have hB := cube_dual_coordinates A B c hc hAunit hAinj hcross e he x hx hA
  exact ⟨e,x,he,hx,hA,hB,cube_coordinate_normalizations A B c hAunit hBunit e he x hA hB⟩

#print axioms cube_coordinate_normalizations
#print axioms disphenoid_coordinates
end Blueprint.Thomson.Tail.Implementation
