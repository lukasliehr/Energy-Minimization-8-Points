import LeanCode.Monotonic.Deformation

set_option maxHeartbeats 2000000
noncomputable section
open Real Set Filter
open scoped BigOperators Topology
namespace SquareAntiprismCounterexample

lemma deformZ_zero (a : ℝ) :
    deformZ a 0 = ![dA a,dB a,dB a,dC a,dC a,dD a,dD a] := by
  ext k
  fin_cases k <;> simp [deformZ,curveC,curveS,dB,dC,dD,C,D,
    div_eq_mul_inv,inv_sqrt_two] <;> ring

lemma deformZ_zero_pos {a : ℝ} (ha : a ∈ Ioo (0:ℝ) 1) (k : Fin 7) :
    0 < deformZ a 0 k := by
  rcases distance_domains ha with ⟨hA,hB,hC,hD⟩
  rw [deformZ_zero]
  fin_cases k <;>
    first | exact hA.1 | exact hB.1 | exact hC.1 | exact hD.1

lemma deform_positive_neighborhood {a : ℝ} (ha : a ∈ Ioo (0:ℝ) 1) :
    ∃ δ > 0, ∀ u ∈ Ioo (-δ) δ, ∀ k : Fin 7, 0 < deformZ a u k := by
  have he (k : Fin 7) : ∀ᶠ u in nhds (0:ℝ), 0 < deformZ a u k :=
    continuousAt_const.eventually_lt (deformZ_continuous a k).1.continuousAt
      (deformZ_zero_pos ha k)
  obtain ⟨δ,hδ,heδ⟩ := Metric.eventually_nhds_iff.mp (Filter.eventually_all.mpr he)
  refine ⟨δ,hδ,?_⟩
  intro u hu k
  exact heδ (by simpa [Real.dist_eq] using abs_lt.mpr hu) k

lemma deform_configuration {a u : ℝ} (ha : a ∈ Ioo (0:ℝ) 1)
    (hz : ∀ k : Fin 7, 0 < deformZ a u k) : IsConfiguration (deform a u) := by
  refine ⟨deform_norm ha u,?_⟩
  have hd (k : Fin 9) : 0 < deformEdgeDistance a u k := by
    rcases distance_domains ha with ⟨hA,hB,hC,hD⟩
    fin_cases k <;> dsimp only [deformEdgeDistance]
    · exact hz 0
    · exact hz 1
    · exact hz 2
    · exact hz 3
    · exact hz 4
    · exact hz 5
    · exact hz 6
    · exact hA.1
    · exact hB.1
  intro i j hij
  by_contra hne
  have hs := deform_sq_distance ha u i j hne
  rw [hij,sub_self,norm_zero,zero_pow (by decide : 2 ≠ 0)] at hs
  linarith [hd (deformEdgeType i j)]

lemma deformH_deriv (v v1 : ℝ → ℝ)
    (hv : ∀ t, 0 < t → HasDerivAt v (v1 t) t) (a u : ℝ)
    (hz : ∀ k : Fin 7, 0 < deformZ a u k) :
    HasDerivAt (deformH a v) (deformH1 a v1 u) u := by
  have hs : HasDerivAt (fun x => ∑ k : Fin 7, deformWeight k*v (deformZ a x k))
      (deformH1 a v1 u) u := by
    apply HasDerivAt.fun_sum
    intro k hk
    exact ((hv _ (hz k)).comp u (deformZ_deriv a u k)).const_mul (deformWeight k)
  exact hs.const_add (4*v (dA a)+2*v (dB a))

lemma deformH1_deriv (v1 v2 : ℝ → ℝ)
    (hv1 : ∀ t, 0 < t → HasDerivAt v1 (v2 t) t) (a u : ℝ)
    (hz : ∀ k : Fin 7, 0 < deformZ a u k) :
    HasDerivAt (deformH1 a v1) (deformH2 a v1 v2 u) u := by
  apply HasDerivAt.fun_sum
  intro k hk
  convert! (((hv1 _ (hz k)).comp u (deformZ_deriv a u k)).mul
    (deformZ1_deriv a u k)).const_mul (deformWeight k) using 1
  all_goals dsimp only [Function.comp_def,Pi.mul_apply]
  all_goals ring

lemma deformH2_continuousAt (v1 v2 : ℝ → ℝ)
    (hv1 : ∀ t, 0 < t → HasDerivAt v1 (v2 t) t)
    (hv2 : ContinuousOn v2 (Ioi 0)) (a u : ℝ)
    (hz : ∀ k : Fin 7, 0 < deformZ a u k) :
    ContinuousAt (deformH2 a v1 v2) u := by
  apply tendsto_finsetSum
  intro k hk
  have h1 : ContinuousAt (fun x => v1 (deformZ a x k)) u :=
    (hv1 _ (hz k)).continuousAt.comp (f := fun x => deformZ a x k) (deformZ_continuous a k).1.continuousAt
  have h2 : ContinuousAt (fun x => v2 (deformZ a x k)) u :=
    (hv2.continuousAt (isOpen_Ioi.mem_nhds (hz k))).comp (f := fun x => deformZ a x k) (deformZ_continuous a k).1.continuousAt
  have hz1 := (deformZ_continuous a k).2.1.continuousAt (x := u)
  have hz2 := (deformZ_continuous a k).2.2.continuousAt (x := u)
  exact continuousAt_const.mul ((h2.mul (hz1.pow 2)).add (h1.mul hz2))

lemma deformH1_zero (a : ℝ) (v1 : ℝ → ℝ) : deformH1 a v1 0 = 0 := by
  simp only [deformH1,deformZ_zero,Fin.sum_univ_seven]
  simp [deformWeight,deformZ1,curveC,curveS,curveC1,curveS1]

lemma deformH2_zero {a : ℝ} (ha : a ∈ Ioo (0:ℝ) 1) (v1 v2 : ℝ → ℝ) :
    deformH2 a v1 v2 0 = 4*Q a v1 v2 := by
  have hr : (√(1-a))^2 = 1-a := Real.sq_sqrt (by linarith [ha.2])
  have hb : (√a)^2 = a := Real.sq_sqrt ha.1.le
  simp only [deformH2,deformZ_zero,Fin.sum_univ_seven]
  simp [deformWeight,deformZ1,deformZ2,curveC,curveS,curveC1,curveS1,curveC2,curveS2]
  dsimp [Q,B]
  ring_nf
  simp only [hr,hb]
  ring

lemma deformation_descent (v v1 v2 : ℝ → ℝ) {a : ℝ} (ha : a ∈ Ioo (0:ℝ) 1)
    (hv : ∀ t, 0 < t → HasDerivAt v (v1 t) t)
    (hv1 : ∀ t, 0 < t → HasDerivAt v1 (v2 t) t)
    (hv2 : ContinuousOn v2 (Ioi 0)) (hQ : Q a v1 v2 < 0) :
    ∃ Y : Fin 8 → Point, IsConfiguration Y ∧ Ef v Y < G v a := by
  obtain ⟨δ,hδ,hpos⟩ := deform_positive_neighborhood ha
  obtain ⟨u,hu,huδ,he⟩ := local_descent hδ
    (fun x hx => deformH_deriv v v1 hv a x (hpos x hx))
    (fun x hx => deformH1_deriv v1 v2 hv1 a x (hpos x hx))
    (deformH2_continuousAt v1 v2 hv1 hv2 a 0 (deformZ_zero_pos ha))
    (deformH1_zero a v1) (by rw [deformH2_zero ha]; linarith)
  refine ⟨deform a u,deform_configuration ha (hpos u ⟨by linarith,huδ⟩),?_⟩
  rw [deform_energy v ha]
  have hzero : deformH a v 0 = G v a := by
    rw [←deform_energy v ha,deform_zero,energy_X v ha]
  rwa [hzero] at he

end SquareAntiprismCounterexample
