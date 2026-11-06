import AllS.Units.N_GI.N_stationary_flow.N_vertex_derivative

noncomputable section
open Real
open scoped BigOperators
open SquareAntiprismVerification (crossVec)
namespace Blueprint.Thomson.Tail.Implementation

def forceFlow (p : ℝ) (u : Point) (Y : Fin 8 → Point) (i j : Fin 8) : ℝ :=
  (squaredDistance Y i j)^(-p-1)*max (orientedArea u Y i j) 0

@[simp] theorem orientedArea_self (u : Point) (Y : Fin 8 → Point) (i : Fin 8) :
    orientedArea u Y i i=0 := by
  have h : crossVec (Y i) (Y i)=0 := by
    ext k
    fin_cases k <;> simp [crossVec] <;> ring
  simp [orientedArea,h]

theorem orientedArea_swap (u : Point) (Y : Fin 8 → Point) (i j : Fin 8) :
    orientedArea u Y j i= -orientedArea u Y i j := by
  rw [orientedArea,SquareAntiprismVerification.crossVec_swap,inner_neg_right]
  rfl

@[simp] theorem forceFlow_self (p : ℝ) (u : Point) (Y : Fin 8 → Point) (i : Fin 8) :
    forceFlow p u Y i i=0 := by simp [forceFlow]

theorem forceFlow_nonneg (p : ℝ) (u : Point) (Y : Fin 8 → Point) (i j : Fin 8) :
    0 ≤ forceFlow p u Y i j :=
  mul_nonneg (Real.rpow_nonneg (squaredDistance_nonneg Y i j) _) (le_max_right _ _)

theorem forceFlow_difference (p : ℝ) (u : Point) (Y : Fin 8 → Point) (i j : Fin 8) :
    forceFlow p u Y i j-forceFlow p u Y j i=
      (squaredDistance Y i j)^(-p-1)*orientedArea u Y i j := by
  have hd : squaredDistance Y j i=squaredDistance Y i j := by
    simp [squaredDistance,norm_sub_rev]
  simp only [forceFlow,hd,orientedArea_swap u Y i j]
  by_cases h : 0 ≤ orientedArea u Y i j
  · rw [max_eq_left h,max_eq_right (by linarith : -orientedArea u Y i j ≤ 0)]
    ring
  · rw [max_eq_right (le_of_not_ge h),max_eq_left (by linarith : 0 ≤ -orientedArea u Y i j)]
    ring

theorem forceFlow_no_opposite (p : ℝ) (u : Point) (Y : Fin 8 → Point) (i j : Fin 8) :
    ¬(0<forceFlow p u Y i j ∧ 0<forceFlow p u Y j i) := by
  by_cases h : 0 ≤ orientedArea u Y i j
  · have hz : forceFlow p u Y j i=0 := by
      simp [forceFlow,orientedArea_swap u Y i j,
        max_eq_right (by linarith : -orientedArea u Y i j ≤ 0)]
    simp [hz]
  · have hz : forceFlow p u Y i j=0 := by
      simp [forceFlow,max_eq_right (le_of_not_ge h)]
    simp [hz]

theorem forceFlow_balanced (p : ℝ) (Y : Fin 8 → Point) (hY : IsConfiguration Y)
    (hp : 0 < p) (hstat : Stationary p Y) (u : Point) (i : Fin 8) :
    (∑ j : Fin 8, forceFlow p u Y i j)=∑ j : Fin 8, forceFlow p u Y j i := by
  have h := stationary_oriented_vertex p Y hY hp hstat u i
  have hf : (∑ j : Fin 8, (squaredDistance Y i j)^(-p-1)*orientedArea u Y i j)=0 := by
    calc
      _ = ∑ j : Fin 8, if j≠i then
          (squaredDistance Y i j)^(-p-1)*orientedArea u Y i j else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hji : j=i
        · subst j
          simp
        · simp [hji]
      _ = 0 := by simpa only [Finset.sum_filter] using h
  apply sub_eq_zero.mp
  rw [← Finset.sum_sub_distrib]
  simpa only [forceFlow_difference] using hf

theorem stationary_flow_circulation (Y : Fin 8 → Point) (p m : ℝ)
    (i₀ j₀ : Fin 8) (hY : IsConfiguration Y) (hp : 0 < p) (hstat : Stationary p Y)
    (_hne : i₀ ≠ j₀) (hm : 0 < m) (hmmax : m ≤ 29/20)
    (hd : squaredDistance Y i₀ j₀=m) (_hmin : ∀ i j, i ≠ j → m ≤ squaredDistance Y i j) :
    (∀ i, (∑ j : Fin 8, forceFlow p (forceAxis Y i₀ j₀ m) Y i j)=
      ∑ j : Fin 8, forceFlow p (forceAxis Y i₀ j₀ m) Y j i) ∧
    forceFlow p (forceAxis Y i₀ j₀ m) Y i₀ j₀=m^(-p-1)*sin (forceAngle m) ∧
    0<forceFlow p (forceAxis Y i₀ j₀ m) Y i₀ j₀ := by
  obtain ⟨ht,hs,hu,harea⟩ := forceAxis_spec Y hY m hm hmmax i₀ j₀ hd
  have he : forceFlow p (forceAxis Y i₀ j₀ m) Y i₀ j₀=m^(-p-1)*sin (forceAngle m) := by
    simp [forceFlow,hd,harea,max_eq_left hs.le]
  refine ⟨forceFlow_balanced p Y hY hp hstat _,he,?_⟩
  rw [he]
  exact mul_pos (Real.rpow_pos_of_pos hm _) hs

#check stationary_flow_circulation
#print axioms stationary_flow_circulation
end Blueprint.Thomson.Tail.Implementation
