import AllS.Units.N_GI.N_incident_bound.N_bi_upper

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def noncontactNeighbors (i : Fin 8) : Finset (Fin 8) :=
  Finset.univ.filter (fun j=>i≠j ∧ ¬IsCyclicContact i j)

theorem noncontactNeighbors_card : ∀ i : Fin 8, (noncontactNeighbors i).card=3 := by decide

theorem chart_squaredDistance_error (q : TangentCoordinates) (hq : ‖q‖<1)
    (i j : Fin 8) (hij : i≠j) :
    |squaredDistance (orthographicChart q) i j-squaredDistance packingReference i j|≤4*‖q‖ := by
  have hinner : inner ℝ (orthographicChart q i) (orthographicChart q j)-inner ℝ (packingReference i) (packingReference j)=
      inner ℝ (orthographicChart q i-packingReference i) (orthographicChart q j)+
        inner ℝ (packingReference i) (orthographicChart q j-packingReference j) := by
    simp only [inner_sub_left,inner_sub_right]
    ring
  have hi := abs_real_inner_le_norm (orthographicChart q i-packingReference i) (orthographicChart q j)
  have hj := abs_real_inner_le_norm (packingReference i) (orthographicChart q j-packingReference j)
  rw [nearest_chart_chart_unit q hq j,mul_one] at hi
  rw [packingReference_norm,one_mul] at hj
  have ht := (abs_add_le _ _).trans (add_le_add hi hj)
  rw [←hinner] at ht
  have he : squaredDistance (orthographicChart q) i j-squaredDistance packingReference i j=
      -2*(inner ℝ (orthographicChart q i) (orthographicChart q j)-inner ℝ (packingReference i) (packingReference j)) := by
    simp only [squaredDistance,norm_sub_sq_real,nearest_chart_chart_unit q hq,
      packingReference_norm]
    ring
  rw [he,abs_mul]
  norm_num only [abs_neg,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
  have hp := chart_deviation_pair_le q hq i j hij
  nlinarith

theorem packing_noncontact_distance (i j : Fin 8) (hij : i≠j) (hnc : ¬IsCyclicContact i j) :
    2*tau≤ squaredDistance packingReference i j := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact constants_pair_table.2.2.2.2 (i,j) (Finset.mem_sdiff.mpr
      ⟨(mem_unorderedPairs i j).mpr h,fun hmem=>hnc ((cyclicContactPairs_mem i j).mp hmem).2⟩)
  · rw [squaredDistance_symm]
    have hnc' : ¬IsCyclicContact j i := by
      simpa only [IsCyclicContact,or_assoc,or_left_comm,or_comm] using hnc
    exact constants_pair_table.2.2.2.2 (j,i) (Finset.mem_sdiff.mpr
      ⟨(mem_unorderedPairs j i).mpr h,fun hmem=>hnc' ((cyclicContactPairs_mem j i).mp hmem).2⟩)

theorem tail_radius_small_noncontact (p : ℝ) (hp : (97:ℝ)/2≤p) (q : TangentCoordinates)
    (hq : ‖q‖≤contraction/p) : 4*‖q‖<tau/2 := by
  have hp0 : 0<p := by linarith
  obtain ⟨_,_,htl,_,_,_,_,_⟩ := tail_geometric_constants
  have hprod : ((147759:ℝ)/10^5)*(97/2)≤tau*p :=
    mul_le_mul htl.le hp (by norm_num) tau_pos.le
  have hr : contraction/p<tau/8 := by
    apply (div_lt_iff₀ hp0).mpr
    dsimp [contraction]
    nlinarith
  linarith [hq.trans_lt hr]

theorem noncontact_distance_lower (p : ℝ) (hp : (97:ℝ)/2≤p) (q : TangentCoordinates)
    (hq : q∈convexTailDomain p) (i j : Fin 8) (hij : i≠j) (hnc : ¬IsCyclicContact i j) :
    2*tau-4*‖q‖≤ squaredDistance (orthographicChart q) i j ∧
      (3/2)*tau<squaredDistance (orthographicChart q) i j := by
  have hq1 : ‖q‖<1 := by linarith [tail_small_radius p hp q hq.2.1]
  have h := (abs_le.mp (chart_squaredDistance_error q hq1 i j hij)).1
  have hP := packing_noncontact_distance i j hij hnc
  have hr := tail_radius_small_noncontact p hp q hq.2.1
  constructor <;> linarith

theorem noncontact_normalized_bound (p : ℝ) (hp : (97:ℝ)/2≤p) (q : TangentCoordinates)
    (hq : q∈convexTailDomain p) (i j : Fin 8) (hij : i≠j) (hnc : ¬IsCyclicContact i j) :
    (tau/squaredDistance (orthographicChart q) i j)^(p+1)≤((2:ℝ)/3)^(p+1) := by
  have h := (noncontact_distance_lower p hp q hq i j hij hnc).2
  have hd : 0<squaredDistance (orthographicChart q) i j := by linarith [tau_pos]
  have hr : tau/squaredDistance (orthographicChart q) i j≤(2:ℝ)/3 := by
    apply (div_le_iff₀ hd).mpr
    linarith
  exact Real.rpow_le_rpow (div_nonneg tau_pos.le hd.le) hr (by linarith)

theorem noncontact_power_small (p : ℝ) (hp : (97:ℝ)/2≤p) :
    3*((2:ℝ)/3)^(p+1)<1/1000 := by
  have h := Real.rpow_le_rpow_of_exponent_ge (by norm_num : (0:ℝ)<2/3)
    (by norm_num : (2:ℝ)/3≤1) (by linarith : (30:ℝ)≤p+1)
  norm_num [Real.rpow_natCast] at h
  linarith

theorem incident_bound_noncontacts (p : ℝ) (hp : (97:ℝ)/2≤p) (q : TangentCoordinates)
    (hq : q∈convexTailDomain p) :
    (∀ i j, i≠j → ¬IsCyclicContact i j →
      2*tau-4*‖q‖≤ squaredDistance (orthographicChart q) i j ∧
        (3/2)*tau<squaredDistance (orthographicChart q) i j) ∧
    (∀ i, (∑ j∈noncontactNeighbors i, (tau/squaredDistance (orthographicChart q) i j)^(p+1))<1/1000) := by
  refine ⟨fun i j hij hnc=>noncontact_distance_lower p hp q hq i j hij hnc,?_⟩
  intro i
  have h := Finset.sum_le_sum (fun j (hj : j∈noncontactNeighbors i)=>by
    have hj' : i≠j ∧ ¬IsCyclicContact i j := (Finset.mem_filter.mp hj).2
    exact noncontact_normalized_bound p hp q hq i j hj'.1 hj'.2)
  simp only [Finset.sum_const,noncontactNeighbors_card,nsmul_eq_mul,Nat.cast_ofNat] at h
  exact h.trans_lt (noncontact_power_small p hp)

#print axioms incident_bound_noncontacts
end Blueprint.Thomson.Tail.Implementation
