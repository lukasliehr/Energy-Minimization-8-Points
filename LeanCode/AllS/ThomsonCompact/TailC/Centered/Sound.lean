import ThomsonCompact.TailC.Centered.Mirror

/-!
# TailC.Centered: the centered quadratic bound from the row checks (workstream TC1)

`ι_gramZ : ι (gramZ j k) = 17210368 · centeredContactRawGram (meanTangentRaw j) (meanTangentRaw k)`, hence
`rowOk j` for all `j` (the kernel leaves `Centered.Row*`) gives the 256 entry identities and the bound
`centered_bound_of_rows`, the same statement as the old `centered_quadratic_bound_four`.
-/

namespace ThomsonCompact.TailC.Centered
open ThomsonCompact.TailC Finset
open Blueprint.Thomson.Tail Blueprint.Thomson.Tail.Implementation

theorem κ49 : κ 49 = 49 := by simpa using (map_ofNat κ 49)
theorem κ112 : κ 112 = 112 := by simpa using (map_ofNat κ 112)
theorem κ1568 : κ 1568 = 1568 := by simpa using (map_ofNat κ 1568)
theorem κ3136 : κ 3136 = 3136 := by simpa using (map_ofNat κ 3136)

theorem ι_rot0 (i : Fin 8) (b : Fin 2) : ι (rotZ 0 i b) = 2 * (boundaryRotation 0) (i, b) := ι_rotZ 0 i b
theorem ι_rot1 (i : Fin 8) (b : Fin 2) : ι (rotZ 1 i b) = 2 * (boundaryRotation 1) (i, b) := ι_rotZ 1 i b

theorem bw0 : boundaryWeight (boundaryRotationIndex 0) = 4 * (1 + packingHeight) := bw_rot01 0
theorem bw1 : boundaryWeight (boundaryRotationIndex 1) = 4 * (1 + packingHeight) := bw_rot01 1

theorem hbw_ne : (4 : ℝ) * (1 + packingHeight) ≠ 0 := by
  have : (0 : ℝ) < packingHeight := by
    rw [← hH2]; exact pow_pos packing_parameters.1 2
  positivity

/-- One contact. -/
theorem contact_term (e : ContactIndex) (j k : Fin 8 × Fin 2) :
    ι (zs (kwZ e) (zs 1568 (∑ c : Fin 4, mul7 (fZ e j c) (fZ e k c)) -
      (zs wZ (mul7 (gZ7 (rotZ 0) (qA j) e) (gZ7 (rotZ 0) (qA k) e)) +
        zs wZ (mul7 (gZ7 (rotZ 1) (qA j) e) (gZ7 (rotZ 1) (qA k) e)) +
        zs 49 (mul7 (bZ e j) (bZ e k))))) =
    17210368 * (contactWeight e * ((∑ c : Fin 4, contactMComponents e (meanTangentRaw j) c *
        contactMComponents e (meanTangentRaw k) c) -
      ∑ r : Fin 3, contactMBilinear e (boundaryRotation r) (meanTangentRaw j) *
        contactMBilinear e (boundaryRotation r) (meanTangentRaw k) / boundaryWeight (boundaryRotationIndex r))) := by
  have hR : packingRadius ≠ 0 := packing_parameters.2.1.ne'
  have hw : κ wZ = 8 / (4 * (1 + packingHeight)) := by rw [eq_div_iff hbw_ne]; exact κ_wZ
  rw [ι_zs, κ_kwZ, ι_sub, ι_zs, κ1568, ι_sum, ι_add, ι_add, ι_zs, ι_zs, ι_zs, κ49, ι_mul7, ι_mul7, ι_mul7,
    ι_gZ7 (rotZ 0) (qA j) (boundaryRotation 0) (meanTangentRaw j) ι_rot0 (ι_qA j) e,
    ι_gZ7 (rotZ 0) (qA k) (boundaryRotation 0) (meanTangentRaw k) ι_rot0 (ι_qA k) e,
    ι_gZ7 (rotZ 1) (qA j) (boundaryRotation 1) (meanTangentRaw j) ι_rot1 (ι_qA j) e,
    ι_gZ7 (rotZ 1) (qA k) (boundaryRotation 1) (meanTangentRaw k) ι_rot1 (ι_qA k) e,
    ι_bZ, ι_bZ, Fin.sum_univ_three, bil_rot2, bil_rot2, bw0, bw1, bw_rot2, hw]
  simp only [ι_mul7, ι_fZ, Fin.sum_univ_four]
  field_simp
  ring

/-- One stress term. -/
theorem stress_term (j k j' : Fin 8 × Fin 2) :
    ι (zs (112 * mswN j'.1 * tZ) (mul7 (hZ j j') (hZ k j'))) =
      17210368 * (stressH (meanTangentRaw j) (meanTangentRaw j') * stressH (meanTangentRaw k) (meanTangentRaw j') /
        meanScalarWeight j'.1) / contactTotalWeight := by
  have hm : meanScalarWeight j'.1 ≠ 0 := (meanScalarWeight_pos j'.1).ne'
  have hT : contactTotalWeight ≠ 0 := by rw [contactTotalWeight]; positivity
  have hmN : κ (mswN j'.1) = 8 / meanScalarWeight j'.1 := by rw [eq_div_iff hm]; exact κ_mswN j'.1
  have hTZ : κ tZ = 56 / contactTotalWeight := by rw [eq_div_iff hT]; exact κ_tZ
  rw [ι_zs, ι_mul7, ι_hZ, ι_hZ, meanH_raw, meanH_raw, map_mul, map_mul, κ112, hmN, hTZ]
  field_simp
  ring

theorem ι_gramZ (j k : Fin 8 × Fin 2) :
    ι (gramZ j k) = 17210368 * centeredContactRawGram (meanTangentRaw j) (meanTangentRaw k) := by
  rw [gramZ, centeredContactRawGram, ι_sub, ι_sum, ι_sum,
    Finset.sum_congr rfl (fun e _ => contact_term e j k), Finset.sum_congr rfl (fun j' _ => stress_term j k j'),
    ← Finset.mul_sum, mul_sub, Finset.sum_div, Finset.mul_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl (fun j' _ => ?_)
  ring

/-- The entry identities from the row checks. -/
theorem centered_entry_of_rows (hrows : ∀ j, rowOk j) (j k : Fin 8 × Fin 2) :
    centeredContactGram (meanTangentRaw j) (meanTangentRaw k) = centeredQEntry j k := by
  have h1 := ι_gramZ j k
  rw [hrows j k, ι_zs, κ3136, ι_qEZ] at h1
  rw [centeredContactGram_raw]
  linarith

/-- The centered quadratic bound (`hQ` of `tail_range_of_tensor_certificates`), from the row checks. -/
theorem centered_bound_of_rows (hrows : ∀ j, rowOk j) (q : TangentCoordinates) :
    (∑ e : ContactIndex, contactWeight e * ‖sliceProjection (contactM e q - contactMeanM q)‖ ^ 2) ≤ 4 * ‖q‖ ^ 2 := by
  rw [centeredContact_projected_norm]
  exact centeredContactGram_bound_of_entries (centered_entry_of_rows hrows) q

end ThomsonCompact.TailC.Centered
