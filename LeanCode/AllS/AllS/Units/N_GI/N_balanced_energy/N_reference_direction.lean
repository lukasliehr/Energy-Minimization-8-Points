import AllS.Units.N_GI.N_balanced_energy.N_reference_data

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem uniform_meridian_mem_slice : boundaryRaw 0∈rotationSlice := by
  rw [mem_rotationSlice_iff]
  intro j
  fin_cases j <;> norm_num [boundaryRotation,boundaryRaw_gram,boundaryRotationIndex]

theorem balancedReference_mem_slice : balancedReference∈rotationSlice :=
  Submodule.smul_mem _ _ uniform_meridian_mem_slice

theorem uniform_meridian_tangent (i : Fin 8) : tangentVector (boundaryRaw 0) i=meridianFrame i := by
  simp [tangentVector,boundaryRaw,boundaryRawPair]

theorem uniform_meridian_contact (e : ContactIndex) :
    contactLinear (boundaryRaw 0) e.1 (contactNext e)=
      if e.2=0 then 4*packingZHeight*packingRadius*contactKappa else -4*packingZHeight*packingRadius := by
  rcases e with ⟨i,k⟩
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < √(2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hinv : (√(2:ℝ))⁻¹=√2/2 := by field_simp; nlinarith
  simp only [contactLinear,uniform_meridian_tangent,packingReference_formula,meridianFrame,PiLp.inner_apply]
  fin_cases i <;> fin_cases k <;>
    norm_num [contactNext,Fin.sum_univ_succ,angularCos,angularSin,layerSign,Fin.val_add,
      contactKappa_formula,div_eq_mul_inv,hinv] <;> ring_nf <;> simp [hs] <;> ring

theorem contactLinear_smul (c : ℝ) (q : TangentCoordinates) (i j : Fin 8) :
    contactLinear (c • q) i j=c*contactLinear q i j := by
  simp only [contactLinear,tangentVector_smul,real_inner_smul_right]
  ring

theorem balancedReference_contact (e : ContactIndex) :
    contactLinear balancedReference e.1 (contactNext e)=balancedZ e := by
  rw [balancedReference,contactLinear_smul,uniform_meridian_contact]
  have hH := ne_of_gt packing_parameters.1
  have hR := ne_of_gt packing_parameters.2.1
  unfold balancedZ
  split_ifs <;> field_simp <;> ring

theorem balancedReference_norm : ‖balancedReference‖=balancedRefNorm := by
  have hH := packing_parameters.1
  have hR := packing_parameters.2.1
  have hraw : ‖boundaryRaw 0‖^2=8 := by
    rw [← real_inner_self_eq_norm_sq,boundaryRaw_gram]
    norm_num [boundaryWeight]
  have hn : ‖balancedReference‖^2=balancedD^2/(2*packingHeight*(1-packingHeight)) := by
    rw [balancedReference,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,hraw]
    have hHs := packing_parameters.2.2.1
    have hRs := packing_parameters.2.2.2
    rw [div_pow]
    simp only [mul_pow,hHs,hRs]
    have ha : packingHeight ≠ 0 := by rw [←hHs]; positivity
    have hb : 1-packingHeight ≠ 0 := by rw [←hRs]; positivity
    field_simp
    ring
  have hbase : 0<2*packingHeight*(1-packingHeight) := by
    have hHa := packing_parameters.2.2.1
    have hRa := packing_parameters.2.2.2
    rw [←hRa,←hHa]
    positivity
  have hroot : (√(2*packingHeight*(1-packingHeight)))^2=2*packingHeight*(1-packingHeight) := Real.sq_sqrt hbase.le
  have hnorm : 0≤balancedRefNorm := (div_pos balancedD_pos (Real.sqrt_pos.mpr hbase)).le
  have hsq : balancedRefNorm^2=balancedD^2/(2*packingHeight*(1-packingHeight)) := by
    rw [balancedRefNorm,div_pow,hroot]
  nlinarith [norm_nonneg balancedReference]

theorem balanced_energy_reference_direction :
    balancedReference∈rotationSlice ∧
    (∀ e : ContactIndex, contactLinear balancedReference e.1 (contactNext e)=balancedZ e) ∧
    ‖balancedReference‖=balancedRefNorm ∧
    (∑ e : ContactIndex, contactWeight e*balancedZ e)=0 ∧
    (∑ e : ContactIndex, contactWeight e*(balancedZ e)^2)=balancedZNorm^2 :=
  ⟨balancedReference_mem_slice,balancedReference_contact,balancedReference_norm,balancedZ_mean,balancedZ_square⟩

#print axioms balanced_energy_reference_direction
end Blueprint.Thomson.Tail.Implementation
