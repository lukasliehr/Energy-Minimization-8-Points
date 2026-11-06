import AllS.Units.N_GI.N_contact_spectrum.N_physical_unweighted
import AllS.Units.N_GI.N_slice_point_bound.N_projection_algebra

set_option maxHeartbeats 2000000
noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem contactLinear_rotation_zero (j : Fin 3) (e : ContactIndex) :
    contactLinear (boundaryRotation j) e.1 (contactNext e)=0 := by
  rw [contactLinear_cyclic_formula]
  have hs : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hpos : 0<Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hinv : (Real.sqrt (2:ℝ))⁻¹=Real.sqrt 2/2 := by field_simp; nlinarith
  rcases e with ⟨i,k⟩
  fin_cases j <;> fin_cases i <;> fin_cases k <;>
    norm_num [boundaryRotation,boundaryRaw,boundaryRawPair,boundaryRotationIndex,
      contactNext,contactSine,contactMeridianFactor,boundaryCos3,boundarySin3,
      angularCos,angularSin,layerSign,contactKappa_formula,div_eq_mul_inv,hinv] <;>
    ring_nf <;> simp [hs] <;> ring_nf <;> simp [hs] <;> ring <;> simp

theorem contactLinear_rotationProjection (q : TangentCoordinates) (e : ContactIndex) :
    contactLinear (rotationProjection q) e.1 (contactNext e)=0 := by
  change contactLinearMap e (∑j, inner ℝ (normalizedRotation j) q • normalizedRotation j)=0
  simp only [map_sum,map_smul,smul_eq_mul]
  have hz (j : Fin 3) : contactLinearMap e (normalizedRotation j)=0 := by
    change contactLinear ((Real.sqrt (boundaryWeight (boundaryRotationIndex j)))⁻¹ • boundaryRotation j) e.1 (contactNext e)=0
    rw [contactLinear_smul_spectrum,contactLinear_rotation_zero,mul_zero]
  simp [hz]

theorem contactLinear_sliceProjection (q : TangentCoordinates) (e : ContactIndex) :
    contactLinear (sliceProjection q) e.1 (contactNext e)=contactLinear q e.1 (contactNext e) := by
  change contactLinearMap e (q-rotationProjection q)=contactLinearMap e q
  rw [map_sub]
  change contactLinearMap e q-contactLinear (rotationProjection q) e.1 (contactNext e)=_
  rw [contactLinear_rotationProjection,sub_zero]

theorem contactLinear_kernel (q : TangentCoordinates) :
    (∀ e : ContactIndex, contactLinear q e.1 (contactNext e)=0) ↔ q=rotationProjection q := by
  constructor
  · intro h
    have hslice := contact_spectrum_physical_unweighted (sliceProjection q) (sliceProjection_mem q)
    simp only [contactLinear_sliceProjection,h,zero_pow (by decide : 2≠0),Finset.sum_const_zero] at hslice
    have hz : sliceProjection q=0 := by
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (sliceProjection q)]
    exact sub_eq_zero.mp hz
  · intro h e
    rw [h]
    exact contactLinear_rotationProjection q e

#print axioms contactLinear_kernel
end Blueprint.Thomson.Tail.Implementation
