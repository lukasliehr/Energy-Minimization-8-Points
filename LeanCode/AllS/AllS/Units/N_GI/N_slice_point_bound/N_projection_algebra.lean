import AllS.Units.N_GI.N_boundary_basis.N_normalized
import AllS.Units.N_GI.N_boundary_basis.N_rotation_coordinates

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def normalizedRotation (j : Fin 3) : TangentCoordinates := boundaryNormalized (boundaryRotationIndex j)

theorem normalizedRotation_orthonormal : Orthonormal ℝ normalizedRotation := by
  apply boundaryNormalized_orthonormal.comp
  intro i j h
  have he := congrArg Fin.val h
  simp only [boundaryRotationIndex] at he
  exact Fin.ext (by omega)

def rotationProjection (v : TangentCoordinates) : TangentCoordinates :=
  ∑ j : Fin 3, inner ℝ (normalizedRotation j) v • normalizedRotation j

def sliceProjection (v : TangentCoordinates) : TangentCoordinates := v-rotationProjection v

theorem rotationProjection_inner (v : TangentCoordinates) (j : Fin 3) :
    inner ℝ (normalizedRotation j) (rotationProjection v)=inner ℝ (normalizedRotation j) v :=
  normalizedRotation_orthonormal.inner_right_fintype _ j

theorem rotationProjection_norm_sq (v : TangentCoordinates) :
    ‖rotationProjection v‖^2=∑ j : Fin 3, (inner ℝ (normalizedRotation j) v)^2 := by
  rw [← real_inner_self_eq_norm_sq]
  simpa only [rotationProjection,starRingEnd_apply,star_trivial,← pow_two] using
    normalizedRotation_orthonormal.inner_sum (fun j=>inner ℝ (normalizedRotation j) v)
      (fun j=>inner ℝ (normalizedRotation j) v) Finset.univ

theorem rotationProjection_inner_self (v : TangentCoordinates) :
    inner ℝ (rotationProjection v) v=∑ j : Fin 3, (inner ℝ (normalizedRotation j) v)^2 := by
  simp [rotationProjection,sum_inner,real_inner_smul_left,pow_two]

theorem sliceProjection_norm_sq (v : TangentCoordinates) :
    ‖sliceProjection v‖^2=‖v‖^2-∑ j : Fin 3, (inner ℝ (normalizedRotation j) v)^2 := by
  rw [sliceProjection,norm_sub_sq_real,rotationProjection_norm_sq,real_inner_comm (rotationProjection v) v,
    rotationProjection_inner_self]
  ring

theorem mem_rotationSlice_iff_normalized (q : TangentCoordinates) :
    q∈rotationSlice ↔ ∀ j, inner ℝ (normalizedRotation j) q=0 := by
  rw [mem_rotationSlice_iff]
  have he (j : Fin 3) : inner ℝ (normalizedRotation j) q=
      (√(boundaryWeight (boundaryRotationIndex j)))⁻¹*inner ℝ (boundaryRotation j) q := by
    simp [normalizedRotation,boundaryNormalized,boundaryRotation,real_inner_smul_left]
  simp_rw [he]
  have hn (j : Fin 3) : (√(boundaryWeight (boundaryRotationIndex j)))⁻¹ ≠ 0 :=
    inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (boundaryWeight_pos _)))
  simp only [mul_eq_zero,hn,false_or]

theorem sliceProjection_mem (v : TangentCoordinates) : sliceProjection v∈rotationSlice := by
  rw [mem_rotationSlice_iff_normalized]
  intro j
  simp [sliceProjection,inner_sub_right,rotationProjection_inner]

theorem sliceProjection_eq_self (q : TangentCoordinates) (hq : q∈rotationSlice) :
    sliceProjection q=q := by
  have h := (mem_rotationSlice_iff_normalized q).mp hq
  simp [sliceProjection,rotationProjection,h]

theorem sliceProjection_inner (q v : TangentCoordinates) (hq : q∈rotationSlice) :
    inner ℝ q (sliceProjection v)=inner ℝ q v := by
  have hz (j : Fin 3) : inner ℝ q (normalizedRotation j)=0 := by
    rw [real_inner_comm]
    exact (mem_rotationSlice_iff_normalized q).mp hq j
  simp [sliceProjection,rotationProjection,inner_sub_right,inner_sum,real_inner_smul_right,hz]

def localEvaluation (i : Fin 8) (u v : ℝ) : TangentCoordinates :=
  WithLp.toLp 2 (fun jk => if jk.1=i then if jk.2=0 then u else v else 0)

theorem localEvaluation_inner (q : TangentCoordinates) (i : Fin 8) (u v : ℝ) :
    inner ℝ q (localEvaluation i u v)=q (i,0)*u+q (i,1)*v := by
  simp [localEvaluation,PiLp.inner_apply,Fintype.sum_prod_type,Fin.sum_univ_two,Real.inner_apply,eq_comm,mul_comm]

theorem localEvaluation_norm_sq (i : Fin 8) (u v : ℝ) :
    ‖localEvaluation i u v‖^2=u^2+v^2 := by
  rw [← real_inner_self_eq_norm_sq,localEvaluation_inner]
  simp [localEvaluation,pow_two]

theorem normalizedRotation_inner_sq (j : Fin 3) (i : Fin 8) (u v : ℝ) :
    (inner ℝ (normalizedRotation j) (localEvaluation i u v))^2=
      (boundaryRawPair (boundaryRotationIndex j) i 0*u+
        boundaryRawPair (boundaryRotationIndex j) i 1*v)^2 / boundaryWeight (boundaryRotationIndex j) := by
  rw [normalizedRotation,boundaryNormalized,real_inner_smul_left,localEvaluation_inner,mul_pow,inv_pow,
    Real.sq_sqrt (boundaryWeight_pos _).le]
  simp [boundaryRaw,div_eq_mul_inv,mul_comm]

#print axioms sliceProjection_inner
end Blueprint.Thomson.Tail.Implementation
