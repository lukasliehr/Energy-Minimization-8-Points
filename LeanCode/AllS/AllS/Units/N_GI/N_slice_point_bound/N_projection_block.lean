import AllS.Units.N_GI.N_slice_point_bound.N_projection_algebra

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem boundaryCos3Sin3_unit (i : Fin 8) : (boundaryCos3 i)^2+(boundarySin3 i)^2=1 := by
  obtain ⟨hc,hl⟩ := angular_unit i
  simp only [boundaryCos3,boundarySin3,mul_pow,neg_sq]
  nlinarith

theorem rotation_block_coefficients :
    packingZHeight^2/(4*(1+packingZHeight^2))+1/8=√2/8 ∧
    1/(4*(1+packingZHeight^2))=(3-√2)/8 := by
  obtain ⟨_,_,hH,_⟩ := packing_parameters
  rw [hH]
  have ha : 0<1+packingHeight := by unfold packingHeight; nlinarith [Real.sqrt_nonneg (2:ℝ)]
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  constructor <;> field_simp <;> dsimp [packingHeight] <;> nlinarith

theorem local_rotation_projection_sq (i : Fin 8) (u v : ℝ) :
    (∑ j : Fin 3, (inner ℝ (normalizedRotation j) (localEvaluation i u v))^2)=
      √2/8*u^2+(3-√2)/8*v^2 := by
  simp_rw [normalizedRotation_inner_sq]
  have hunit := boundaryCos3Sin3_unit i
  have hR : packingRadius ≠ 0 := ne_of_gt packing_parameters.2.1
  have hden : 4*(1+packingZHeight^2) ≠ 0 := by positivity
  have hexp :
      (-packingZHeight*boundaryCos3 i*u-boundarySin3 i*v)^2+
      (packingZHeight*boundarySin3 i*u-boundaryCos3 i*v)^2=
      packingZHeight^2*u^2+v^2 := by
    linear_combination (packingZHeight^2*u^2+v^2)*hunit
  have hrot :
      (∑ j : Fin 3,
        (boundaryRawPair (boundaryRotationIndex j) i 0*u+
          boundaryRawPair (boundaryRotationIndex j) i 1*v)^2 / boundaryWeight (boundaryRotationIndex j))=
        (packingZHeight^2/(4*(1+packingZHeight^2))+1/8)*u^2+
          1/(4*(1+packingZHeight^2))*v^2 := by
    norm_num [Fin.sum_univ_succ,boundaryRotationIndex,boundaryRawPair,boundaryWeight]
    field_simp
    nlinarith [hexp]
  rw [hrot,rotation_block_coefficients.1,rotation_block_coefficients.2]

theorem slice_point_bound_projection_block :
    (∀ v : TangentCoordinates, sliceProjection v∈rotationSlice) ∧
    (∀ q : TangentCoordinates, q∈rotationSlice → sliceProjection q=q) ∧
    (∀ q v : TangentCoordinates, q∈rotationSlice → inner ℝ q (sliceProjection v)=inner ℝ q v) ∧
    (∀ (i : Fin 8) (u v : ℝ),
      ‖rotationProjection (localEvaluation i u v)‖^2=√2/8*u^2+(3-√2)/8*v^2) := by
  refine ⟨sliceProjection_mem,sliceProjection_eq_self,sliceProjection_inner,?_⟩
  intro i u v
  rw [rotationProjection_norm_sq,local_rotation_projection_sq]

#print axioms slice_point_bound_projection_block
end Blueprint.Thomson.Tail.Implementation
