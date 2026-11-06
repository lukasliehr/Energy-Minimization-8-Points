import AllS.Units.N_GI.N_boundary_basis.N_scaling

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def boundaryATriple (i : Fin 8) (w : ℝ) : Point :=
  !₂[-angularSin i*w,angularCos i*w,0]
def boundaryBTriple (i : Fin 8) (w : ℝ) : Point :=
  !₂[-angularCos i*w,-angularSin i*w,layerSign i*w]

def boundaryTriple (j : Fin 13) (i : Fin 8) : Point :=
  (![boundaryBTriple i (√2/4),boundaryATriple i (angularCos i/2),boundaryATriple i (angularSin i/2),
    boundaryBTriple i (angularCos i/2),boundaryBTriple i (angularSin i/2),
    boundaryATriple i (boundaryCos2 i/2),boundaryATriple i (boundarySin2 i/2),
    boundaryBTriple i (boundaryCos2 i/2),boundaryBTriple i (boundarySin2 i/2),
    !₂[(-angularSin i*boundarySin3 i-packingHeight*angularCos i*boundaryCos3 i)/2,
        (angularCos i*boundarySin3 i-packingHeight*angularSin i*boundaryCos3 i)/2,
        layerSign i*packingHeight*boundaryCos3 i/2],
    !₂[(-angularSin i*boundaryCos3 i+packingHeight*angularCos i*boundarySin3 i)/2,
        (angularCos i*boundaryCos3 i+packingHeight*angularSin i*boundarySin3 i)/2,
        -layerSign i*packingHeight*boundarySin3 i/2],
    boundaryATriple i (layerSign i*√2/4),boundaryBTriple i (layerSign i*√2/4)] : Fin 13 → Point) j

def boundaryPhysical (j : Fin 13) (i : Fin 8) : Point := tangentVector (boundaryScaled j) i

set_option maxHeartbeats 4000000 in
theorem boundaryPhysical_triple (j : Fin 13) (i : Fin 8) :
    boundaryPhysical j i= !₂[boundaryTriple j i 0/packingRadius,
      boundaryTriple j i 1/packingRadius,boundaryTriple j i 2/packingZHeight] := by
  obtain ⟨hHp,hRp,hH,hR⟩ := packing_parameters
  have hnH : packingZHeight≠0 := ne_of_gt hHp
  have hnR : packingRadius≠0 := ne_of_gt hRp
  rw [boundaryPhysical,boundaryScaled_raw,tangentVector_smul]
  fin_cases j <;> ext k <;> fin_cases k <;>
    simp [tangentVector,boundaryRaw,boundaryRawPair,boundaryBasisIndex,boundaryCoefficient,
      boundaryTriple,boundaryATriple,boundaryBTriple,azimuthFrame,meridianFrame] <;>
    field_simp <;> ring_nf <;> simp [hH] <;> ring

theorem boundary_reference_dot (i k : Fin 8) (j : Fin 13) :
    inner ℝ (packingReference i) (boundaryPhysical j k)=
      angularCos i*boundaryTriple j k 0+angularSin i*boundaryTriple j k 1+layerSign i*boundaryTriple j k 2 := by
  obtain ⟨hHp,hRp,_,_⟩ := packing_parameters
  have hnH : packingZHeight≠0 := ne_of_gt hHp
  have hnR : packingRadius≠0 := ne_of_gt hRp
  rw [packingReference_formula,boundaryPhysical_triple,PiLp.inner_apply]
  simp [Fin.sum_univ_succ]
  field_simp
  ring

theorem boundary_physical_dot (i k : Fin 8) (j l : Fin 13) :
    inner ℝ (boundaryPhysical j i) (boundaryPhysical l k)=
      boundaryZ*(boundaryTriple j i 0*boundaryTriple l k 0+boundaryTriple j i 1*boundaryTriple l k 1)+
      (1+2*√2)*boundaryTriple j i 2*boundaryTriple l k 2 := by
  obtain ⟨hHp,hRp,_,_⟩ := packing_parameters
  have hnH : packingZHeight≠0 := ne_of_gt hHp
  have hnR : packingRadius≠0 := ne_of_gt hRp
  obtain ⟨hz,_,_,hh⟩ := boundary_field_identities
  have hiR : (packingRadius^2)⁻¹=boundaryZ := by field_simp; nlinarith [hz]
  have hiH : (packingZHeight^2)⁻¹=1+2*√2 := by field_simp; nlinarith [hh]
  rw [boundaryPhysical_triple,boundaryPhysical_triple,PiLp.inner_apply]
  simp only [Fin.sum_univ_succ,Fin.isValue,WithLp.ofLp_toLp,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Matrix.head_cons,Matrix.head_fin_const,Real.inner_apply,Finset.sum_empty,add_zero]
  calc
    _ = (boundaryTriple j i 0*boundaryTriple l k 0+boundaryTriple j i 1*boundaryTriple l k 1)*
        (packingRadius^2)⁻¹+(boundaryTriple j i 2*boundaryTriple l k 2)*(packingZHeight^2)⁻¹ := by ring
    _ = _ := by rw [hiR,hiH]; ring

#print axioms boundaryPhysical_triple
#print axioms boundary_physical_dot
end Blueprint.Thomson.Tail.Implementation
