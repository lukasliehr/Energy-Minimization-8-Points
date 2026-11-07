import AllS.Units.N_GI.N_boundary_basis.N_basis_of_slice
import AllS.Units.N_GI.N_boundary_basis.N_rational_algebra

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def boundaryDiagonal : Fin 13 → ℝ :=
  ![boundaryM,boundaryZ,boundaryZ,boundaryM,boundaryM,boundaryZ,boundaryZ,boundaryM,boundaryM,
    boundaryT,boundaryT,boundaryZ,boundaryM]

def boundaryScaled (j : Fin 13) : TangentCoordinates :=
  √(boundaryDiagonal j) • boundaryFourier j

def boundaryCoefficient : Fin 13 → ℝ :=
  ![(√2/4)/(packingZHeight*packingRadius),1/(2*packingRadius),1/(2*packingRadius),
    1/(2*packingZHeight*packingRadius),1/(2*packingZHeight*packingRadius),
    1/(2*packingRadius),1/(2*packingRadius),1/(2*packingZHeight*packingRadius),
    1/(2*packingZHeight*packingRadius),1/(2*packingRadius),1/(2*packingRadius),
    (√2/4)/packingRadius,(√2/4)/(packingZHeight*packingRadius)]

theorem boundaryDiagonal_pos (j : Fin 13) : 0<boundaryDiagonal j := by
  fin_cases j <;> dsimp [boundaryDiagonal,boundaryM,boundaryZ,boundaryT] <;> positivity

theorem sqrt_ratio_of_sq (d w c : ℝ) (hd : 0≤d) (hw : 0<w) (hc : 0≤c)
    (he : c^2*w=d) : √d/√w=c := by
  apply (div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr hw))).mpr
  have hds := Real.sq_sqrt hd
  have hws := Real.sq_sqrt hw.le
  have hp := mul_nonneg hc (Real.sqrt_nonneg w)
  have hcs : (c*√w)^2=d := by rw [mul_pow,hws,he]
  nlinarith [Real.sqrt_nonneg d]

theorem boundaryCoefficient_sq (j : Fin 13) :
    boundaryCoefficient j^2*boundaryWeight (boundaryBasisIndex j)=boundaryDiagonal j := by
  obtain ⟨hH,hR,_,_⟩ := packing_parameters
  obtain ⟨hz,hm,ht,hh⟩ := boundary_field_identities
  have hnH : packingZHeight≠0 := ne_of_gt hH
  have hnR : packingRadius≠0 := ne_of_gt hR
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  fin_cases j <;> norm_num [boundaryCoefficient,boundaryWeight,boundaryBasisIndex,boundaryDiagonal] <;>
    field_simp <;> norm_num [hs] <;> nlinarith [hz,hm,ht]

theorem boundaryScaled_raw (j : Fin 13) :
    boundaryScaled j=boundaryCoefficient j • boundaryRaw (boundaryBasisIndex j) := by
  have hc : 0≤boundaryCoefficient j := by
    obtain ⟨hH,hR,_,_⟩ := packing_parameters
    fin_cases j <;> dsimp [boundaryCoefficient] <;> positivity
  have h := sqrt_ratio_of_sq (boundaryDiagonal j) (boundaryWeight (boundaryBasisIndex j))
    (boundaryCoefficient j) (boundaryDiagonal_pos j).le (boundaryWeight_pos _) hc (boundaryCoefficient_sq j)
  simp only [boundaryScaled,boundaryFourier,boundaryNormalized,smul_smul,←div_eq_mul_inv,h]

theorem boundaryScaled_gram (j k : Fin 13) :
    inner ℝ (boundaryScaled j) (boundaryScaled k)=if j=k then boundaryDiagonal j else 0 := by
  have h := orthonormal_iff_ite.mp boundaryFourier_orthonormal j k
  simp only [boundaryScaled,inner_smul_left,inner_smul_right,starRingEnd_apply,star_trivial,h]
  split_ifs with he
  · subst k
    nlinarith [Real.sq_sqrt (boundaryDiagonal_pos j).le]
  · ring

#print axioms boundaryScaled_raw
#print axioms boundaryScaled_gram
end Blueprint.Thomson.Tail.Implementation
