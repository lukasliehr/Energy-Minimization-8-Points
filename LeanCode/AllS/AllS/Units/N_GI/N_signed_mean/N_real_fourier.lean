import AllS.Units.N_GI.N_boundary_basis.N_definitions

set_option maxHeartbeats 4000000
noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

/-- Real cosine/sine coordinates for the eight cyclic Fourier modes. -/
def meanScalarRaw (j i : Fin 8) : ℝ :=
  (![1,angularCos i,angularSin i,boundaryCos2 i,boundarySin2 i,
    boundaryCos3 i,boundarySin3 i,layerSign i] : Fin 8 → ℝ) j

def meanScalarWeight (j : Fin 8) : ℝ := if j=0 ∨ j=7 then 8 else 4

def meanScalarVector (j : Fin 8) : EuclideanSpace ℝ (Fin 8) := WithLp.toLp 2 (meanScalarRaw j)

def meanTangentRaw (j : Fin 8 × Fin 2) : TangentCoordinates :=
  WithLp.toLp 2 (fun ik => if ik.2=j.2 then meanScalarRaw j.1 ik.1 else 0)

theorem meanScalarRaw_gram (j k : Fin 8) :
    (∑ i : Fin 8,meanScalarRaw j i*meanScalarRaw k i)=if j=k then meanScalarWeight j else 0 := by
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hpos : 0<√(2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hinv : (√(2:ℝ))⁻¹=√2/2 := by field_simp; nlinarith
  fin_cases j <;> fin_cases k <;>
    norm_num [meanScalarRaw,meanScalarWeight,Fin.sum_univ_succ,angularCos,angularSin,
      boundaryCos2,boundarySin2,boundaryCos3,boundarySin3,layerSign,div_eq_mul_inv,hinv] <;>
    ring_nf <;> simp [hs] <;> ring

theorem meanScalarWeight_pos (j : Fin 8) : 0 < meanScalarWeight j := by
  unfold meanScalarWeight
  split_ifs <;> norm_num

theorem meanScalarVector_gram (j k : Fin 8) :
    inner ℝ (meanScalarVector j) (meanScalarVector k)=if j=k then meanScalarWeight j else 0 := by
  simpa [meanScalarVector,PiLp.inner_apply,Real.inner_apply,mul_comm] using meanScalarRaw_gram j k

theorem meanTangentRaw_gram (j k : Fin 8 × Fin 2) :
    inner ℝ (meanTangentRaw j) (meanTangentRaw k)=if j=k then meanScalarWeight j.1 else 0 := by
  rcases j with ⟨j,b⟩
  rcases k with ⟨k,c⟩
  fin_cases b <;> fin_cases c <;>
    simp [meanTangentRaw,PiLp.inner_apply,Fintype.sum_prod_type,Fin.sum_univ_two,
      Real.inner_apply,mul_comm,meanScalarRaw_gram]

def meanScalarNormalized (j : Fin 8) : EuclideanSpace ℝ (Fin 8) :=
  (√(meanScalarWeight j))⁻¹ • meanScalarVector j

def meanTangentNormalized (j : Fin 8 × Fin 2) : TangentCoordinates :=
  (√(meanScalarWeight j.1))⁻¹ • meanTangentRaw j

theorem meanScalarNormalized_orthonormal : Orthonormal ℝ meanScalarNormalized := by
  rw [orthonormal_iff_ite]
  intro i j
  simp only [meanScalarNormalized,real_inner_smul_left,real_inner_smul_right,meanScalarVector_gram]
  split_ifs with h
  · subst j
    have hn := Real.sqrt_pos.mpr (meanScalarWeight_pos i)
    have hs := Real.sq_sqrt (meanScalarWeight_pos i).le
    field_simp
    nlinarith
  · ring

theorem meanTangentNormalized_orthonormal : Orthonormal ℝ meanTangentNormalized := by
  rw [orthonormal_iff_ite]
  intro i j
  simp only [meanTangentNormalized,real_inner_smul_left,real_inner_smul_right,meanTangentRaw_gram]
  split_ifs with h
  · subst j
    have hn := Real.sqrt_pos.mpr (meanScalarWeight_pos i.1)
    have hs := Real.sq_sqrt (meanScalarWeight_pos i.1).le
    field_simp
    nlinarith
  · ring

def meanScalarBasis : OrthonormalBasis (Fin 8) ℝ (EuclideanSpace ℝ (Fin 8)) :=
  let b := basisOfOrthonormalOfCardEqFinrank meanScalarNormalized_orthonormal (by simp)
  b.toOrthonormalBasis (by simpa [b] using meanScalarNormalized_orthonormal)

def meanTangentBasis : OrthonormalBasis (Fin 8 × Fin 2) ℝ TangentCoordinates :=
  let b := basisOfOrthonormalOfCardEqFinrank meanTangentNormalized_orthonormal (by simp [TangentCoordinates])
  b.toOrthonormalBasis (by simpa [b] using meanTangentNormalized_orthonormal)

theorem meanScalarBasis_apply (j : Fin 8) : meanScalarBasis j=meanScalarNormalized j := by
  simp [meanScalarBasis]

theorem meanTangentBasis_apply (j : Fin 8 × Fin 2) : meanTangentBasis j=meanTangentNormalized j := by
  simp [meanTangentBasis]

#print axioms meanTangentBasis_apply
end Blueprint.Thomson.Tail.Implementation
