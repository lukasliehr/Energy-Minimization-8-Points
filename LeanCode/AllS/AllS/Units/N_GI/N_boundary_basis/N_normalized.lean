import AllS.Units.N_GI.N_boundary_basis.N_raw_gram

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem boundaryNormalized_orthonormal : Orthonormal ℝ boundaryNormalized := by
  rw [orthonormal_iff_ite]
  intro j k
  simp only [boundaryNormalized,inner_smul_left,inner_smul_right,starRingEnd_apply,star_trivial,
    boundaryRaw_gram]
  split_ifs with h
  · subst k
    have hs := Real.sq_sqrt (boundaryWeight_pos j).le
    have hn : √(boundaryWeight j)≠0 := ne_of_gt (Real.sqrt_pos.mpr (boundaryWeight_pos j))
    field_simp
    nlinarith
  · ring

def boundaryCompleteBasis : OrthonormalBasis (Fin 16) ℝ TangentCoordinates :=
  let b := basisOfOrthonormalOfCardEqFinrank boundaryNormalized_orthonormal (by simp [TangentCoordinates])
  b.toOrthonormalBasis (by simpa [b] using boundaryNormalized_orthonormal)

@[simp] theorem boundaryCompleteBasis_apply (j : Fin 16) : boundaryCompleteBasis j=boundaryNormalized j := by
  simp [boundaryCompleteBasis]

theorem boundaryCompleteBasis_expand (q : TangentCoordinates) :
    (∑j,inner ℝ (boundaryNormalized j) q • boundaryNormalized j)=q := by
  simpa using boundaryCompleteBasis.sum_repr' q

#print axioms boundaryNormalized_orthonormal
end Blueprint.Thomson.Tail.Implementation
