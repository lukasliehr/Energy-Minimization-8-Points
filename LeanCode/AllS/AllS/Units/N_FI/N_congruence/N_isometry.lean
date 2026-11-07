import AllS.Units.N_FI.N_exclude_six.N_frame

noncomputable section
namespace Blueprint.Thomson.Finite

theorem congruence_isometry (v : Fin 3 → Point) (hv : Orthonormal ℝ v) :
    ∃ U : Point ≃ₗᵢ[ℝ] Point, (∀ x, U x=∑ i, x i • v i) ∧
      ∀ x i, (U.symm x) i=inner ℝ (v i) x := by
  let b := basisOfOrthonormalOfCardEqFinrank hv (by simp [Point])
  let B := b.toOrthonormalBasis (by simpa [b] using hv)
  have hB : (B : Fin 3 → Point)=v := by simp [B,b]
  refine ⟨B.repr.symm,?_,?_⟩
  · intro x
    have he := B.sum_repr_symm x
    rw [hB] at he
    exact he.symm
  · intro x i
    have he := B.repr_apply_apply x i
    rw [hB] at he
    exact he

#check congruence_isometry
#print axioms congruence_isometry
end Blueprint.Thomson.Finite
