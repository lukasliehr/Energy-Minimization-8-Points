import AllS.Units.N_FI.N_zero_tensors.N_equivalence

namespace Blueprint.Thomson.Finite

theorem vertex_moments_zero_tensors (Y : Fin 8 → Point) :
    ((∀ i, (∑ j, inner ℝ (Y i) (Y j))=0 ∧ (∑ j, (inner ℝ (Y i) (Y j))^3)=0) ↔
      (∑ i, Y i)=0 ∧ oddMoment 3 Y=0) ∧
    ((∑ i, Y i)=0 → oddMoment 3 Y=0 →
      ∀ x : Point, (∑ j, inner ℝ x (Y j))=0 ∧ (∑ j, (inner ℝ x (Y j))^3)=0) :=
  ⟨zero_tensors_equivalence Y, fun h1 h3 x => zero_tensors_arbitrary_moments Y h1 h3 x⟩

#check vertex_moments_zero_tensors
#print axioms vertex_moments_zero_tensors
end Blueprint.Thomson.Finite
