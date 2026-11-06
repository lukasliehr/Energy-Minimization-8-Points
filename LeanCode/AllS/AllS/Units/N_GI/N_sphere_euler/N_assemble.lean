import AllS.Units.N_GI.N_sphere_euler.N_vertex_face_counts

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem sphere_euler_assemble (Y : Fin 8 → Point) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c < 3/10) (hirr : PackingIrreducible c Y)
    (hbound : PackingInnerBound c Y) (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport) :
    let T := Fintype.card (BoundaryOfLength Y c hY hc 3)
    let Q := Fintype.card (BoundaryOfLength Y c hY hc 4)
    let E := Fintype.card (PermutationOrbit (contactReverse Y c))
    let k := (degreeThreeVertices Y c).card
    T+2*Q=12 ∧ (8 : ℤ)-(E : ℤ)+((T : ℤ)+(Q : ℤ))=2 ∧
      T=8-k ∧ 2*Q=4+k ∧ (k=0 ∨ k=2 ∨ k=4 ∨ k=6 ∨ k=8) := by
  dsimp only
  have he := sphere_euler_euler_exact Y c hY hc hcupper hirr hbound hne hsupport
  have hd := (tiling_data_counts Y c hY hc hcupper hirr hsupport).2
  rw [contact_reverse_dart_count] at hd
  have hdeg := sphere_euler_degree_sum Y c hY hc hcupper hirr hbound hne hsupport
  rw [contact_reverse_dart_count] at hdeg
  exact ⟨he, sphere_euler_vertex_face_counts _ _ _ _ he hd hdeg.1 hdeg.2⟩

#print axioms sphere_euler_assemble

end Blueprint.Thomson.Tail.Implementation
