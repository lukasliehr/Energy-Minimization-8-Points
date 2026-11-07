import AllS.Units.N_GI.N_sphere_euler.N_euler_exact
import AllS.Units.N_GI.N_degree.N_degree_four

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

def degreeThreeVertices (Y : Fin 8 → Point) (c : ℝ) : Finset (Fin 8) := by
  classical
  exact Finset.univ.filter (fun v => Fintype.card (ContactNeighbor Y c v) = 3)

theorem contactNeighbor_card_eq (Y : Fin 8 → Point) (c : ℝ) (v : Fin 8) :
    Fintype.card (ContactNeighbor Y c v) = (contactNeighborsWithin Y c Finset.univ v).card := by
  classical
  simp only [ContactNeighbor, Fintype.card_subtype, contactNeighborsWithin, Finset.mem_univ, true_and]

theorem sphere_euler_degree_sum (Y : Fin 8 → Point) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c < 3/10) (hirr : PackingIrreducible c Y)
    (hbound : PackingInnerBound c Y) (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport) :
    Fintype.card (ContactDart Y c) + (degreeThreeVertices Y c).card = 32 ∧
      (degreeThreeVertices Y c).card ≤ 8 := by
  classical
  have hactive := covering_no_rattlers Y c hY hc hcupper hirr hbound hne hsupport
  have hv (v : Fin 8) : Fintype.card (ContactNeighbor Y c v) +
      (if Fintype.card (ContactNeighbor Y c v) = 3 then 1 else 0) = 4 := by
    have h := degree_degree_four Y c hY hc.1 hcupper hirr hbound v (hactive v)
    rw [← contactNeighbor_card_eq] at h
    split_ifs <;> omega
  have hs := congrArg (fun f : Fin 8 → ℕ => ∑ v, f v) (funext hv)
  have hk : (∑ v : Fin 8, if Fintype.card (ContactNeighbor Y c v) = 3 then 1 else 0) =
      (degreeThreeVertices Y c).card := by
    simp only [degreeThreeVertices, Finset.card_filter]
  simp only [Finset.sum_add_distrib, hk, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at hs
  constructor
  · simpa only [ContactDart, Fintype.card_sigma] using hs
  · simpa using Finset.card_le_univ (degreeThreeVertices Y c)

theorem sphere_euler_vertex_face_counts (T Q E k : ℕ)
    (heuler : T + 2*Q = 12) (hdarts : 3*T + 4*Q = 2*E)
    (hdegree : 2*E + k = 32) (hk : k ≤ 8) :
    (8 : ℤ) - (E : ℤ) + ((T : ℤ) + (Q : ℤ)) = 2 ∧
      T = 8-k ∧ 2*Q = 4+k ∧ (k=0 ∨ k=2 ∨ k=4 ∨ k=6 ∨ k=8) := by
  omega

#print axioms sphere_euler_degree_sum
#print axioms sphere_euler_vertex_face_counts

end Blueprint.Thomson.Tail.Implementation
