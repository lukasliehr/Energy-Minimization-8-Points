import AllS.Units.N_GI.N_tiling_data.N_construct_existing_data
import Lean_Code.BoundaryAdjacency

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem tiling_data_reindex_sum {M : Type*} [AddCommMonoid M]
    {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y} {hc : c ∈ Set.Ioo (0:ℝ) 1}
    (C : ContactBoundaryCycle Y c hY hc) {n : ℕ} (hlen : C.size+1=n) (w : Fin 8 → M) :
    (∑ j : Fin n, w (C.reindex hlen j)) = ∑ i, w (C.vertex i) := by
  exact Equiv.sum_comp (finIndexEquiv hlen.symm) (fun i => w (C.vertex i))

theorem tiling_data_array_sum {M : Type*} [AddCommMonoid M]
    (Y : Fin 8 → Point) (c : ℝ) (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1)
    (n : ℕ) (w : Fin 8 → M) :
    (∑ f, ∑ j, w (boundaryArray Y c hY hc n f j)) =
      ∑ f : BoundaryOfLength Y c hY hc n, ∑ i, w ((boundaryOrbitCycle Y c hY hc f.val).vertex i) := by
  classical
  let e := (Fintype.equivFin (BoundaryOfLength Y c hY hc n)).symm
  calc
    _ = ∑ f, ∑ i, w ((boundaryOrbitCycle Y c hY hc (e f).val).vertex i) := by
      apply Finset.sum_congr rfl
      intro f _
      exact tiling_data_reindex_sum (boundaryOrbitCycle Y c hY hc (e f).val) (e f).property w
    _ = _ := Equiv.sum_comp e (fun f => ∑ i, w ((boundaryOrbitCycle Y c hY hc f.val).vertex i))

theorem tiling_data_face_arrays {M : Type*} [AddCommMonoid M]
    (Y : Fin 8 → Point) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10) (hirr : PackingIrreducible c Y)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport) (w : Fin 8 → M) :
    (∑ f, ∑ j, w (boundaryArray Y c hY hc 3 f j)) +
      (∑ f, ∑ j, w (boundaryArray Y c hY hc 4 f j)) =
      ∑ d : ContactDart Y c, w d.1 := by
  rw [tiling_data_array_sum, tiling_data_array_sum]
  exact (tiling_data_partition_by_length Y c hY hc hcupper hirr hsupport
    (fun f => ∑ i, w ((boundaryOrbitCycle Y c hY hc f).vertex i))).trans
    (sum_over_permutation_cycles (contactFaceNext Y c hY hc) (fun d => w d.1))

theorem tiling_data_vertex_incidence (Y : Fin 8 → Point) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10) (hirr : PackingIrreducible c Y)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport) (v : Fin 8) :
    faceCornerCount (boundaryArray Y c hY hc 3) v +
      faceCornerCount (boundaryArray Y c hY hc 4) v = Fintype.card (ContactNeighbor Y c v) := by
  classical
  have h := tiling_data_face_arrays Y c hY hc hcupper hirr hsupport
    (fun i => if i=v then (1:ℕ) else 0)
  have hr : (∑ d : ContactDart Y c, if d.1=v then (1:ℕ) else 0) =
      Fintype.card (ContactNeighbor Y c v) := by
    rw [Fintype.sum_sigma, Finset.sum_eq_single v]
    · simp
    · intro i _ hiv
      simp [hiv]
    · simp
  rw [hr] at h
  simpa only [faceCornerCount, faceCornersAt, Finset.card_filter, Fintype.sum_prod_type] using h

#print axioms tiling_data_face_arrays
#print axioms tiling_data_vertex_incidence
theorem tiling_data_boundary_adjacency (Y : Fin 8 → Point) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (hcupper : c < 3/10) (hirr : PackingIrreducible c Y)
    (hbound : PackingInnerBound c Y) (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport) :
    (tiling_data_construct_existing_data Y c hY hc hcupper hirr hbound hne hsupport).BoundaryAdjacency := by
  classical
  intro f k
  let b : BoundaryOfLength Y c hY hc 4 := (Fintype.equivFin (BoundaryOfLength Y c hY hc 4)).symm f
  let C := boundaryOrbitCycle Y c hY hc b.val
  let i : Fin (C.size + 1) := Fin.cast b.property.symm k
  have hk : boundaryArray Y c hY hc 4 f k = C.vertex i := rfl
  have hknext : boundaryArray Y c hY hc 4 f (k + 1) = C.vertex (i + 1) := by
    change C.vertex (Fin.cast b.property.symm (k + 1)) = _
    rw [fin_cast_add_one]
  obtain ⟨g, j, hgf, hreverse⟩ := opposite_boundary_orbit Y c hY hc hirr hsupport b.val i
  let D := boundaryOrbitCycle Y c hY hc g
  have hbase : D.vertex j = C.vertex (i + 1) := by
    rw [C.vertex_next]
    exact congrArg Sigma.fst hreverse
  have htip : D.vertex (j + 1) = C.vertex i := by
    rw [D.vertex_next]
    exact congrArg (fun d : ContactDart Y c => d.2.val) hreverse
  have hlength := face_lengths_length_three_four D hirr hcupper (hsupport D)
  change (∃ t : Fin 8, (∀ l : Fin 4, t ≠ boundaryArray Y c hY hc 4 f l) ∧
      inner ℝ (Y (boundaryArray Y c hY hc 4 f k)) (Y t) = c ∧
      inner ℝ (Y (boundaryArray Y c hY hc 4 f (k + 1))) (Y t) = c) ∨
    (∃ g' : Fin (Fintype.card (BoundaryOfLength Y c hY hc 4)), g' ≠ f ∧
      ∃ l : Fin 4, boundaryArray Y c hY hc 4 g' l = boundaryArray Y c hY hc 4 f k)
  rcases hlength with h3 | h4
  · left
    let t := D.vertex (j + 1 + 1)
    have hturn := D.strict_turn hirr j
    have houtside : inner ℝ (crossVec (Y (C.vertex i)) (Y (C.vertex (i + 1)))) (Y t) < 0 := by
      rw [hbase, htip, crossVec_swap, inner_neg_left] at hturn
      change 0 < -inner ℝ (crossVec (Y (C.vertex i)) (Y (C.vertex (i + 1)))) (Y t) at hturn
      linarith
    refine ⟨t, ?_, ?_, ?_⟩
    · intro l heq
      have hl := C.edge_vertex_nonneg (hsupport C) i (Fin.cast b.property.symm l)
      change 0 ≤ inner ℝ (crossVec (Y (C.vertex i)) (Y (C.vertex (i + 1))))
        (Y (boundaryArray Y c hY hc 4 f l)) at hl
      rw [← heq] at hl
      linarith
    · rw [hk, ← htip]
      exact D.contact (j + 1)
    · rw [hknext, ← hbase]
      apply D.triangle_contacts h3
      intro h
      have ht := D.strict_turn hirr j
      rw [← h, crossVec_inner_left] at ht
      exact lt_irrefl 0 ht
  · right
    let b' : BoundaryOfLength Y c hY hc 4 := ⟨g, h4⟩
    let f' := (Fintype.equivFin (BoundaryOfLength Y c hY hc 4)) b'
    refine ⟨f', ?_, Fin.cast h4 (j + 1), ?_⟩
    · intro heq
      have hb : b' = b := by
        have h := congrArg (Fintype.equivFin (BoundaryOfLength Y c hY hc 4)).symm heq
        simpa only [f', Equiv.symm_apply_apply] using h
      exact hgf (congrArg Subtype.val hb)
    · rw [hk]
      change boundaryArray Y c hY hc 4 ((Fintype.equivFin (BoundaryOfLength Y c hY hc 4)) b')
        (Fin.cast h4 (j + 1)) = _
      exact (boundaryArray_ofLength Y c hY hc 4 b' (Fin.cast h4 (j+1))).trans htip

#print axioms tiling_data_boundary_adjacency
end Blueprint.Thomson.Tail.Implementation
