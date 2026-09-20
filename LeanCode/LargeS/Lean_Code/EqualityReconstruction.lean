import Lean_Code.RegularSquare
import Lean_Code.ExteriorTriangle

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Reconstruct the eight vertices from one regular square and its four
exterior contact triangles. The packing bound rules out the inward roots. -/
theorem regular_square_cross_contact_reconstruction (Y : Fin 8 → ℝ³)
    (hY : ∀ i, ‖Y i‖ = 1) (hpacking : PackingInnerBound aInf Y)
    (hgram : ∀ i j : Fin 4,
      inner ℝ (Y (Fin.castAdd 4 i)) (Y (Fin.castAdd 4 j)) =
        rhombusGram aInf (2 * aInf - 1) (2 * aInf - 1) i j)
    (hcross0 : ∀ j : Fin 4, inner ℝ (Y (Fin.castAdd 4 j)) (Y (Fin.natAdd 4 j)) = aInf)
    (hcross1 : ∀ j : Fin 4, inner ℝ (Y (Fin.castAdd 4 (j + 1))) (Y (Fin.natAdd 4 j)) = aInf) :
    Congruent Y P := by
  obtain ⟨U, hU⟩ := square_gram_congruent (fun j => Y (Fin.castAdd 4 j)) aInf aInf_mem_Ioo hgram
  let W : Fin 8 → ℝ³ := fun i => U.symm (Y i)
  have hWinner : ∀ i j, inner ℝ (W i) (W j) = inner ℝ (Y i) (Y j) := by
    intro i j
    exact U.symm.inner_map_map (Y i) (Y j)
  have hWnorm : ∀ i, ‖W i‖ = 1 := by intro i; simpa [W] using hY i
  have hupper : ∀ j : Fin 4, W (Fin.castAdd 4 j) = Xc aInf (Fin.castAdd 4 j) := by
    intro j
    change U.symm (Y (Fin.castAdd 4 j)) = _
    rw [← hU j, U.symm_apply_apply]
  have hlower : ∀ j : Fin 4, W (Fin.natAdd 4 j) = Xc aInf (Fin.natAdd 4 j) := by
    intro j
    apply exterior_triangle_vertex_cyclic j (W (Fin.natAdd 4 j)) (hWnorm _)
    · rw [← hupper j, hWinner]
      exact hcross0 j
    · rw [← hupper (j + 1), hWinner]
      exact hcross1 j
    · rw [← hupper (j + 2), hWinner]
      apply hpacking
      intro heq
      have := congrArg Fin.val heq
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega
  refine ⟨U.symm, Equiv.refl _, ?_⟩
  intro i
  change P i = W i
  rw [P, X_eq_Xc]
  rcases finEight_split i with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact (hupper j).symm
  · exact (hlower j).symm

theorem relabeled_regular_square_cross_contact_reconstruction
    (Y : Fin 8 → ℝ³) (e : Equiv.Perm (Fin 8))
    (hY : ∀ i, ‖Y i‖ = 1) (hpacking : PackingInnerBound aInf Y)
    (hgram : ∀ i j : Fin 4,
      inner ℝ (Y (e (Fin.castAdd 4 i))) (Y (e (Fin.castAdd 4 j))) =
        rhombusGram aInf (2 * aInf - 1) (2 * aInf - 1) i j)
    (hcross0 : ∀ j : Fin 4,
      inner ℝ (Y (e (Fin.castAdd 4 j))) (Y (e (Fin.natAdd 4 j))) = aInf)
    (hcross1 : ∀ j : Fin 4,
      inner ℝ (Y (e (Fin.castAdd 4 (j + 1)))) (Y (e (Fin.natAdd 4 j))) = aInf) :
    Congruent Y P := by
  have hbound : PackingInnerBound aInf (fun i => Y (e i)) := by
    intro i j hij
    exact hpacking (e i) (e j) (fun h => hij (e.injective h))
  obtain ⟨U, f, hf⟩ := regular_square_cross_contact_reconstruction (fun i => Y (e i))
    (fun i => hY (e i)) hbound hgram hcross0 hcross1
  exact ⟨U, f.trans e, hf⟩

lemma congruent_of_model_point_witnesses (Y : Fin 8 → ℝ³) (U : ℝ³ ≃ₗᵢ[ℝ] ℝ³)
    (hwitness : ∀ i : Fin 8, ∃ j : Fin 8, P i = U (Y j)) : Congruent Y P := by
  choose f hf using hwitness
  have hinj : Function.Injective f := by
    intro i j hij
    apply P_isConfiguration.2
    rw [hf i, hf j, hij]
  let e : Equiv.Perm (Fin 8) := Equiv.ofBijective f ⟨hinj, Finite.surjective_of_injective hinj⟩
  exact ⟨U, e, hf⟩

/-- A single regular square with a contact triangle on each boundary edge
already reconstructs all eight points. Distinctness and exhaustion of the
four exterior vertices follow from the reconstruction, so no separate
classification of the cross-edge cycles is needed. -/
theorem square_triangle_witness_reconstruction (Y : Fin 8 → ℝ³) (Q : Fin 4 → Fin 8)
    (hY : ∀ i, ‖Y i‖ = 1) (hpacking : PackingInnerBound aInf Y)
    (hgram : ∀ i j : Fin 4, inner ℝ (Y (Q i)) (Y (Q j)) =
      rhombusGram aInf (2 * aInf - 1) (2 * aInf - 1) i j)
    (htriangle : ∀ j : Fin 4, ∃ k : Fin 8,
      (∀ i : Fin 4, k ≠ Q i) ∧ inner ℝ (Y (Q j)) (Y k) = aInf ∧
        inner ℝ (Y (Q (j + 1))) (Y k) = aInf) : Congruent Y P := by
  obtain ⟨U, hU⟩ := square_gram_congruent (fun j => Y (Q j)) aInf aInf_mem_Ioo hgram
  have hupper : ∀ j : Fin 4, U.symm (Y (Q j)) = Xc aInf (Fin.castAdd 4 j) := by
    intro j
    rw [← hU j, U.symm_apply_apply]
  have hlower : ∀ j : Fin 4, ∃ k : Fin 8, U.symm (Y k) = Xc aInf (Fin.natAdd 4 j) := by
    intro j
    obtain ⟨k, hk, h0, h1⟩ := htriangle j
    refine ⟨k, exterior_triangle_vertex_cyclic j (U.symm (Y k)) (by simpa using hY k) ?_ ?_ ?_⟩
    · rw [← hupper j, U.symm.inner_map_map]
      exact h0
    · rw [← hupper (j + 1), U.symm.inner_map_map]
      exact h1
    · rw [← hupper (j + 2), U.symm.inner_map_map]
      exact hpacking _ _ (Ne.symm (hk (j + 2)))
  apply congruent_of_model_point_witnesses Y U.symm
  intro i
  rw [P, X_eq_Xc]
  rcases finEight_split i with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact ⟨Q j, (hupper j).symm⟩
  · obtain ⟨k, hk⟩ := hlower j
    exact ⟨k, hk.symm⟩

theorem regular_square_triangle_witness_reconstruction (Y : Fin 8 → ℝ³) (Q : Fin 4 → Fin 8)
    (hY : IsConfiguration Y) (hQ : Function.Injective Q) (hpacking : PackingInnerBound aInf Y)
    (hside : ∀ j : Fin 4, inner ℝ (Y (Q j)) (Y (Q (j + 1))) = aInf)
    (hangle : contactAngle aInf (Y (Q 1)) (Y (Q 3)) = contactAngle aInf (Y (Q 0)) (Y (Q 2)))
    (htriangle : ∀ j : Fin 4, ∃ k : Fin 8,
      (∀ i : Fin 4, k ≠ Q i) ∧ inner ℝ (Y (Q j)) (Y k) = aInf ∧
        inner ℝ (Y (Q (j + 1))) (Y k) = aInf) : Congruent Y P := by
  have hunit : ∀ j : Fin 4, ‖Y (Q j)‖ = 1 := fun j => hY.1 (Q j)
  have h01 : inner ℝ (Y (Q 0)) (Y (Q 1)) = aInf := hside 0
  have h12 : inner ℝ (Y (Q 1)) (Y (Q 2)) = aInf := hside 1
  have h23 : inner ℝ (Y (Q 2)) (Y (Q 3)) = aInf := hside 2
  have h30 : inner ℝ (Y (Q 3)) (Y (Q 0)) = aInf := hside 3
  have h02 : Y (Q 0) ≠ Y (Q 2) := fun h => (by decide : (0 : Fin 4) ≠ 2) (hQ (hY.2 h))
  have h13 : Y (Q 1) ≠ Y (Q 3) := fun h => (by decide : (1 : Fin 4) ≠ 3) (hQ (hY.2 h))
  obtain ⟨hd02, hd13⟩ := regular_square_diagonals (fun j => Y (Q j)) aInf hunit
    aInf_mem_Ioo h02 h13 h01 h12 h23 h30 hangle
  apply square_triangle_witness_reconstruction Y Q hY.1 hpacking
    (square_gram_of_diagonals (fun j => Y (Q j)) aInf hunit h01 h12 h23 h30 hd02 hd13) htriangle

end SquareAntiprismVerification
