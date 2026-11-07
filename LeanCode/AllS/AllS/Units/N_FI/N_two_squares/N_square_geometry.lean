import AllS.Units.N_FI.N_two_squares.N_common_A
import AllS.Units.N_FI.N_geometry.N_gram_entries
import Lean_Code.RegularSquare

noncomputable section
open Real
namespace Blueprint.Thomson.Finite

/-- An actual ordered square, represented by an isometry of the target upper square. -/
structure SquareRealization (a : ℝ) (Y : Fin 8 → Point) where
  label : Fin 4 → Fin 8
  injective : Function.Injective label
  isometry : Point ≃ₗᵢ[ℝ] Point
  points : ∀ i, Y (label i)=isometry (X a (Fin.castAdd 4 i))

def SquareRealization.labels {a : ℝ} {Y : Fin 8 → Point} (S : SquareRealization a Y) : Finset (Fin 8) :=
  Finset.univ.image S.label

def SquareRealization.center {a : ℝ} {Y : Fin 8 → Point} (S : SquareRealization a Y) : Point :=
  S.isometry !₂[0,0,√a]

theorem SquareRealization.card {a : ℝ} {Y : Fin 8 → Point} (S : SquareRealization a Y) :
    S.labels.card=4 := by simp [labels,Finset.card_image_of_injective _ S.injective]

theorem SquareRealization.gram {a : ℝ} {Y : Fin 8 → Point} (S : SquareRealization a Y)
    (ha : physical a) (i j : Fin 4) :
    inner ℝ (Y (S.label i)) (Y (S.label j))=
      if i=j then 1 else contacts a (candidateContactLabel (Fin.castAdd 4 i) (Fin.castAdd 4 j)) := by
  rw [S.points,S.points,S.isometry.inner_map_map,candidate_gram_entry a ha]
  by_cases hij : i=j
  · subst j
    simp
  · rw [if_neg hij,if_neg (show Fin.castAdd 4 i ≠ Fin.castAdd 4 j from
      fun he => hij (Fin.ext (congrArg (fun k : Fin 8 => k.val) he)))]

def squareLocalNeighbors (i : Fin 4) (k : Fin 4) : Finset (Fin 4) :=
  Finset.univ.filter (fun j => j ≠ i ∧ candidateContactLabel (Fin.castAdd 4 i) (Fin.castAdd 4 j)=k)

theorem squareLocalNeighbors_card (i k : Fin 4) (hk : k=0 ∨ k=1) :
    (squareLocalNeighbors i k).card=baselineCounts k := by
  have hf : ∀ i k : Fin 4, k=0 ∨ k=1 → (squareLocalNeighbors i k).card=baselineCounts k := by decide
  exact hf i k hk

theorem SquareRealization.neighbors {a : ℝ} {Y : Fin 8 → Point} (S : SquareRealization a Y)
    (h : ContactCountData a Y) (i k : Fin 4) (hk : k=0 ∨ k=1) :
    contactNeighbors a Y (S.label i) k=(squareLocalNeighbors i k).image S.label := by
  classical
  have hsub : (squareLocalNeighbors i k).image S.label ⊆ contactNeighbors a Y (S.label i) k := by
    intro l hl
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨hji,hkij⟩ := (Finset.mem_filter.mp hj).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,S.injective.ne hji,?_⟩
    rw [S.gram h.physical,if_neg (Ne.symm hji),hkij]
  apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [Finset.card_image_of_injective _ S.injective,squareLocalNeighbors_card i k hk]
  have hc := congrFun (h.counts (S.label i)) k
  exact le_of_eq hc

theorem SquareRealization.closed_AB {a : ℝ} {Y : Fin 8 → Point} (S : SquareRealization a Y)
    (h : ContactCountData a Y) (i j : Fin 8) (hi : i ∈ S.labels) (hij : i ≠ j)
    (hc : inner ℝ (Y i) (Y j)=contacts a 0 ∨ inner ℝ (Y i) (Y j)=contacts a 1) : j ∈ S.labels := by
  classical
  obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hi
  have one (k : Fin 4) (hk : k=0 ∨ k=1) (hprod : inner ℝ (Y (S.label u)) (Y j)=contacts a k) : j ∈ S.labels := by
    have hj : j ∈ contactNeighbors a Y (S.label u) k :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,Ne.symm hij,hprod⟩
    rw [S.neighbors h u k hk] at hj
    obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩
  exact hc.elim (one 0 (Or.inl rfl)) (one 1 (Or.inr rfl))

theorem SquareRealization.sum {a : ℝ} {Y : Fin 8 → Point} (S : SquareRealization a Y) :
    (∑ i ∈ S.labels, Y i)=(4:ℝ) • S.center := by
  classical
  rw [labels,Finset.sum_image (fun i _ j _ hij => S.injective hij)]
  simp_rw [S.points]
  rw [← map_sum]
  have hs : (∑ i : Fin 4, X a (Fin.castAdd 4 i))=(4:ℝ) • (!₂[0,0,√a] : Point) := by
    ext j
    fin_cases j <;> simp [Fin.sum_univ_four,X] <;> ring
  rw [hs,map_smul]
  rfl

theorem SquareRealization.center_norm {a : ℝ} {Y : Fin 8 → Point} (S : SquareRealization a Y)
    (ha : 0 ≤ a) : ‖S.center‖^2=a := by
  rw [center,S.isometry.norm_map]
  rw [← real_inner_self_eq_norm_sq]
  rw [PiLp.inner_apply]
  norm_num [Fin.sum_univ_succ,← pow_two,Real.sq_sqrt ha]

#print axioms SquareRealization.closed_AB
#print axioms SquareRealization.sum
end Blueprint.Thomson.Finite
