import AllS.Units.N_GI.N_cube_parameters.N_duality

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem cube_at_most_one_upper (c : ℝ) (q : Fin 3 → ℝ) (h : CubeEquations c q)
    (i j : Fin 3) (hi : q i=cubeUpper c) (hj : q j=cubeUpper c) : i=j := by
  classical
  by_contra hij
  have hp : (∑k∈({i,j} : Finset (Fin 3)),q k)≤∑k,q k :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun k _ _ => (h.2.1 k).le)
  rw [Finset.sum_pair hij,h.2.2.1,hi,hj] at hp
  unfold cubeUpper at hp
  linarith [h.1]

theorem cube_parameters_active_count (c : ℝ) (q : Fin 3 → ℝ) (h : CubeFeasible c q) :
    (∀i j,q i=cubeUpper c → q j=cubeUpper c → i=j) ∧
    (∀i j,q i=cubeLower c → q j=cubeLower c → i=j) := by
  refine ⟨cube_at_most_one_upper c q h.1,?_⟩
  intro i j hi hj
  obtain ⟨hd,_,hs,_⟩ := cube_parameters_duality c q h
  exact cube_at_most_one_upper c (cubeDual c q) hd.1 i j ((hs i).mpr hi) ((hs j).mpr hj)

#print axioms cube_parameters_active_count
end Blueprint.Thomson.Tail.Implementation
