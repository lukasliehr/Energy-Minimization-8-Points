import AllS.Units.N_G.N_setup

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def separationBudget (p : ℝ) (Z : Fin 8 → Point) : ℝ := squaredEnergy p Z+1
def separationThreshold (p : ℝ) (Z : Fin 8 → Point) : ℝ := (separationBudget p Z)^(-1/p)
def separatedConfigurations (ε : ℝ) : Set (Fin 8 → Point) :=
  {Y | (∀ i, ‖Y i‖=1) ∧ ∀ i j, i ≠ j → ε ≤ squaredDistance Y i j}

theorem squaredEnergy_pairs (p : ℝ) (Y : Fin 8 → Point) :
    squaredEnergy p Y=∑ ij ∈ unorderedPairs, (squaredDistance Y ij.1 ij.2)^(-p) := by
  simp [squaredEnergy,unorderedPairs,Finset.sum_filter,Fintype.sum_prod_type]

theorem squaredEnergy_nonneg (p : ℝ) (Y : Fin 8 → Point) : 0 ≤ squaredEnergy p Y := by
  rw [squaredEnergy_pairs]
  exact Finset.sum_nonneg (fun ij _ => Real.rpow_nonneg (squaredDistance_nonneg Y ij.1 ij.2) _)

theorem squaredEnergy_term_le (p : ℝ) (Y : Fin 8 → Point) (i j : Fin 8) (hij : i ≠ j) :
    (squaredDistance Y i j)^(-p) ≤ squaredEnergy p Y := by
  have one (i j : Fin 8) (hij : i < j) : (squaredDistance Y i j)^(-p) ≤ squaredEnergy p Y := by
    rw [squaredEnergy_pairs]
    exact Finset.single_le_sum (fun ij _ => Real.rpow_nonneg (squaredDistance_nonneg Y ij.1 ij.2) _)
      (mem_unorderedPairs i j |>.mpr hij)
  rcases lt_or_gt_of_ne hij with hij | hij
  · exact one i j hij
  · rw [squaredDistance_symm]
    exact one j i hij

theorem minimizer_exists_separation_threshold (p : ℝ) (Z : Fin 8 → Point) (hp : 0 < p)
    (hZ : IsConfiguration Z) :
    0 < separationBudget p Z ∧ 0 < separationThreshold p Z ∧
      (separationThreshold p Z)^(-p)=separationBudget p Z ∧
      ∀ i j, i ≠ j → separationThreshold p Z < squaredDistance Z i j := by
  have hB : 0 < separationBudget p Z := by dsimp [separationBudget]; linarith [squaredEnergy_nonneg p Z]
  have he : 0 < separationThreshold p Z := Real.rpow_pos_of_pos hB _
  have heq : (separationThreshold p Z)^(-p)=separationBudget p Z := by
    unfold separationThreshold
    rw [← Real.rpow_mul hB.le]
    have hx : (-1/p)*(-p)=(1:ℝ) := by field_simp
    rw [hx,Real.rpow_one]
  refine ⟨hB,he,heq,?_⟩
  intro i j hij
  apply (Real.rpow_lt_rpow_iff_of_neg (setup_positive_distance Z hZ i j hij) he (show -p < 0 by linarith)).mp
  rw [heq]
  have ht := squaredEnergy_term_le p Z i j hij
  dsimp [separationBudget]
  linarith

#check minimizer_exists_separation_threshold
#print axioms minimizer_exists_separation_threshold
end Blueprint.Thomson.Tail.Implementation
