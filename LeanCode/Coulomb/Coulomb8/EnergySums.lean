import Coulomb8.Statement
import Coulomb8.Minorant
import Thomson8.EnergySums

namespace Coulomb8
open scoped InnerProductSpace
open Thomson8 (pairSum offSum onTriples distinctSum distinctSum_add distinctSum_mul
  distinctSum_pair distinctSum_pair13 distinctSum_pair23 distinctSum_const offSum_eq_two_pairSum)

noncomputable def hermiteEnergy (x : Configuration) : ℝ := pairSum fun i j => H ⟪x i,x j⟫_ℝ

theorem pair_energy_inner (x y : Point) (hx : ‖x‖=1) (hy : ‖y‖=1) :
    1/‖x-y‖=phi ⟪x,y⟫_ℝ := by
  have h := norm_sub_sq_real x y
  rw [hx,hy] at h
  have he : 2-2*⟪x,y⟫_ℝ=‖x-y‖^2 := by nlinarith
  rw [phi,he,Real.sqrt_sq (norm_nonneg _)]

theorem coulombEnergy_eq_pairs (x : Configuration) (hx : ∀ i, ‖x i‖=1) :
    coulombEnergy x=pairSum (fun i j => phi ⟪x i,x j⟫_ℝ) := by
  simp only [coulombEnergy,pairSum,Finset.sum_filter,pair_energy_inner _ _ (hx _) (hx _)]

theorem hermiteEnergy_le_coulombEnergy (x : Configuration) (hx : Admissible x) :
    hermiteEnergy x ≤ coulombEnergy x := by
  rw [coulombEnergy_eq_pairs x hx.1]
  unfold hermiteEnergy pairSum
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  split_ifs with hij
  · exact minorant ⟨(Thomson8.inner_unit_bounds _ _ (hx.1 i) (hx.1 j)).1,
      Thomson8.admissible_inner_lt_one x hx i j hij.ne⟩
  · exact le_rfl

theorem distinctSum_energy (x : Configuration) (e : ℝ) :
    distinctSum (onTriples x (fun u v t => (H u+H v+H t)/3-e/28))=
      12*(hermiteEnergy x-e) := by
  have hf : onTriples x (fun u v t => (H u+H v+H t)/3-e/28)=
      fun i j k => (1/3)*(H ⟪x i,x j⟫_ℝ+H ⟪x i,x k⟫_ℝ+H ⟪x j,x k⟫_ℝ)+(-e/28) := by
    funext i j k
    unfold onTriples
    ring
  rw [hf,distinctSum_add,distinctSum_mul,distinctSum_add,distinctSum_add,
    distinctSum_pair,distinctSum_pair13,distinctSum_pair23,distinctSum_const,
    offSum_eq_two_pairSum _ (fun i j => by rw [real_inner_comm])]
  unfold hermiteEnergy
  ring

end Coulomb8

#print axioms Coulomb8.hermiteEnergy_le_coulombEnergy
