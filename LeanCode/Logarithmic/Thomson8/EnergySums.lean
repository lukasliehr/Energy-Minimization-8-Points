import Thomson8.Minorant
import Thomson8.SumLinearity
import Thomson8.TripleSymmetry

namespace Thomson8

open scoped InnerProductSpace

noncomputable def pairSum (f : Index → Index → ℝ) : ℝ :=
  ∑ i, ∑ j, if i < j then f i j else 0

theorem offSum_eq_two_pairSum (f : Index → Index → ℝ) (hf : ∀ i j, f i j=f j i) :
    offSum f=2*pairSum f := by
  have h (i j : Index) : (if i≠j then f i j else 0) =
      (if i < j then f i j else 0)+(if j < i then f j i else 0) := by
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · simp [hlt,hlt.ne,hlt.not_gt]
    · simp
    · simp [hgt,hgt.ne',hgt.not_gt,hf i j]
  have hswap : (∑ i : Index, ∑ j : Index, if j < i then f j i else 0)=pairSum f := by
    rw [Finset.sum_comm]
    rfl
  simp only [offSum,h,Finset.sum_add_distrib,hswap]
  change pairSum f+pairSum f=2*pairSum f
  ring

noncomputable def hermiteEnergy (x : Configuration) : ℝ :=
  pairSum fun i j => H ⟪x i,x j⟫_ℝ

theorem logEnergy_eq_pairs (x : Configuration) (hx : ∀ i, ‖x i‖=1) :
    logEnergy x=pairSum (fun i j => phi ⟪x i,x j⟫_ℝ) := by
  simp only [logEnergy,pairSum,Finset.sum_filter,pair_energy_inner _ _ (hx _) (hx _)]

theorem hermiteEnergy_le_logEnergy (x : Configuration) (hx : Admissible x) :
    hermiteEnergy x ≤ logEnergy x := by
  rw [logEnergy_eq_pairs x hx.1]
  unfold hermiteEnergy pairSum
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  split_ifs with hij
  · exact H_minorant ⟨(inner_unit_bounds _ _ (hx.1 i) (hx.1 j)).1,
      admissible_inner_lt_one x hx i j hij.ne⟩
  · exact le_rfl

theorem distinctSum_energy (x : Configuration) (e : ℝ) :
    distinctSum (onTriples x (fun u v t => (H u+H v+H t)/3-e/28)) =
      12*(hermiteEnergy x-e) := by
  have hfun : onTriples x (fun u v t => (H u+H v+H t)/3-e/28) =
      fun i j k => (1/3)*(H ⟪x i,x j⟫_ℝ+H ⟪x i,x k⟫_ℝ+H ⟪x j,x k⟫_ℝ)+(-e/28) := by
    funext i j k
    unfold onTriples
    ring
  rw [hfun,distinctSum_add,distinctSum_mul,distinctSum_add,distinctSum_add,
    distinctSum_pair,distinctSum_pair13,distinctSum_pair23,distinctSum_const,
    offSum_eq_two_pairSum _ (fun i j => by rw [real_inner_comm])]
  unfold hermiteEnergy
  ring

theorem distinctSum_nonneg (f : Index → Index → Index → ℝ) (hf : ∀ i j k, 0≤f i j k) :
    0 ≤ distinctSum f := by
  unfold distinctSum
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro k _
  split_ifs
  · exact hf i j k
  · exact le_rfl

end Thomson8
