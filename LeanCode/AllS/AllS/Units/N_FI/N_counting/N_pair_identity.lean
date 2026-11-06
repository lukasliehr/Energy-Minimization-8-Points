import AllS.Units.N_FI.N_counting.N_finite_partitions

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

def PairCountingContract : Prop := ∀ f : ℝ → ℝ, ∀ e : ℝ, ∀ Y : Configuration,
  DistinctSum (fun i j k => (f (inner ℝ (Y i) (Y j))+f (inner ℝ (Y i) (Y k))+
    f (inner ℝ (Y j) (Y k)))/3-e/28) =
      12*(PairSum (fun i j => f (inner ℝ (Y i) (Y j)))-e)
theorem offSum_eq_pairSum_add_transpose (f : Fin 8 → Fin 8 → ℝ) :
    GenericMoments.offSum f = PairSum f+PairSum (fun i j => f j i) := by
  have h (i j : Fin 8) : (if i ≠ j then f i j else 0) =
      (if i < j then f i j else 0)+(if j < i then f i j else 0) := by
    rcases lt_trichotomy i j with hij | hij | hij
    · simp [hij,ne_of_lt hij,not_lt.mpr hij.le]
    · simp [hij]
    · simp [hij,ne_of_gt hij,not_lt.mpr hij.le]
  unfold GenericMoments.offSum PairSum
  simp_rw [h,Finset.sum_add_distrib,Finset.sum_filter]
  congr 1
  rw [Finset.sum_comm]

theorem offSum_eq_twoPairSum (f : Fin 8 → Fin 8 → ℝ) (hf : ∀ i j, f i j=f j i) :
    GenericMoments.offSum f = 2*PairSum f := by
  rw [offSum_eq_pairSum_add_transpose]
  have he : (fun i j => f j i) = f := by funext i j; exact hf j i
  rw [he]
  ring

theorem counting_pair_identity : PairCountingContract := by
  intro f e Y
  let g : Fin 8 → Fin 8 → ℝ := fun i j => f (inner ℝ (Y i) (Y j))
  have hg : ∀ i j, g i j=g j i := by intro i j; simp [g,real_inner_comm]
  have he : (fun i j k => (g i j+g i k+g j k)/3-e/28) =
      (fun i j k => (1/3 : ℝ)*(g i j+g i k+g j k)+(-e/28)) := by
    funext i j k
    ring
  change GenericMoments.distinctSum (fun i j k => (g i j+g i k+g j k)/3-e/28) = _
  rw [he,GenericMoments.distinctSum_add,GenericMoments.distinctSum_mul,
    GenericMoments.distinctSum_add,GenericMoments.distinctSum_add,
    GenericMoments.distinctSum_pair,GenericMoments.distinctSum_pair13,
    GenericMoments.distinctSum_pair23,GenericMoments.distinctSum_const,
    offSum_eq_twoPairSum g hg]
  change (1/3 : ℝ)*(6*(2*PairSum g)+6*(2*PairSum g)+6*(2*PairSum g))+
    336*(-e/28)=12*(PairSum g-e)
  ring

#check counting_pair_identity
#print axioms counting_pair_identity
#check PairCountingContract
#print axioms PairCountingContract
end Blueprint.Thomson.Finite
