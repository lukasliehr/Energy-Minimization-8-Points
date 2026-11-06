import ThomsonNegative.Geometry.GramSound
import ThomsonNegative.Geometry.ScalarGeometry

noncomputable section
open scoped BigOperators

open scoped BigOperators
namespace ThomsonNegative.Geometry

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
  unfold GenericMoments.offSum PairSum pairSum
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

end ThomsonNegative.Geometry
namespace ThomsonNegative.Geometry

def univariateLift (i : Fin 3) (H : Polynomial ℝ) : Poly3 :=
  Polynomial.aeval (MvPolynomial.X i) H

def averagedPolynomial (H : Polynomial ℝ) : Poly3 :=
  MvPolynomial.C (1/3:ℝ)*(univariateLift 0 H+univariateLift 1 H+univariateLift 2 H)

def centeredPolynomial (H : Polynomial ℝ) (e : ℝ) : Poly3 :=
  averagedPolynomial H-MvPolynomial.C (e/28)

lemma univariateLift_eval (x : Fin 3 → ℝ) (i : Fin 3) (H : Polynomial ℝ) :
    MvPolynomial.eval x (univariateLift i H)=H.eval (x i) := by
  unfold univariateLift
  induction H using Polynomial.induction_on' with
  | add H K hH hK => simp only [map_add,hH,hK,Polynomial.eval_add]
  | monomial n c => simp [univariateLift,Polynomial.aeval_monomial]

lemma centeredPolynomial_eval (x : Fin 3 → ℝ) (H : Polynomial ℝ) (e : ℝ) :
    MvPolynomial.eval x (centeredPolynomial H e)=
      (H.eval (x 0)+H.eval (x 1)+H.eval (x 2))/3-e/28 := by
  simp [centeredPolynomial,averagedPolynomial,univariateLift_eval]
  ring

lemma centeredPolynomial_distinctSum (Y : Configuration) (H : Polynomial ℝ) (e : ℝ) :
    distinctPolySum Y (centeredPolynomial H e)=12*(polyPairEnergy H Y-e) := by
  unfold distinctPolySum polyOnTriples
  simp only [centeredPolynomial_eval,sphericalTriple,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two]
  exact counting_pair_identity (fun t => H.eval t) e Y

lemma half_contacts (a : ℝ) (i : Fin 4) :
    (1+contacts a i)/2= ![(1+a)/2,a,(1-a)*(2+Real.sqrt 2)/4,(1-a)*(2-Real.sqrt 2)/4] i := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hn : Real.sqrt (2:ℝ) ≠ 0 := by positivity
  have hinv : (Real.sqrt (2:ℝ))⁻¹=Real.sqrt 2/2 := by field_simp; nlinarith
  fin_cases i <;> simp [contacts,div_eq_mul_inv,hinv] <;> ring

def candidateSlope (H : Polynomial ℝ) (a : ℝ) : ℝ :=
  8*H.derivative.eval (contacts a 0)+8*H.derivative.eval (contacts a 1)-
    8*(1+1/Real.sqrt 2)*H.derivative.eval (contacts a 2)-
    8*(1-1/Real.sqrt 2)*H.derivative.eval (contacts a 3)

/-- Frozen-height stationarity of the exact H7 target. -/
lemma concreteH_candidateSlope (q a : ℝ) (ha : physical a) :
    candidateSlope (concreteH q a) a=seriesRoot q a/4 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hn : Real.sqrt (2:ℝ) ≠ 0 := by positivity
  have hinv : (Real.sqrt (2:ℝ))⁻¹=Real.sqrt 2/2 := by field_simp; nlinarith
  simp only [candidateSlope,concreteH_slope q a ha,half_contacts]
  norm_num only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three]
  simp only [Matrix.head_cons,Matrix.tail_cons]
  unfold seriesRoot
  simp only [one_div,hinv]
  ring

lemma root_concreteH_candidateSlope (q : ℝ) (hq : 0 < q) :
    candidateSlope (concreteH q (aStar (2*q-2))) (aStar (2*q-2))=0 := by
  have hs : -2 < 2*q-2 := by linarith
  have ha := aStar_spec (2*q-2) hs
  rw [concreteH_candidateSlope q _ (root_physical q hq),
    (stationarity_series_iff q _ hq ha.1).mp ((ha.2 _ ha.1).mpr rfl)]
  norm_num

#print axioms centeredPolynomial_distinctSum
#print axioms concreteH_candidateSlope
end ThomsonNegative.Geometry
