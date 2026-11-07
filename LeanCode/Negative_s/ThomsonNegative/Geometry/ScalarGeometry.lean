import ThomsonNegative.Geometry.Candidate
import ThomsonNegative.Geometry.Confluent

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Geometry

def sourceContactOrder : Equiv.Perm (Fin 4) := Equiv.swap 1 2

def sourceContacts (a : ℝ) : Fin 4 → ℝ := contacts a ∘ sourceContactOrder

lemma sourceContacts_injective (a : ℝ) (ha : physical a) : Function.Injective (sourceContacts a) :=
  (contacts_injective a ha).comp sourceContactOrder.injective

/-- The exact H7 polynomial used by the scalar checker, in A,C,B,D source order. -/
def concreteH (q a : ℝ) : Polynomial ℝ := hermiteH7 q (sourceContacts a)

lemma concreteH_degree (q a : ℝ) : (concreteH q a).degree < 8 := hermiteH7_degree _ _

lemma concreteH_value (q a : ℝ) (ha : physical a) (i : Fin 4) :
    (concreteH q a).eval (contacts a i)=Analytic.auxiliaryT q (contacts a i) := by
  have h := hermiteH7_value q (sourceContacts a) (sourceContacts_injective a ha) (sourceContactOrder.symm i)
  simpa only [concreteH,sourceContacts,Function.comp_apply,Equiv.apply_symm_apply] using h

lemma concreteH_slope (q a : ℝ) (ha : physical a) (i : Fin 4) :
    (concreteH q a).derivative.eval (contacts a i)=auxSlope q ((1+contacts a i)/2)/2 := by
  have h := hermiteH7_slope q (sourceContacts a) (sourceContacts_injective a ha) (sourceContactOrder.symm i)
  simpa only [concreteH,sourceContacts,Function.comp_apply,Equiv.apply_symm_apply] using h

lemma concreteH_minorant (q a t : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1) (ha : physical a)
    (ht : t ∈ Set.Ico (-1:ℝ) 1) :
    (concreteH q a).eval t ≤ Analytic.auxiliaryT q t ∧
      ((concreteH q a).eval t=Analytic.auxiliaryT q t ↔ t ∈ Set.range (contacts a)) := by
  have hh := hermiteH7_minorant q hq (sourceContacts a) (sourceContacts_injective a ha)
    (fun i => ⟨(contacts_bounds a ha _).1.le,(contacts_bounds a ha _).2⟩) t ht
  refine ⟨hh.1,?_⟩
  unfold concreteH
  rw [hh.2.2]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨sourceContactOrder i,hi.symm⟩
  · rintro ⟨i,hi⟩
    exact ⟨sourceContactOrder.symm i,by simpa [sourceContacts] using hi.symm⟩

lemma pair_inner_domain (y z : Point) (hy : ‖y‖=1) (hz : ‖z‖=1) (hne : y ≠ z) :
    inner ℝ y z ∈ Set.Ico (-1:ℝ) 1 := by
  have hab := abs_real_inner_le_norm y z
  rw [hy,hz,mul_one] at hab
  have hp : 0 < ‖y-z‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  rw [norm_sub_sq_real,hy,hz] at hp
  exact ⟨(abs_le.mp hab).1,by nlinarith⟩

def polyPairEnergy (H : Polynomial ℝ) (Y : Configuration) : ℝ :=
  PairSum (fun i j => H.eval (inner ℝ (Y i) (Y j)))

lemma concreteH_pair_le (q a : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1) (ha : physical a)
    (Y : Configuration) (hY : IsConfiguration Y) : polyPairEnergy (concreteH q a) Y ≤ auxEnergy q Y := by
  unfold polyPairEnergy PairSum auxEnergy pairSum
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  have hij : i ≠ j := ne_of_lt (Finset.mem_filter.mp hj).2
  exact (concreteH_minorant q a _ hq ha
    (pair_inner_domain (Y i) (Y j) (hY.1 i) (hY.1 j) (hY.2.ne hij))).1

lemma concreteH_candidate_pair (q a : ℝ) (ha : physical a) :
    polyPairEnergy (concreteH q a) (X a)=auxEnergy q (X a) := by
  unfold polyPairEnergy PairSum auxEnergy pairSum
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hij : i ≠ j := ne_of_lt (Finset.mem_filter.mp hj).2
  obtain ⟨k,hk⟩ := candidate_pair_contact a ha i j hij
  dsimp only
  rw [← hk]
  exact concreteH_value q a ha k

lemma candidate_auxEnergy (q a : ℝ) (ha : physical a) :
    auxEnergy q (X a)=8*Analytic.auxiliaryT q (contacts a 0)+
      4*Analytic.auxiliaryT q (contacts a 1)+8*Analytic.auxiliaryT q (contacts a 2)+
      8*Analytic.auxiliaryT q (contacts a 3) :=
  candidate_pair_sum a ha (Analytic.auxiliaryT q)

/-- Equality of the original energy supplies the centroid condition; no strict
Gram floor is needed for equality reconstruction in the negative range. -/
theorem energy_equality_centroid_aux (q a : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1)
    (ha : physical a) (Y : Configuration) (hY : IsConfiguration Y)
    (haux : auxEnergy q (X a) ≤ auxEnergy q Y)
    (he : E (2*q-2) Y=E (2*q-2) (X a)) :
    (∑ i,Y i)=0 ∧ auxEnergy q Y=auxEnergy q (X a) := by
  rw [energy_decomposition q hq Y hY.1,
    energy_decomposition q hq (X a) (candidate_is_configuration a ha).1,
    antiprism_centroid] at he
  simp only [norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),zero_div,add_zero] at he
  have hc : 0 < (4:ℝ)^(-q) := Real.rpow_pos_of_pos (by norm_num) _
  have hd : 0 < 2*q*(4:ℝ)^(-q) := by positivity [hq.1]
  have hp := mul_nonneg hd.le (sub_nonneg.mpr haux)
  have hn := sq_nonneg ‖∑ i,Y i‖
  have hprod : (4:ℝ)^(-q)*‖∑ i,Y i‖^2=0 := by
    apply le_antisymm
    · nlinarith
    · exact mul_nonneg hc.le hn
  have hzero : ‖∑ i,Y i‖=0 := sq_eq_zero_iff.mp ((mul_eq_zero.mp hprod).resolve_left hc.ne')
  refine ⟨norm_eq_zero.mp hzero,?_⟩
  rw [hzero] at he
  have hx : (2*q*(4:ℝ)^(-q))*(auxEnergy q Y-auxEnergy q (X a))=0 := by nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left hd.ne')

lemma centroid_first_moment (Y : Configuration) (hc : ∑ i,Y i=0) (i : Fin 8) :
    (∑ j,inner ℝ (Y i) (Y j))=0 := by rw [← inner_sum,hc]; simp

#print axioms concreteH_minorant
#print axioms concreteH_candidate_pair
#print axioms energy_equality_centroid_aux
end ThomsonNegative.Geometry
