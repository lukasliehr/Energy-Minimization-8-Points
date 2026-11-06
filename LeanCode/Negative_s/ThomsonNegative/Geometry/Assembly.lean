import ThomsonNegative.Geometry.Target
import ThomsonNegative.Geometry.Reconstruction

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Geometry

/-- The remaining pointwise numerical certificate: eight PSD matrices and one
explicit polynomial identity. It contains no energy or congruence premise. -/
def Certificate (q a : ℝ) (P : Structure.PolynomialFamily) : Prop :=
  ∃ W : Structure.GramFamily, (∀ b,(W b).PosSemidef) ∧
    Structure.gramPolynomial P W=centeredPolynomial (concreteH q a) (auxEnergy q (X a))

lemma certificate_polynomial_lower (q a : ℝ) (P : Structure.PolynomialFamily)
    (hP : ∀ b,BlockRealization (P b)) (hc : Certificate q a P)
    (Y : Configuration) (hY : IsConfiguration Y) :
    auxEnergy q (X a) ≤ polyPairEnergy (concreteH q a) Y := by
  obtain ⟨W,hW,he⟩ := hc
  have hn := gramPolynomial_nonneg P hP W hW Y hY.1
  rw [he,centeredPolynomial_distinctSum] at hn
  linarith

lemma equality_pair_contacts (q a : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1)
    (ha : physical a) (Y : Configuration) (hY : IsConfiguration Y)
    (he : polyPairEnergy (concreteH q a) Y=auxEnergy q Y) : AllowedContacts a Y := by
  let gap : Fin 8 → Fin 8 → ℝ := fun i j =>
    Analytic.auxiliaryT q (inner ℝ (Y i) (Y j))-(concreteH q a).eval (inner ℝ (Y i) (Y j))
  have hn (i j : Fin 8) (hij : i < j) : 0 ≤ gap i j := by
    exact sub_nonneg.mpr (concreteH_minorant q a _ hq ha
      (pair_inner_domain _ _ (hY.1 i) (hY.1 j) (hY.2.ne (ne_of_lt hij)))).1
  have hz : pairSum gap=0 := by
    unfold gap pairSum
    simp only [Finset.sum_sub_distrib]
    change auxEnergy q Y-polyPairEnergy (concreteH q a) Y=0
    rw [he,sub_self]
  have hrow (i : Fin 8) : (∑ j : Fin 8 with i<j,gap i j)=0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg
      (fun j hj => hn i j (Finset.mem_filter.mp hj).2))).mp hz i (Finset.mem_univ _)
  have ho (i j : Fin 8) (hij : i < j) : inner ℝ (Y i) (Y j) ∈ Set.range (contacts a) := by
    have hj := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j hj => hn i j (Finset.mem_filter.mp hj).2)).mp (hrow i) j
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij⟩)
    have hd := pair_inner_domain _ _ (hY.1 i) (hY.1 j) (hY.2.ne (ne_of_lt hij))
    exact (concreteH_minorant q a _ hq ha hd).2.mp (sub_eq_zero.mp hj).symm
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact ho i j h
  · rw [real_inner_comm]
    exact ho j i h

def pairEnergyTerm (s : ℝ) (Y : Configuration) (i j : Fin 8) : ℝ :=
  if s=0 then -Real.log ‖Y i-Y j‖ else ‖Y i-Y j‖^(-s)/s

lemma offSum_permutation (f : Fin 8 → Fin 8 → ℝ) (σ : Equiv.Perm (Fin 8)) :
    GenericMoments.offSum (fun i j => f (σ i) (σ j))=GenericMoments.offSum f := by
  unfold GenericMoments.offSum
  have he (i j : Fin 8) : (if i≠j then f (σ i) (σ j) else 0)=
      if σ i≠σ j then f (σ i) (σ j) else 0 := by simp only [σ.injective.ne_iff]
  simp_rw [he]
  trans ∑ i : Fin 8,∑ j : Fin 8,if σ i≠j then f (σ i) j else 0
  · apply Finset.sum_congr rfl
    intro i hi
    exact Equiv.sum_comp σ (fun j => if σ i≠j then f (σ i) j else 0)
  · exact Equiv.sum_comp σ (fun i => ∑ j : Fin 8,if i≠j then f i j else 0)

lemma congruence_energy (s : ℝ) (Y Z : Configuration) (h : Congruent Y Z) : E s Y=E s Z := by
  obtain ⟨U,σ,h⟩ := h
  have hp (i j : Fin 8) : pairEnergyTerm s Y i j=pairEnergyTerm s Z (σ i) (σ j) := by
    have hn : ‖Y i-Y j‖=‖Z (σ i)-Z (σ j)‖ := by rw [h i,h j,← U.map_sub,U.norm_map]
    simp only [pairEnergyTerm,hn]
  have ho : GenericMoments.offSum (pairEnergyTerm s Y)=GenericMoments.offSum (pairEnergyTerm s Z) := by
    simp_rw [show pairEnergyTerm s Y=(fun i j => pairEnergyTerm s Z (σ i) (σ j)) from funext fun i => funext (hp i)]
    exact offSum_permutation _ σ
  have hsym (V : Configuration) (i j : Fin 8) : pairEnergyTerm s V i j=pairEnergyTerm s V j i := by
    simp only [pairEnergyTerm,norm_sub_rev]
  rw [offSum_eq_twoPairSum _ (hsym Y),offSum_eq_twoPairSum _ (hsym Z)] at ho
  change PairSum (pairEnergyTerm s Y)=PairSum (pairEnergyTerm s Z)
  linarith

/-- Complete geometric soundness: the numerical matrix certificate is the only
remaining hypothesis beyond exact block evaluation identities. PSD suffices. -/
theorem certificate_global (q a : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1)
    (ha : physical a) (hlo : (5/16:ℝ) ≤ a) (P : Structure.PolynomialFamily)
    (hP : ∀ b,BlockRealization (P b)) (hc : Certificate q a P) :
    IsUniqueMinimizer (2*q-2) (X a) := by
  refine ⟨candidate_is_configuration a ha,?_⟩
  intro Y hY
  have hpoly := certificate_polynomial_lower q a P hP hc Y hY
  have hminor := concreteH_pair_le q a hq ha Y hY
  have haux : auxEnergy q (X a) ≤ auxEnergy q Y := hpoly.trans hminor
  refine ⟨energy_le_of_auxEnergy_le q hq Y (X a) hY.1 (candidate_is_configuration a ha).1
    (antiprism_centroid a) haux,?_⟩
  constructor
  · intro he
    obtain ⟨hcent,hauxeq⟩ := energy_equality_centroid_aux q a hq ha Y hY haux he
    have hpolyeq : polyPairEnergy (concreteH q a) Y=auxEnergy q Y := by linarith
    have hcontacts := equality_pair_contacts q a hq ha Y hY hpolyeq
    exact first_moment_congruence a Y ha hlo hY hcontacts (centroid_first_moment Y hcent)
  · intro hcong
    exact congruence_energy (2*q-2) Y (X a) hcong

/-- Closed cell coverage is checked independently; geometric soundness is
consumed only for the requested open interval. -/
def CellSpec (lo hi : ℝ) (P : ℝ → Structure.PolynomialFamily) : Prop :=
  ∀ q ∈ Set.Icc lo hi, q ∈ Set.Ioo (0:ℝ) 1 → Certificate q (aStar (2*q-2)) (P q)

def cellLower (i : Fin 5) : ℝ := (i:ℝ)/5

def cellUpper (i : Fin 5) : ℝ := ((i:ℝ)+1)/5

lemma five_cell_cover (q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) :
    ∃ i : Fin 5,q ∈ Set.Icc (cellLower i) (cellUpper i) := by
  by_cases h1 : q ≤ 1/5
  · exact ⟨0,by norm_num [cellLower,cellUpper]; exact ⟨hq.1,h1⟩⟩
  by_cases h2 : q ≤ 2/5
  · exact ⟨1,by norm_num [cellLower,cellUpper]; exact ⟨by linarith,h2⟩⟩
  by_cases h3 : q ≤ 3/5
  · exact ⟨2,by norm_num [cellLower,cellUpper]; exact ⟨by linarith,h3⟩⟩
  by_cases h4 : q ≤ 4/5
  · exact ⟨3,by norm_num [cellLower,cellUpper]; exact ⟨by linarith,h4⟩⟩
  exact ⟨4,by norm_num [cellLower,cellUpper]; exact ⟨by linarith,hq.2⟩⟩

theorem global_of_five_cells (P : ℝ → Structure.PolynomialFamily)
    (hP : ∀ q ∈ Set.Ioo (0:ℝ) 1,∀ b,BlockRealization (P q b))
    (hc : ∀ i : Fin 5,CellSpec (cellLower i) (cellUpper i) P)
    (q : ℝ) (hq : q ∈ Set.Ioo (0:ℝ) 1) : IsUniqueMinimizer (2*q-2) (X (aStar (2*q-2))) := by
  obtain ⟨i,hi⟩ := five_cell_cover q ⟨hq.1.le,hq.2.le⟩
  exact certificate_global q _ hq (root_physical q hq.1)
    (aStar_negative_range q ⟨hq.1,hq.2.le⟩).1.le (P q) (hP q hq) (hc i q hi hq)

/-- The exact requested negative-s global theorem, conditional only on the
explicit five-cell matrix certificates and their fixed algebraic block meanings. -/
theorem negative_thomson_of_five_cells (P : ℝ → Structure.PolynomialFamily)
    (hP : ∀ q ∈ Set.Ioo (0:ℝ) 1,∀ b,BlockRealization (P q b))
    (hc : ∀ i : Fin 5,CellSpec (cellLower i) (cellUpper i) P)
    (s : ℝ) (hs : s ∈ Set.Ioo (-2:ℝ) 0) : IsUniqueMinimizer s (X (aStar s)) := by
  let q : ℝ := (s+2)/2
  have hq : q ∈ Set.Ioo (0:ℝ) 1 := by dsimp [q]; constructor <;> linarith [hs.1,hs.2]
  have he : 2*q-2=s := by dsimp [q]; ring
  simpa only [he] using global_of_five_cells P hP hc q hq

#print axioms certificate_global
#print axioms negative_thomson_of_five_cells
end ThomsonNegative.Geometry
