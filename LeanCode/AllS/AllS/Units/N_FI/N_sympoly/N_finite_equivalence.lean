import AllS.Units.N_F.N_definitions
import AllS.Units.N_FI.N_definitions.N_tags
import AllS.Units.N_FI.N_sympoly.N_bounded_inverse
import Blueprint.FiniteDefinitions
import Blueprint.Target

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

abbrev TagIndex (D : ℕ) := {t : Tag // t ∈ InvariantTags D}

def tagExponent (t : Tag) : Fin 3 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm ![t.1, t.2.1, t.2.2]

def exponentTag (d : Fin 3 →₀ ℕ) : Tag := (d 0, d 1, d 2)

def boundedSymmetric (D : ℕ) : Submodule ℝ Poly3 :=
  (MvPolynomial.symmetricSubalgebra (Fin 3) ℝ).toSubmodule ⊓
    MvPolynomial.restrictTotalDegree (Fin 3) ℝ D

@[simp] theorem exponentTag_tagExponent (t : Tag) : exponentTag (tagExponent t) = t := by
  rcases t with ⟨i, j, k⟩
  rfl

@[simp] theorem tagExponent_exponentTag (d : Fin 3 →₀ ℕ) : tagExponent (exponentTag d) = d := by
  ext i
  fin_cases i <;> rfl

theorem tagExponent_injective : Function.Injective tagExponent := by
  intro t u h
  simpa only [exponentTag_tagExponent] using congrArg exponentTag h

@[simp] theorem weight_tagExponent (t : Tag) :
    Finsupp.weight invariantWeight (tagExponent t) = tagWeight t := by
  rw [invariantWeight_eq]
  rfl

@[simp] theorem tagWeight_exponentTag (d : Fin 3 →₀ ℕ) :
    tagWeight (exponentTag d) = Finsupp.weight invariantWeight d := by
  rw [invariantWeight_eq]
  rfl

@[simp] theorem mem_boundedSymmetric (D : ℕ) (p : Poly3) :
    p ∈ boundedSymmetric D ↔ p.IsSymmetric ∧ p.totalDegree ≤ D := by
  simp only [boundedSymmetric, Submodule.mem_inf, Subalgebra.mem_toSubmodule,
    MvPolynomial.mem_symmetricSubalgebra, MvPolynomial.mem_restrictTotalDegree]

def rawInvariantSynthesis (D : ℕ) : (TagIndex D → ℝ) →ₗ[ℝ] Poly3 where
  toFun c := ∑ t : TagIndex D, MvPolynomial.monomial (tagExponent t.val) (c t)
  map_add' c d := by simp [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' r c := by simp [Pi.smul_apply, Finset.smul_sum, MvPolynomial.smul_monomial]

@[simp] theorem rawInvariantSynthesis_apply (D : ℕ) (c : TagIndex D → ℝ) :
    rawInvariantSynthesis D c =
      ∑ t : TagIndex D, MvPolynomial.monomial (tagExponent t.val) (c t) := rfl

theorem coeff_rawInvariantSynthesis (D : ℕ) (c : TagIndex D → ℝ) (t : TagIndex D) :
    MvPolynomial.coeff (tagExponent t.val) (rawInvariantSynthesis D c) = c t := by
  classical
  simp only [rawInvariantSynthesis_apply, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single t]
  · simp
  · intro b hb hbt
    have hne : tagExponent b.val ≠ tagExponent t.val := by
      intro h
      exact hbt (Subtype.ext (tagExponent_injective h))
    simp [hne]
  · simp

theorem rawInvariantSynthesis_injective (D : ℕ) :
    Function.Injective (rawInvariantSynthesis D) := by
  intro c e h
  funext t
  have h' := congrArg (MvPolynomial.coeff (tagExponent t.val)) h
  simpa only [coeff_rawInvariantSynthesis] using h'

theorem rawInvariantSynthesis_recover (D : ℕ) (q : Poly3)
    (hq : ∀ d ∈ q.support, Finsupp.weight invariantWeight d ≤ D) :
    rawInvariantSynthesis D (fun t => MvPolynomial.coeff (tagExponent t.val) q) = q := by
  classical
  ext d
  by_cases hd : Finsupp.weight invariantWeight d ≤ D
  · let t : TagIndex D := ⟨exponentTag d, mem_InvariantTags.mpr (by simpa using hd)⟩
    have ht : tagExponent t.val = d := tagExponent_exponentTag d
    simpa only [ht] using coeff_rawInvariantSynthesis D
      (fun t => MvPolynomial.coeff (tagExponent t.val) q) t
  · have hq0 : MvPolynomial.coeff d q = 0 := by
      by_contra h
      exact hd (hq d (MvPolynomial.mem_support_iff.mpr h))
    rw [hq0, rawInvariantSynthesis_apply, MvPolynomial.coeff_sum]
    apply Finset.sum_eq_zero
    intro t ht
    rw [MvPolynomial.coeff_monomial]
    have hne : tagExponent t.val ≠ d := by
      intro h
      apply hd
      rw [← h, weight_tagExponent]
      exact mem_InvariantTags.mp t.property
    simp [hne]

def invariantSynthesis (D : ℕ) : (TagIndex D → ℝ) →ₗ[ℝ] Poly3 :=
  invariantSubst.toLinearMap.comp (rawInvariantSynthesis D)

theorem invariantSynthesis_eq (D : ℕ) (c : TagIndex D → ℝ) :
    invariantSynthesis D c = ∑ t : TagIndex D, c t • invariantMonomial t.val := by
  change invariantSubst (rawInvariantSynthesis D c) = _
  rw [rawInvariantSynthesis_apply, map_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [invariantSubst_monomial]
  change MvPolynomial.C (c t) * invariantMonomial t.val = c t • invariantMonomial t.val
  rw [MvPolynomial.C_mul']

theorem invariantSynthesis_mem (D : ℕ) (c : TagIndex D → ℝ) :
    invariantSynthesis D c ∈ boundedSymmetric D := by
  rw [mem_boundedSymmetric]
  constructor
  · exact invariantSubst_symmetric _
  · change (invariantSubst (rawInvariantSynthesis D c)).totalDegree ≤ D
    apply (MvPolynomial.mem_restrictTotalDegree _ _ _).mp
    rw [rawInvariantSynthesis_apply, map_sum]
    apply Submodule.sum_mem
    intro t ht
    apply (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr
    exact (sympoly_monomial_grade (tagExponent t.val) (c t)).totalDegree_le.trans
      (by simpa using mem_InvariantTags.mp t.property)

def invariantSynthesisBounded (D : ℕ) :
    (TagIndex D → ℝ) →ₗ[ℝ] boundedSymmetric D :=
  (invariantSynthesis D).codRestrict (boundedSymmetric D) (invariantSynthesis_mem D)

theorem invariantSynthesisBounded_bijective (D : ℕ) :
    Function.Bijective (invariantSynthesisBounded D) := by
  constructor
  · intro c e h
    apply rawInvariantSynthesis_injective D
    apply invariantSubst_injective
    exact congrArg Subtype.val h
  · intro p
    obtain ⟨q, ⟨hS, hq⟩, _⟩ := sympoly_bounded_inverse p.val D
      ((mem_boundedSymmetric D p.val).mp p.property).1
      ((mem_boundedSymmetric D p.val).mp p.property).2
    refine ⟨fun t => MvPolynomial.coeff (tagExponent t.val) q, ?_⟩
    apply Subtype.ext
    change invariantSubst (rawInvariantSynthesis D _) = p.val
    rw [rawInvariantSynthesis_recover D q hq, hS]

/-- Exact invariant coordinates on all symmetric polynomials of bounded degree. -/
def sympoly_finite_equivalence (D : ℕ) :
    (TagIndex D → ℝ) ≃ₗ[ℝ] boundedSymmetric D :=
  LinearEquiv.ofBijective (invariantSynthesisBounded D) (invariantSynthesisBounded_bijective D)

theorem sympoly_finite_equivalence_apply (D : ℕ) (c : TagIndex D → ℝ) :
    (sympoly_finite_equivalence D c).val =
      ∑ t : TagIndex D, c t • invariantMonomial t.val := invariantSynthesis_eq D c

#check sympoly_finite_equivalence
#print axioms sympoly_finite_equivalence
#check sympoly_finite_equivalence_apply
#print axioms sympoly_finite_equivalence_apply
end Blueprint.Thomson.Finite
