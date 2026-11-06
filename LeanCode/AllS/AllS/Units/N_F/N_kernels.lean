import AllS.Units.N_FI.N_kernels.N_finite_layout_linkage
import AllS.Units.N_FI.N_kernels.N_s3_vanishing
import AllS.Units.N_FI.N_kernels.N_parity_interpolation
import AllS.Units.N_FI.N_kernels.N_standard_metric

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

/-- Source coefficients are extracted in the bivariate `(u,z)` coordinates,
not in the final `(u,v,t)` polynomial. -/
def parityKernelCoefficients (a : ℝ) (odd : Bool) (t v : Tag) : ℝ :=
  MvPolynomial.coeff (tagExponent v) (parityBiInterpolant a odd (paritySourceData a odd t))

def scalarS3PlusFeatures (a : ℝ) (d : ℕ) : List Poly3 :=
  ((freeRows (invariantTagList d).length (invariantPivots d)).map
    (fun i => invariantKernelFeature a ((invariantTagList d)[i]?.getD (0,0,0))))
def scalarS3SignFeatures (a : ℝ) (d : ℕ) : List Poly3 :=
  ((freeRows (invariantTagList (d-3)).length (signPivots d)).map
    (fun i => signKernelFeature a ((invariantTagList (d-3))[i]?.getD (0,0,0))))
def scalarS3StandardFeatures (minus : Bool) (a : ℝ) (d : ℕ) : List Poly3 :=
  ((freeRows (standardTagList d).length (standardPivots d)).map
    (fun i => standardKernelFeature minus a ((standardTagList d)[i]?.getD (false,0,0,0))))
def scalarS2Features (odd : Bool) (a : ℝ) (d : ℕ) : List Poly3 :=
  ((freeRows (parityTagList (d-(if odd then 1 else 0))).length (parityPivots odd d)).map
    (fun i => parityKernelFeature odd a
      ((parityTagList (d-(if odd then 1 else 0)))[i]?.getD (0,0,0))))

inductive ScalarBlockName | m0Plus | m0Sign | m0Standard | m1Even | m1Odd |
  mdetPlus | mdetSign | mdetStandard deriving DecidableEq

def scalarBlockFeatures (b : ScalarBlockName) (a : ℝ) (d : ℕ) : List (List Poly3) :=
  match b with
  | .m0Plus => [scalarS3PlusFeatures a d]
  | .m0Sign => [scalarS3SignFeatures a d]
  | .m0Standard => [scalarS3StandardFeatures false a d,scalarS3StandardFeatures true a d]
  | .m1Even => [scalarS2Features false a (d-1)]
  | .m1Odd => [scalarS2Features true a (d-1)]
  | .mdetPlus => [scalarS3PlusFeatures a (d-2)]
  | .mdetSign => [scalarS3SignFeatures a (d-2)]
  | .mdetStandard => [scalarS3StandardFeatures false a (d-2),scalarS3StandardFeatures true a (d-2)]

def scalarBlockAllowance (b : ScalarBlockName) (d : ℕ) : ℕ :=
  match b with
  | .m0Plus | .m0Sign | .m0Standard => d
  | .m1Even | .m1Odd => d-1
  | .mdetPlus | .mdetSign | .mdetStandard => d-2

/-- Row position in the source raw feature list. The column is indexed by one
free row; interpolation affects only the listed pivot rows. -/
def kernelColumnVector (pivots : List ℕ) (c : ℕ → ℝ) (free i : ℕ) : ℝ :=
  (if i=free then 1 else 0)-∑ j ∈ pivots.toFinset,if i=j then c j else 0

def CanonicalScalarKernelsContract : Prop :=
  FiniteLayoutLinkageContract ∧ S3VanishingContract ∧ StandardMetricContract ∧
  (∀ a,physical a → ∀ d,6≤d → ∀ b,∀ g ∈ scalarBlockFeatures b a d,∀ p ∈ g,
    p.totalDegree ≤ scalarBlockAllowance b d ∧
      ∀ r σ,MvPolynomial.eval (permutedContact a r σ) p=0) ∧
  (∀ pivots c free i,i∉pivots → kernelColumnVector pivots c free i=(if i=free then 1 else 0)) ∧
  (∀ a,physical a → ∀ odd t,parityKernelFeature odd a t=
    (if odd then parityOdd else 1)*parityMonomial t-
      ∑ v ∈ (parityPivotTags odd).toFinset,
        MvPolynomial.C (parityKernelCoefficients a odd t v)*
          ((if odd then parityOdd else 1)*parityMonomial v))

theorem parityPivot_third_zero (odd : Bool) (t : Tag)
    (ht : t ∈ (parityPivotTags odd).toFinset) : t.2.2=0 := by
  have h := List.mem_toFinset.mp ht
  simp only [parityPivotTags,List.mem_flatMap,List.mem_map] at h
  obtain ⟨i,hi,j,hj,rfl⟩ := h
  rfl

theorem parityBiPivot_monomial (t : Tag) (ht : t.2.2=0) :
    parityBiPivot t=MvPolynomial.monomial (tagExponent t) (1 : ℝ) := by
  rw [MvPolynomial.monomial_eq]
  rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  simp [parityBiPivot,tagExponent,Fin.prod_univ_succ,ht]

theorem parityBiInterpolant_coeff_expansion (a : ℝ) (ha : physical a) (odd : Bool)
    (V : ParityData odd) :
    parityBiInterpolant a odd V = ∑ t ∈ (parityPivotTags odd).toFinset,
      MvPolynomial.C (MvPolynomial.coeff (tagExponent t) (parityBiInterpolant a odd V))*parityBiPivot t := by
  classical
  obtain ⟨c,hc⟩ := parityBiInterpolant_expansion a ha odd V
  have hcoef (t : Tag) (ht : t ∈ (parityPivotTags odd).toFinset) :
      MvPolynomial.coeff (tagExponent t) (parityBiInterpolant a odd V)=c t := by
    rw [hc,MvPolynomial.coeff_sum]
    rw [Finset.sum_eq_single t]
    · rw [parityBiPivot_monomial t (parityPivot_third_zero odd t ht)]
      simp
    · intro b hb hbt
      rw [parityBiPivot_monomial b (parityPivot_third_zero odd b hb)]
      have hne : tagExponent b ≠ tagExponent t := fun h => hbt (tagExponent_injective h)
      simp [hne]
    · exact fun h => False.elim (h ht)
  rw [hc]
  apply Finset.sum_congr rfl
  intro t ht
  rw [← hc,hcoef t ht]

theorem parityEmbed_biPivot (odd : Bool) (t : Tag)
    (ht : t ∈ (parityPivotTags odd).toFinset) :
    parityEmbed (parityBiPivot t)=parityMonomial t := by
  simp [parityEmbed,parityBiPivot,parityMonomial,parityPivot_third_zero odd t ht]

theorem parityKernelFeature_expansion (a : ℝ) (ha : physical a) (odd : Bool) (t : Tag) :
    parityKernelFeature odd a t=(if odd then parityOdd else 1)*parityMonomial t-
      ∑ v ∈ (parityPivotTags odd).toFinset,
        MvPolynomial.C (parityKernelCoefficients a odd t v)*
          ((if odd then parityOdd else 1)*parityMonomial v) := by
  unfold parityKernelCoefficients
  conv_lhs => rw [parityKernelFeature,parityInterpolant,parityBiInterpolant_coeff_expansion a ha odd]
  rw [mul_sub,map_sum,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  rw [map_mul,parityEmbed_biPivot odd v hv]
  simp only [parityEmbed,MvPolynomial.aeval_C,MvPolynomial.algebraMap_eq]
  ring

theorem kernelColumnVector_free (pivots : List ℕ) (c : ℕ → ℝ) (free i : ℕ)
    (hi : i∉pivots) : kernelColumnVector pivots c free i=(if i=free then 1 else 0) := by
  unfold kernelColumnVector
  have hz : (∑ j ∈ pivots.toFinset,if i=j then c j else 0)=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hne : i≠j := fun h => hi (h ▸ List.mem_toFinset.mp hj)
    simp [hne]
  rw [hz,sub_zero]

theorem invariantKernelFeature_degree (a : ℝ) (ha : physical a) (d : ℕ) (hd : 4≤d)
    (t : Tag) (ht : t∈invariantTagList d) : (invariantKernelFeature a t).totalDegree≤d := by
  apply polyDegree_sub_le
  · exact (invariantMonomial_degree t).trans (mem_invariantTagList.mp ht)
  · exact (invariantProjector_degree a ha _).trans hd

theorem signKernelFeature_degree (a : ℝ) (ha : physical a) (d : ℕ) (hd : 4≤d)
    (t : Tag) (ht : t∈invariantTagList (d-3)) : (signKernelFeature a t).totalDegree≤d := by
  apply polyDegree_sub_le
  · exact s3SignRaw_degree d hd _ (List.mem_map.mpr ⟨t,ht,rfl⟩)
  · exact (alternatingProjector_degree a ha _).trans hd

theorem standardKernelFeature_raw_sub (minus : Bool) (a : ℝ) (t : StandardTag) :
    standardKernelFeature minus a t=standardRawFeature minus t-
      (if minus then standardProjector a (standardInputF t) (standardInputG t) 1-
        standardProjector a (standardInputF t) (standardInputG t) 2
       else standardProjector a (standardInputF t) (standardInputG t) 0) := by
  rw [standardRawFeature_component]
  cases minus <;> simp only [standardKernelFeature,standardKernelComponent,
    Bool.false_eq_true,if_false,if_true]
  ring

theorem standardKernelFeature_degree (a : ℝ) (ha : physical a) (d : ℕ) (hd : 4≤d)
    (minus : Bool) (t : StandardTag) (ht : t∈standardTagList d) :
    (standardKernelFeature minus a t).totalDegree≤d := by
  rw [standardKernelFeature_raw_sub]
  apply polyDegree_sub_le
  · exact s3StandardRaw_degree d hd minus _ (List.mem_map.mpr ⟨t,ht,rfl⟩)
  · cases minus
    · exact (standardProjector_degree a ha _ _ _).trans hd
    · exact (polyDegree_sub_le _ _ _ (standardProjector_degree a ha _ _ _)
        (standardProjector_degree a ha _ _ _)).trans hd

theorem parityKernelFeature_degree (a : ℝ) (ha : physical a) (d : ℕ) (hd : 4≤d)
    (odd : Bool) (t : Tag) (ht : t∈parityTagList (d-(if odd then 1 else 0))) :
    (parityKernelFeature odd a t).totalDegree≤d := by
  have hw := ((parityTagList_spec _).2.2 t).mp ht
  cases odd
  · simp only [parityKernelFeature,Bool.false_eq_true,if_false,one_mul]
    apply polyDegree_sub_le
    · exact (parityMonomial_degree t).trans (by simpa using hw)
    · exact (parityInterpolant_degree a ha false _).trans hd
  · simp only [parityKernelFeature,if_true]
    have hc : (parityMonomial t-parityInterpolant a true (paritySourceData a true t)).totalDegree≤d-1 := by
      apply polyDegree_sub_le
      · exact (parityMonomial_degree t).trans hw
      · exact (parityInterpolant_degree a ha true _).trans (by dsimp;omega)
    exact (polyDegree_mul_le _ _ 1 (d-1) parityOdd_degree hc).trans (by omega)

theorem freeRows_bound (n : ℕ) (pivots : List ℕ) (i : ℕ) (hi : i∈freeRows n pivots) : i<n := by
  have h := List.mem_filter.mp hi
  exact List.mem_range.mp h.1

theorem source_getD_mem {α : Type*} (l : List α) (default : α) (i : ℕ) (hi : i<l.length) :
    l[i]?.getD default∈l := by
  simp only [List.getElem?_eq_getElem hi,Option.getD_some]
  exact List.getElem_mem hi

theorem scalarS3PlusFeatures_spec (a : ℝ) (ha : physical a) (d : ℕ) (hd : 4≤d)
    (p : Poly3) (hp : p∈scalarS3PlusFeatures a d) :
    p.totalDegree≤d ∧ ∀ r σ,MvPolynomial.eval (permutedContact a r σ) p=0 := by
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
  exact ⟨invariantKernelFeature_degree a ha d hd _
    (source_getD_mem _ _ i (freeRows_bound _ _ i hi)),invariantKernelFeature_vanish a ha _⟩

theorem scalarS3SignFeatures_spec (a : ℝ) (ha : physical a) (d : ℕ) (hd : 4≤d)
    (p : Poly3) (hp : p∈scalarS3SignFeatures a d) :
    p.totalDegree≤d ∧ ∀ r σ,MvPolynomial.eval (permutedContact a r σ) p=0 := by
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
  exact ⟨signKernelFeature_degree a ha d hd _
    (source_getD_mem _ _ i (freeRows_bound _ _ i hi)),signKernelFeature_vanish a ha _⟩

theorem scalarS3StandardFeatures_spec (a : ℝ) (ha : physical a) (d : ℕ) (hd : 4≤d)
    (minus : Bool) (p : Poly3) (hp : p∈scalarS3StandardFeatures minus a d) :
    p.totalDegree≤d ∧ ∀ r σ,MvPolynomial.eval (permutedContact a r σ) p=0 := by
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
  exact ⟨standardKernelFeature_degree a ha d hd minus _
    (source_getD_mem _ _ i (freeRows_bound _ _ i hi)),standardKernelFeature_vanish minus a ha _⟩

theorem scalarS2Features_spec (a : ℝ) (ha : physical a) (d : ℕ) (hd : 4≤d)
    (odd : Bool) (p : Poly3) (hp : p∈scalarS2Features odd a d) :
    p.totalDegree≤d ∧ ∀ r σ,MvPolynomial.eval (permutedContact a r σ) p=0 := by
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
  exact ⟨parityKernelFeature_degree a ha d hd odd _
    (source_getD_mem _ _ i (freeRows_bound _ _ i hi)),parityKernelFeature_vanish a ha odd _⟩

theorem scalarBlockFeatures_spec (a : ℝ) (ha : physical a) (d : ℕ) (hd : 6≤d)
    (b : ScalarBlockName) (g : List Poly3) (hg : g∈scalarBlockFeatures b a d)
    (p : Poly3) (hp : p∈g) :
    p.totalDegree≤ scalarBlockAllowance b d ∧
      ∀ r σ,MvPolynomial.eval (permutedContact a r σ) p=0 := by
  cases b <;> simp only [scalarBlockFeatures,List.mem_cons,List.not_mem_nil,or_false] at hg
  · subst g; exact scalarS3PlusFeatures_spec a ha d (by omega) p hp
  · subst g; exact scalarS3SignFeatures_spec a ha d (by omega) p hp
  · rcases hg with rfl | rfl
    · exact scalarS3StandardFeatures_spec a ha d (by omega) false p hp
    · exact scalarS3StandardFeatures_spec a ha d (by omega) true p hp
  · subst g; exact scalarS2Features_spec a ha (d-1) (by omega) false p hp
  · subst g; exact scalarS2Features_spec a ha (d-1) (by omega) true p hp
  · subst g; exact scalarS3PlusFeatures_spec a ha (d-2) (by omega) p hp
  · subst g; exact scalarS3SignFeatures_spec a ha (d-2) (by omega) p hp
  · rcases hg with rfl | rfl
    · exact scalarS3StandardFeatures_spec a ha (d-2) (by omega) false p hp
    · exact scalarS3StandardFeatures_spec a ha (d-2) (by omega) true p hp

theorem sourceCatalogue_covers (s2 : Bool) (d : ℕ) (hl : 4≤d) (hu : d≤9) :
    ∃ i : Fin 12,(RawCatalogue.entries i).s2=s2 ∧ (RawCatalogue.entries i).degree=d ∧
      RawCatalogue.EntryAgrees (RawCatalogue.entries i) := by
  have he : ∃ i : Fin 12,(RawCatalogue.entries i).s2=s2 ∧ (RawCatalogue.entries i).degree=d := by
    interval_cases d <;> cases s2 <;> decide
  obtain ⟨i,hi,hd⟩ := he
  exact ⟨i,hi,hd,RawCatalogue.source_catalogue_verified i⟩

theorem canonical_scalar_kernels : CanonicalScalarKernelsContract :=
  ⟨kernels_finite_layout_linkage,kernels_s3_vanishing,kernels_standard_metric,
    scalarBlockFeatures_spec,kernelColumnVector_free,parityKernelFeature_expansion⟩

#check canonical_scalar_kernels
#print axioms canonical_scalar_kernels
#check CanonicalScalarKernelsContract
#print axioms CanonicalScalarKernelsContract
end Blueprint.Thomson.Finite
