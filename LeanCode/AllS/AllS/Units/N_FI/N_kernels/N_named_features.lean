import AllS.Units.N_F.N_sympoly
import AllS.Units.N_FI.N_moment_kernels.N_canonical_QSR
import AllS.Units.N_FI.N_contact_interpolation.N_trivial_sign_parts

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

/-- The literal `P,Q,Z,W,ODD` formulas in canonical.py. -/
def standardPPoly (i : Fin 3) : Poly3 := MvPolynomial.X i-MvPolynomial.C (1/3)*sigma
def standardQPoly (i : Fin 3) : Poly3 :=
  standardPPoly i^2-MvPolynomial.C (1/3)*(∑ j : Fin 3,standardPPoly j^2)
def parityZ : Poly3 := MvPolynomial.X 1+MvPolynomial.X 2
def parityW : Poly3 := MvPolynomial.X 1*MvPolynomial.X 2
def parityOdd : Poly3 := MvPolynomial.X 1-MvPolynomial.X 2

def parityWeight (t : Tag) : ℕ := t.1+t.2.1+2*t.2.2
def parityKey (t : Tag) : TagKey :=
  toLex (parityWeight t,toLex (t.1,toLex (t.2.1,t.2.2)))
def parityLE (t u : Tag) : Prop := parityKey t ≤ parityKey u

local instance : DecidableRel parityLE := fun t u =>
  inferInstanceAs (Decidable (parityKey t ≤ parityKey u))
local instance : IsTrans Tag parityLE := ⟨fun _ _ _ h₁ h₂ => le_trans h₁ h₂⟩
local instance : Std.Antisymm parityLE := ⟨fun _ _ h₁ h₂ => by
  have h := congrArg tagOfKey (le_antisymm h₁ h₂)
  exact h⟩
local instance : Std.Total parityLE := ⟨fun t u => le_total (parityKey t) (parityKey u)⟩

def ParityTags (d : ℕ) : Finset Tag :=
  ((Finset.range (d+1)).product
    ((Finset.range (d+1)).product (Finset.range (d/2+1)))).filter
      (fun t => parityWeight t ≤ d)
def parityTagList (d : ℕ) : List Tag := (ParityTags d).sort parityLE

def parityMonomial (t : Tag) : Poly3 :=
  MvPolynomial.X 0^t.1*parityZ^t.2.1*parityW^t.2.2

abbrev StandardTag := Bool × Tag
/-- False labels p; true labels q. Source concatenation is preserved. -/
def standardTagList (d : ℕ) : List StandardTag :=
  (invariantTagList (d-1)).map (false,·) ++ (invariantTagList (d-2)).map (true,·)
def standardRawFeature (minus : Bool) (t : StandardTag) : Poly3 :=
  (if t.1 then
    (if minus then standardQPoly 1-standardQPoly 2 else standardQPoly 0)
   else (if minus then standardPPoly 1-standardPPoly 2 else standardPPoly 0))*
    invariantMonomial t.2

def s3PlusRaw (d : ℕ) : List Poly3 := (invariantTagList d).map invariantMonomial
def s3SignRaw (d : ℕ) : List Poly3 :=
  (invariantTagList (d-3)).map (fun t => deltaPoly*invariantMonomial t)
def s3StandardRaw (minus : Bool) (d : ℕ) : List Poly3 :=
  (standardTagList d).map (standardRawFeature minus)
def s2EvenRaw (d : ℕ) : List Poly3 := (parityTagList d).map parityMonomial
def s2OddRaw (d : ℕ) : List Poly3 :=
  (parityTagList (d-1)).map (fun t => parityOdd*parityMonomial t)

/-- Pivot positions are indices in the actual sorted source lists. -/
def invariantPivots (d : ℕ) : List ℕ :=
  (List.range 5).map (fun i => (invariantTagList d).idxOf (i,0,0))
def signPivots (d : ℕ) : List ℕ :=
  (List.range 2).map (fun i => (invariantTagList (d-3)).idxOf (i,0,0))
def standardPivots (d : ℕ) : List ℕ :=
  (List.range 4).map (fun i => (standardTagList d).idxOf (false,i,0,0)) ++
  (List.range 3).map (fun i => (standardTagList d).idxOf (true,i,0,0))
def evenFiberSizes : Fin 4 → ℕ := ![4,3,3,2]
def oddFiberSizes : Fin 4 → ℕ := ![3,3,2,1]
def parityPivotTags (odd : Bool) : List Tag :=
  (List.finRange 4).flatMap (fun i =>
    (List.range ((if odd then oddFiberSizes else evenFiberSizes) i)).map (fun j => (i.val,j,0)))
def parityPivots (odd : Bool) (d : ℕ) : List ℕ :=
  (parityPivotTags odd).map (fun t => (parityTagList (d-(if odd then 1 else 0))).idxOf t)
def freeRows (n : ℕ) (pivots : List ℕ) : List ℕ :=
  (List.range n).filter (fun i => i ∉ pivots)

def NamedFeaturesContract : Prop :=
  (∀ d, (parityTagList d).Nodup ∧
    (parityTagList d).Pairwise (fun t u => parityKey t ≤ parityKey u) ∧
    ∀ t, t ∈ parityTagList d ↔ parityWeight t ≤ d) ∧
  (∀ d, 4 ≤ d →
    (∀ p ∈ s3PlusRaw d, p.totalDegree ≤ d) ∧
    (∀ p ∈ s3SignRaw d, p.totalDegree ≤ d) ∧
    (∀ b, ∀ p ∈ s3StandardRaw b d, p.totalDegree ≤ d) ∧
    (∀ p ∈ s2EvenRaw d, p.totalDegree ≤ d) ∧
    (∀ p ∈ s2OddRaw d, p.totalDegree ≤ d))

theorem mem_ParityTags {d : ℕ} {t : Tag} : t ∈ ParityTags d ↔ parityWeight t ≤ d := by
  rcases t with ⟨i,j,k⟩
  simp only [ParityTags,Finset.mem_filter,Finset.product_eq_sprod,Finset.mem_product,Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨?_,?_,?_⟩,h⟩ <;> dsimp [parityWeight] at h <;> omega

theorem parityTagList_spec (d : ℕ) : (parityTagList d).Nodup ∧
    (parityTagList d).Pairwise (fun t u => parityKey t ≤ parityKey u) ∧
    ∀ t, t ∈ parityTagList d ↔ parityWeight t ≤ d := by
  refine ⟨Finset.sort_nodup _ _,Finset.pairwise_sort (ParityTags d) parityLE,?_⟩
  intro t
  simp only [parityTagList,Finset.mem_sort,mem_ParityTags]

theorem invariantMonomial_degree (t : Tag) : (invariantMonomial t).totalDegree ≤ tagWeight t := by
  have h := (sympoly_monomial_grade (tagExponent t) (1 : ℝ)).totalDegree_le
  rw [weight_tagExponent] at h
  simpa [invariantSubst_monomial,tagExponent,invariantMonomial] using h

theorem sigma_degree : sigma.totalDegree ≤ 1 := sigma_homogeneous.totalDegree_le

theorem standardPPoly_degree (i : Fin 3) : (standardPPoly i).totalDegree ≤ 1 := by
  apply polyDegree_sub_le
  · simp
  · exact (polyDegree_C_mul_le _ _).trans sigma_degree

theorem standardQPoly_degree (i : Fin 3) : (standardQPoly i).totalDegree ≤ 2 := by
  have hp (j : Fin 3) : (standardPPoly j^2).totalDegree ≤ 2 :=
    (MvPolynomial.totalDegree_pow _ _).trans (by have h := standardPPoly_degree j; omega)
  apply polyDegree_sub_le
  · exact hp i
  · apply (polyDegree_C_mul_le _ _).trans
    exact MvPolynomial.totalDegree_finsetSum_le (fun j hj => hp j)

theorem deltaPoly_degree : deltaPoly.totalDegree ≤ 3 := by
  have hx (i j : Fin 3) : ((MvPolynomial.X i-MvPolynomial.X j) : Poly3).totalDegree ≤ 1 :=
    polyDegree_sub_le _ _ _ (by simp) (by simp)
  exact polyDegree_mul_le _ _ 2 1
    (polyDegree_mul_le _ _ 1 1 (hx 0 1) (hx 0 2)) (hx 1 2)

theorem parityZ_degree : parityZ.totalDegree ≤ 1 :=
  polyDegree_add_le _ _ _ (by simp) (by simp)
theorem parityW_degree : parityW.totalDegree ≤ 2 :=
  polyDegree_mul_le _ _ 1 1 (by simp) (by simp)
theorem parityOdd_degree : parityOdd.totalDegree ≤ 1 :=
  polyDegree_sub_le _ _ _ (by simp) (by simp)

theorem parityMonomial_degree (t : Tag) : (parityMonomial t).totalDegree ≤ parityWeight t := by
  have hZ : (parityZ^t.2.1).totalDegree ≤ t.2.1 :=
    (MvPolynomial.totalDegree_pow _ _).trans (by simpa using Nat.mul_le_mul_left t.2.1 parityZ_degree)
  have hW : (parityW^t.2.2).totalDegree ≤ 2*t.2.2 :=
    (MvPolynomial.totalDegree_pow _ _).trans (by simpa [Nat.mul_comm] using Nat.mul_le_mul_left t.2.2 parityW_degree)
  exact polyDegree_mul_le _ _ (t.1+t.2.1) (2*t.2.2)
    (polyDegree_mul_le _ _ t.1 t.2.1 (by simp) hZ) hW

theorem standardRawFeature_degree (minus : Bool) (t : StandardTag) :
    (standardRawFeature minus t).totalDegree ≤ (if t.1 then 2 else 1)+tagWeight t.2 := by
  apply polyDegree_mul_le
  · cases ht : t.1 <;> cases minus <;> simp only [Bool.false_eq_true,if_false,if_true]
    · exact standardPPoly_degree 0
    · exact polyDegree_sub_le _ _ _ (standardPPoly_degree 1) (standardPPoly_degree 2)
    · exact standardQPoly_degree 0
    · exact polyDegree_sub_le _ _ _ (standardQPoly_degree 1) (standardQPoly_degree 2)
  · exact invariantMonomial_degree _

theorem s3PlusRaw_degree (d : ℕ) (p : Poly3) (hp : p ∈ s3PlusRaw d) : p.totalDegree ≤ d := by
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hp
  exact (invariantMonomial_degree t).trans (mem_invariantTagList.mp ht)

theorem s3SignRaw_degree (d : ℕ) (hd : 4 ≤ d) (p : Poly3) (hp : p ∈ s3SignRaw d) :
    p.totalDegree ≤ d := by
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hp
  have hw := mem_invariantTagList.mp ht
  exact (polyDegree_mul_le _ _ _ _ deltaPoly_degree (invariantMonomial_degree t)).trans (by omega)

theorem s3StandardRaw_degree (d : ℕ) (hd : 4 ≤ d) (b : Bool) (p : Poly3)
    (hp : p ∈ s3StandardRaw b d) : p.totalDegree ≤ d := by
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hp
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
    have hw := mem_invariantTagList.mp hu
    exact (standardRawFeature_degree b (false,u)).trans (by dsimp; omega)
  · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp ht
    have hw := mem_invariantTagList.mp hu
    exact (standardRawFeature_degree b (true,u)).trans (by dsimp; omega)

theorem s2EvenRaw_degree (d : ℕ) (p : Poly3) (hp : p ∈ s2EvenRaw d) : p.totalDegree ≤ d := by
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hp
  have hw := (parityTagList_spec d).2.2 t |>.mp ht
  exact (parityMonomial_degree t).trans hw

theorem s2OddRaw_degree (d : ℕ) (hd : 4 ≤ d) (p : Poly3) (hp : p ∈ s2OddRaw d) :
    p.totalDegree ≤ d := by
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hp
  have hw := (parityTagList_spec (d-1)).2.2 t |>.mp ht
  exact (polyDegree_mul_le _ _ _ _ parityOdd_degree (parityMonomial_degree t)).trans (by omega)

theorem kernels_named_features : NamedFeaturesContract := by
  refine ⟨parityTagList_spec,?_⟩
  intro d hd
  exact ⟨s3PlusRaw_degree d,s3SignRaw_degree d hd,s3StandardRaw_degree d hd,
    s2EvenRaw_degree d,s2OddRaw_degree d hd⟩

#check kernels_named_features
#print axioms kernels_named_features

#check NamedFeaturesContract
#print axioms NamedFeaturesContract
end Blueprint.Thomson.Finite
