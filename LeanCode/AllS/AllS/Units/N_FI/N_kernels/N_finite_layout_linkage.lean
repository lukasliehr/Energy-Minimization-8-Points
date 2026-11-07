import Mathlib.Algebra.MvPolynomial.Funext
import AllS.Generated.FiniteRawCatalogue
import AllS.Units.N_FI.N_kernels.N_s3_vanishing
import AllS.Units.N_FI.N_kernels.N_parity_interpolation
import AllS.Units.N_FI.N_kernels.N_standard_metric

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite
namespace RawCatalogue

abbrev RatPoly3 := MvPolynomial (Fin 3) ℚ

def ratSigma : RatPoly3 := MvPolynomial.X 0+MvPolynomial.X 1+MvPolynomial.X 2
def ratE2 : RatPoly3 := MvPolynomial.X 0*MvPolynomial.X 1+MvPolynomial.X 0*MvPolynomial.X 2+
  MvPolynomial.X 1*MvPolynomial.X 2
def ratE3 : RatPoly3 := MvPolynomial.X 0*MvPolynomial.X 1*MvPolynomial.X 2
def ratInvariant (t : Tag) : RatPoly3 := ratSigma^t.1*ratE2^t.2.1*ratE3^t.2.2
def ratDelta : RatPoly3 := (MvPolynomial.X 0-MvPolynomial.X 1)*(MvPolynomial.X 0-MvPolynomial.X 2)*
  (MvPolynomial.X 1-MvPolynomial.X 2)
def ratP (i : Fin 3) : RatPoly3 := MvPolynomial.X i-MvPolynomial.C (1/3)*ratSigma
def ratQ (i : Fin 3) : RatPoly3 := ratP i^2-MvPolynomial.C (1/3)*(∑ j : Fin 3,ratP j^2)
def ratParity (t : Tag) : RatPoly3 := MvPolynomial.X 0^t.1*(MvPolynomial.X 1+MvPolynomial.X 2)^t.2.1*
  (MvPolynomial.X 1*MvPolynomial.X 2)^t.2.2
def ratOdd : RatPoly3 := MvPolynomial.X 1-MvPolynomial.X 2

def ratStandard (minus : Bool) (t : StandardTag) : RatPoly3 :=
  (if t.1 then (if minus then ratQ 1-ratQ 2 else ratQ 0)
   else (if minus then ratP 1-ratP 2 else ratP 0))*ratInvariant t.2

def sparsePolynomial (p : SparsePoly) : RatPoly3 :=
  (p.map (fun e => MvPolynomial.C e.2*MvPolynomial.X 0^e.1.1*
    MvPolynomial.X 1^e.1.2.1*MvPolynomial.X 2^e.1.2.2)).sum

def expectedGroups (s2 : Bool) (d : ℕ) : List (List RatPoly3) :=
  if s2 then [(parityTagList d).map ratParity,
    (parityTagList (d-1)).map (fun t => ratOdd*ratParity t)]
  else [(invariantTagList d).map ratInvariant,
    (invariantTagList (d-3)).map (fun t => ratDelta*ratInvariant t),
    (standardTagList d).map (ratStandard false),(standardTagList d).map (ratStandard true)]

def encodeTag (t : Tag) : List ℕ := [t.1,t.2.1,t.2.2]
def encodeStandardTag (t : StandardTag) : List ℕ := (if t.1 then 1 else 0)::encodeTag t.2

def expectedTags (s2 : Bool) (d : ℕ) : List (List (List ℕ)) :=
  if s2 then [(parityTagList d).map encodeTag,(parityTagList (d-1)).map encodeTag]
  else [(invariantTagList d).map encodeTag,(invariantTagList (d-3)).map encodeTag,
    (standardTagList d).map encodeStandardTag,(standardTagList d).map encodeStandardTag]

def expectedPivots (s2 : Bool) (d : ℕ) : List (List ℕ) :=
  if s2 then [parityPivots false d,parityPivots true d]
  else [invariantPivots d,signPivots d,standardPivots d,standardPivots d]
def expectedFrees (s2 : Bool) (d : ℕ) : List (List ℕ) :=
  List.zipWith (fun tags pivots => freeRows tags.length pivots) (expectedTags s2 d) (expectedPivots s2 d)

def EntryAgrees (e : Entry) : Prop :=
  e.tags=expectedTags e.s2 e.degree ∧ e.pivots=expectedPivots e.s2 e.degree ∧
  e.frees=expectedFrees e.s2 e.degree ∧
  e.groups.map (List.map sparsePolynomial)=expectedGroups e.s2 e.degree

end RawCatalogue

def FiniteLayoutLinkageContract : Prop :=
  (∀ i : Fin 12, RawCatalogue.EntryAgrees (RawCatalogue.entries i)) ∧
  (∀ s2 d, (RawCatalogue.expectedGroups s2 d).map (List.map (MvPolynomial.map (Rat.castHom ℝ)))=
    if s2 then [s2EvenRaw d,s2OddRaw d] else [s3PlusRaw d,s3SignRaw d,s3StandardRaw false d,s3StandardRaw true d])

namespace RawCatalogue

def ratToReal : RatPoly3 →+* Poly3 := MvPolynomial.map (Rat.castHom ℝ)

theorem ratSigma_map : ratToReal ratSigma=sigma := by simp [ratToReal,ratSigma,sigma]
theorem ratE2_map : ratToReal ratE2=e2 := by simp [ratToReal,ratE2,e2]
theorem ratE3_map : ratToReal ratE3=e3 := by simp [ratToReal,ratE3,e3]
theorem ratDelta_map : ratToReal ratDelta=deltaPoly := by simp [ratToReal,ratDelta,deltaPoly]
theorem ratInvariant_map (t : Tag) : ratToReal (ratInvariant t)=invariantMonomial t := by
  simp [ratInvariant,map_mul,map_pow,ratSigma_map,ratE2_map,ratE3_map,invariantMonomial]
@[simp] theorem ratToReal_C (q : ℚ) : ratToReal (MvPolynomial.C q)=MvPolynomial.C (q : ℝ) := by
  simp [ratToReal]
@[simp] theorem ratToReal_X (i : Fin 3) : ratToReal (MvPolynomial.X i)=MvPolynomial.X i := by
  simp [ratToReal]

theorem ratP_map (i : Fin 3) : ratToReal (ratP i)=standardPPoly i := by
  simp only [ratP,standardPPoly,map_sub,map_mul,ratSigma_map,ratToReal_C,ratToReal_X]
  norm_num
theorem ratQ_map (i : Fin 3) : ratToReal (ratQ i)=standardQPoly i := by
  simp only [ratQ,standardQPoly,map_sub,map_mul,map_pow,map_sum,ratP_map,ratToReal_C]
  norm_num
theorem ratParity_map (t : Tag) : ratToReal (ratParity t)=parityMonomial t := by
  simp [ratParity,parityMonomial,parityZ,parityW,ratToReal]
theorem ratOdd_map : ratToReal ratOdd=parityOdd := by simp [ratOdd,parityOdd,ratToReal]
theorem ratStandard_map (b : Bool) (t : StandardTag) : ratToReal (ratStandard b t)=standardRawFeature b t := by
  cases ht : t.1 <;> cases b <;>
    simp [ratStandard,standardRawFeature,ht,map_mul,map_sub,ratP_map,ratQ_map,ratInvariant_map]

theorem expectedGroups_map (s2 : Bool) (d : ℕ) :
    (expectedGroups s2 d).map (List.map (MvPolynomial.map (Rat.castHom ℝ)))=
      if s2 then [s2EvenRaw d,s2OddRaw d] else [s3PlusRaw d,s3SignRaw d,s3StandardRaw false d,s3StandardRaw true d] := by
  change (expectedGroups s2 d).map (List.map ratToReal)=_
  cases s2 <;>
    simp [expectedGroups,s3PlusRaw,s3SignRaw,s3StandardRaw,s2EvenRaw,s2OddRaw,
      List.map_map,Function.comp_def,ratInvariant_map,map_mul,ratDelta_map,ratStandard_map,
      ratParity_map,ratOdd_map]

local instance : DecidableRel tagLE := fun t u => inferInstanceAs (Decidable (tagKey t≤tagKey u))
local instance : IsTrans Tag tagLE := ⟨fun _ _ _ h₁ h₂ => le_trans h₁ h₂⟩
local instance : Std.Antisymm tagLE := ⟨fun _ _ h₁ h₂ => tagKey_injective (le_antisymm h₁ h₂)⟩
local instance : Std.Total tagLE := ⟨fun t u => le_total (tagKey t) (tagKey u)⟩
local instance : DecidableRel parityLE := fun t u => inferInstanceAs (Decidable (parityKey t≤parityKey u))
local instance : IsTrans Tag parityLE := ⟨fun _ _ _ h₁ h₂ => le_trans h₁ h₂⟩
local instance : Std.Antisymm parityLE := ⟨fun _ _ h₁ h₂ => by
  exact congrArg tagOfKey (le_antisymm h₁ h₂)⟩
local instance : Std.Total parityLE := ⟨fun t u => le_total (parityKey t) (parityKey u)⟩

theorem invariantTagList_literal (D : ℕ) (l : List Tag) (hn : l.Nodup)
    (he : l.toFinset=InvariantTags D) (hs : l.Pairwise tagLE) : invariantTagList D=l := by
  unfold invariantTagList
  rw [← he]
  exact (List.toFinset_sort (r:=tagLE) hn).2 hs

theorem parityTagList_literal (D : ℕ) (l : List Tag) (hn : l.Nodup)
    (he : l.toFinset=ParityTags D) (hs : l.Pairwise parityLE) : parityTagList D=l := by
  unfold parityTagList
  rw [← he]
  exact (List.toFinset_sort (r:=parityLE) hn).2 hs

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem invariantTagList_1 : invariantTagList 1 = [(0,0,0),(1,0,0)] := by
  apply invariantTagList_literal <;> decide

theorem invariantTagList_2 : invariantTagList 2 = [(0,0,0),(1,0,0),(0,1,0),(2,0,0)] := by
  apply invariantTagList_literal <;> decide

theorem invariantTagList_3 : invariantTagList 3 = [(0,0,0),(1,0,0),(0,1,0),(2,0,0),(0,0,1),(1,1,0),(3,0,0)] := by
  apply invariantTagList_literal <;> decide

theorem invariantTagList_4 : invariantTagList 4 = [(0,0,0),(1,0,0),(0,1,0),(2,0,0),(0,0,1),(1,1,0),(3,0,0),(0,2,0),(1,0,1),(2,1,0),(4,0,0)] := by
  apply invariantTagList_literal <;> decide

theorem invariantTagList_5 : invariantTagList 5 = [(0,0,0),(1,0,0),(0,1,0),(2,0,0),(0,0,1),(1,1,0),(3,0,0),(0,2,0),(1,0,1),(2,1,0),(4,0,0),(0,1,1),(1,2,0),(2,0,1),(3,1,0),(5,0,0)] := by
  apply invariantTagList_literal <;> decide

theorem invariantTagList_6 : invariantTagList 6 = [(0,0,0),(1,0,0),(0,1,0),(2,0,0),(0,0,1),(1,1,0),(3,0,0),(0,2,0),(1,0,1),(2,1,0),(4,0,0),(0,1,1),(1,2,0),(2,0,1),(3,1,0),(5,0,0),(0,0,2),(0,3,0),(1,1,1),(2,2,0),(3,0,1),(4,1,0),(6,0,0)] := by
  apply invariantTagList_literal <;> decide

theorem invariantTagList_7 : invariantTagList 7 = [(0,0,0),(1,0,0),(0,1,0),(2,0,0),(0,0,1),(1,1,0),(3,0,0),(0,2,0),(1,0,1),(2,1,0),(4,0,0),(0,1,1),(1,2,0),(2,0,1),(3,1,0),(5,0,0),(0,0,2),(0,3,0),(1,1,1),(2,2,0),(3,0,1),(4,1,0),(6,0,0),(0,2,1),(1,0,2),(1,3,0),(2,1,1),(3,2,0),(4,0,1),(5,1,0),(7,0,0)] := by
  apply invariantTagList_literal <;> decide

theorem invariantTagList_8 : invariantTagList 8 = [(0,0,0),(1,0,0),(0,1,0),(2,0,0),(0,0,1),(1,1,0),(3,0,0),(0,2,0),(1,0,1),(2,1,0),(4,0,0),(0,1,1),(1,2,0),(2,0,1),(3,1,0),(5,0,0),(0,0,2),(0,3,0),(1,1,1),(2,2,0),(3,0,1),(4,1,0),(6,0,0),(0,2,1),(1,0,2),(1,3,0),(2,1,1),(3,2,0),(4,0,1),(5,1,0),(7,0,0),(0,1,2),(0,4,0),(1,2,1),(2,0,2),(2,3,0),(3,1,1),(4,2,0),(5,0,1),(6,1,0),(8,0,0)] := by
  apply invariantTagList_literal <;> decide

theorem invariantTagList_9 : invariantTagList 9 = [(0,0,0),(1,0,0),(0,1,0),(2,0,0),(0,0,1),(1,1,0),(3,0,0),(0,2,0),(1,0,1),(2,1,0),(4,0,0),(0,1,1),(1,2,0),(2,0,1),(3,1,0),(5,0,0),(0,0,2),(0,3,0),(1,1,1),(2,2,0),(3,0,1),(4,1,0),(6,0,0),(0,2,1),(1,0,2),(1,3,0),(2,1,1),(3,2,0),(4,0,1),(5,1,0),(7,0,0),(0,1,2),(0,4,0),(1,2,1),(2,0,2),(2,3,0),(3,1,1),(4,2,0),(5,0,1),(6,1,0),(8,0,0),(0,0,3),(0,3,1),(1,1,2),(1,4,0),(2,2,1),(3,0,2),(3,3,0),(4,1,1),(5,2,0),(6,0,1),(7,1,0),(9,0,0)] := by
  apply invariantTagList_literal <;> decide

theorem parityTagList_3 : parityTagList 3 = [(0,0,0),(0,1,0),(1,0,0),(0,0,1),(0,2,0),(1,1,0),(2,0,0),(0,1,1),(0,3,0),(1,0,1),(1,2,0),(2,1,0),(3,0,0)] := by
  apply parityTagList_literal <;> decide

theorem parityTagList_4 : parityTagList 4 = [(0,0,0),(0,1,0),(1,0,0),(0,0,1),(0,2,0),(1,1,0),(2,0,0),(0,1,1),(0,3,0),(1,0,1),(1,2,0),(2,1,0),(3,0,0),(0,0,2),(0,2,1),(0,4,0),(1,1,1),(1,3,0),(2,0,1),(2,2,0),(3,1,0),(4,0,0)] := by
  apply parityTagList_literal <;> decide

theorem parityTagList_5 : parityTagList 5 = [(0,0,0),(0,1,0),(1,0,0),(0,0,1),(0,2,0),(1,1,0),(2,0,0),(0,1,1),(0,3,0),(1,0,1),(1,2,0),(2,1,0),(3,0,0),(0,0,2),(0,2,1),(0,4,0),(1,1,1),(1,3,0),(2,0,1),(2,2,0),(3,1,0),(4,0,0),(0,1,2),(0,3,1),(0,5,0),(1,0,2),(1,2,1),(1,4,0),(2,1,1),(2,3,0),(3,0,1),(3,2,0),(4,1,0),(5,0,0)] := by
  apply parityTagList_literal <;> decide

theorem parityTagList_6 : parityTagList 6 = [(0,0,0),(0,1,0),(1,0,0),(0,0,1),(0,2,0),(1,1,0),(2,0,0),(0,1,1),(0,3,0),(1,0,1),(1,2,0),(2,1,0),(3,0,0),(0,0,2),(0,2,1),(0,4,0),(1,1,1),(1,3,0),(2,0,1),(2,2,0),(3,1,0),(4,0,0),(0,1,2),(0,3,1),(0,5,0),(1,0,2),(1,2,1),(1,4,0),(2,1,1),(2,3,0),(3,0,1),(3,2,0),(4,1,0),(5,0,0),(0,0,3),(0,2,2),(0,4,1),(0,6,0),(1,1,2),(1,3,1),(1,5,0),(2,0,2),(2,2,1),(2,4,0),(3,1,1),(3,3,0),(4,0,1),(4,2,0),(5,1,0),(6,0,0)] := by
  apply parityTagList_literal <;> decide

theorem parityTagList_7 : parityTagList 7 = [(0,0,0),(0,1,0),(1,0,0),(0,0,1),(0,2,0),(1,1,0),(2,0,0),(0,1,1),(0,3,0),(1,0,1),(1,2,0),(2,1,0),(3,0,0),(0,0,2),(0,2,1),(0,4,0),(1,1,1),(1,3,0),(2,0,1),(2,2,0),(3,1,0),(4,0,0),(0,1,2),(0,3,1),(0,5,0),(1,0,2),(1,2,1),(1,4,0),(2,1,1),(2,3,0),(3,0,1),(3,2,0),(4,1,0),(5,0,0),(0,0,3),(0,2,2),(0,4,1),(0,6,0),(1,1,2),(1,3,1),(1,5,0),(2,0,2),(2,2,1),(2,4,0),(3,1,1),(3,3,0),(4,0,1),(4,2,0),(5,1,0),(6,0,0),(0,1,3),(0,3,2),(0,5,1),(0,7,0),(1,0,3),(1,2,2),(1,4,1),(1,6,0),(2,1,2),(2,3,1),(2,5,0),(3,0,2),(3,2,1),(3,4,0),(4,1,1),(4,3,0),(5,0,1),(5,2,0),(6,1,0),(7,0,0)] := by
  apply parityTagList_literal <;> decide

theorem parityTagList_8 : parityTagList 8 = [(0,0,0),(0,1,0),(1,0,0),(0,0,1),(0,2,0),(1,1,0),(2,0,0),(0,1,1),(0,3,0),(1,0,1),(1,2,0),(2,1,0),(3,0,0),(0,0,2),(0,2,1),(0,4,0),(1,1,1),(1,3,0),(2,0,1),(2,2,0),(3,1,0),(4,0,0),(0,1,2),(0,3,1),(0,5,0),(1,0,2),(1,2,1),(1,4,0),(2,1,1),(2,3,0),(3,0,1),(3,2,0),(4,1,0),(5,0,0),(0,0,3),(0,2,2),(0,4,1),(0,6,0),(1,1,2),(1,3,1),(1,5,0),(2,0,2),(2,2,1),(2,4,0),(3,1,1),(3,3,0),(4,0,1),(4,2,0),(5,1,0),(6,0,0),(0,1,3),(0,3,2),(0,5,1),(0,7,0),(1,0,3),(1,2,2),(1,4,1),(1,6,0),(2,1,2),(2,3,1),(2,5,0),(3,0,2),(3,2,1),(3,4,0),(4,1,1),(4,3,0),(5,0,1),(5,2,0),(6,1,0),(7,0,0),(0,0,4),(0,2,3),(0,4,2),(0,6,1),(0,8,0),(1,1,3),(1,3,2),(1,5,1),(1,7,0),(2,0,3),(2,2,2),(2,4,1),(2,6,0),(3,1,2),(3,3,1),(3,5,0),(4,0,2),(4,2,1),(4,4,0),(5,1,1),(5,3,0),(6,0,1),(6,2,0),(7,1,0),(8,0,0)] := by
  apply parityTagList_literal <;> decide

theorem parityTagList_9 : parityTagList 9 = [(0,0,0),(0,1,0),(1,0,0),(0,0,1),(0,2,0),(1,1,0),(2,0,0),(0,1,1),(0,3,0),(1,0,1),(1,2,0),(2,1,0),(3,0,0),(0,0,2),(0,2,1),(0,4,0),(1,1,1),(1,3,0),(2,0,1),(2,2,0),(3,1,0),(4,0,0),(0,1,2),(0,3,1),(0,5,0),(1,0,2),(1,2,1),(1,4,0),(2,1,1),(2,3,0),(3,0,1),(3,2,0),(4,1,0),(5,0,0),(0,0,3),(0,2,2),(0,4,1),(0,6,0),(1,1,2),(1,3,1),(1,5,0),(2,0,2),(2,2,1),(2,4,0),(3,1,1),(3,3,0),(4,0,1),(4,2,0),(5,1,0),(6,0,0),(0,1,3),(0,3,2),(0,5,1),(0,7,0),(1,0,3),(1,2,2),(1,4,1),(1,6,0),(2,1,2),(2,3,1),(2,5,0),(3,0,2),(3,2,1),(3,4,0),(4,1,1),(4,3,0),(5,0,1),(5,2,0),(6,1,0),(7,0,0),(0,0,4),(0,2,3),(0,4,2),(0,6,1),(0,8,0),(1,1,3),(1,3,2),(1,5,1),(1,7,0),(2,0,3),(2,2,2),(2,4,1),(2,6,0),(3,1,2),(3,3,1),(3,5,0),(4,0,2),(4,2,1),(4,4,0),(5,1,1),(5,3,0),(6,0,1),(6,2,0),(7,1,0),(8,0,0),(0,1,4),(0,3,3),(0,5,2),(0,7,1),(0,9,0),(1,0,4),(1,2,3),(1,4,2),(1,6,1),(1,8,0),(2,1,3),(2,3,2),(2,5,1),(2,7,0),(3,0,3),(3,2,2),(3,4,1),(3,6,0),(4,1,2),(4,3,1),(4,5,0),(5,0,2),(5,2,1),(5,4,0),(6,1,1),(6,3,0),(7,0,1),(7,2,0),(8,1,0),(9,0,0)] := by
  apply parityTagList_literal <;> decide

theorem raw_identity_0000 : sparsePolynomial p0000=ratInvariant (0,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0000,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0001 : sparsePolynomial p0001=ratInvariant (1,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0001,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0002 : sparsePolynomial p0002=ratInvariant (0,1,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0002,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0003 : sparsePolynomial p0003=ratInvariant (2,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0003,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0004 : sparsePolynomial p0004=ratInvariant (0,0,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0004,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0005 : sparsePolynomial p0005=ratInvariant (1,1,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0005,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0006 : sparsePolynomial p0006=ratInvariant (3,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0006,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0007 : sparsePolynomial p0007=ratInvariant (0,2,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0007,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0008 : sparsePolynomial p0008=ratInvariant (1,0,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0008,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0009 : sparsePolynomial p0009=ratInvariant (2,1,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0009,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0010 : sparsePolynomial p0010=ratInvariant (4,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0010,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0011 : sparsePolynomial p0011=ratDelta*ratInvariant (0,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0011,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0012 : sparsePolynomial p0012=ratDelta*ratInvariant (1,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0012,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0013 : sparsePolynomial p0013=ratStandard false (false,(0,0,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0013,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0014 : sparsePolynomial p0014=ratStandard false (false,(1,0,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0014,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0015 : sparsePolynomial p0015=ratStandard false (false,(0,1,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0015,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0016 : sparsePolynomial p0016=ratStandard false (false,(2,0,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0016,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0017 : sparsePolynomial p0017=ratStandard false (false,(0,0,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0017,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0018 : sparsePolynomial p0018=ratStandard false (false,(1,1,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0018,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0019 : sparsePolynomial p0019=ratStandard false (false,(3,0,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0019,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0020 : sparsePolynomial p0020=ratStandard false (true,(0,0,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0020,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0021 : sparsePolynomial p0021=ratStandard false (true,(1,0,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0021,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0022 : sparsePolynomial p0022=ratStandard false (true,(0,1,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0022,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0023 : sparsePolynomial p0023=ratStandard false (true,(2,0,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0023,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0024 : sparsePolynomial p0024=ratStandard true (false,(0,0,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0024,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0025 : sparsePolynomial p0025=ratStandard true (false,(1,0,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0025,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0026 : sparsePolynomial p0026=ratStandard true (false,(0,1,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0026,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0027 : sparsePolynomial p0027=ratStandard true (false,(2,0,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0027,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0028 : sparsePolynomial p0028=ratStandard true (false,(0,0,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0028,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0029 : sparsePolynomial p0029=ratStandard true (false,(1,1,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0029,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0030 : sparsePolynomial p0030=ratStandard true (false,(3,0,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0030,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0031 : sparsePolynomial p0031=ratStandard true (true,(0,0,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0031,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0032 : sparsePolynomial p0032=ratStandard true (true,(1,0,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0032,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0033 : sparsePolynomial p0033=ratStandard true (true,(0,1,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0033,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0034 : sparsePolynomial p0034=ratStandard true (true,(2,0,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0034,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0035 : sparsePolynomial p0035=ratInvariant (0,1,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0035,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0036 : sparsePolynomial p0036=ratInvariant (1,2,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0036,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0037 : sparsePolynomial p0037=ratInvariant (2,0,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0037,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0038 : sparsePolynomial p0038=ratInvariant (3,1,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0038,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0039 : sparsePolynomial p0039=ratInvariant (5,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0039,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0040 : sparsePolynomial p0040=ratDelta*ratInvariant (0,1,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0040,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0041 : sparsePolynomial p0041=ratDelta*ratInvariant (2,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0041,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0042 : sparsePolynomial p0042=ratStandard false (false,(0,2,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0042,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0043 : sparsePolynomial p0043=ratStandard false (false,(1,0,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0043,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0044 : sparsePolynomial p0044=ratStandard false (false,(2,1,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0044,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0045 : sparsePolynomial p0045=ratStandard false (false,(4,0,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0045,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0046 : sparsePolynomial p0046=ratStandard false (true,(0,0,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0046,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0047 : sparsePolynomial p0047=ratStandard false (true,(1,1,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0047,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0048 : sparsePolynomial p0048=ratStandard false (true,(3,0,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0048,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0049 : sparsePolynomial p0049=ratStandard true (false,(0,2,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0049,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0050 : sparsePolynomial p0050=ratStandard true (false,(1,0,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0050,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0051 : sparsePolynomial p0051=ratStandard true (false,(2,1,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0051,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0052 : sparsePolynomial p0052=ratStandard true (false,(4,0,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0052,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0053 : sparsePolynomial p0053=ratStandard true (true,(0,0,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0053,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0054 : sparsePolynomial p0054=ratStandard true (true,(1,1,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0054,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0055 : sparsePolynomial p0055=ratStandard true (true,(3,0,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0055,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0056 : sparsePolynomial p0056=ratInvariant (0,0,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0056,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0057 : sparsePolynomial p0057=ratInvariant (0,3,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0057,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0058 : sparsePolynomial p0058=ratInvariant (1,1,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0058,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0059 : sparsePolynomial p0059=ratInvariant (2,2,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0059,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0060 : sparsePolynomial p0060=ratInvariant (3,0,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0060,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0061 : sparsePolynomial p0061=ratInvariant (4,1,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0061,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0062 : sparsePolynomial p0062=ratInvariant (6,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0062,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0063 : sparsePolynomial p0063=ratDelta*ratInvariant (0,0,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0063,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0064 : sparsePolynomial p0064=ratDelta*ratInvariant (1,1,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0064,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0065 : sparsePolynomial p0065=ratDelta*ratInvariant (3,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0065,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0066 : sparsePolynomial p0066=ratStandard false (false,(0,1,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0066,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0067 : sparsePolynomial p0067=ratStandard false (false,(1,2,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0067,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0068 : sparsePolynomial p0068=ratStandard false (false,(2,0,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0068,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0069 : sparsePolynomial p0069=ratStandard false (false,(3,1,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0069,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0070 : sparsePolynomial p0070=ratStandard false (false,(5,0,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0070,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0071 : sparsePolynomial p0071=ratStandard false (true,(0,2,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0071,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0072 : sparsePolynomial p0072=ratStandard false (true,(1,0,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0072,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0073 : sparsePolynomial p0073=ratStandard false (true,(2,1,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0073,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0074 : sparsePolynomial p0074=ratStandard false (true,(4,0,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0074,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0075 : sparsePolynomial p0075=ratStandard true (false,(0,1,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0075,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0076 : sparsePolynomial p0076=ratStandard true (false,(1,2,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0076,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0077 : sparsePolynomial p0077=ratStandard true (false,(2,0,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0077,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0078 : sparsePolynomial p0078=ratStandard true (false,(3,1,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0078,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0079 : sparsePolynomial p0079=ratStandard true (false,(5,0,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0079,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0080 : sparsePolynomial p0080=ratStandard true (true,(0,2,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0080,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0081 : sparsePolynomial p0081=ratStandard true (true,(1,0,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0081,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0082 : sparsePolynomial p0082=ratStandard true (true,(2,1,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0082,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0083 : sparsePolynomial p0083=ratStandard true (true,(4,0,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0083,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0084 : sparsePolynomial p0084=ratInvariant (0,2,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0084,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0085 : sparsePolynomial p0085=ratInvariant (1,0,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0085,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0086 : sparsePolynomial p0086=ratInvariant (1,3,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0086,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0087 : sparsePolynomial p0087=ratInvariant (2,1,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0087,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0088 : sparsePolynomial p0088=ratInvariant (3,2,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0088,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0089 : sparsePolynomial p0089=ratInvariant (4,0,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0089,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0090 : sparsePolynomial p0090=ratInvariant (5,1,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0090,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0091 : sparsePolynomial p0091=ratInvariant (7,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0091,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0092 : sparsePolynomial p0092=ratDelta*ratInvariant (0,2,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0092,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0093 : sparsePolynomial p0093=ratDelta*ratInvariant (1,0,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0093,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0094 : sparsePolynomial p0094=ratDelta*ratInvariant (2,1,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0094,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0095 : sparsePolynomial p0095=ratDelta*ratInvariant (4,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0095,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0096 : sparsePolynomial p0096=ratStandard false (false,(0,0,2)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0096,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0097 : sparsePolynomial p0097=ratStandard false (false,(0,3,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0097,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0098 : sparsePolynomial p0098=ratStandard false (false,(1,1,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0098,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0099 : sparsePolynomial p0099=ratStandard false (false,(2,2,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0099,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0100 : sparsePolynomial p0100=ratStandard false (false,(3,0,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0100,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0101 : sparsePolynomial p0101=ratStandard false (false,(4,1,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0101,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0102 : sparsePolynomial p0102=ratStandard false (false,(6,0,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0102,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0103 : sparsePolynomial p0103=ratStandard false (true,(0,1,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0103,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0104 : sparsePolynomial p0104=ratStandard false (true,(1,2,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0104,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0105 : sparsePolynomial p0105=ratStandard false (true,(2,0,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0105,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0106 : sparsePolynomial p0106=ratStandard false (true,(3,1,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0106,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0107 : sparsePolynomial p0107=ratStandard false (true,(5,0,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0107,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0108 : sparsePolynomial p0108=ratStandard true (false,(0,0,2)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0108,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0109 : sparsePolynomial p0109=ratStandard true (false,(0,3,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0109,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0110 : sparsePolynomial p0110=ratStandard true (false,(1,1,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0110,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0111 : sparsePolynomial p0111=ratStandard true (false,(2,2,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0111,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0112 : sparsePolynomial p0112=ratStandard true (false,(3,0,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0112,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0113 : sparsePolynomial p0113=ratStandard true (false,(4,1,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0113,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0114 : sparsePolynomial p0114=ratStandard true (false,(6,0,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0114,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0115 : sparsePolynomial p0115=ratStandard true (true,(0,1,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0115,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0116 : sparsePolynomial p0116=ratStandard true (true,(1,2,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0116,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0117 : sparsePolynomial p0117=ratStandard true (true,(2,0,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0117,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0118 : sparsePolynomial p0118=ratStandard true (true,(3,1,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0118,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0119 : sparsePolynomial p0119=ratStandard true (true,(5,0,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0119,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0120 : sparsePolynomial p0120=ratInvariant (0,1,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0120,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0121 : sparsePolynomial p0121=ratInvariant (0,4,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0121,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0122 : sparsePolynomial p0122=ratInvariant (1,2,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0122,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0123 : sparsePolynomial p0123=ratInvariant (2,0,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0123,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0124 : sparsePolynomial p0124=ratInvariant (2,3,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0124,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0125 : sparsePolynomial p0125=ratInvariant (3,1,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0125,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0126 : sparsePolynomial p0126=ratInvariant (4,2,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0126,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0127 : sparsePolynomial p0127=ratInvariant (5,0,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0127,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0128 : sparsePolynomial p0128=ratInvariant (6,1,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0128,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0129 : sparsePolynomial p0129=ratInvariant (8,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0129,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0130 : sparsePolynomial p0130=ratDelta*ratInvariant (0,1,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0130,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0131 : sparsePolynomial p0131=ratDelta*ratInvariant (1,2,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0131,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0132 : sparsePolynomial p0132=ratDelta*ratInvariant (2,0,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0132,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0133 : sparsePolynomial p0133=ratDelta*ratInvariant (3,1,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0133,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0134 : sparsePolynomial p0134=ratDelta*ratInvariant (5,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0134,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0135 : sparsePolynomial p0135=ratStandard false (false,(0,2,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0135,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0136 : sparsePolynomial p0136=ratStandard false (false,(1,0,2)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0136,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0137 : sparsePolynomial p0137=ratStandard false (false,(1,3,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0137,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0138 : sparsePolynomial p0138=ratStandard false (false,(2,1,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0138,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0139 : sparsePolynomial p0139=ratStandard false (false,(3,2,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0139,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0140 : sparsePolynomial p0140=ratStandard false (false,(4,0,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0140,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0141 : sparsePolynomial p0141=ratStandard false (false,(5,1,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0141,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0142 : sparsePolynomial p0142=ratStandard false (false,(7,0,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0142,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0143 : sparsePolynomial p0143=ratStandard false (true,(0,0,2)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0143,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0144 : sparsePolynomial p0144=ratStandard false (true,(0,3,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0144,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0145 : sparsePolynomial p0145=ratStandard false (true,(1,1,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0145,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0146 : sparsePolynomial p0146=ratStandard false (true,(2,2,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0146,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0147 : sparsePolynomial p0147=ratStandard false (true,(3,0,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0147,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0148 : sparsePolynomial p0148=ratStandard false (true,(4,1,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0148,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0149 : sparsePolynomial p0149=ratStandard false (true,(6,0,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0149,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0150 : sparsePolynomial p0150=ratStandard true (false,(0,2,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0150,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0151 : sparsePolynomial p0151=ratStandard true (false,(1,0,2)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0151,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0152 : sparsePolynomial p0152=ratStandard true (false,(1,3,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0152,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0153 : sparsePolynomial p0153=ratStandard true (false,(2,1,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0153,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0154 : sparsePolynomial p0154=ratStandard true (false,(3,2,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0154,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0155 : sparsePolynomial p0155=ratStandard true (false,(4,0,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0155,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0156 : sparsePolynomial p0156=ratStandard true (false,(5,1,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0156,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0157 : sparsePolynomial p0157=ratStandard true (false,(7,0,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0157,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0158 : sparsePolynomial p0158=ratStandard true (true,(0,0,2)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0158,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0159 : sparsePolynomial p0159=ratStandard true (true,(0,3,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0159,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0160 : sparsePolynomial p0160=ratStandard true (true,(1,1,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0160,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0161 : sparsePolynomial p0161=ratStandard true (true,(2,2,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0161,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0162 : sparsePolynomial p0162=ratStandard true (true,(3,0,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0162,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0163 : sparsePolynomial p0163=ratStandard true (true,(4,1,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0163,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0164 : sparsePolynomial p0164=ratStandard true (true,(6,0,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0164,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0165 : sparsePolynomial p0165=ratInvariant (0,0,3) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0165,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0166 : sparsePolynomial p0166=ratInvariant (0,3,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0166,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0167 : sparsePolynomial p0167=ratInvariant (1,1,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0167,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0168 : sparsePolynomial p0168=ratInvariant (1,4,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0168,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0169 : sparsePolynomial p0169=ratInvariant (2,2,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0169,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0170 : sparsePolynomial p0170=ratInvariant (3,0,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0170,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0171 : sparsePolynomial p0171=ratInvariant (3,3,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0171,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0172 : sparsePolynomial p0172=ratInvariant (4,1,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0172,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0173 : sparsePolynomial p0173=ratInvariant (5,2,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0173,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0174 : sparsePolynomial p0174=ratInvariant (6,0,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0174,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0175 : sparsePolynomial p0175=ratInvariant (7,1,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0175,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0176 : sparsePolynomial p0176=ratInvariant (9,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0176,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0177 : sparsePolynomial p0177=ratDelta*ratInvariant (0,0,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0177,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0178 : sparsePolynomial p0178=ratDelta*ratInvariant (0,3,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0178,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0179 : sparsePolynomial p0179=ratDelta*ratInvariant (1,1,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0179,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0180 : sparsePolynomial p0180=ratDelta*ratInvariant (2,2,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0180,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0181 : sparsePolynomial p0181=ratDelta*ratInvariant (3,0,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0181,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0182 : sparsePolynomial p0182=ratDelta*ratInvariant (4,1,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0182,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0183 : sparsePolynomial p0183=ratDelta*ratInvariant (6,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0183,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0184 : sparsePolynomial p0184=ratStandard false (false,(0,1,2)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0184,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0185 : sparsePolynomial p0185=ratStandard false (false,(0,4,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0185,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0186 : sparsePolynomial p0186=ratStandard false (false,(1,2,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0186,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0187 : sparsePolynomial p0187=ratStandard false (false,(2,0,2)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0187,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0188 : sparsePolynomial p0188=ratStandard false (false,(2,3,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0188,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0189 : sparsePolynomial p0189=ratStandard false (false,(3,1,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0189,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0190 : sparsePolynomial p0190=ratStandard false (false,(4,2,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0190,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0191 : sparsePolynomial p0191=ratStandard false (false,(5,0,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0191,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0192 : sparsePolynomial p0192=ratStandard false (false,(6,1,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0192,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0193 : sparsePolynomial p0193=ratStandard false (false,(8,0,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0193,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0194 : sparsePolynomial p0194=ratStandard false (true,(0,2,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0194,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0195 : sparsePolynomial p0195=ratStandard false (true,(1,0,2)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0195,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0196 : sparsePolynomial p0196=ratStandard false (true,(1,3,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0196,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0197 : sparsePolynomial p0197=ratStandard false (true,(2,1,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0197,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0198 : sparsePolynomial p0198=ratStandard false (true,(3,2,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0198,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0199 : sparsePolynomial p0199=ratStandard false (true,(4,0,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0199,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0200 : sparsePolynomial p0200=ratStandard false (true,(5,1,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0200,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0201 : sparsePolynomial p0201=ratStandard false (true,(7,0,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0201,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0202 : sparsePolynomial p0202=ratStandard true (false,(0,1,2)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0202,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0203 : sparsePolynomial p0203=ratStandard true (false,(0,4,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0203,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0204 : sparsePolynomial p0204=ratStandard true (false,(1,2,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0204,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0205 : sparsePolynomial p0205=ratStandard true (false,(2,0,2)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0205,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0206 : sparsePolynomial p0206=ratStandard true (false,(2,3,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0206,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0207 : sparsePolynomial p0207=ratStandard true (false,(3,1,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0207,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0208 : sparsePolynomial p0208=ratStandard true (false,(4,2,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0208,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0209 : sparsePolynomial p0209=ratStandard true (false,(5,0,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0209,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0210 : sparsePolynomial p0210=ratStandard true (false,(6,1,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0210,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0211 : sparsePolynomial p0211=ratStandard true (false,(8,0,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0211,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0212 : sparsePolynomial p0212=ratStandard true (true,(0,2,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0212,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0213 : sparsePolynomial p0213=ratStandard true (true,(1,0,2)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0213,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0214 : sparsePolynomial p0214=ratStandard true (true,(1,3,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0214,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0215 : sparsePolynomial p0215=ratStandard true (true,(2,1,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0215,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0216 : sparsePolynomial p0216=ratStandard true (true,(3,2,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0216,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0217 : sparsePolynomial p0217=ratStandard true (true,(4,0,1)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0217,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0218 : sparsePolynomial p0218=ratStandard true (true,(5,1,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0218,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0219 : sparsePolynomial p0219=ratStandard true (true,(7,0,0)) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0219,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0220 : sparsePolynomial p0000=ratParity (0,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0000,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0221 : sparsePolynomial p0220=ratParity (0,1,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0220,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0222 : sparsePolynomial p0221=ratParity (1,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0221,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0223 : sparsePolynomial p0222=ratParity (0,0,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0222,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0224 : sparsePolynomial p0223=ratParity (0,2,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0223,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0225 : sparsePolynomial p0224=ratParity (1,1,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0224,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0226 : sparsePolynomial p0225=ratParity (2,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0225,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0227 : sparsePolynomial p0226=ratParity (0,1,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0226,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0228 : sparsePolynomial p0227=ratParity (0,3,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0227,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0229 : sparsePolynomial p0004=ratParity (1,0,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0004,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0230 : sparsePolynomial p0228=ratParity (1,2,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0228,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0231 : sparsePolynomial p0229=ratParity (2,1,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0229,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0232 : sparsePolynomial p0230=ratParity (3,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0230,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0233 : sparsePolynomial p0231=ratParity (0,0,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0231,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0234 : sparsePolynomial p0232=ratParity (0,2,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0232,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0235 : sparsePolynomial p0233=ratParity (0,4,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0233,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0236 : sparsePolynomial p0234=ratParity (1,1,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0234,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0237 : sparsePolynomial p0235=ratParity (1,3,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0235,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0238 : sparsePolynomial p0236=ratParity (2,0,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0236,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0239 : sparsePolynomial p0237=ratParity (2,2,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0237,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0240 : sparsePolynomial p0238=ratParity (3,1,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0238,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0241 : sparsePolynomial p0239=ratParity (4,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0239,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0242 : sparsePolynomial p0024=ratOdd*ratParity (0,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0024,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0243 : sparsePolynomial p0240=ratOdd*ratParity (0,1,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0240,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0244 : sparsePolynomial p0241=ratOdd*ratParity (1,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0241,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0245 : sparsePolynomial p0242=ratOdd*ratParity (0,0,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0242,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0246 : sparsePolynomial p0243=ratOdd*ratParity (0,2,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0243,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0247 : sparsePolynomial p0244=ratOdd*ratParity (1,1,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0244,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0248 : sparsePolynomial p0245=ratOdd*ratParity (2,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0245,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0249 : sparsePolynomial p0246=ratOdd*ratParity (0,1,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0246,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0250 : sparsePolynomial p0247=ratOdd*ratParity (0,3,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0247,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0251 : sparsePolynomial p0028=ratOdd*ratParity (1,0,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0028,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0252 : sparsePolynomial p0248=ratOdd*ratParity (1,2,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0248,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0253 : sparsePolynomial p0249=ratOdd*ratParity (2,1,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0249,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0254 : sparsePolynomial p0250=ratOdd*ratParity (3,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0250,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0255 : sparsePolynomial p0251=ratParity (0,1,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0251,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0256 : sparsePolynomial p0252=ratParity (0,3,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0252,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0257 : sparsePolynomial p0253=ratParity (0,5,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0253,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0258 : sparsePolynomial p0254=ratParity (1,0,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0254,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0259 : sparsePolynomial p0255=ratParity (1,2,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0255,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0260 : sparsePolynomial p0256=ratParity (1,4,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0256,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0261 : sparsePolynomial p0257=ratParity (2,1,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0257,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0262 : sparsePolynomial p0258=ratParity (2,3,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0258,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0263 : sparsePolynomial p0259=ratParity (3,0,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0259,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0264 : sparsePolynomial p0260=ratParity (3,2,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0260,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0265 : sparsePolynomial p0261=ratParity (4,1,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0261,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0266 : sparsePolynomial p0262=ratParity (5,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0262,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0267 : sparsePolynomial p0263=ratOdd*ratParity (0,0,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0263,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0268 : sparsePolynomial p0264=ratOdd*ratParity (0,2,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0264,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0269 : sparsePolynomial p0265=ratOdd*ratParity (0,4,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0265,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0270 : sparsePolynomial p0266=ratOdd*ratParity (1,1,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0266,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0271 : sparsePolynomial p0267=ratOdd*ratParity (1,3,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0267,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0272 : sparsePolynomial p0268=ratOdd*ratParity (2,0,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0268,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0273 : sparsePolynomial p0269=ratOdd*ratParity (2,2,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0269,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0274 : sparsePolynomial p0270=ratOdd*ratParity (3,1,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0270,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0275 : sparsePolynomial p0271=ratOdd*ratParity (4,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0271,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0276 : sparsePolynomial p0272=ratParity (0,0,3) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0272,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0277 : sparsePolynomial p0273=ratParity (0,2,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0273,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0278 : sparsePolynomial p0274=ratParity (0,4,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0274,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0279 : sparsePolynomial p0275=ratParity (0,6,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0275,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0280 : sparsePolynomial p0276=ratParity (1,1,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0276,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0281 : sparsePolynomial p0277=ratParity (1,3,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0277,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0282 : sparsePolynomial p0278=ratParity (1,5,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0278,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0283 : sparsePolynomial p0056=ratParity (2,0,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0056,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0284 : sparsePolynomial p0279=ratParity (2,2,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0279,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0285 : sparsePolynomial p0280=ratParity (2,4,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0280,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0286 : sparsePolynomial p0281=ratParity (3,1,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0281,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0287 : sparsePolynomial p0282=ratParity (3,3,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0282,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0288 : sparsePolynomial p0283=ratParity (4,0,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0283,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0289 : sparsePolynomial p0284=ratParity (4,2,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0284,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0290 : sparsePolynomial p0285=ratParity (5,1,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0285,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0291 : sparsePolynomial p0286=ratParity (6,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0286,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0292 : sparsePolynomial p0287=ratOdd*ratParity (0,1,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0287,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0293 : sparsePolynomial p0288=ratOdd*ratParity (0,3,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0288,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0294 : sparsePolynomial p0289=ratOdd*ratParity (0,5,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0289,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0295 : sparsePolynomial p0290=ratOdd*ratParity (1,0,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0290,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0296 : sparsePolynomial p0291=ratOdd*ratParity (1,2,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0291,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0297 : sparsePolynomial p0292=ratOdd*ratParity (1,4,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0292,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0298 : sparsePolynomial p0293=ratOdd*ratParity (2,1,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0293,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0299 : sparsePolynomial p0294=ratOdd*ratParity (2,3,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0294,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0300 : sparsePolynomial p0295=ratOdd*ratParity (3,0,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0295,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0301 : sparsePolynomial p0296=ratOdd*ratParity (3,2,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0296,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0302 : sparsePolynomial p0297=ratOdd*ratParity (4,1,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0297,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0303 : sparsePolynomial p0298=ratOdd*ratParity (5,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0298,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0304 : sparsePolynomial p0299=ratParity (0,1,3) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0299,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0305 : sparsePolynomial p0300=ratParity (0,3,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0300,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0306 : sparsePolynomial p0301=ratParity (0,5,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0301,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0307 : sparsePolynomial p0302=ratParity (0,7,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0302,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0308 : sparsePolynomial p0303=ratParity (1,0,3) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0303,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0309 : sparsePolynomial p0304=ratParity (1,2,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0304,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0310 : sparsePolynomial p0305=ratParity (1,4,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0305,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0311 : sparsePolynomial p0306=ratParity (1,6,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0306,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0312 : sparsePolynomial p0307=ratParity (2,1,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0307,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0313 : sparsePolynomial p0308=ratParity (2,3,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0308,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0314 : sparsePolynomial p0309=ratParity (2,5,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0309,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0315 : sparsePolynomial p0310=ratParity (3,0,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0310,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0316 : sparsePolynomial p0311=ratParity (3,2,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0311,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0317 : sparsePolynomial p0312=ratParity (3,4,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0312,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0318 : sparsePolynomial p0313=ratParity (4,1,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0313,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0319 : sparsePolynomial p0314=ratParity (4,3,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0314,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0320 : sparsePolynomial p0315=ratParity (5,0,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0315,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0321 : sparsePolynomial p0316=ratParity (5,2,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0316,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0322 : sparsePolynomial p0317=ratParity (6,1,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0317,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0323 : sparsePolynomial p0318=ratParity (7,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0318,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0324 : sparsePolynomial p0319=ratOdd*ratParity (0,0,3) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0319,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0325 : sparsePolynomial p0320=ratOdd*ratParity (0,2,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0320,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0326 : sparsePolynomial p0321=ratOdd*ratParity (0,4,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0321,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0327 : sparsePolynomial p0322=ratOdd*ratParity (0,6,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0322,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0328 : sparsePolynomial p0323=ratOdd*ratParity (1,1,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0323,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0329 : sparsePolynomial p0324=ratOdd*ratParity (1,3,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0324,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0330 : sparsePolynomial p0325=ratOdd*ratParity (1,5,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0325,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0331 : sparsePolynomial p0108=ratOdd*ratParity (2,0,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0108,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0332 : sparsePolynomial p0326=ratOdd*ratParity (2,2,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0326,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0333 : sparsePolynomial p0327=ratOdd*ratParity (2,4,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0327,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0334 : sparsePolynomial p0328=ratOdd*ratParity (3,1,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0328,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0335 : sparsePolynomial p0329=ratOdd*ratParity (3,3,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0329,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0336 : sparsePolynomial p0330=ratOdd*ratParity (4,0,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0330,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0337 : sparsePolynomial p0331=ratOdd*ratParity (4,2,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0331,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0338 : sparsePolynomial p0332=ratOdd*ratParity (5,1,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0332,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0339 : sparsePolynomial p0333=ratOdd*ratParity (6,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0333,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0340 : sparsePolynomial p0334=ratParity (0,0,4) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0334,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0341 : sparsePolynomial p0335=ratParity (0,2,3) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0335,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0342 : sparsePolynomial p0336=ratParity (0,4,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0336,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0343 : sparsePolynomial p0337=ratParity (0,6,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0337,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0344 : sparsePolynomial p0338=ratParity (0,8,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0338,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0345 : sparsePolynomial p0339=ratParity (1,1,3) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0339,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0346 : sparsePolynomial p0340=ratParity (1,3,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0340,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0347 : sparsePolynomial p0341=ratParity (1,5,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0341,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0348 : sparsePolynomial p0342=ratParity (1,7,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0342,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0349 : sparsePolynomial p0343=ratParity (2,0,3) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0343,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0350 : sparsePolynomial p0344=ratParity (2,2,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0344,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0351 : sparsePolynomial p0345=ratParity (2,4,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0345,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0352 : sparsePolynomial p0346=ratParity (2,6,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0346,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0353 : sparsePolynomial p0347=ratParity (3,1,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0347,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0354 : sparsePolynomial p0348=ratParity (3,3,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0348,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0355 : sparsePolynomial p0349=ratParity (3,5,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0349,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0356 : sparsePolynomial p0350=ratParity (4,0,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0350,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0357 : sparsePolynomial p0351=ratParity (4,2,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0351,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0358 : sparsePolynomial p0352=ratParity (4,4,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0352,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0359 : sparsePolynomial p0353=ratParity (5,1,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0353,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0360 : sparsePolynomial p0354=ratParity (5,3,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0354,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0361 : sparsePolynomial p0355=ratParity (6,0,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0355,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0362 : sparsePolynomial p0356=ratParity (6,2,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0356,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0363 : sparsePolynomial p0357=ratParity (7,1,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0357,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0364 : sparsePolynomial p0358=ratParity (8,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0358,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0365 : sparsePolynomial p0359=ratOdd*ratParity (0,1,3) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0359,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0366 : sparsePolynomial p0360=ratOdd*ratParity (0,3,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0360,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0367 : sparsePolynomial p0361=ratOdd*ratParity (0,5,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0361,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0368 : sparsePolynomial p0362=ratOdd*ratParity (0,7,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0362,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0369 : sparsePolynomial p0363=ratOdd*ratParity (1,0,3) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0363,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0370 : sparsePolynomial p0364=ratOdd*ratParity (1,2,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0364,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0371 : sparsePolynomial p0365=ratOdd*ratParity (1,4,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0365,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0372 : sparsePolynomial p0366=ratOdd*ratParity (1,6,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0366,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0373 : sparsePolynomial p0367=ratOdd*ratParity (2,1,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0367,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0374 : sparsePolynomial p0368=ratOdd*ratParity (2,3,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0368,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0375 : sparsePolynomial p0369=ratOdd*ratParity (2,5,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0369,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0376 : sparsePolynomial p0370=ratOdd*ratParity (3,0,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0370,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0377 : sparsePolynomial p0371=ratOdd*ratParity (3,2,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0371,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0378 : sparsePolynomial p0372=ratOdd*ratParity (3,4,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0372,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0379 : sparsePolynomial p0373=ratOdd*ratParity (4,1,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0373,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0380 : sparsePolynomial p0374=ratOdd*ratParity (4,3,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0374,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0381 : sparsePolynomial p0375=ratOdd*ratParity (5,0,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0375,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0382 : sparsePolynomial p0376=ratOdd*ratParity (5,2,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0376,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0383 : sparsePolynomial p0377=ratOdd*ratParity (6,1,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0377,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0384 : sparsePolynomial p0378=ratOdd*ratParity (7,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0378,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0385 : sparsePolynomial p0379=ratParity (0,1,4) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0379,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0386 : sparsePolynomial p0380=ratParity (0,3,3) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0380,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0387 : sparsePolynomial p0381=ratParity (0,5,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0381,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0388 : sparsePolynomial p0382=ratParity (0,7,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0382,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0389 : sparsePolynomial p0383=ratParity (0,9,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0383,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0390 : sparsePolynomial p0384=ratParity (1,0,4) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0384,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0391 : sparsePolynomial p0385=ratParity (1,2,3) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0385,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0392 : sparsePolynomial p0386=ratParity (1,4,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0386,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0393 : sparsePolynomial p0387=ratParity (1,6,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0387,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0394 : sparsePolynomial p0388=ratParity (1,8,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0388,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0395 : sparsePolynomial p0389=ratParity (2,1,3) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0389,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0396 : sparsePolynomial p0390=ratParity (2,3,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0390,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0397 : sparsePolynomial p0391=ratParity (2,5,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0391,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0398 : sparsePolynomial p0392=ratParity (2,7,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0392,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0399 : sparsePolynomial p0165=ratParity (3,0,3) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0165,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0400 : sparsePolynomial p0393=ratParity (3,2,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0393,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0401 : sparsePolynomial p0394=ratParity (3,4,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0394,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0402 : sparsePolynomial p0395=ratParity (3,6,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0395,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0403 : sparsePolynomial p0396=ratParity (4,1,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0396,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0404 : sparsePolynomial p0397=ratParity (4,3,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0397,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0405 : sparsePolynomial p0398=ratParity (4,5,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0398,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0406 : sparsePolynomial p0399=ratParity (5,0,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0399,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0407 : sparsePolynomial p0400=ratParity (5,2,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0400,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0408 : sparsePolynomial p0401=ratParity (5,4,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0401,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0409 : sparsePolynomial p0402=ratParity (6,1,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0402,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0410 : sparsePolynomial p0403=ratParity (6,3,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0403,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0411 : sparsePolynomial p0404=ratParity (7,0,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0404,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0412 : sparsePolynomial p0405=ratParity (7,2,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0405,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0413 : sparsePolynomial p0406=ratParity (8,1,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0406,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0414 : sparsePolynomial p0407=ratParity (9,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0407,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0415 : sparsePolynomial p0408=ratOdd*ratParity (0,0,4) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0408,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0416 : sparsePolynomial p0409=ratOdd*ratParity (0,2,3) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0409,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0417 : sparsePolynomial p0410=ratOdd*ratParity (0,4,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0410,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0418 : sparsePolynomial p0411=ratOdd*ratParity (0,6,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0411,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0419 : sparsePolynomial p0412=ratOdd*ratParity (0,8,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0412,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0420 : sparsePolynomial p0413=ratOdd*ratParity (1,1,3) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0413,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0421 : sparsePolynomial p0414=ratOdd*ratParity (1,3,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0414,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0422 : sparsePolynomial p0415=ratOdd*ratParity (1,5,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0415,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0423 : sparsePolynomial p0416=ratOdd*ratParity (1,7,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0416,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0424 : sparsePolynomial p0417=ratOdd*ratParity (2,0,3) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0417,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0425 : sparsePolynomial p0418=ratOdd*ratParity (2,2,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0418,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0426 : sparsePolynomial p0419=ratOdd*ratParity (2,4,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0419,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0427 : sparsePolynomial p0420=ratOdd*ratParity (2,6,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0420,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0428 : sparsePolynomial p0421=ratOdd*ratParity (3,1,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0421,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0429 : sparsePolynomial p0422=ratOdd*ratParity (3,3,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0422,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0430 : sparsePolynomial p0423=ratOdd*ratParity (3,5,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0423,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0431 : sparsePolynomial p0424=ratOdd*ratParity (4,0,2) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0424,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0432 : sparsePolynomial p0425=ratOdd*ratParity (4,2,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0425,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0433 : sparsePolynomial p0426=ratOdd*ratParity (4,4,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0426,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0434 : sparsePolynomial p0427=ratOdd*ratParity (5,1,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0427,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0435 : sparsePolynomial p0428=ratOdd*ratParity (5,3,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0428,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0436 : sparsePolynomial p0429=ratOdd*ratParity (6,0,1) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0429,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0437 : sparsePolynomial p0430=ratOdd*ratParity (6,2,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0430,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0438 : sparsePolynomial p0431=ratOdd*ratParity (7,1,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0431,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

theorem raw_identity_0439 : sparsePolynomial p0432=ratOdd*ratParity (8,0,0) := by
  apply MvPolynomial.funext
  intro x
  norm_num [sparsePolynomial,p0432,ratInvariant,ratSigma,ratE2,ratE3,ratDelta,ratStandard,ratP,ratQ,ratParity,ratOdd,Fin.sum_univ_succ]
  <;> ring

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem source_entry0 : EntryAgrees entry0 := by
  simp only [EntryAgrees,entry0,expectedTags,expectedPivots,expectedFrees,expectedGroups,standardTagList,invariantPivots,signPivots,standardPivots,parityPivots,Bool.false_eq_true,if_false,if_true,Nat.reduceSub,invariantTagList_1,invariantTagList_2,invariantTagList_3,invariantTagList_4,invariantTagList_5,invariantTagList_6,invariantTagList_7,invariantTagList_8,invariantTagList_9,parityTagList_3,parityTagList_4,parityTagList_5,parityTagList_6,parityTagList_7,parityTagList_8,parityTagList_9]
  refine ⟨by decide,by decide,by decide,?_⟩
  change [[sparsePolynomial p0000,sparsePolynomial p0001,sparsePolynomial p0002,sparsePolynomial p0003,sparsePolynomial p0004,sparsePolynomial p0005,sparsePolynomial p0006,sparsePolynomial p0007,sparsePolynomial p0008,sparsePolynomial p0009,sparsePolynomial p0010],[sparsePolynomial p0011,sparsePolynomial p0012],[sparsePolynomial p0013,sparsePolynomial p0014,sparsePolynomial p0015,sparsePolynomial p0016,sparsePolynomial p0017,sparsePolynomial p0018,sparsePolynomial p0019,sparsePolynomial p0020,sparsePolynomial p0021,sparsePolynomial p0022,sparsePolynomial p0023],[sparsePolynomial p0024,sparsePolynomial p0025,sparsePolynomial p0026,sparsePolynomial p0027,sparsePolynomial p0028,sparsePolynomial p0029,sparsePolynomial p0030,sparsePolynomial p0031,sparsePolynomial p0032,sparsePolynomial p0033,sparsePolynomial p0034]]=[[ratInvariant (0,0,0),ratInvariant (1,0,0),ratInvariant (0,1,0),ratInvariant (2,0,0),ratInvariant (0,0,1),ratInvariant (1,1,0),ratInvariant (3,0,0),ratInvariant (0,2,0),ratInvariant (1,0,1),ratInvariant (2,1,0),ratInvariant (4,0,0)],[ratDelta*ratInvariant (0,0,0),ratDelta*ratInvariant (1,0,0)],[ratStandard false (false,(0,0,0)),ratStandard false (false,(1,0,0)),ratStandard false (false,(0,1,0)),ratStandard false (false,(2,0,0)),ratStandard false (false,(0,0,1)),ratStandard false (false,(1,1,0)),ratStandard false (false,(3,0,0)),ratStandard false (true,(0,0,0)),ratStandard false (true,(1,0,0)),ratStandard false (true,(0,1,0)),ratStandard false (true,(2,0,0))],[ratStandard true (false,(0,0,0)),ratStandard true (false,(1,0,0)),ratStandard true (false,(0,1,0)),ratStandard true (false,(2,0,0)),ratStandard true (false,(0,0,1)),ratStandard true (false,(1,1,0)),ratStandard true (false,(3,0,0)),ratStandard true (true,(0,0,0)),ratStandard true (true,(1,0,0)),ratStandard true (true,(0,1,0)),ratStandard true (true,(2,0,0))]]
  simp only [List.cons.injEq,and_true]
  exact ⟨⟨raw_identity_0000,⟨raw_identity_0001,⟨raw_identity_0002,⟨raw_identity_0003,⟨raw_identity_0004,⟨raw_identity_0005,⟨raw_identity_0006,⟨raw_identity_0007,⟨raw_identity_0008,⟨raw_identity_0009,raw_identity_0010⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,⟨⟨raw_identity_0011,raw_identity_0012⟩,⟨⟨raw_identity_0013,⟨raw_identity_0014,⟨raw_identity_0015,⟨raw_identity_0016,⟨raw_identity_0017,⟨raw_identity_0018,⟨raw_identity_0019,⟨raw_identity_0020,⟨raw_identity_0021,⟨raw_identity_0022,raw_identity_0023⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,⟨raw_identity_0024,⟨raw_identity_0025,⟨raw_identity_0026,⟨raw_identity_0027,⟨raw_identity_0028,⟨raw_identity_0029,⟨raw_identity_0030,⟨raw_identity_0031,⟨raw_identity_0032,⟨raw_identity_0033,raw_identity_0034⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem source_entry1 : EntryAgrees entry1 := by
  simp only [EntryAgrees,entry1,expectedTags,expectedPivots,expectedFrees,expectedGroups,standardTagList,invariantPivots,signPivots,standardPivots,parityPivots,Bool.false_eq_true,if_false,if_true,Nat.reduceSub,invariantTagList_1,invariantTagList_2,invariantTagList_3,invariantTagList_4,invariantTagList_5,invariantTagList_6,invariantTagList_7,invariantTagList_8,invariantTagList_9,parityTagList_3,parityTagList_4,parityTagList_5,parityTagList_6,parityTagList_7,parityTagList_8,parityTagList_9]
  refine ⟨by decide,by decide,by decide,?_⟩
  change [[sparsePolynomial p0000,sparsePolynomial p0001,sparsePolynomial p0002,sparsePolynomial p0003,sparsePolynomial p0004,sparsePolynomial p0005,sparsePolynomial p0006,sparsePolynomial p0007,sparsePolynomial p0008,sparsePolynomial p0009,sparsePolynomial p0010,sparsePolynomial p0035,sparsePolynomial p0036,sparsePolynomial p0037,sparsePolynomial p0038,sparsePolynomial p0039],[sparsePolynomial p0011,sparsePolynomial p0012,sparsePolynomial p0040,sparsePolynomial p0041],[sparsePolynomial p0013,sparsePolynomial p0014,sparsePolynomial p0015,sparsePolynomial p0016,sparsePolynomial p0017,sparsePolynomial p0018,sparsePolynomial p0019,sparsePolynomial p0042,sparsePolynomial p0043,sparsePolynomial p0044,sparsePolynomial p0045,sparsePolynomial p0020,sparsePolynomial p0021,sparsePolynomial p0022,sparsePolynomial p0023,sparsePolynomial p0046,sparsePolynomial p0047,sparsePolynomial p0048],[sparsePolynomial p0024,sparsePolynomial p0025,sparsePolynomial p0026,sparsePolynomial p0027,sparsePolynomial p0028,sparsePolynomial p0029,sparsePolynomial p0030,sparsePolynomial p0049,sparsePolynomial p0050,sparsePolynomial p0051,sparsePolynomial p0052,sparsePolynomial p0031,sparsePolynomial p0032,sparsePolynomial p0033,sparsePolynomial p0034,sparsePolynomial p0053,sparsePolynomial p0054,sparsePolynomial p0055]]=[[ratInvariant (0,0,0),ratInvariant (1,0,0),ratInvariant (0,1,0),ratInvariant (2,0,0),ratInvariant (0,0,1),ratInvariant (1,1,0),ratInvariant (3,0,0),ratInvariant (0,2,0),ratInvariant (1,0,1),ratInvariant (2,1,0),ratInvariant (4,0,0),ratInvariant (0,1,1),ratInvariant (1,2,0),ratInvariant (2,0,1),ratInvariant (3,1,0),ratInvariant (5,0,0)],[ratDelta*ratInvariant (0,0,0),ratDelta*ratInvariant (1,0,0),ratDelta*ratInvariant (0,1,0),ratDelta*ratInvariant (2,0,0)],[ratStandard false (false,(0,0,0)),ratStandard false (false,(1,0,0)),ratStandard false (false,(0,1,0)),ratStandard false (false,(2,0,0)),ratStandard false (false,(0,0,1)),ratStandard false (false,(1,1,0)),ratStandard false (false,(3,0,0)),ratStandard false (false,(0,2,0)),ratStandard false (false,(1,0,1)),ratStandard false (false,(2,1,0)),ratStandard false (false,(4,0,0)),ratStandard false (true,(0,0,0)),ratStandard false (true,(1,0,0)),ratStandard false (true,(0,1,0)),ratStandard false (true,(2,0,0)),ratStandard false (true,(0,0,1)),ratStandard false (true,(1,1,0)),ratStandard false (true,(3,0,0))],[ratStandard true (false,(0,0,0)),ratStandard true (false,(1,0,0)),ratStandard true (false,(0,1,0)),ratStandard true (false,(2,0,0)),ratStandard true (false,(0,0,1)),ratStandard true (false,(1,1,0)),ratStandard true (false,(3,0,0)),ratStandard true (false,(0,2,0)),ratStandard true (false,(1,0,1)),ratStandard true (false,(2,1,0)),ratStandard true (false,(4,0,0)),ratStandard true (true,(0,0,0)),ratStandard true (true,(1,0,0)),ratStandard true (true,(0,1,0)),ratStandard true (true,(2,0,0)),ratStandard true (true,(0,0,1)),ratStandard true (true,(1,1,0)),ratStandard true (true,(3,0,0))]]
  simp only [List.cons.injEq,and_true]
  exact ⟨⟨raw_identity_0000,⟨raw_identity_0001,⟨raw_identity_0002,⟨raw_identity_0003,⟨raw_identity_0004,⟨raw_identity_0005,⟨raw_identity_0006,⟨raw_identity_0007,⟨raw_identity_0008,⟨raw_identity_0009,⟨raw_identity_0010,⟨raw_identity_0035,⟨raw_identity_0036,⟨raw_identity_0037,⟨raw_identity_0038,raw_identity_0039⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,⟨⟨raw_identity_0011,⟨raw_identity_0012,⟨raw_identity_0040,raw_identity_0041⟩⟩⟩,⟨⟨raw_identity_0013,⟨raw_identity_0014,⟨raw_identity_0015,⟨raw_identity_0016,⟨raw_identity_0017,⟨raw_identity_0018,⟨raw_identity_0019,⟨raw_identity_0042,⟨raw_identity_0043,⟨raw_identity_0044,⟨raw_identity_0045,⟨raw_identity_0020,⟨raw_identity_0021,⟨raw_identity_0022,⟨raw_identity_0023,⟨raw_identity_0046,⟨raw_identity_0047,raw_identity_0048⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,⟨raw_identity_0024,⟨raw_identity_0025,⟨raw_identity_0026,⟨raw_identity_0027,⟨raw_identity_0028,⟨raw_identity_0029,⟨raw_identity_0030,⟨raw_identity_0049,⟨raw_identity_0050,⟨raw_identity_0051,⟨raw_identity_0052,⟨raw_identity_0031,⟨raw_identity_0032,⟨raw_identity_0033,⟨raw_identity_0034,⟨raw_identity_0053,⟨raw_identity_0054,raw_identity_0055⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem source_entry2 : EntryAgrees entry2 := by
  simp only [EntryAgrees,entry2,expectedTags,expectedPivots,expectedFrees,expectedGroups,standardTagList,invariantPivots,signPivots,standardPivots,parityPivots,Bool.false_eq_true,if_false,if_true,Nat.reduceSub,invariantTagList_1,invariantTagList_2,invariantTagList_3,invariantTagList_4,invariantTagList_5,invariantTagList_6,invariantTagList_7,invariantTagList_8,invariantTagList_9,parityTagList_3,parityTagList_4,parityTagList_5,parityTagList_6,parityTagList_7,parityTagList_8,parityTagList_9]
  refine ⟨by decide,by decide,by decide,?_⟩
  change [[sparsePolynomial p0000,sparsePolynomial p0001,sparsePolynomial p0002,sparsePolynomial p0003,sparsePolynomial p0004,sparsePolynomial p0005,sparsePolynomial p0006,sparsePolynomial p0007,sparsePolynomial p0008,sparsePolynomial p0009,sparsePolynomial p0010,sparsePolynomial p0035,sparsePolynomial p0036,sparsePolynomial p0037,sparsePolynomial p0038,sparsePolynomial p0039,sparsePolynomial p0056,sparsePolynomial p0057,sparsePolynomial p0058,sparsePolynomial p0059,sparsePolynomial p0060,sparsePolynomial p0061,sparsePolynomial p0062],[sparsePolynomial p0011,sparsePolynomial p0012,sparsePolynomial p0040,sparsePolynomial p0041,sparsePolynomial p0063,sparsePolynomial p0064,sparsePolynomial p0065],[sparsePolynomial p0013,sparsePolynomial p0014,sparsePolynomial p0015,sparsePolynomial p0016,sparsePolynomial p0017,sparsePolynomial p0018,sparsePolynomial p0019,sparsePolynomial p0042,sparsePolynomial p0043,sparsePolynomial p0044,sparsePolynomial p0045,sparsePolynomial p0066,sparsePolynomial p0067,sparsePolynomial p0068,sparsePolynomial p0069,sparsePolynomial p0070,sparsePolynomial p0020,sparsePolynomial p0021,sparsePolynomial p0022,sparsePolynomial p0023,sparsePolynomial p0046,sparsePolynomial p0047,sparsePolynomial p0048,sparsePolynomial p0071,sparsePolynomial p0072,sparsePolynomial p0073,sparsePolynomial p0074],[sparsePolynomial p0024,sparsePolynomial p0025,sparsePolynomial p0026,sparsePolynomial p0027,sparsePolynomial p0028,sparsePolynomial p0029,sparsePolynomial p0030,sparsePolynomial p0049,sparsePolynomial p0050,sparsePolynomial p0051,sparsePolynomial p0052,sparsePolynomial p0075,sparsePolynomial p0076,sparsePolynomial p0077,sparsePolynomial p0078,sparsePolynomial p0079,sparsePolynomial p0031,sparsePolynomial p0032,sparsePolynomial p0033,sparsePolynomial p0034,sparsePolynomial p0053,sparsePolynomial p0054,sparsePolynomial p0055,sparsePolynomial p0080,sparsePolynomial p0081,sparsePolynomial p0082,sparsePolynomial p0083]]=[[ratInvariant (0,0,0),ratInvariant (1,0,0),ratInvariant (0,1,0),ratInvariant (2,0,0),ratInvariant (0,0,1),ratInvariant (1,1,0),ratInvariant (3,0,0),ratInvariant (0,2,0),ratInvariant (1,0,1),ratInvariant (2,1,0),ratInvariant (4,0,0),ratInvariant (0,1,1),ratInvariant (1,2,0),ratInvariant (2,0,1),ratInvariant (3,1,0),ratInvariant (5,0,0),ratInvariant (0,0,2),ratInvariant (0,3,0),ratInvariant (1,1,1),ratInvariant (2,2,0),ratInvariant (3,0,1),ratInvariant (4,1,0),ratInvariant (6,0,0)],[ratDelta*ratInvariant (0,0,0),ratDelta*ratInvariant (1,0,0),ratDelta*ratInvariant (0,1,0),ratDelta*ratInvariant (2,0,0),ratDelta*ratInvariant (0,0,1),ratDelta*ratInvariant (1,1,0),ratDelta*ratInvariant (3,0,0)],[ratStandard false (false,(0,0,0)),ratStandard false (false,(1,0,0)),ratStandard false (false,(0,1,0)),ratStandard false (false,(2,0,0)),ratStandard false (false,(0,0,1)),ratStandard false (false,(1,1,0)),ratStandard false (false,(3,0,0)),ratStandard false (false,(0,2,0)),ratStandard false (false,(1,0,1)),ratStandard false (false,(2,1,0)),ratStandard false (false,(4,0,0)),ratStandard false (false,(0,1,1)),ratStandard false (false,(1,2,0)),ratStandard false (false,(2,0,1)),ratStandard false (false,(3,1,0)),ratStandard false (false,(5,0,0)),ratStandard false (true,(0,0,0)),ratStandard false (true,(1,0,0)),ratStandard false (true,(0,1,0)),ratStandard false (true,(2,0,0)),ratStandard false (true,(0,0,1)),ratStandard false (true,(1,1,0)),ratStandard false (true,(3,0,0)),ratStandard false (true,(0,2,0)),ratStandard false (true,(1,0,1)),ratStandard false (true,(2,1,0)),ratStandard false (true,(4,0,0))],[ratStandard true (false,(0,0,0)),ratStandard true (false,(1,0,0)),ratStandard true (false,(0,1,0)),ratStandard true (false,(2,0,0)),ratStandard true (false,(0,0,1)),ratStandard true (false,(1,1,0)),ratStandard true (false,(3,0,0)),ratStandard true (false,(0,2,0)),ratStandard true (false,(1,0,1)),ratStandard true (false,(2,1,0)),ratStandard true (false,(4,0,0)),ratStandard true (false,(0,1,1)),ratStandard true (false,(1,2,0)),ratStandard true (false,(2,0,1)),ratStandard true (false,(3,1,0)),ratStandard true (false,(5,0,0)),ratStandard true (true,(0,0,0)),ratStandard true (true,(1,0,0)),ratStandard true (true,(0,1,0)),ratStandard true (true,(2,0,0)),ratStandard true (true,(0,0,1)),ratStandard true (true,(1,1,0)),ratStandard true (true,(3,0,0)),ratStandard true (true,(0,2,0)),ratStandard true (true,(1,0,1)),ratStandard true (true,(2,1,0)),ratStandard true (true,(4,0,0))]]
  simp only [List.cons.injEq,and_true]
  exact ⟨⟨raw_identity_0000,⟨raw_identity_0001,⟨raw_identity_0002,⟨raw_identity_0003,⟨raw_identity_0004,⟨raw_identity_0005,⟨raw_identity_0006,⟨raw_identity_0007,⟨raw_identity_0008,⟨raw_identity_0009,⟨raw_identity_0010,⟨raw_identity_0035,⟨raw_identity_0036,⟨raw_identity_0037,⟨raw_identity_0038,⟨raw_identity_0039,⟨raw_identity_0056,⟨raw_identity_0057,⟨raw_identity_0058,⟨raw_identity_0059,⟨raw_identity_0060,⟨raw_identity_0061,raw_identity_0062⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,⟨⟨raw_identity_0011,⟨raw_identity_0012,⟨raw_identity_0040,⟨raw_identity_0041,⟨raw_identity_0063,⟨raw_identity_0064,raw_identity_0065⟩⟩⟩⟩⟩⟩,⟨⟨raw_identity_0013,⟨raw_identity_0014,⟨raw_identity_0015,⟨raw_identity_0016,⟨raw_identity_0017,⟨raw_identity_0018,⟨raw_identity_0019,⟨raw_identity_0042,⟨raw_identity_0043,⟨raw_identity_0044,⟨raw_identity_0045,⟨raw_identity_0066,⟨raw_identity_0067,⟨raw_identity_0068,⟨raw_identity_0069,⟨raw_identity_0070,⟨raw_identity_0020,⟨raw_identity_0021,⟨raw_identity_0022,⟨raw_identity_0023,⟨raw_identity_0046,⟨raw_identity_0047,⟨raw_identity_0048,⟨raw_identity_0071,⟨raw_identity_0072,⟨raw_identity_0073,raw_identity_0074⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,⟨raw_identity_0024,⟨raw_identity_0025,⟨raw_identity_0026,⟨raw_identity_0027,⟨raw_identity_0028,⟨raw_identity_0029,⟨raw_identity_0030,⟨raw_identity_0049,⟨raw_identity_0050,⟨raw_identity_0051,⟨raw_identity_0052,⟨raw_identity_0075,⟨raw_identity_0076,⟨raw_identity_0077,⟨raw_identity_0078,⟨raw_identity_0079,⟨raw_identity_0031,⟨raw_identity_0032,⟨raw_identity_0033,⟨raw_identity_0034,⟨raw_identity_0053,⟨raw_identity_0054,⟨raw_identity_0055,⟨raw_identity_0080,⟨raw_identity_0081,⟨raw_identity_0082,raw_identity_0083⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem source_entry3 : EntryAgrees entry3 := by
  simp only [EntryAgrees,entry3,expectedTags,expectedPivots,expectedFrees,expectedGroups,standardTagList,invariantPivots,signPivots,standardPivots,parityPivots,Bool.false_eq_true,if_false,if_true,Nat.reduceSub,invariantTagList_1,invariantTagList_2,invariantTagList_3,invariantTagList_4,invariantTagList_5,invariantTagList_6,invariantTagList_7,invariantTagList_8,invariantTagList_9,parityTagList_3,parityTagList_4,parityTagList_5,parityTagList_6,parityTagList_7,parityTagList_8,parityTagList_9]
  refine ⟨by decide,by decide,by decide,?_⟩
  change [[sparsePolynomial p0000,sparsePolynomial p0001,sparsePolynomial p0002,sparsePolynomial p0003,sparsePolynomial p0004,sparsePolynomial p0005,sparsePolynomial p0006,sparsePolynomial p0007,sparsePolynomial p0008,sparsePolynomial p0009,sparsePolynomial p0010,sparsePolynomial p0035,sparsePolynomial p0036,sparsePolynomial p0037,sparsePolynomial p0038,sparsePolynomial p0039,sparsePolynomial p0056,sparsePolynomial p0057,sparsePolynomial p0058,sparsePolynomial p0059,sparsePolynomial p0060,sparsePolynomial p0061,sparsePolynomial p0062,sparsePolynomial p0084,sparsePolynomial p0085,sparsePolynomial p0086,sparsePolynomial p0087,sparsePolynomial p0088,sparsePolynomial p0089,sparsePolynomial p0090,sparsePolynomial p0091],[sparsePolynomial p0011,sparsePolynomial p0012,sparsePolynomial p0040,sparsePolynomial p0041,sparsePolynomial p0063,sparsePolynomial p0064,sparsePolynomial p0065,sparsePolynomial p0092,sparsePolynomial p0093,sparsePolynomial p0094,sparsePolynomial p0095],[sparsePolynomial p0013,sparsePolynomial p0014,sparsePolynomial p0015,sparsePolynomial p0016,sparsePolynomial p0017,sparsePolynomial p0018,sparsePolynomial p0019,sparsePolynomial p0042,sparsePolynomial p0043,sparsePolynomial p0044,sparsePolynomial p0045,sparsePolynomial p0066,sparsePolynomial p0067,sparsePolynomial p0068,sparsePolynomial p0069,sparsePolynomial p0070,sparsePolynomial p0096,sparsePolynomial p0097,sparsePolynomial p0098,sparsePolynomial p0099,sparsePolynomial p0100,sparsePolynomial p0101,sparsePolynomial p0102,sparsePolynomial p0020,sparsePolynomial p0021,sparsePolynomial p0022,sparsePolynomial p0023,sparsePolynomial p0046,sparsePolynomial p0047,sparsePolynomial p0048,sparsePolynomial p0071,sparsePolynomial p0072,sparsePolynomial p0073,sparsePolynomial p0074,sparsePolynomial p0103,sparsePolynomial p0104,sparsePolynomial p0105,sparsePolynomial p0106,sparsePolynomial p0107],[sparsePolynomial p0024,sparsePolynomial p0025,sparsePolynomial p0026,sparsePolynomial p0027,sparsePolynomial p0028,sparsePolynomial p0029,sparsePolynomial p0030,sparsePolynomial p0049,sparsePolynomial p0050,sparsePolynomial p0051,sparsePolynomial p0052,sparsePolynomial p0075,sparsePolynomial p0076,sparsePolynomial p0077,sparsePolynomial p0078,sparsePolynomial p0079,sparsePolynomial p0108,sparsePolynomial p0109,sparsePolynomial p0110,sparsePolynomial p0111,sparsePolynomial p0112,sparsePolynomial p0113,sparsePolynomial p0114,sparsePolynomial p0031,sparsePolynomial p0032,sparsePolynomial p0033,sparsePolynomial p0034,sparsePolynomial p0053,sparsePolynomial p0054,sparsePolynomial p0055,sparsePolynomial p0080,sparsePolynomial p0081,sparsePolynomial p0082,sparsePolynomial p0083,sparsePolynomial p0115,sparsePolynomial p0116,sparsePolynomial p0117,sparsePolynomial p0118,sparsePolynomial p0119]]=[[ratInvariant (0,0,0),ratInvariant (1,0,0),ratInvariant (0,1,0),ratInvariant (2,0,0),ratInvariant (0,0,1),ratInvariant (1,1,0),ratInvariant (3,0,0),ratInvariant (0,2,0),ratInvariant (1,0,1),ratInvariant (2,1,0),ratInvariant (4,0,0),ratInvariant (0,1,1),ratInvariant (1,2,0),ratInvariant (2,0,1),ratInvariant (3,1,0),ratInvariant (5,0,0),ratInvariant (0,0,2),ratInvariant (0,3,0),ratInvariant (1,1,1),ratInvariant (2,2,0),ratInvariant (3,0,1),ratInvariant (4,1,0),ratInvariant (6,0,0),ratInvariant (0,2,1),ratInvariant (1,0,2),ratInvariant (1,3,0),ratInvariant (2,1,1),ratInvariant (3,2,0),ratInvariant (4,0,1),ratInvariant (5,1,0),ratInvariant (7,0,0)],[ratDelta*ratInvariant (0,0,0),ratDelta*ratInvariant (1,0,0),ratDelta*ratInvariant (0,1,0),ratDelta*ratInvariant (2,0,0),ratDelta*ratInvariant (0,0,1),ratDelta*ratInvariant (1,1,0),ratDelta*ratInvariant (3,0,0),ratDelta*ratInvariant (0,2,0),ratDelta*ratInvariant (1,0,1),ratDelta*ratInvariant (2,1,0),ratDelta*ratInvariant (4,0,0)],[ratStandard false (false,(0,0,0)),ratStandard false (false,(1,0,0)),ratStandard false (false,(0,1,0)),ratStandard false (false,(2,0,0)),ratStandard false (false,(0,0,1)),ratStandard false (false,(1,1,0)),ratStandard false (false,(3,0,0)),ratStandard false (false,(0,2,0)),ratStandard false (false,(1,0,1)),ratStandard false (false,(2,1,0)),ratStandard false (false,(4,0,0)),ratStandard false (false,(0,1,1)),ratStandard false (false,(1,2,0)),ratStandard false (false,(2,0,1)),ratStandard false (false,(3,1,0)),ratStandard false (false,(5,0,0)),ratStandard false (false,(0,0,2)),ratStandard false (false,(0,3,0)),ratStandard false (false,(1,1,1)),ratStandard false (false,(2,2,0)),ratStandard false (false,(3,0,1)),ratStandard false (false,(4,1,0)),ratStandard false (false,(6,0,0)),ratStandard false (true,(0,0,0)),ratStandard false (true,(1,0,0)),ratStandard false (true,(0,1,0)),ratStandard false (true,(2,0,0)),ratStandard false (true,(0,0,1)),ratStandard false (true,(1,1,0)),ratStandard false (true,(3,0,0)),ratStandard false (true,(0,2,0)),ratStandard false (true,(1,0,1)),ratStandard false (true,(2,1,0)),ratStandard false (true,(4,0,0)),ratStandard false (true,(0,1,1)),ratStandard false (true,(1,2,0)),ratStandard false (true,(2,0,1)),ratStandard false (true,(3,1,0)),ratStandard false (true,(5,0,0))],[ratStandard true (false,(0,0,0)),ratStandard true (false,(1,0,0)),ratStandard true (false,(0,1,0)),ratStandard true (false,(2,0,0)),ratStandard true (false,(0,0,1)),ratStandard true (false,(1,1,0)),ratStandard true (false,(3,0,0)),ratStandard true (false,(0,2,0)),ratStandard true (false,(1,0,1)),ratStandard true (false,(2,1,0)),ratStandard true (false,(4,0,0)),ratStandard true (false,(0,1,1)),ratStandard true (false,(1,2,0)),ratStandard true (false,(2,0,1)),ratStandard true (false,(3,1,0)),ratStandard true (false,(5,0,0)),ratStandard true (false,(0,0,2)),ratStandard true (false,(0,3,0)),ratStandard true (false,(1,1,1)),ratStandard true (false,(2,2,0)),ratStandard true (false,(3,0,1)),ratStandard true (false,(4,1,0)),ratStandard true (false,(6,0,0)),ratStandard true (true,(0,0,0)),ratStandard true (true,(1,0,0)),ratStandard true (true,(0,1,0)),ratStandard true (true,(2,0,0)),ratStandard true (true,(0,0,1)),ratStandard true (true,(1,1,0)),ratStandard true (true,(3,0,0)),ratStandard true (true,(0,2,0)),ratStandard true (true,(1,0,1)),ratStandard true (true,(2,1,0)),ratStandard true (true,(4,0,0)),ratStandard true (true,(0,1,1)),ratStandard true (true,(1,2,0)),ratStandard true (true,(2,0,1)),ratStandard true (true,(3,1,0)),ratStandard true (true,(5,0,0))]]
  simp only [List.cons.injEq,and_true]
  exact ⟨⟨raw_identity_0000,⟨raw_identity_0001,⟨raw_identity_0002,⟨raw_identity_0003,⟨raw_identity_0004,⟨raw_identity_0005,⟨raw_identity_0006,⟨raw_identity_0007,⟨raw_identity_0008,⟨raw_identity_0009,⟨raw_identity_0010,⟨raw_identity_0035,⟨raw_identity_0036,⟨raw_identity_0037,⟨raw_identity_0038,⟨raw_identity_0039,⟨raw_identity_0056,⟨raw_identity_0057,⟨raw_identity_0058,⟨raw_identity_0059,⟨raw_identity_0060,⟨raw_identity_0061,⟨raw_identity_0062,⟨raw_identity_0084,⟨raw_identity_0085,⟨raw_identity_0086,⟨raw_identity_0087,⟨raw_identity_0088,⟨raw_identity_0089,⟨raw_identity_0090,raw_identity_0091⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,⟨⟨raw_identity_0011,⟨raw_identity_0012,⟨raw_identity_0040,⟨raw_identity_0041,⟨raw_identity_0063,⟨raw_identity_0064,⟨raw_identity_0065,⟨raw_identity_0092,⟨raw_identity_0093,⟨raw_identity_0094,raw_identity_0095⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,⟨⟨raw_identity_0013,⟨raw_identity_0014,⟨raw_identity_0015,⟨raw_identity_0016,⟨raw_identity_0017,⟨raw_identity_0018,⟨raw_identity_0019,⟨raw_identity_0042,⟨raw_identity_0043,⟨raw_identity_0044,⟨raw_identity_0045,⟨raw_identity_0066,⟨raw_identity_0067,⟨raw_identity_0068,⟨raw_identity_0069,⟨raw_identity_0070,⟨raw_identity_0096,⟨raw_identity_0097,⟨raw_identity_0098,⟨raw_identity_0099,⟨raw_identity_0100,⟨raw_identity_0101,⟨raw_identity_0102,⟨raw_identity_0020,⟨raw_identity_0021,⟨raw_identity_0022,⟨raw_identity_0023,⟨raw_identity_0046,⟨raw_identity_0047,⟨raw_identity_0048,⟨raw_identity_0071,⟨raw_identity_0072,⟨raw_identity_0073,⟨raw_identity_0074,⟨raw_identity_0103,⟨raw_identity_0104,⟨raw_identity_0105,⟨raw_identity_0106,raw_identity_0107⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,⟨raw_identity_0024,⟨raw_identity_0025,⟨raw_identity_0026,⟨raw_identity_0027,⟨raw_identity_0028,⟨raw_identity_0029,⟨raw_identity_0030,⟨raw_identity_0049,⟨raw_identity_0050,⟨raw_identity_0051,⟨raw_identity_0052,⟨raw_identity_0075,⟨raw_identity_0076,⟨raw_identity_0077,⟨raw_identity_0078,⟨raw_identity_0079,⟨raw_identity_0108,⟨raw_identity_0109,⟨raw_identity_0110,⟨raw_identity_0111,⟨raw_identity_0112,⟨raw_identity_0113,⟨raw_identity_0114,⟨raw_identity_0031,⟨raw_identity_0032,⟨raw_identity_0033,⟨raw_identity_0034,⟨raw_identity_0053,⟨raw_identity_0054,⟨raw_identity_0055,⟨raw_identity_0080,⟨raw_identity_0081,⟨raw_identity_0082,⟨raw_identity_0083,⟨raw_identity_0115,⟨raw_identity_0116,⟨raw_identity_0117,⟨raw_identity_0118,raw_identity_0119⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem source_entry4 : EntryAgrees entry4 := by
  simp only [EntryAgrees,entry4,expectedTags,expectedPivots,expectedFrees,expectedGroups,standardTagList,invariantPivots,signPivots,standardPivots,parityPivots,Bool.false_eq_true,if_false,if_true,Nat.reduceSub,invariantTagList_1,invariantTagList_2,invariantTagList_3,invariantTagList_4,invariantTagList_5,invariantTagList_6,invariantTagList_7,invariantTagList_8,invariantTagList_9,parityTagList_3,parityTagList_4,parityTagList_5,parityTagList_6,parityTagList_7,parityTagList_8,parityTagList_9]
  refine ⟨by decide,by decide,by decide,?_⟩
  change [[sparsePolynomial p0000,sparsePolynomial p0001,sparsePolynomial p0002,sparsePolynomial p0003,sparsePolynomial p0004,sparsePolynomial p0005,sparsePolynomial p0006,sparsePolynomial p0007,sparsePolynomial p0008,sparsePolynomial p0009,sparsePolynomial p0010,sparsePolynomial p0035,sparsePolynomial p0036,sparsePolynomial p0037,sparsePolynomial p0038,sparsePolynomial p0039,sparsePolynomial p0056,sparsePolynomial p0057,sparsePolynomial p0058,sparsePolynomial p0059,sparsePolynomial p0060,sparsePolynomial p0061,sparsePolynomial p0062,sparsePolynomial p0084,sparsePolynomial p0085,sparsePolynomial p0086,sparsePolynomial p0087,sparsePolynomial p0088,sparsePolynomial p0089,sparsePolynomial p0090,sparsePolynomial p0091,sparsePolynomial p0120,sparsePolynomial p0121,sparsePolynomial p0122,sparsePolynomial p0123,sparsePolynomial p0124,sparsePolynomial p0125,sparsePolynomial p0126,sparsePolynomial p0127,sparsePolynomial p0128,sparsePolynomial p0129],[sparsePolynomial p0011,sparsePolynomial p0012,sparsePolynomial p0040,sparsePolynomial p0041,sparsePolynomial p0063,sparsePolynomial p0064,sparsePolynomial p0065,sparsePolynomial p0092,sparsePolynomial p0093,sparsePolynomial p0094,sparsePolynomial p0095,sparsePolynomial p0130,sparsePolynomial p0131,sparsePolynomial p0132,sparsePolynomial p0133,sparsePolynomial p0134],[sparsePolynomial p0013,sparsePolynomial p0014,sparsePolynomial p0015,sparsePolynomial p0016,sparsePolynomial p0017,sparsePolynomial p0018,sparsePolynomial p0019,sparsePolynomial p0042,sparsePolynomial p0043,sparsePolynomial p0044,sparsePolynomial p0045,sparsePolynomial p0066,sparsePolynomial p0067,sparsePolynomial p0068,sparsePolynomial p0069,sparsePolynomial p0070,sparsePolynomial p0096,sparsePolynomial p0097,sparsePolynomial p0098,sparsePolynomial p0099,sparsePolynomial p0100,sparsePolynomial p0101,sparsePolynomial p0102,sparsePolynomial p0135,sparsePolynomial p0136,sparsePolynomial p0137,sparsePolynomial p0138,sparsePolynomial p0139,sparsePolynomial p0140,sparsePolynomial p0141,sparsePolynomial p0142,sparsePolynomial p0020,sparsePolynomial p0021,sparsePolynomial p0022,sparsePolynomial p0023,sparsePolynomial p0046,sparsePolynomial p0047,sparsePolynomial p0048,sparsePolynomial p0071,sparsePolynomial p0072,sparsePolynomial p0073,sparsePolynomial p0074,sparsePolynomial p0103,sparsePolynomial p0104,sparsePolynomial p0105,sparsePolynomial p0106,sparsePolynomial p0107,sparsePolynomial p0143,sparsePolynomial p0144,sparsePolynomial p0145,sparsePolynomial p0146,sparsePolynomial p0147,sparsePolynomial p0148,sparsePolynomial p0149],[sparsePolynomial p0024,sparsePolynomial p0025,sparsePolynomial p0026,sparsePolynomial p0027,sparsePolynomial p0028,sparsePolynomial p0029,sparsePolynomial p0030,sparsePolynomial p0049,sparsePolynomial p0050,sparsePolynomial p0051,sparsePolynomial p0052,sparsePolynomial p0075,sparsePolynomial p0076,sparsePolynomial p0077,sparsePolynomial p0078,sparsePolynomial p0079,sparsePolynomial p0108,sparsePolynomial p0109,sparsePolynomial p0110,sparsePolynomial p0111,sparsePolynomial p0112,sparsePolynomial p0113,sparsePolynomial p0114,sparsePolynomial p0150,sparsePolynomial p0151,sparsePolynomial p0152,sparsePolynomial p0153,sparsePolynomial p0154,sparsePolynomial p0155,sparsePolynomial p0156,sparsePolynomial p0157,sparsePolynomial p0031,sparsePolynomial p0032,sparsePolynomial p0033,sparsePolynomial p0034,sparsePolynomial p0053,sparsePolynomial p0054,sparsePolynomial p0055,sparsePolynomial p0080,sparsePolynomial p0081,sparsePolynomial p0082,sparsePolynomial p0083,sparsePolynomial p0115,sparsePolynomial p0116,sparsePolynomial p0117,sparsePolynomial p0118,sparsePolynomial p0119,sparsePolynomial p0158,sparsePolynomial p0159,sparsePolynomial p0160,sparsePolynomial p0161,sparsePolynomial p0162,sparsePolynomial p0163,sparsePolynomial p0164]]=[[ratInvariant (0,0,0),ratInvariant (1,0,0),ratInvariant (0,1,0),ratInvariant (2,0,0),ratInvariant (0,0,1),ratInvariant (1,1,0),ratInvariant (3,0,0),ratInvariant (0,2,0),ratInvariant (1,0,1),ratInvariant (2,1,0),ratInvariant (4,0,0),ratInvariant (0,1,1),ratInvariant (1,2,0),ratInvariant (2,0,1),ratInvariant (3,1,0),ratInvariant (5,0,0),ratInvariant (0,0,2),ratInvariant (0,3,0),ratInvariant (1,1,1),ratInvariant (2,2,0),ratInvariant (3,0,1),ratInvariant (4,1,0),ratInvariant (6,0,0),ratInvariant (0,2,1),ratInvariant (1,0,2),ratInvariant (1,3,0),ratInvariant (2,1,1),ratInvariant (3,2,0),ratInvariant (4,0,1),ratInvariant (5,1,0),ratInvariant (7,0,0),ratInvariant (0,1,2),ratInvariant (0,4,0),ratInvariant (1,2,1),ratInvariant (2,0,2),ratInvariant (2,3,0),ratInvariant (3,1,1),ratInvariant (4,2,0),ratInvariant (5,0,1),ratInvariant (6,1,0),ratInvariant (8,0,0)],[ratDelta*ratInvariant (0,0,0),ratDelta*ratInvariant (1,0,0),ratDelta*ratInvariant (0,1,0),ratDelta*ratInvariant (2,0,0),ratDelta*ratInvariant (0,0,1),ratDelta*ratInvariant (1,1,0),ratDelta*ratInvariant (3,0,0),ratDelta*ratInvariant (0,2,0),ratDelta*ratInvariant (1,0,1),ratDelta*ratInvariant (2,1,0),ratDelta*ratInvariant (4,0,0),ratDelta*ratInvariant (0,1,1),ratDelta*ratInvariant (1,2,0),ratDelta*ratInvariant (2,0,1),ratDelta*ratInvariant (3,1,0),ratDelta*ratInvariant (5,0,0)],[ratStandard false (false,(0,0,0)),ratStandard false (false,(1,0,0)),ratStandard false (false,(0,1,0)),ratStandard false (false,(2,0,0)),ratStandard false (false,(0,0,1)),ratStandard false (false,(1,1,0)),ratStandard false (false,(3,0,0)),ratStandard false (false,(0,2,0)),ratStandard false (false,(1,0,1)),ratStandard false (false,(2,1,0)),ratStandard false (false,(4,0,0)),ratStandard false (false,(0,1,1)),ratStandard false (false,(1,2,0)),ratStandard false (false,(2,0,1)),ratStandard false (false,(3,1,0)),ratStandard false (false,(5,0,0)),ratStandard false (false,(0,0,2)),ratStandard false (false,(0,3,0)),ratStandard false (false,(1,1,1)),ratStandard false (false,(2,2,0)),ratStandard false (false,(3,0,1)),ratStandard false (false,(4,1,0)),ratStandard false (false,(6,0,0)),ratStandard false (false,(0,2,1)),ratStandard false (false,(1,0,2)),ratStandard false (false,(1,3,0)),ratStandard false (false,(2,1,1)),ratStandard false (false,(3,2,0)),ratStandard false (false,(4,0,1)),ratStandard false (false,(5,1,0)),ratStandard false (false,(7,0,0)),ratStandard false (true,(0,0,0)),ratStandard false (true,(1,0,0)),ratStandard false (true,(0,1,0)),ratStandard false (true,(2,0,0)),ratStandard false (true,(0,0,1)),ratStandard false (true,(1,1,0)),ratStandard false (true,(3,0,0)),ratStandard false (true,(0,2,0)),ratStandard false (true,(1,0,1)),ratStandard false (true,(2,1,0)),ratStandard false (true,(4,0,0)),ratStandard false (true,(0,1,1)),ratStandard false (true,(1,2,0)),ratStandard false (true,(2,0,1)),ratStandard false (true,(3,1,0)),ratStandard false (true,(5,0,0)),ratStandard false (true,(0,0,2)),ratStandard false (true,(0,3,0)),ratStandard false (true,(1,1,1)),ratStandard false (true,(2,2,0)),ratStandard false (true,(3,0,1)),ratStandard false (true,(4,1,0)),ratStandard false (true,(6,0,0))],[ratStandard true (false,(0,0,0)),ratStandard true (false,(1,0,0)),ratStandard true (false,(0,1,0)),ratStandard true (false,(2,0,0)),ratStandard true (false,(0,0,1)),ratStandard true (false,(1,1,0)),ratStandard true (false,(3,0,0)),ratStandard true (false,(0,2,0)),ratStandard true (false,(1,0,1)),ratStandard true (false,(2,1,0)),ratStandard true (false,(4,0,0)),ratStandard true (false,(0,1,1)),ratStandard true (false,(1,2,0)),ratStandard true (false,(2,0,1)),ratStandard true (false,(3,1,0)),ratStandard true (false,(5,0,0)),ratStandard true (false,(0,0,2)),ratStandard true (false,(0,3,0)),ratStandard true (false,(1,1,1)),ratStandard true (false,(2,2,0)),ratStandard true (false,(3,0,1)),ratStandard true (false,(4,1,0)),ratStandard true (false,(6,0,0)),ratStandard true (false,(0,2,1)),ratStandard true (false,(1,0,2)),ratStandard true (false,(1,3,0)),ratStandard true (false,(2,1,1)),ratStandard true (false,(3,2,0)),ratStandard true (false,(4,0,1)),ratStandard true (false,(5,1,0)),ratStandard true (false,(7,0,0)),ratStandard true (true,(0,0,0)),ratStandard true (true,(1,0,0)),ratStandard true (true,(0,1,0)),ratStandard true (true,(2,0,0)),ratStandard true (true,(0,0,1)),ratStandard true (true,(1,1,0)),ratStandard true (true,(3,0,0)),ratStandard true (true,(0,2,0)),ratStandard true (true,(1,0,1)),ratStandard true (true,(2,1,0)),ratStandard true (true,(4,0,0)),ratStandard true (true,(0,1,1)),ratStandard true (true,(1,2,0)),ratStandard true (true,(2,0,1)),ratStandard true (true,(3,1,0)),ratStandard true (true,(5,0,0)),ratStandard true (true,(0,0,2)),ratStandard true (true,(0,3,0)),ratStandard true (true,(1,1,1)),ratStandard true (true,(2,2,0)),ratStandard true (true,(3,0,1)),ratStandard true (true,(4,1,0)),ratStandard true (true,(6,0,0))]]
  simp only [List.cons.injEq,and_true]
  exact ⟨⟨raw_identity_0000,⟨raw_identity_0001,⟨raw_identity_0002,⟨raw_identity_0003,⟨raw_identity_0004,⟨raw_identity_0005,⟨raw_identity_0006,⟨raw_identity_0007,⟨raw_identity_0008,⟨raw_identity_0009,⟨raw_identity_0010,⟨raw_identity_0035,⟨raw_identity_0036,⟨raw_identity_0037,⟨raw_identity_0038,⟨raw_identity_0039,⟨raw_identity_0056,⟨raw_identity_0057,⟨raw_identity_0058,⟨raw_identity_0059,⟨raw_identity_0060,⟨raw_identity_0061,⟨raw_identity_0062,⟨raw_identity_0084,⟨raw_identity_0085,⟨raw_identity_0086,⟨raw_identity_0087,⟨raw_identity_0088,⟨raw_identity_0089,⟨raw_identity_0090,⟨raw_identity_0091,⟨raw_identity_0120,⟨raw_identity_0121,⟨raw_identity_0122,⟨raw_identity_0123,⟨raw_identity_0124,⟨raw_identity_0125,⟨raw_identity_0126,⟨raw_identity_0127,⟨raw_identity_0128,raw_identity_0129⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,⟨⟨raw_identity_0011,⟨raw_identity_0012,⟨raw_identity_0040,⟨raw_identity_0041,⟨raw_identity_0063,⟨raw_identity_0064,⟨raw_identity_0065,⟨raw_identity_0092,⟨raw_identity_0093,⟨raw_identity_0094,⟨raw_identity_0095,⟨raw_identity_0130,⟨raw_identity_0131,⟨raw_identity_0132,⟨raw_identity_0133,raw_identity_0134⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,⟨⟨raw_identity_0013,⟨raw_identity_0014,⟨raw_identity_0015,⟨raw_identity_0016,⟨raw_identity_0017,⟨raw_identity_0018,⟨raw_identity_0019,⟨raw_identity_0042,⟨raw_identity_0043,⟨raw_identity_0044,⟨raw_identity_0045,⟨raw_identity_0066,⟨raw_identity_0067,⟨raw_identity_0068,⟨raw_identity_0069,⟨raw_identity_0070,⟨raw_identity_0096,⟨raw_identity_0097,⟨raw_identity_0098,⟨raw_identity_0099,⟨raw_identity_0100,⟨raw_identity_0101,⟨raw_identity_0102,⟨raw_identity_0135,⟨raw_identity_0136,⟨raw_identity_0137,⟨raw_identity_0138,⟨raw_identity_0139,⟨raw_identity_0140,⟨raw_identity_0141,⟨raw_identity_0142,⟨raw_identity_0020,⟨raw_identity_0021,⟨raw_identity_0022,⟨raw_identity_0023,⟨raw_identity_0046,⟨raw_identity_0047,⟨raw_identity_0048,⟨raw_identity_0071,⟨raw_identity_0072,⟨raw_identity_0073,⟨raw_identity_0074,⟨raw_identity_0103,⟨raw_identity_0104,⟨raw_identity_0105,⟨raw_identity_0106,⟨raw_identity_0107,⟨raw_identity_0143,⟨raw_identity_0144,⟨raw_identity_0145,⟨raw_identity_0146,⟨raw_identity_0147,⟨raw_identity_0148,raw_identity_0149⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,⟨raw_identity_0024,⟨raw_identity_0025,⟨raw_identity_0026,⟨raw_identity_0027,⟨raw_identity_0028,⟨raw_identity_0029,⟨raw_identity_0030,⟨raw_identity_0049,⟨raw_identity_0050,⟨raw_identity_0051,⟨raw_identity_0052,⟨raw_identity_0075,⟨raw_identity_0076,⟨raw_identity_0077,⟨raw_identity_0078,⟨raw_identity_0079,⟨raw_identity_0108,⟨raw_identity_0109,⟨raw_identity_0110,⟨raw_identity_0111,⟨raw_identity_0112,⟨raw_identity_0113,⟨raw_identity_0114,⟨raw_identity_0150,⟨raw_identity_0151,⟨raw_identity_0152,⟨raw_identity_0153,⟨raw_identity_0154,⟨raw_identity_0155,⟨raw_identity_0156,⟨raw_identity_0157,⟨raw_identity_0031,⟨raw_identity_0032,⟨raw_identity_0033,⟨raw_identity_0034,⟨raw_identity_0053,⟨raw_identity_0054,⟨raw_identity_0055,⟨raw_identity_0080,⟨raw_identity_0081,⟨raw_identity_0082,⟨raw_identity_0083,⟨raw_identity_0115,⟨raw_identity_0116,⟨raw_identity_0117,⟨raw_identity_0118,⟨raw_identity_0119,⟨raw_identity_0158,⟨raw_identity_0159,⟨raw_identity_0160,⟨raw_identity_0161,⟨raw_identity_0162,⟨raw_identity_0163,raw_identity_0164⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem source_entry5 : EntryAgrees entry5 := by
  simp only [EntryAgrees,entry5,expectedTags,expectedPivots,expectedFrees,expectedGroups,standardTagList,invariantPivots,signPivots,standardPivots,parityPivots,Bool.false_eq_true,if_false,if_true,Nat.reduceSub,invariantTagList_1,invariantTagList_2,invariantTagList_3,invariantTagList_4,invariantTagList_5,invariantTagList_6,invariantTagList_7,invariantTagList_8,invariantTagList_9,parityTagList_3,parityTagList_4,parityTagList_5,parityTagList_6,parityTagList_7,parityTagList_8,parityTagList_9]
  refine ⟨by decide,by decide,by decide,?_⟩
  change [[sparsePolynomial p0000,sparsePolynomial p0001,sparsePolynomial p0002,sparsePolynomial p0003,sparsePolynomial p0004,sparsePolynomial p0005,sparsePolynomial p0006,sparsePolynomial p0007,sparsePolynomial p0008,sparsePolynomial p0009,sparsePolynomial p0010,sparsePolynomial p0035,sparsePolynomial p0036,sparsePolynomial p0037,sparsePolynomial p0038,sparsePolynomial p0039,sparsePolynomial p0056,sparsePolynomial p0057,sparsePolynomial p0058,sparsePolynomial p0059,sparsePolynomial p0060,sparsePolynomial p0061,sparsePolynomial p0062,sparsePolynomial p0084,sparsePolynomial p0085,sparsePolynomial p0086,sparsePolynomial p0087,sparsePolynomial p0088,sparsePolynomial p0089,sparsePolynomial p0090,sparsePolynomial p0091,sparsePolynomial p0120,sparsePolynomial p0121,sparsePolynomial p0122,sparsePolynomial p0123,sparsePolynomial p0124,sparsePolynomial p0125,sparsePolynomial p0126,sparsePolynomial p0127,sparsePolynomial p0128,sparsePolynomial p0129,sparsePolynomial p0165,sparsePolynomial p0166,sparsePolynomial p0167,sparsePolynomial p0168,sparsePolynomial p0169,sparsePolynomial p0170,sparsePolynomial p0171,sparsePolynomial p0172,sparsePolynomial p0173,sparsePolynomial p0174,sparsePolynomial p0175,sparsePolynomial p0176],[sparsePolynomial p0011,sparsePolynomial p0012,sparsePolynomial p0040,sparsePolynomial p0041,sparsePolynomial p0063,sparsePolynomial p0064,sparsePolynomial p0065,sparsePolynomial p0092,sparsePolynomial p0093,sparsePolynomial p0094,sparsePolynomial p0095,sparsePolynomial p0130,sparsePolynomial p0131,sparsePolynomial p0132,sparsePolynomial p0133,sparsePolynomial p0134,sparsePolynomial p0177,sparsePolynomial p0178,sparsePolynomial p0179,sparsePolynomial p0180,sparsePolynomial p0181,sparsePolynomial p0182,sparsePolynomial p0183],[sparsePolynomial p0013,sparsePolynomial p0014,sparsePolynomial p0015,sparsePolynomial p0016,sparsePolynomial p0017,sparsePolynomial p0018,sparsePolynomial p0019,sparsePolynomial p0042,sparsePolynomial p0043,sparsePolynomial p0044,sparsePolynomial p0045,sparsePolynomial p0066,sparsePolynomial p0067,sparsePolynomial p0068,sparsePolynomial p0069,sparsePolynomial p0070,sparsePolynomial p0096,sparsePolynomial p0097,sparsePolynomial p0098,sparsePolynomial p0099,sparsePolynomial p0100,sparsePolynomial p0101,sparsePolynomial p0102,sparsePolynomial p0135,sparsePolynomial p0136,sparsePolynomial p0137,sparsePolynomial p0138,sparsePolynomial p0139,sparsePolynomial p0140,sparsePolynomial p0141,sparsePolynomial p0142,sparsePolynomial p0184,sparsePolynomial p0185,sparsePolynomial p0186,sparsePolynomial p0187,sparsePolynomial p0188,sparsePolynomial p0189,sparsePolynomial p0190,sparsePolynomial p0191,sparsePolynomial p0192,sparsePolynomial p0193,sparsePolynomial p0020,sparsePolynomial p0021,sparsePolynomial p0022,sparsePolynomial p0023,sparsePolynomial p0046,sparsePolynomial p0047,sparsePolynomial p0048,sparsePolynomial p0071,sparsePolynomial p0072,sparsePolynomial p0073,sparsePolynomial p0074,sparsePolynomial p0103,sparsePolynomial p0104,sparsePolynomial p0105,sparsePolynomial p0106,sparsePolynomial p0107,sparsePolynomial p0143,sparsePolynomial p0144,sparsePolynomial p0145,sparsePolynomial p0146,sparsePolynomial p0147,sparsePolynomial p0148,sparsePolynomial p0149,sparsePolynomial p0194,sparsePolynomial p0195,sparsePolynomial p0196,sparsePolynomial p0197,sparsePolynomial p0198,sparsePolynomial p0199,sparsePolynomial p0200,sparsePolynomial p0201],[sparsePolynomial p0024,sparsePolynomial p0025,sparsePolynomial p0026,sparsePolynomial p0027,sparsePolynomial p0028,sparsePolynomial p0029,sparsePolynomial p0030,sparsePolynomial p0049,sparsePolynomial p0050,sparsePolynomial p0051,sparsePolynomial p0052,sparsePolynomial p0075,sparsePolynomial p0076,sparsePolynomial p0077,sparsePolynomial p0078,sparsePolynomial p0079,sparsePolynomial p0108,sparsePolynomial p0109,sparsePolynomial p0110,sparsePolynomial p0111,sparsePolynomial p0112,sparsePolynomial p0113,sparsePolynomial p0114,sparsePolynomial p0150,sparsePolynomial p0151,sparsePolynomial p0152,sparsePolynomial p0153,sparsePolynomial p0154,sparsePolynomial p0155,sparsePolynomial p0156,sparsePolynomial p0157,sparsePolynomial p0202,sparsePolynomial p0203,sparsePolynomial p0204,sparsePolynomial p0205,sparsePolynomial p0206,sparsePolynomial p0207,sparsePolynomial p0208,sparsePolynomial p0209,sparsePolynomial p0210,sparsePolynomial p0211,sparsePolynomial p0031,sparsePolynomial p0032,sparsePolynomial p0033,sparsePolynomial p0034,sparsePolynomial p0053,sparsePolynomial p0054,sparsePolynomial p0055,sparsePolynomial p0080,sparsePolynomial p0081,sparsePolynomial p0082,sparsePolynomial p0083,sparsePolynomial p0115,sparsePolynomial p0116,sparsePolynomial p0117,sparsePolynomial p0118,sparsePolynomial p0119,sparsePolynomial p0158,sparsePolynomial p0159,sparsePolynomial p0160,sparsePolynomial p0161,sparsePolynomial p0162,sparsePolynomial p0163,sparsePolynomial p0164,sparsePolynomial p0212,sparsePolynomial p0213,sparsePolynomial p0214,sparsePolynomial p0215,sparsePolynomial p0216,sparsePolynomial p0217,sparsePolynomial p0218,sparsePolynomial p0219]]=[[ratInvariant (0,0,0),ratInvariant (1,0,0),ratInvariant (0,1,0),ratInvariant (2,0,0),ratInvariant (0,0,1),ratInvariant (1,1,0),ratInvariant (3,0,0),ratInvariant (0,2,0),ratInvariant (1,0,1),ratInvariant (2,1,0),ratInvariant (4,0,0),ratInvariant (0,1,1),ratInvariant (1,2,0),ratInvariant (2,0,1),ratInvariant (3,1,0),ratInvariant (5,0,0),ratInvariant (0,0,2),ratInvariant (0,3,0),ratInvariant (1,1,1),ratInvariant (2,2,0),ratInvariant (3,0,1),ratInvariant (4,1,0),ratInvariant (6,0,0),ratInvariant (0,2,1),ratInvariant (1,0,2),ratInvariant (1,3,0),ratInvariant (2,1,1),ratInvariant (3,2,0),ratInvariant (4,0,1),ratInvariant (5,1,0),ratInvariant (7,0,0),ratInvariant (0,1,2),ratInvariant (0,4,0),ratInvariant (1,2,1),ratInvariant (2,0,2),ratInvariant (2,3,0),ratInvariant (3,1,1),ratInvariant (4,2,0),ratInvariant (5,0,1),ratInvariant (6,1,0),ratInvariant (8,0,0),ratInvariant (0,0,3),ratInvariant (0,3,1),ratInvariant (1,1,2),ratInvariant (1,4,0),ratInvariant (2,2,1),ratInvariant (3,0,2),ratInvariant (3,3,0),ratInvariant (4,1,1),ratInvariant (5,2,0),ratInvariant (6,0,1),ratInvariant (7,1,0),ratInvariant (9,0,0)],[ratDelta*ratInvariant (0,0,0),ratDelta*ratInvariant (1,0,0),ratDelta*ratInvariant (0,1,0),ratDelta*ratInvariant (2,0,0),ratDelta*ratInvariant (0,0,1),ratDelta*ratInvariant (1,1,0),ratDelta*ratInvariant (3,0,0),ratDelta*ratInvariant (0,2,0),ratDelta*ratInvariant (1,0,1),ratDelta*ratInvariant (2,1,0),ratDelta*ratInvariant (4,0,0),ratDelta*ratInvariant (0,1,1),ratDelta*ratInvariant (1,2,0),ratDelta*ratInvariant (2,0,1),ratDelta*ratInvariant (3,1,0),ratDelta*ratInvariant (5,0,0),ratDelta*ratInvariant (0,0,2),ratDelta*ratInvariant (0,3,0),ratDelta*ratInvariant (1,1,1),ratDelta*ratInvariant (2,2,0),ratDelta*ratInvariant (3,0,1),ratDelta*ratInvariant (4,1,0),ratDelta*ratInvariant (6,0,0)],[ratStandard false (false,(0,0,0)),ratStandard false (false,(1,0,0)),ratStandard false (false,(0,1,0)),ratStandard false (false,(2,0,0)),ratStandard false (false,(0,0,1)),ratStandard false (false,(1,1,0)),ratStandard false (false,(3,0,0)),ratStandard false (false,(0,2,0)),ratStandard false (false,(1,0,1)),ratStandard false (false,(2,1,0)),ratStandard false (false,(4,0,0)),ratStandard false (false,(0,1,1)),ratStandard false (false,(1,2,0)),ratStandard false (false,(2,0,1)),ratStandard false (false,(3,1,0)),ratStandard false (false,(5,0,0)),ratStandard false (false,(0,0,2)),ratStandard false (false,(0,3,0)),ratStandard false (false,(1,1,1)),ratStandard false (false,(2,2,0)),ratStandard false (false,(3,0,1)),ratStandard false (false,(4,1,0)),ratStandard false (false,(6,0,0)),ratStandard false (false,(0,2,1)),ratStandard false (false,(1,0,2)),ratStandard false (false,(1,3,0)),ratStandard false (false,(2,1,1)),ratStandard false (false,(3,2,0)),ratStandard false (false,(4,0,1)),ratStandard false (false,(5,1,0)),ratStandard false (false,(7,0,0)),ratStandard false (false,(0,1,2)),ratStandard false (false,(0,4,0)),ratStandard false (false,(1,2,1)),ratStandard false (false,(2,0,2)),ratStandard false (false,(2,3,0)),ratStandard false (false,(3,1,1)),ratStandard false (false,(4,2,0)),ratStandard false (false,(5,0,1)),ratStandard false (false,(6,1,0)),ratStandard false (false,(8,0,0)),ratStandard false (true,(0,0,0)),ratStandard false (true,(1,0,0)),ratStandard false (true,(0,1,0)),ratStandard false (true,(2,0,0)),ratStandard false (true,(0,0,1)),ratStandard false (true,(1,1,0)),ratStandard false (true,(3,0,0)),ratStandard false (true,(0,2,0)),ratStandard false (true,(1,0,1)),ratStandard false (true,(2,1,0)),ratStandard false (true,(4,0,0)),ratStandard false (true,(0,1,1)),ratStandard false (true,(1,2,0)),ratStandard false (true,(2,0,1)),ratStandard false (true,(3,1,0)),ratStandard false (true,(5,0,0)),ratStandard false (true,(0,0,2)),ratStandard false (true,(0,3,0)),ratStandard false (true,(1,1,1)),ratStandard false (true,(2,2,0)),ratStandard false (true,(3,0,1)),ratStandard false (true,(4,1,0)),ratStandard false (true,(6,0,0)),ratStandard false (true,(0,2,1)),ratStandard false (true,(1,0,2)),ratStandard false (true,(1,3,0)),ratStandard false (true,(2,1,1)),ratStandard false (true,(3,2,0)),ratStandard false (true,(4,0,1)),ratStandard false (true,(5,1,0)),ratStandard false (true,(7,0,0))],[ratStandard true (false,(0,0,0)),ratStandard true (false,(1,0,0)),ratStandard true (false,(0,1,0)),ratStandard true (false,(2,0,0)),ratStandard true (false,(0,0,1)),ratStandard true (false,(1,1,0)),ratStandard true (false,(3,0,0)),ratStandard true (false,(0,2,0)),ratStandard true (false,(1,0,1)),ratStandard true (false,(2,1,0)),ratStandard true (false,(4,0,0)),ratStandard true (false,(0,1,1)),ratStandard true (false,(1,2,0)),ratStandard true (false,(2,0,1)),ratStandard true (false,(3,1,0)),ratStandard true (false,(5,0,0)),ratStandard true (false,(0,0,2)),ratStandard true (false,(0,3,0)),ratStandard true (false,(1,1,1)),ratStandard true (false,(2,2,0)),ratStandard true (false,(3,0,1)),ratStandard true (false,(4,1,0)),ratStandard true (false,(6,0,0)),ratStandard true (false,(0,2,1)),ratStandard true (false,(1,0,2)),ratStandard true (false,(1,3,0)),ratStandard true (false,(2,1,1)),ratStandard true (false,(3,2,0)),ratStandard true (false,(4,0,1)),ratStandard true (false,(5,1,0)),ratStandard true (false,(7,0,0)),ratStandard true (false,(0,1,2)),ratStandard true (false,(0,4,0)),ratStandard true (false,(1,2,1)),ratStandard true (false,(2,0,2)),ratStandard true (false,(2,3,0)),ratStandard true (false,(3,1,1)),ratStandard true (false,(4,2,0)),ratStandard true (false,(5,0,1)),ratStandard true (false,(6,1,0)),ratStandard true (false,(8,0,0)),ratStandard true (true,(0,0,0)),ratStandard true (true,(1,0,0)),ratStandard true (true,(0,1,0)),ratStandard true (true,(2,0,0)),ratStandard true (true,(0,0,1)),ratStandard true (true,(1,1,0)),ratStandard true (true,(3,0,0)),ratStandard true (true,(0,2,0)),ratStandard true (true,(1,0,1)),ratStandard true (true,(2,1,0)),ratStandard true (true,(4,0,0)),ratStandard true (true,(0,1,1)),ratStandard true (true,(1,2,0)),ratStandard true (true,(2,0,1)),ratStandard true (true,(3,1,0)),ratStandard true (true,(5,0,0)),ratStandard true (true,(0,0,2)),ratStandard true (true,(0,3,0)),ratStandard true (true,(1,1,1)),ratStandard true (true,(2,2,0)),ratStandard true (true,(3,0,1)),ratStandard true (true,(4,1,0)),ratStandard true (true,(6,0,0)),ratStandard true (true,(0,2,1)),ratStandard true (true,(1,0,2)),ratStandard true (true,(1,3,0)),ratStandard true (true,(2,1,1)),ratStandard true (true,(3,2,0)),ratStandard true (true,(4,0,1)),ratStandard true (true,(5,1,0)),ratStandard true (true,(7,0,0))]]
  simp only [List.cons.injEq,and_true]
  exact ⟨⟨raw_identity_0000,⟨raw_identity_0001,⟨raw_identity_0002,⟨raw_identity_0003,⟨raw_identity_0004,⟨raw_identity_0005,⟨raw_identity_0006,⟨raw_identity_0007,⟨raw_identity_0008,⟨raw_identity_0009,⟨raw_identity_0010,⟨raw_identity_0035,⟨raw_identity_0036,⟨raw_identity_0037,⟨raw_identity_0038,⟨raw_identity_0039,⟨raw_identity_0056,⟨raw_identity_0057,⟨raw_identity_0058,⟨raw_identity_0059,⟨raw_identity_0060,⟨raw_identity_0061,⟨raw_identity_0062,⟨raw_identity_0084,⟨raw_identity_0085,⟨raw_identity_0086,⟨raw_identity_0087,⟨raw_identity_0088,⟨raw_identity_0089,⟨raw_identity_0090,⟨raw_identity_0091,⟨raw_identity_0120,⟨raw_identity_0121,⟨raw_identity_0122,⟨raw_identity_0123,⟨raw_identity_0124,⟨raw_identity_0125,⟨raw_identity_0126,⟨raw_identity_0127,⟨raw_identity_0128,⟨raw_identity_0129,⟨raw_identity_0165,⟨raw_identity_0166,⟨raw_identity_0167,⟨raw_identity_0168,⟨raw_identity_0169,⟨raw_identity_0170,⟨raw_identity_0171,⟨raw_identity_0172,⟨raw_identity_0173,⟨raw_identity_0174,⟨raw_identity_0175,raw_identity_0176⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,⟨⟨raw_identity_0011,⟨raw_identity_0012,⟨raw_identity_0040,⟨raw_identity_0041,⟨raw_identity_0063,⟨raw_identity_0064,⟨raw_identity_0065,⟨raw_identity_0092,⟨raw_identity_0093,⟨raw_identity_0094,⟨raw_identity_0095,⟨raw_identity_0130,⟨raw_identity_0131,⟨raw_identity_0132,⟨raw_identity_0133,⟨raw_identity_0134,⟨raw_identity_0177,⟨raw_identity_0178,⟨raw_identity_0179,⟨raw_identity_0180,⟨raw_identity_0181,⟨raw_identity_0182,raw_identity_0183⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,⟨⟨raw_identity_0013,⟨raw_identity_0014,⟨raw_identity_0015,⟨raw_identity_0016,⟨raw_identity_0017,⟨raw_identity_0018,⟨raw_identity_0019,⟨raw_identity_0042,⟨raw_identity_0043,⟨raw_identity_0044,⟨raw_identity_0045,⟨raw_identity_0066,⟨raw_identity_0067,⟨raw_identity_0068,⟨raw_identity_0069,⟨raw_identity_0070,⟨raw_identity_0096,⟨raw_identity_0097,⟨raw_identity_0098,⟨raw_identity_0099,⟨raw_identity_0100,⟨raw_identity_0101,⟨raw_identity_0102,⟨raw_identity_0135,⟨raw_identity_0136,⟨raw_identity_0137,⟨raw_identity_0138,⟨raw_identity_0139,⟨raw_identity_0140,⟨raw_identity_0141,⟨raw_identity_0142,⟨raw_identity_0184,⟨raw_identity_0185,⟨raw_identity_0186,⟨raw_identity_0187,⟨raw_identity_0188,⟨raw_identity_0189,⟨raw_identity_0190,⟨raw_identity_0191,⟨raw_identity_0192,⟨raw_identity_0193,⟨raw_identity_0020,⟨raw_identity_0021,⟨raw_identity_0022,⟨raw_identity_0023,⟨raw_identity_0046,⟨raw_identity_0047,⟨raw_identity_0048,⟨raw_identity_0071,⟨raw_identity_0072,⟨raw_identity_0073,⟨raw_identity_0074,⟨raw_identity_0103,⟨raw_identity_0104,⟨raw_identity_0105,⟨raw_identity_0106,⟨raw_identity_0107,⟨raw_identity_0143,⟨raw_identity_0144,⟨raw_identity_0145,⟨raw_identity_0146,⟨raw_identity_0147,⟨raw_identity_0148,⟨raw_identity_0149,⟨raw_identity_0194,⟨raw_identity_0195,⟨raw_identity_0196,⟨raw_identity_0197,⟨raw_identity_0198,⟨raw_identity_0199,⟨raw_identity_0200,raw_identity_0201⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,⟨raw_identity_0024,⟨raw_identity_0025,⟨raw_identity_0026,⟨raw_identity_0027,⟨raw_identity_0028,⟨raw_identity_0029,⟨raw_identity_0030,⟨raw_identity_0049,⟨raw_identity_0050,⟨raw_identity_0051,⟨raw_identity_0052,⟨raw_identity_0075,⟨raw_identity_0076,⟨raw_identity_0077,⟨raw_identity_0078,⟨raw_identity_0079,⟨raw_identity_0108,⟨raw_identity_0109,⟨raw_identity_0110,⟨raw_identity_0111,⟨raw_identity_0112,⟨raw_identity_0113,⟨raw_identity_0114,⟨raw_identity_0150,⟨raw_identity_0151,⟨raw_identity_0152,⟨raw_identity_0153,⟨raw_identity_0154,⟨raw_identity_0155,⟨raw_identity_0156,⟨raw_identity_0157,⟨raw_identity_0202,⟨raw_identity_0203,⟨raw_identity_0204,⟨raw_identity_0205,⟨raw_identity_0206,⟨raw_identity_0207,⟨raw_identity_0208,⟨raw_identity_0209,⟨raw_identity_0210,⟨raw_identity_0211,⟨raw_identity_0031,⟨raw_identity_0032,⟨raw_identity_0033,⟨raw_identity_0034,⟨raw_identity_0053,⟨raw_identity_0054,⟨raw_identity_0055,⟨raw_identity_0080,⟨raw_identity_0081,⟨raw_identity_0082,⟨raw_identity_0083,⟨raw_identity_0115,⟨raw_identity_0116,⟨raw_identity_0117,⟨raw_identity_0118,⟨raw_identity_0119,⟨raw_identity_0158,⟨raw_identity_0159,⟨raw_identity_0160,⟨raw_identity_0161,⟨raw_identity_0162,⟨raw_identity_0163,⟨raw_identity_0164,⟨raw_identity_0212,⟨raw_identity_0213,⟨raw_identity_0214,⟨raw_identity_0215,⟨raw_identity_0216,⟨raw_identity_0217,⟨raw_identity_0218,raw_identity_0219⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem source_entry6 : EntryAgrees entry6 := by
  simp only [EntryAgrees,entry6,expectedTags,expectedPivots,expectedFrees,expectedGroups,standardTagList,invariantPivots,signPivots,standardPivots,parityPivots,Bool.false_eq_true,if_false,if_true,Nat.reduceSub,invariantTagList_1,invariantTagList_2,invariantTagList_3,invariantTagList_4,invariantTagList_5,invariantTagList_6,invariantTagList_7,invariantTagList_8,invariantTagList_9,parityTagList_3,parityTagList_4,parityTagList_5,parityTagList_6,parityTagList_7,parityTagList_8,parityTagList_9]
  refine ⟨by decide,by decide,by decide,?_⟩
  change [[sparsePolynomial p0000,sparsePolynomial p0220,sparsePolynomial p0221,sparsePolynomial p0222,sparsePolynomial p0223,sparsePolynomial p0224,sparsePolynomial p0225,sparsePolynomial p0226,sparsePolynomial p0227,sparsePolynomial p0004,sparsePolynomial p0228,sparsePolynomial p0229,sparsePolynomial p0230,sparsePolynomial p0231,sparsePolynomial p0232,sparsePolynomial p0233,sparsePolynomial p0234,sparsePolynomial p0235,sparsePolynomial p0236,sparsePolynomial p0237,sparsePolynomial p0238,sparsePolynomial p0239],[sparsePolynomial p0024,sparsePolynomial p0240,sparsePolynomial p0241,sparsePolynomial p0242,sparsePolynomial p0243,sparsePolynomial p0244,sparsePolynomial p0245,sparsePolynomial p0246,sparsePolynomial p0247,sparsePolynomial p0028,sparsePolynomial p0248,sparsePolynomial p0249,sparsePolynomial p0250]]=[[ratParity (0,0,0),ratParity (0,1,0),ratParity (1,0,0),ratParity (0,0,1),ratParity (0,2,0),ratParity (1,1,0),ratParity (2,0,0),ratParity (0,1,1),ratParity (0,3,0),ratParity (1,0,1),ratParity (1,2,0),ratParity (2,1,0),ratParity (3,0,0),ratParity (0,0,2),ratParity (0,2,1),ratParity (0,4,0),ratParity (1,1,1),ratParity (1,3,0),ratParity (2,0,1),ratParity (2,2,0),ratParity (3,1,0),ratParity (4,0,0)],[ratOdd*ratParity (0,0,0),ratOdd*ratParity (0,1,0),ratOdd*ratParity (1,0,0),ratOdd*ratParity (0,0,1),ratOdd*ratParity (0,2,0),ratOdd*ratParity (1,1,0),ratOdd*ratParity (2,0,0),ratOdd*ratParity (0,1,1),ratOdd*ratParity (0,3,0),ratOdd*ratParity (1,0,1),ratOdd*ratParity (1,2,0),ratOdd*ratParity (2,1,0),ratOdd*ratParity (3,0,0)]]
  simp only [List.cons.injEq,and_true]
  exact ⟨⟨raw_identity_0220,⟨raw_identity_0221,⟨raw_identity_0222,⟨raw_identity_0223,⟨raw_identity_0224,⟨raw_identity_0225,⟨raw_identity_0226,⟨raw_identity_0227,⟨raw_identity_0228,⟨raw_identity_0229,⟨raw_identity_0230,⟨raw_identity_0231,⟨raw_identity_0232,⟨raw_identity_0233,⟨raw_identity_0234,⟨raw_identity_0235,⟨raw_identity_0236,⟨raw_identity_0237,⟨raw_identity_0238,⟨raw_identity_0239,⟨raw_identity_0240,raw_identity_0241⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,⟨raw_identity_0242,⟨raw_identity_0243,⟨raw_identity_0244,⟨raw_identity_0245,⟨raw_identity_0246,⟨raw_identity_0247,⟨raw_identity_0248,⟨raw_identity_0249,⟨raw_identity_0250,⟨raw_identity_0251,⟨raw_identity_0252,⟨raw_identity_0253,raw_identity_0254⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem source_entry7 : EntryAgrees entry7 := by
  simp only [EntryAgrees,entry7,expectedTags,expectedPivots,expectedFrees,expectedGroups,standardTagList,invariantPivots,signPivots,standardPivots,parityPivots,Bool.false_eq_true,if_false,if_true,Nat.reduceSub,invariantTagList_1,invariantTagList_2,invariantTagList_3,invariantTagList_4,invariantTagList_5,invariantTagList_6,invariantTagList_7,invariantTagList_8,invariantTagList_9,parityTagList_3,parityTagList_4,parityTagList_5,parityTagList_6,parityTagList_7,parityTagList_8,parityTagList_9]
  refine ⟨by decide,by decide,by decide,?_⟩
  change [[sparsePolynomial p0000,sparsePolynomial p0220,sparsePolynomial p0221,sparsePolynomial p0222,sparsePolynomial p0223,sparsePolynomial p0224,sparsePolynomial p0225,sparsePolynomial p0226,sparsePolynomial p0227,sparsePolynomial p0004,sparsePolynomial p0228,sparsePolynomial p0229,sparsePolynomial p0230,sparsePolynomial p0231,sparsePolynomial p0232,sparsePolynomial p0233,sparsePolynomial p0234,sparsePolynomial p0235,sparsePolynomial p0236,sparsePolynomial p0237,sparsePolynomial p0238,sparsePolynomial p0239,sparsePolynomial p0251,sparsePolynomial p0252,sparsePolynomial p0253,sparsePolynomial p0254,sparsePolynomial p0255,sparsePolynomial p0256,sparsePolynomial p0257,sparsePolynomial p0258,sparsePolynomial p0259,sparsePolynomial p0260,sparsePolynomial p0261,sparsePolynomial p0262],[sparsePolynomial p0024,sparsePolynomial p0240,sparsePolynomial p0241,sparsePolynomial p0242,sparsePolynomial p0243,sparsePolynomial p0244,sparsePolynomial p0245,sparsePolynomial p0246,sparsePolynomial p0247,sparsePolynomial p0028,sparsePolynomial p0248,sparsePolynomial p0249,sparsePolynomial p0250,sparsePolynomial p0263,sparsePolynomial p0264,sparsePolynomial p0265,sparsePolynomial p0266,sparsePolynomial p0267,sparsePolynomial p0268,sparsePolynomial p0269,sparsePolynomial p0270,sparsePolynomial p0271]]=[[ratParity (0,0,0),ratParity (0,1,0),ratParity (1,0,0),ratParity (0,0,1),ratParity (0,2,0),ratParity (1,1,0),ratParity (2,0,0),ratParity (0,1,1),ratParity (0,3,0),ratParity (1,0,1),ratParity (1,2,0),ratParity (2,1,0),ratParity (3,0,0),ratParity (0,0,2),ratParity (0,2,1),ratParity (0,4,0),ratParity (1,1,1),ratParity (1,3,0),ratParity (2,0,1),ratParity (2,2,0),ratParity (3,1,0),ratParity (4,0,0),ratParity (0,1,2),ratParity (0,3,1),ratParity (0,5,0),ratParity (1,0,2),ratParity (1,2,1),ratParity (1,4,0),ratParity (2,1,1),ratParity (2,3,0),ratParity (3,0,1),ratParity (3,2,0),ratParity (4,1,0),ratParity (5,0,0)],[ratOdd*ratParity (0,0,0),ratOdd*ratParity (0,1,0),ratOdd*ratParity (1,0,0),ratOdd*ratParity (0,0,1),ratOdd*ratParity (0,2,0),ratOdd*ratParity (1,1,0),ratOdd*ratParity (2,0,0),ratOdd*ratParity (0,1,1),ratOdd*ratParity (0,3,0),ratOdd*ratParity (1,0,1),ratOdd*ratParity (1,2,0),ratOdd*ratParity (2,1,0),ratOdd*ratParity (3,0,0),ratOdd*ratParity (0,0,2),ratOdd*ratParity (0,2,1),ratOdd*ratParity (0,4,0),ratOdd*ratParity (1,1,1),ratOdd*ratParity (1,3,0),ratOdd*ratParity (2,0,1),ratOdd*ratParity (2,2,0),ratOdd*ratParity (3,1,0),ratOdd*ratParity (4,0,0)]]
  simp only [List.cons.injEq,and_true]
  exact ⟨⟨raw_identity_0220,⟨raw_identity_0221,⟨raw_identity_0222,⟨raw_identity_0223,⟨raw_identity_0224,⟨raw_identity_0225,⟨raw_identity_0226,⟨raw_identity_0227,⟨raw_identity_0228,⟨raw_identity_0229,⟨raw_identity_0230,⟨raw_identity_0231,⟨raw_identity_0232,⟨raw_identity_0233,⟨raw_identity_0234,⟨raw_identity_0235,⟨raw_identity_0236,⟨raw_identity_0237,⟨raw_identity_0238,⟨raw_identity_0239,⟨raw_identity_0240,⟨raw_identity_0241,⟨raw_identity_0255,⟨raw_identity_0256,⟨raw_identity_0257,⟨raw_identity_0258,⟨raw_identity_0259,⟨raw_identity_0260,⟨raw_identity_0261,⟨raw_identity_0262,⟨raw_identity_0263,⟨raw_identity_0264,⟨raw_identity_0265,raw_identity_0266⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,⟨raw_identity_0242,⟨raw_identity_0243,⟨raw_identity_0244,⟨raw_identity_0245,⟨raw_identity_0246,⟨raw_identity_0247,⟨raw_identity_0248,⟨raw_identity_0249,⟨raw_identity_0250,⟨raw_identity_0251,⟨raw_identity_0252,⟨raw_identity_0253,⟨raw_identity_0254,⟨raw_identity_0267,⟨raw_identity_0268,⟨raw_identity_0269,⟨raw_identity_0270,⟨raw_identity_0271,⟨raw_identity_0272,⟨raw_identity_0273,⟨raw_identity_0274,raw_identity_0275⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem source_entry8 : EntryAgrees entry8 := by
  simp only [EntryAgrees,entry8,expectedTags,expectedPivots,expectedFrees,expectedGroups,standardTagList,invariantPivots,signPivots,standardPivots,parityPivots,Bool.false_eq_true,if_false,if_true,Nat.reduceSub,invariantTagList_1,invariantTagList_2,invariantTagList_3,invariantTagList_4,invariantTagList_5,invariantTagList_6,invariantTagList_7,invariantTagList_8,invariantTagList_9,parityTagList_3,parityTagList_4,parityTagList_5,parityTagList_6,parityTagList_7,parityTagList_8,parityTagList_9]
  refine ⟨by decide,by decide,by decide,?_⟩
  change [[sparsePolynomial p0000,sparsePolynomial p0220,sparsePolynomial p0221,sparsePolynomial p0222,sparsePolynomial p0223,sparsePolynomial p0224,sparsePolynomial p0225,sparsePolynomial p0226,sparsePolynomial p0227,sparsePolynomial p0004,sparsePolynomial p0228,sparsePolynomial p0229,sparsePolynomial p0230,sparsePolynomial p0231,sparsePolynomial p0232,sparsePolynomial p0233,sparsePolynomial p0234,sparsePolynomial p0235,sparsePolynomial p0236,sparsePolynomial p0237,sparsePolynomial p0238,sparsePolynomial p0239,sparsePolynomial p0251,sparsePolynomial p0252,sparsePolynomial p0253,sparsePolynomial p0254,sparsePolynomial p0255,sparsePolynomial p0256,sparsePolynomial p0257,sparsePolynomial p0258,sparsePolynomial p0259,sparsePolynomial p0260,sparsePolynomial p0261,sparsePolynomial p0262,sparsePolynomial p0272,sparsePolynomial p0273,sparsePolynomial p0274,sparsePolynomial p0275,sparsePolynomial p0276,sparsePolynomial p0277,sparsePolynomial p0278,sparsePolynomial p0056,sparsePolynomial p0279,sparsePolynomial p0280,sparsePolynomial p0281,sparsePolynomial p0282,sparsePolynomial p0283,sparsePolynomial p0284,sparsePolynomial p0285,sparsePolynomial p0286],[sparsePolynomial p0024,sparsePolynomial p0240,sparsePolynomial p0241,sparsePolynomial p0242,sparsePolynomial p0243,sparsePolynomial p0244,sparsePolynomial p0245,sparsePolynomial p0246,sparsePolynomial p0247,sparsePolynomial p0028,sparsePolynomial p0248,sparsePolynomial p0249,sparsePolynomial p0250,sparsePolynomial p0263,sparsePolynomial p0264,sparsePolynomial p0265,sparsePolynomial p0266,sparsePolynomial p0267,sparsePolynomial p0268,sparsePolynomial p0269,sparsePolynomial p0270,sparsePolynomial p0271,sparsePolynomial p0287,sparsePolynomial p0288,sparsePolynomial p0289,sparsePolynomial p0290,sparsePolynomial p0291,sparsePolynomial p0292,sparsePolynomial p0293,sparsePolynomial p0294,sparsePolynomial p0295,sparsePolynomial p0296,sparsePolynomial p0297,sparsePolynomial p0298]]=[[ratParity (0,0,0),ratParity (0,1,0),ratParity (1,0,0),ratParity (0,0,1),ratParity (0,2,0),ratParity (1,1,0),ratParity (2,0,0),ratParity (0,1,1),ratParity (0,3,0),ratParity (1,0,1),ratParity (1,2,0),ratParity (2,1,0),ratParity (3,0,0),ratParity (0,0,2),ratParity (0,2,1),ratParity (0,4,0),ratParity (1,1,1),ratParity (1,3,0),ratParity (2,0,1),ratParity (2,2,0),ratParity (3,1,0),ratParity (4,0,0),ratParity (0,1,2),ratParity (0,3,1),ratParity (0,5,0),ratParity (1,0,2),ratParity (1,2,1),ratParity (1,4,0),ratParity (2,1,1),ratParity (2,3,0),ratParity (3,0,1),ratParity (3,2,0),ratParity (4,1,0),ratParity (5,0,0),ratParity (0,0,3),ratParity (0,2,2),ratParity (0,4,1),ratParity (0,6,0),ratParity (1,1,2),ratParity (1,3,1),ratParity (1,5,0),ratParity (2,0,2),ratParity (2,2,1),ratParity (2,4,0),ratParity (3,1,1),ratParity (3,3,0),ratParity (4,0,1),ratParity (4,2,0),ratParity (5,1,0),ratParity (6,0,0)],[ratOdd*ratParity (0,0,0),ratOdd*ratParity (0,1,0),ratOdd*ratParity (1,0,0),ratOdd*ratParity (0,0,1),ratOdd*ratParity (0,2,0),ratOdd*ratParity (1,1,0),ratOdd*ratParity (2,0,0),ratOdd*ratParity (0,1,1),ratOdd*ratParity (0,3,0),ratOdd*ratParity (1,0,1),ratOdd*ratParity (1,2,0),ratOdd*ratParity (2,1,0),ratOdd*ratParity (3,0,0),ratOdd*ratParity (0,0,2),ratOdd*ratParity (0,2,1),ratOdd*ratParity (0,4,0),ratOdd*ratParity (1,1,1),ratOdd*ratParity (1,3,0),ratOdd*ratParity (2,0,1),ratOdd*ratParity (2,2,0),ratOdd*ratParity (3,1,0),ratOdd*ratParity (4,0,0),ratOdd*ratParity (0,1,2),ratOdd*ratParity (0,3,1),ratOdd*ratParity (0,5,0),ratOdd*ratParity (1,0,2),ratOdd*ratParity (1,2,1),ratOdd*ratParity (1,4,0),ratOdd*ratParity (2,1,1),ratOdd*ratParity (2,3,0),ratOdd*ratParity (3,0,1),ratOdd*ratParity (3,2,0),ratOdd*ratParity (4,1,0),ratOdd*ratParity (5,0,0)]]
  simp only [List.cons.injEq,and_true]
  exact ⟨⟨raw_identity_0220,⟨raw_identity_0221,⟨raw_identity_0222,⟨raw_identity_0223,⟨raw_identity_0224,⟨raw_identity_0225,⟨raw_identity_0226,⟨raw_identity_0227,⟨raw_identity_0228,⟨raw_identity_0229,⟨raw_identity_0230,⟨raw_identity_0231,⟨raw_identity_0232,⟨raw_identity_0233,⟨raw_identity_0234,⟨raw_identity_0235,⟨raw_identity_0236,⟨raw_identity_0237,⟨raw_identity_0238,⟨raw_identity_0239,⟨raw_identity_0240,⟨raw_identity_0241,⟨raw_identity_0255,⟨raw_identity_0256,⟨raw_identity_0257,⟨raw_identity_0258,⟨raw_identity_0259,⟨raw_identity_0260,⟨raw_identity_0261,⟨raw_identity_0262,⟨raw_identity_0263,⟨raw_identity_0264,⟨raw_identity_0265,⟨raw_identity_0266,⟨raw_identity_0276,⟨raw_identity_0277,⟨raw_identity_0278,⟨raw_identity_0279,⟨raw_identity_0280,⟨raw_identity_0281,⟨raw_identity_0282,⟨raw_identity_0283,⟨raw_identity_0284,⟨raw_identity_0285,⟨raw_identity_0286,⟨raw_identity_0287,⟨raw_identity_0288,⟨raw_identity_0289,⟨raw_identity_0290,raw_identity_0291⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,⟨raw_identity_0242,⟨raw_identity_0243,⟨raw_identity_0244,⟨raw_identity_0245,⟨raw_identity_0246,⟨raw_identity_0247,⟨raw_identity_0248,⟨raw_identity_0249,⟨raw_identity_0250,⟨raw_identity_0251,⟨raw_identity_0252,⟨raw_identity_0253,⟨raw_identity_0254,⟨raw_identity_0267,⟨raw_identity_0268,⟨raw_identity_0269,⟨raw_identity_0270,⟨raw_identity_0271,⟨raw_identity_0272,⟨raw_identity_0273,⟨raw_identity_0274,⟨raw_identity_0275,⟨raw_identity_0292,⟨raw_identity_0293,⟨raw_identity_0294,⟨raw_identity_0295,⟨raw_identity_0296,⟨raw_identity_0297,⟨raw_identity_0298,⟨raw_identity_0299,⟨raw_identity_0300,⟨raw_identity_0301,⟨raw_identity_0302,raw_identity_0303⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem source_entry9 : EntryAgrees entry9 := by
  simp only [EntryAgrees,entry9,expectedTags,expectedPivots,expectedFrees,expectedGroups,standardTagList,invariantPivots,signPivots,standardPivots,parityPivots,Bool.false_eq_true,if_false,if_true,Nat.reduceSub,invariantTagList_1,invariantTagList_2,invariantTagList_3,invariantTagList_4,invariantTagList_5,invariantTagList_6,invariantTagList_7,invariantTagList_8,invariantTagList_9,parityTagList_3,parityTagList_4,parityTagList_5,parityTagList_6,parityTagList_7,parityTagList_8,parityTagList_9]
  refine ⟨by decide,by decide,by decide,?_⟩
  change [[sparsePolynomial p0000,sparsePolynomial p0220,sparsePolynomial p0221,sparsePolynomial p0222,sparsePolynomial p0223,sparsePolynomial p0224,sparsePolynomial p0225,sparsePolynomial p0226,sparsePolynomial p0227,sparsePolynomial p0004,sparsePolynomial p0228,sparsePolynomial p0229,sparsePolynomial p0230,sparsePolynomial p0231,sparsePolynomial p0232,sparsePolynomial p0233,sparsePolynomial p0234,sparsePolynomial p0235,sparsePolynomial p0236,sparsePolynomial p0237,sparsePolynomial p0238,sparsePolynomial p0239,sparsePolynomial p0251,sparsePolynomial p0252,sparsePolynomial p0253,sparsePolynomial p0254,sparsePolynomial p0255,sparsePolynomial p0256,sparsePolynomial p0257,sparsePolynomial p0258,sparsePolynomial p0259,sparsePolynomial p0260,sparsePolynomial p0261,sparsePolynomial p0262,sparsePolynomial p0272,sparsePolynomial p0273,sparsePolynomial p0274,sparsePolynomial p0275,sparsePolynomial p0276,sparsePolynomial p0277,sparsePolynomial p0278,sparsePolynomial p0056,sparsePolynomial p0279,sparsePolynomial p0280,sparsePolynomial p0281,sparsePolynomial p0282,sparsePolynomial p0283,sparsePolynomial p0284,sparsePolynomial p0285,sparsePolynomial p0286,sparsePolynomial p0299,sparsePolynomial p0300,sparsePolynomial p0301,sparsePolynomial p0302,sparsePolynomial p0303,sparsePolynomial p0304,sparsePolynomial p0305,sparsePolynomial p0306,sparsePolynomial p0307,sparsePolynomial p0308,sparsePolynomial p0309,sparsePolynomial p0310,sparsePolynomial p0311,sparsePolynomial p0312,sparsePolynomial p0313,sparsePolynomial p0314,sparsePolynomial p0315,sparsePolynomial p0316,sparsePolynomial p0317,sparsePolynomial p0318],[sparsePolynomial p0024,sparsePolynomial p0240,sparsePolynomial p0241,sparsePolynomial p0242,sparsePolynomial p0243,sparsePolynomial p0244,sparsePolynomial p0245,sparsePolynomial p0246,sparsePolynomial p0247,sparsePolynomial p0028,sparsePolynomial p0248,sparsePolynomial p0249,sparsePolynomial p0250,sparsePolynomial p0263,sparsePolynomial p0264,sparsePolynomial p0265,sparsePolynomial p0266,sparsePolynomial p0267,sparsePolynomial p0268,sparsePolynomial p0269,sparsePolynomial p0270,sparsePolynomial p0271,sparsePolynomial p0287,sparsePolynomial p0288,sparsePolynomial p0289,sparsePolynomial p0290,sparsePolynomial p0291,sparsePolynomial p0292,sparsePolynomial p0293,sparsePolynomial p0294,sparsePolynomial p0295,sparsePolynomial p0296,sparsePolynomial p0297,sparsePolynomial p0298,sparsePolynomial p0319,sparsePolynomial p0320,sparsePolynomial p0321,sparsePolynomial p0322,sparsePolynomial p0323,sparsePolynomial p0324,sparsePolynomial p0325,sparsePolynomial p0108,sparsePolynomial p0326,sparsePolynomial p0327,sparsePolynomial p0328,sparsePolynomial p0329,sparsePolynomial p0330,sparsePolynomial p0331,sparsePolynomial p0332,sparsePolynomial p0333]]=[[ratParity (0,0,0),ratParity (0,1,0),ratParity (1,0,0),ratParity (0,0,1),ratParity (0,2,0),ratParity (1,1,0),ratParity (2,0,0),ratParity (0,1,1),ratParity (0,3,0),ratParity (1,0,1),ratParity (1,2,0),ratParity (2,1,0),ratParity (3,0,0),ratParity (0,0,2),ratParity (0,2,1),ratParity (0,4,0),ratParity (1,1,1),ratParity (1,3,0),ratParity (2,0,1),ratParity (2,2,0),ratParity (3,1,0),ratParity (4,0,0),ratParity (0,1,2),ratParity (0,3,1),ratParity (0,5,0),ratParity (1,0,2),ratParity (1,2,1),ratParity (1,4,0),ratParity (2,1,1),ratParity (2,3,0),ratParity (3,0,1),ratParity (3,2,0),ratParity (4,1,0),ratParity (5,0,0),ratParity (0,0,3),ratParity (0,2,2),ratParity (0,4,1),ratParity (0,6,0),ratParity (1,1,2),ratParity (1,3,1),ratParity (1,5,0),ratParity (2,0,2),ratParity (2,2,1),ratParity (2,4,0),ratParity (3,1,1),ratParity (3,3,0),ratParity (4,0,1),ratParity (4,2,0),ratParity (5,1,0),ratParity (6,0,0),ratParity (0,1,3),ratParity (0,3,2),ratParity (0,5,1),ratParity (0,7,0),ratParity (1,0,3),ratParity (1,2,2),ratParity (1,4,1),ratParity (1,6,0),ratParity (2,1,2),ratParity (2,3,1),ratParity (2,5,0),ratParity (3,0,2),ratParity (3,2,1),ratParity (3,4,0),ratParity (4,1,1),ratParity (4,3,0),ratParity (5,0,1),ratParity (5,2,0),ratParity (6,1,0),ratParity (7,0,0)],[ratOdd*ratParity (0,0,0),ratOdd*ratParity (0,1,0),ratOdd*ratParity (1,0,0),ratOdd*ratParity (0,0,1),ratOdd*ratParity (0,2,0),ratOdd*ratParity (1,1,0),ratOdd*ratParity (2,0,0),ratOdd*ratParity (0,1,1),ratOdd*ratParity (0,3,0),ratOdd*ratParity (1,0,1),ratOdd*ratParity (1,2,0),ratOdd*ratParity (2,1,0),ratOdd*ratParity (3,0,0),ratOdd*ratParity (0,0,2),ratOdd*ratParity (0,2,1),ratOdd*ratParity (0,4,0),ratOdd*ratParity (1,1,1),ratOdd*ratParity (1,3,0),ratOdd*ratParity (2,0,1),ratOdd*ratParity (2,2,0),ratOdd*ratParity (3,1,0),ratOdd*ratParity (4,0,0),ratOdd*ratParity (0,1,2),ratOdd*ratParity (0,3,1),ratOdd*ratParity (0,5,0),ratOdd*ratParity (1,0,2),ratOdd*ratParity (1,2,1),ratOdd*ratParity (1,4,0),ratOdd*ratParity (2,1,1),ratOdd*ratParity (2,3,0),ratOdd*ratParity (3,0,1),ratOdd*ratParity (3,2,0),ratOdd*ratParity (4,1,0),ratOdd*ratParity (5,0,0),ratOdd*ratParity (0,0,3),ratOdd*ratParity (0,2,2),ratOdd*ratParity (0,4,1),ratOdd*ratParity (0,6,0),ratOdd*ratParity (1,1,2),ratOdd*ratParity (1,3,1),ratOdd*ratParity (1,5,0),ratOdd*ratParity (2,0,2),ratOdd*ratParity (2,2,1),ratOdd*ratParity (2,4,0),ratOdd*ratParity (3,1,1),ratOdd*ratParity (3,3,0),ratOdd*ratParity (4,0,1),ratOdd*ratParity (4,2,0),ratOdd*ratParity (5,1,0),ratOdd*ratParity (6,0,0)]]
  simp only [List.cons.injEq,and_true]
  exact ⟨⟨raw_identity_0220,⟨raw_identity_0221,⟨raw_identity_0222,⟨raw_identity_0223,⟨raw_identity_0224,⟨raw_identity_0225,⟨raw_identity_0226,⟨raw_identity_0227,⟨raw_identity_0228,⟨raw_identity_0229,⟨raw_identity_0230,⟨raw_identity_0231,⟨raw_identity_0232,⟨raw_identity_0233,⟨raw_identity_0234,⟨raw_identity_0235,⟨raw_identity_0236,⟨raw_identity_0237,⟨raw_identity_0238,⟨raw_identity_0239,⟨raw_identity_0240,⟨raw_identity_0241,⟨raw_identity_0255,⟨raw_identity_0256,⟨raw_identity_0257,⟨raw_identity_0258,⟨raw_identity_0259,⟨raw_identity_0260,⟨raw_identity_0261,⟨raw_identity_0262,⟨raw_identity_0263,⟨raw_identity_0264,⟨raw_identity_0265,⟨raw_identity_0266,⟨raw_identity_0276,⟨raw_identity_0277,⟨raw_identity_0278,⟨raw_identity_0279,⟨raw_identity_0280,⟨raw_identity_0281,⟨raw_identity_0282,⟨raw_identity_0283,⟨raw_identity_0284,⟨raw_identity_0285,⟨raw_identity_0286,⟨raw_identity_0287,⟨raw_identity_0288,⟨raw_identity_0289,⟨raw_identity_0290,⟨raw_identity_0291,⟨raw_identity_0304,⟨raw_identity_0305,⟨raw_identity_0306,⟨raw_identity_0307,⟨raw_identity_0308,⟨raw_identity_0309,⟨raw_identity_0310,⟨raw_identity_0311,⟨raw_identity_0312,⟨raw_identity_0313,⟨raw_identity_0314,⟨raw_identity_0315,⟨raw_identity_0316,⟨raw_identity_0317,⟨raw_identity_0318,⟨raw_identity_0319,⟨raw_identity_0320,⟨raw_identity_0321,⟨raw_identity_0322,raw_identity_0323⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,⟨raw_identity_0242,⟨raw_identity_0243,⟨raw_identity_0244,⟨raw_identity_0245,⟨raw_identity_0246,⟨raw_identity_0247,⟨raw_identity_0248,⟨raw_identity_0249,⟨raw_identity_0250,⟨raw_identity_0251,⟨raw_identity_0252,⟨raw_identity_0253,⟨raw_identity_0254,⟨raw_identity_0267,⟨raw_identity_0268,⟨raw_identity_0269,⟨raw_identity_0270,⟨raw_identity_0271,⟨raw_identity_0272,⟨raw_identity_0273,⟨raw_identity_0274,⟨raw_identity_0275,⟨raw_identity_0292,⟨raw_identity_0293,⟨raw_identity_0294,⟨raw_identity_0295,⟨raw_identity_0296,⟨raw_identity_0297,⟨raw_identity_0298,⟨raw_identity_0299,⟨raw_identity_0300,⟨raw_identity_0301,⟨raw_identity_0302,⟨raw_identity_0303,⟨raw_identity_0324,⟨raw_identity_0325,⟨raw_identity_0326,⟨raw_identity_0327,⟨raw_identity_0328,⟨raw_identity_0329,⟨raw_identity_0330,⟨raw_identity_0331,⟨raw_identity_0332,⟨raw_identity_0333,⟨raw_identity_0334,⟨raw_identity_0335,⟨raw_identity_0336,⟨raw_identity_0337,⟨raw_identity_0338,raw_identity_0339⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem source_entry10 : EntryAgrees entry10 := by
  simp only [EntryAgrees,entry10,expectedTags,expectedPivots,expectedFrees,expectedGroups,standardTagList,invariantPivots,signPivots,standardPivots,parityPivots,Bool.false_eq_true,if_false,if_true,Nat.reduceSub,invariantTagList_1,invariantTagList_2,invariantTagList_3,invariantTagList_4,invariantTagList_5,invariantTagList_6,invariantTagList_7,invariantTagList_8,invariantTagList_9,parityTagList_3,parityTagList_4,parityTagList_5,parityTagList_6,parityTagList_7,parityTagList_8,parityTagList_9]
  refine ⟨by decide,by decide,by decide,?_⟩
  change [[sparsePolynomial p0000,sparsePolynomial p0220,sparsePolynomial p0221,sparsePolynomial p0222,sparsePolynomial p0223,sparsePolynomial p0224,sparsePolynomial p0225,sparsePolynomial p0226,sparsePolynomial p0227,sparsePolynomial p0004,sparsePolynomial p0228,sparsePolynomial p0229,sparsePolynomial p0230,sparsePolynomial p0231,sparsePolynomial p0232,sparsePolynomial p0233,sparsePolynomial p0234,sparsePolynomial p0235,sparsePolynomial p0236,sparsePolynomial p0237,sparsePolynomial p0238,sparsePolynomial p0239,sparsePolynomial p0251,sparsePolynomial p0252,sparsePolynomial p0253,sparsePolynomial p0254,sparsePolynomial p0255,sparsePolynomial p0256,sparsePolynomial p0257,sparsePolynomial p0258,sparsePolynomial p0259,sparsePolynomial p0260,sparsePolynomial p0261,sparsePolynomial p0262,sparsePolynomial p0272,sparsePolynomial p0273,sparsePolynomial p0274,sparsePolynomial p0275,sparsePolynomial p0276,sparsePolynomial p0277,sparsePolynomial p0278,sparsePolynomial p0056,sparsePolynomial p0279,sparsePolynomial p0280,sparsePolynomial p0281,sparsePolynomial p0282,sparsePolynomial p0283,sparsePolynomial p0284,sparsePolynomial p0285,sparsePolynomial p0286,sparsePolynomial p0299,sparsePolynomial p0300,sparsePolynomial p0301,sparsePolynomial p0302,sparsePolynomial p0303,sparsePolynomial p0304,sparsePolynomial p0305,sparsePolynomial p0306,sparsePolynomial p0307,sparsePolynomial p0308,sparsePolynomial p0309,sparsePolynomial p0310,sparsePolynomial p0311,sparsePolynomial p0312,sparsePolynomial p0313,sparsePolynomial p0314,sparsePolynomial p0315,sparsePolynomial p0316,sparsePolynomial p0317,sparsePolynomial p0318,sparsePolynomial p0334,sparsePolynomial p0335,sparsePolynomial p0336,sparsePolynomial p0337,sparsePolynomial p0338,sparsePolynomial p0339,sparsePolynomial p0340,sparsePolynomial p0341,sparsePolynomial p0342,sparsePolynomial p0343,sparsePolynomial p0344,sparsePolynomial p0345,sparsePolynomial p0346,sparsePolynomial p0347,sparsePolynomial p0348,sparsePolynomial p0349,sparsePolynomial p0350,sparsePolynomial p0351,sparsePolynomial p0352,sparsePolynomial p0353,sparsePolynomial p0354,sparsePolynomial p0355,sparsePolynomial p0356,sparsePolynomial p0357,sparsePolynomial p0358],[sparsePolynomial p0024,sparsePolynomial p0240,sparsePolynomial p0241,sparsePolynomial p0242,sparsePolynomial p0243,sparsePolynomial p0244,sparsePolynomial p0245,sparsePolynomial p0246,sparsePolynomial p0247,sparsePolynomial p0028,sparsePolynomial p0248,sparsePolynomial p0249,sparsePolynomial p0250,sparsePolynomial p0263,sparsePolynomial p0264,sparsePolynomial p0265,sparsePolynomial p0266,sparsePolynomial p0267,sparsePolynomial p0268,sparsePolynomial p0269,sparsePolynomial p0270,sparsePolynomial p0271,sparsePolynomial p0287,sparsePolynomial p0288,sparsePolynomial p0289,sparsePolynomial p0290,sparsePolynomial p0291,sparsePolynomial p0292,sparsePolynomial p0293,sparsePolynomial p0294,sparsePolynomial p0295,sparsePolynomial p0296,sparsePolynomial p0297,sparsePolynomial p0298,sparsePolynomial p0319,sparsePolynomial p0320,sparsePolynomial p0321,sparsePolynomial p0322,sparsePolynomial p0323,sparsePolynomial p0324,sparsePolynomial p0325,sparsePolynomial p0108,sparsePolynomial p0326,sparsePolynomial p0327,sparsePolynomial p0328,sparsePolynomial p0329,sparsePolynomial p0330,sparsePolynomial p0331,sparsePolynomial p0332,sparsePolynomial p0333,sparsePolynomial p0359,sparsePolynomial p0360,sparsePolynomial p0361,sparsePolynomial p0362,sparsePolynomial p0363,sparsePolynomial p0364,sparsePolynomial p0365,sparsePolynomial p0366,sparsePolynomial p0367,sparsePolynomial p0368,sparsePolynomial p0369,sparsePolynomial p0370,sparsePolynomial p0371,sparsePolynomial p0372,sparsePolynomial p0373,sparsePolynomial p0374,sparsePolynomial p0375,sparsePolynomial p0376,sparsePolynomial p0377,sparsePolynomial p0378]]=[[ratParity (0,0,0),ratParity (0,1,0),ratParity (1,0,0),ratParity (0,0,1),ratParity (0,2,0),ratParity (1,1,0),ratParity (2,0,0),ratParity (0,1,1),ratParity (0,3,0),ratParity (1,0,1),ratParity (1,2,0),ratParity (2,1,0),ratParity (3,0,0),ratParity (0,0,2),ratParity (0,2,1),ratParity (0,4,0),ratParity (1,1,1),ratParity (1,3,0),ratParity (2,0,1),ratParity (2,2,0),ratParity (3,1,0),ratParity (4,0,0),ratParity (0,1,2),ratParity (0,3,1),ratParity (0,5,0),ratParity (1,0,2),ratParity (1,2,1),ratParity (1,4,0),ratParity (2,1,1),ratParity (2,3,0),ratParity (3,0,1),ratParity (3,2,0),ratParity (4,1,0),ratParity (5,0,0),ratParity (0,0,3),ratParity (0,2,2),ratParity (0,4,1),ratParity (0,6,0),ratParity (1,1,2),ratParity (1,3,1),ratParity (1,5,0),ratParity (2,0,2),ratParity (2,2,1),ratParity (2,4,0),ratParity (3,1,1),ratParity (3,3,0),ratParity (4,0,1),ratParity (4,2,0),ratParity (5,1,0),ratParity (6,0,0),ratParity (0,1,3),ratParity (0,3,2),ratParity (0,5,1),ratParity (0,7,0),ratParity (1,0,3),ratParity (1,2,2),ratParity (1,4,1),ratParity (1,6,0),ratParity (2,1,2),ratParity (2,3,1),ratParity (2,5,0),ratParity (3,0,2),ratParity (3,2,1),ratParity (3,4,0),ratParity (4,1,1),ratParity (4,3,0),ratParity (5,0,1),ratParity (5,2,0),ratParity (6,1,0),ratParity (7,0,0),ratParity (0,0,4),ratParity (0,2,3),ratParity (0,4,2),ratParity (0,6,1),ratParity (0,8,0),ratParity (1,1,3),ratParity (1,3,2),ratParity (1,5,1),ratParity (1,7,0),ratParity (2,0,3),ratParity (2,2,2),ratParity (2,4,1),ratParity (2,6,0),ratParity (3,1,2),ratParity (3,3,1),ratParity (3,5,0),ratParity (4,0,2),ratParity (4,2,1),ratParity (4,4,0),ratParity (5,1,1),ratParity (5,3,0),ratParity (6,0,1),ratParity (6,2,0),ratParity (7,1,0),ratParity (8,0,0)],[ratOdd*ratParity (0,0,0),ratOdd*ratParity (0,1,0),ratOdd*ratParity (1,0,0),ratOdd*ratParity (0,0,1),ratOdd*ratParity (0,2,0),ratOdd*ratParity (1,1,0),ratOdd*ratParity (2,0,0),ratOdd*ratParity (0,1,1),ratOdd*ratParity (0,3,0),ratOdd*ratParity (1,0,1),ratOdd*ratParity (1,2,0),ratOdd*ratParity (2,1,0),ratOdd*ratParity (3,0,0),ratOdd*ratParity (0,0,2),ratOdd*ratParity (0,2,1),ratOdd*ratParity (0,4,0),ratOdd*ratParity (1,1,1),ratOdd*ratParity (1,3,0),ratOdd*ratParity (2,0,1),ratOdd*ratParity (2,2,0),ratOdd*ratParity (3,1,0),ratOdd*ratParity (4,0,0),ratOdd*ratParity (0,1,2),ratOdd*ratParity (0,3,1),ratOdd*ratParity (0,5,0),ratOdd*ratParity (1,0,2),ratOdd*ratParity (1,2,1),ratOdd*ratParity (1,4,0),ratOdd*ratParity (2,1,1),ratOdd*ratParity (2,3,0),ratOdd*ratParity (3,0,1),ratOdd*ratParity (3,2,0),ratOdd*ratParity (4,1,0),ratOdd*ratParity (5,0,0),ratOdd*ratParity (0,0,3),ratOdd*ratParity (0,2,2),ratOdd*ratParity (0,4,1),ratOdd*ratParity (0,6,0),ratOdd*ratParity (1,1,2),ratOdd*ratParity (1,3,1),ratOdd*ratParity (1,5,0),ratOdd*ratParity (2,0,2),ratOdd*ratParity (2,2,1),ratOdd*ratParity (2,4,0),ratOdd*ratParity (3,1,1),ratOdd*ratParity (3,3,0),ratOdd*ratParity (4,0,1),ratOdd*ratParity (4,2,0),ratOdd*ratParity (5,1,0),ratOdd*ratParity (6,0,0),ratOdd*ratParity (0,1,3),ratOdd*ratParity (0,3,2),ratOdd*ratParity (0,5,1),ratOdd*ratParity (0,7,0),ratOdd*ratParity (1,0,3),ratOdd*ratParity (1,2,2),ratOdd*ratParity (1,4,1),ratOdd*ratParity (1,6,0),ratOdd*ratParity (2,1,2),ratOdd*ratParity (2,3,1),ratOdd*ratParity (2,5,0),ratOdd*ratParity (3,0,2),ratOdd*ratParity (3,2,1),ratOdd*ratParity (3,4,0),ratOdd*ratParity (4,1,1),ratOdd*ratParity (4,3,0),ratOdd*ratParity (5,0,1),ratOdd*ratParity (5,2,0),ratOdd*ratParity (6,1,0),ratOdd*ratParity (7,0,0)]]
  simp only [List.cons.injEq,and_true]
  exact ⟨⟨raw_identity_0220,⟨raw_identity_0221,⟨raw_identity_0222,⟨raw_identity_0223,⟨raw_identity_0224,⟨raw_identity_0225,⟨raw_identity_0226,⟨raw_identity_0227,⟨raw_identity_0228,⟨raw_identity_0229,⟨raw_identity_0230,⟨raw_identity_0231,⟨raw_identity_0232,⟨raw_identity_0233,⟨raw_identity_0234,⟨raw_identity_0235,⟨raw_identity_0236,⟨raw_identity_0237,⟨raw_identity_0238,⟨raw_identity_0239,⟨raw_identity_0240,⟨raw_identity_0241,⟨raw_identity_0255,⟨raw_identity_0256,⟨raw_identity_0257,⟨raw_identity_0258,⟨raw_identity_0259,⟨raw_identity_0260,⟨raw_identity_0261,⟨raw_identity_0262,⟨raw_identity_0263,⟨raw_identity_0264,⟨raw_identity_0265,⟨raw_identity_0266,⟨raw_identity_0276,⟨raw_identity_0277,⟨raw_identity_0278,⟨raw_identity_0279,⟨raw_identity_0280,⟨raw_identity_0281,⟨raw_identity_0282,⟨raw_identity_0283,⟨raw_identity_0284,⟨raw_identity_0285,⟨raw_identity_0286,⟨raw_identity_0287,⟨raw_identity_0288,⟨raw_identity_0289,⟨raw_identity_0290,⟨raw_identity_0291,⟨raw_identity_0304,⟨raw_identity_0305,⟨raw_identity_0306,⟨raw_identity_0307,⟨raw_identity_0308,⟨raw_identity_0309,⟨raw_identity_0310,⟨raw_identity_0311,⟨raw_identity_0312,⟨raw_identity_0313,⟨raw_identity_0314,⟨raw_identity_0315,⟨raw_identity_0316,⟨raw_identity_0317,⟨raw_identity_0318,⟨raw_identity_0319,⟨raw_identity_0320,⟨raw_identity_0321,⟨raw_identity_0322,⟨raw_identity_0323,⟨raw_identity_0340,⟨raw_identity_0341,⟨raw_identity_0342,⟨raw_identity_0343,⟨raw_identity_0344,⟨raw_identity_0345,⟨raw_identity_0346,⟨raw_identity_0347,⟨raw_identity_0348,⟨raw_identity_0349,⟨raw_identity_0350,⟨raw_identity_0351,⟨raw_identity_0352,⟨raw_identity_0353,⟨raw_identity_0354,⟨raw_identity_0355,⟨raw_identity_0356,⟨raw_identity_0357,⟨raw_identity_0358,⟨raw_identity_0359,⟨raw_identity_0360,⟨raw_identity_0361,⟨raw_identity_0362,⟨raw_identity_0363,raw_identity_0364⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,⟨raw_identity_0242,⟨raw_identity_0243,⟨raw_identity_0244,⟨raw_identity_0245,⟨raw_identity_0246,⟨raw_identity_0247,⟨raw_identity_0248,⟨raw_identity_0249,⟨raw_identity_0250,⟨raw_identity_0251,⟨raw_identity_0252,⟨raw_identity_0253,⟨raw_identity_0254,⟨raw_identity_0267,⟨raw_identity_0268,⟨raw_identity_0269,⟨raw_identity_0270,⟨raw_identity_0271,⟨raw_identity_0272,⟨raw_identity_0273,⟨raw_identity_0274,⟨raw_identity_0275,⟨raw_identity_0292,⟨raw_identity_0293,⟨raw_identity_0294,⟨raw_identity_0295,⟨raw_identity_0296,⟨raw_identity_0297,⟨raw_identity_0298,⟨raw_identity_0299,⟨raw_identity_0300,⟨raw_identity_0301,⟨raw_identity_0302,⟨raw_identity_0303,⟨raw_identity_0324,⟨raw_identity_0325,⟨raw_identity_0326,⟨raw_identity_0327,⟨raw_identity_0328,⟨raw_identity_0329,⟨raw_identity_0330,⟨raw_identity_0331,⟨raw_identity_0332,⟨raw_identity_0333,⟨raw_identity_0334,⟨raw_identity_0335,⟨raw_identity_0336,⟨raw_identity_0337,⟨raw_identity_0338,⟨raw_identity_0339,⟨raw_identity_0365,⟨raw_identity_0366,⟨raw_identity_0367,⟨raw_identity_0368,⟨raw_identity_0369,⟨raw_identity_0370,⟨raw_identity_0371,⟨raw_identity_0372,⟨raw_identity_0373,⟨raw_identity_0374,⟨raw_identity_0375,⟨raw_identity_0376,⟨raw_identity_0377,⟨raw_identity_0378,⟨raw_identity_0379,⟨raw_identity_0380,⟨raw_identity_0381,⟨raw_identity_0382,⟨raw_identity_0383,raw_identity_0384⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem source_entry11 : EntryAgrees entry11 := by
  simp only [EntryAgrees,entry11,expectedTags,expectedPivots,expectedFrees,expectedGroups,standardTagList,invariantPivots,signPivots,standardPivots,parityPivots,Bool.false_eq_true,if_false,if_true,Nat.reduceSub,invariantTagList_1,invariantTagList_2,invariantTagList_3,invariantTagList_4,invariantTagList_5,invariantTagList_6,invariantTagList_7,invariantTagList_8,invariantTagList_9,parityTagList_3,parityTagList_4,parityTagList_5,parityTagList_6,parityTagList_7,parityTagList_8,parityTagList_9]
  refine ⟨by decide,by decide,by decide,?_⟩
  change [[sparsePolynomial p0000,sparsePolynomial p0220,sparsePolynomial p0221,sparsePolynomial p0222,sparsePolynomial p0223,sparsePolynomial p0224,sparsePolynomial p0225,sparsePolynomial p0226,sparsePolynomial p0227,sparsePolynomial p0004,sparsePolynomial p0228,sparsePolynomial p0229,sparsePolynomial p0230,sparsePolynomial p0231,sparsePolynomial p0232,sparsePolynomial p0233,sparsePolynomial p0234,sparsePolynomial p0235,sparsePolynomial p0236,sparsePolynomial p0237,sparsePolynomial p0238,sparsePolynomial p0239,sparsePolynomial p0251,sparsePolynomial p0252,sparsePolynomial p0253,sparsePolynomial p0254,sparsePolynomial p0255,sparsePolynomial p0256,sparsePolynomial p0257,sparsePolynomial p0258,sparsePolynomial p0259,sparsePolynomial p0260,sparsePolynomial p0261,sparsePolynomial p0262,sparsePolynomial p0272,sparsePolynomial p0273,sparsePolynomial p0274,sparsePolynomial p0275,sparsePolynomial p0276,sparsePolynomial p0277,sparsePolynomial p0278,sparsePolynomial p0056,sparsePolynomial p0279,sparsePolynomial p0280,sparsePolynomial p0281,sparsePolynomial p0282,sparsePolynomial p0283,sparsePolynomial p0284,sparsePolynomial p0285,sparsePolynomial p0286,sparsePolynomial p0299,sparsePolynomial p0300,sparsePolynomial p0301,sparsePolynomial p0302,sparsePolynomial p0303,sparsePolynomial p0304,sparsePolynomial p0305,sparsePolynomial p0306,sparsePolynomial p0307,sparsePolynomial p0308,sparsePolynomial p0309,sparsePolynomial p0310,sparsePolynomial p0311,sparsePolynomial p0312,sparsePolynomial p0313,sparsePolynomial p0314,sparsePolynomial p0315,sparsePolynomial p0316,sparsePolynomial p0317,sparsePolynomial p0318,sparsePolynomial p0334,sparsePolynomial p0335,sparsePolynomial p0336,sparsePolynomial p0337,sparsePolynomial p0338,sparsePolynomial p0339,sparsePolynomial p0340,sparsePolynomial p0341,sparsePolynomial p0342,sparsePolynomial p0343,sparsePolynomial p0344,sparsePolynomial p0345,sparsePolynomial p0346,sparsePolynomial p0347,sparsePolynomial p0348,sparsePolynomial p0349,sparsePolynomial p0350,sparsePolynomial p0351,sparsePolynomial p0352,sparsePolynomial p0353,sparsePolynomial p0354,sparsePolynomial p0355,sparsePolynomial p0356,sparsePolynomial p0357,sparsePolynomial p0358,sparsePolynomial p0379,sparsePolynomial p0380,sparsePolynomial p0381,sparsePolynomial p0382,sparsePolynomial p0383,sparsePolynomial p0384,sparsePolynomial p0385,sparsePolynomial p0386,sparsePolynomial p0387,sparsePolynomial p0388,sparsePolynomial p0389,sparsePolynomial p0390,sparsePolynomial p0391,sparsePolynomial p0392,sparsePolynomial p0165,sparsePolynomial p0393,sparsePolynomial p0394,sparsePolynomial p0395,sparsePolynomial p0396,sparsePolynomial p0397,sparsePolynomial p0398,sparsePolynomial p0399,sparsePolynomial p0400,sparsePolynomial p0401,sparsePolynomial p0402,sparsePolynomial p0403,sparsePolynomial p0404,sparsePolynomial p0405,sparsePolynomial p0406,sparsePolynomial p0407],[sparsePolynomial p0024,sparsePolynomial p0240,sparsePolynomial p0241,sparsePolynomial p0242,sparsePolynomial p0243,sparsePolynomial p0244,sparsePolynomial p0245,sparsePolynomial p0246,sparsePolynomial p0247,sparsePolynomial p0028,sparsePolynomial p0248,sparsePolynomial p0249,sparsePolynomial p0250,sparsePolynomial p0263,sparsePolynomial p0264,sparsePolynomial p0265,sparsePolynomial p0266,sparsePolynomial p0267,sparsePolynomial p0268,sparsePolynomial p0269,sparsePolynomial p0270,sparsePolynomial p0271,sparsePolynomial p0287,sparsePolynomial p0288,sparsePolynomial p0289,sparsePolynomial p0290,sparsePolynomial p0291,sparsePolynomial p0292,sparsePolynomial p0293,sparsePolynomial p0294,sparsePolynomial p0295,sparsePolynomial p0296,sparsePolynomial p0297,sparsePolynomial p0298,sparsePolynomial p0319,sparsePolynomial p0320,sparsePolynomial p0321,sparsePolynomial p0322,sparsePolynomial p0323,sparsePolynomial p0324,sparsePolynomial p0325,sparsePolynomial p0108,sparsePolynomial p0326,sparsePolynomial p0327,sparsePolynomial p0328,sparsePolynomial p0329,sparsePolynomial p0330,sparsePolynomial p0331,sparsePolynomial p0332,sparsePolynomial p0333,sparsePolynomial p0359,sparsePolynomial p0360,sparsePolynomial p0361,sparsePolynomial p0362,sparsePolynomial p0363,sparsePolynomial p0364,sparsePolynomial p0365,sparsePolynomial p0366,sparsePolynomial p0367,sparsePolynomial p0368,sparsePolynomial p0369,sparsePolynomial p0370,sparsePolynomial p0371,sparsePolynomial p0372,sparsePolynomial p0373,sparsePolynomial p0374,sparsePolynomial p0375,sparsePolynomial p0376,sparsePolynomial p0377,sparsePolynomial p0378,sparsePolynomial p0408,sparsePolynomial p0409,sparsePolynomial p0410,sparsePolynomial p0411,sparsePolynomial p0412,sparsePolynomial p0413,sparsePolynomial p0414,sparsePolynomial p0415,sparsePolynomial p0416,sparsePolynomial p0417,sparsePolynomial p0418,sparsePolynomial p0419,sparsePolynomial p0420,sparsePolynomial p0421,sparsePolynomial p0422,sparsePolynomial p0423,sparsePolynomial p0424,sparsePolynomial p0425,sparsePolynomial p0426,sparsePolynomial p0427,sparsePolynomial p0428,sparsePolynomial p0429,sparsePolynomial p0430,sparsePolynomial p0431,sparsePolynomial p0432]]=[[ratParity (0,0,0),ratParity (0,1,0),ratParity (1,0,0),ratParity (0,0,1),ratParity (0,2,0),ratParity (1,1,0),ratParity (2,0,0),ratParity (0,1,1),ratParity (0,3,0),ratParity (1,0,1),ratParity (1,2,0),ratParity (2,1,0),ratParity (3,0,0),ratParity (0,0,2),ratParity (0,2,1),ratParity (0,4,0),ratParity (1,1,1),ratParity (1,3,0),ratParity (2,0,1),ratParity (2,2,0),ratParity (3,1,0),ratParity (4,0,0),ratParity (0,1,2),ratParity (0,3,1),ratParity (0,5,0),ratParity (1,0,2),ratParity (1,2,1),ratParity (1,4,0),ratParity (2,1,1),ratParity (2,3,0),ratParity (3,0,1),ratParity (3,2,0),ratParity (4,1,0),ratParity (5,0,0),ratParity (0,0,3),ratParity (0,2,2),ratParity (0,4,1),ratParity (0,6,0),ratParity (1,1,2),ratParity (1,3,1),ratParity (1,5,0),ratParity (2,0,2),ratParity (2,2,1),ratParity (2,4,0),ratParity (3,1,1),ratParity (3,3,0),ratParity (4,0,1),ratParity (4,2,0),ratParity (5,1,0),ratParity (6,0,0),ratParity (0,1,3),ratParity (0,3,2),ratParity (0,5,1),ratParity (0,7,0),ratParity (1,0,3),ratParity (1,2,2),ratParity (1,4,1),ratParity (1,6,0),ratParity (2,1,2),ratParity (2,3,1),ratParity (2,5,0),ratParity (3,0,2),ratParity (3,2,1),ratParity (3,4,0),ratParity (4,1,1),ratParity (4,3,0),ratParity (5,0,1),ratParity (5,2,0),ratParity (6,1,0),ratParity (7,0,0),ratParity (0,0,4),ratParity (0,2,3),ratParity (0,4,2),ratParity (0,6,1),ratParity (0,8,0),ratParity (1,1,3),ratParity (1,3,2),ratParity (1,5,1),ratParity (1,7,0),ratParity (2,0,3),ratParity (2,2,2),ratParity (2,4,1),ratParity (2,6,0),ratParity (3,1,2),ratParity (3,3,1),ratParity (3,5,0),ratParity (4,0,2),ratParity (4,2,1),ratParity (4,4,0),ratParity (5,1,1),ratParity (5,3,0),ratParity (6,0,1),ratParity (6,2,0),ratParity (7,1,0),ratParity (8,0,0),ratParity (0,1,4),ratParity (0,3,3),ratParity (0,5,2),ratParity (0,7,1),ratParity (0,9,0),ratParity (1,0,4),ratParity (1,2,3),ratParity (1,4,2),ratParity (1,6,1),ratParity (1,8,0),ratParity (2,1,3),ratParity (2,3,2),ratParity (2,5,1),ratParity (2,7,0),ratParity (3,0,3),ratParity (3,2,2),ratParity (3,4,1),ratParity (3,6,0),ratParity (4,1,2),ratParity (4,3,1),ratParity (4,5,0),ratParity (5,0,2),ratParity (5,2,1),ratParity (5,4,0),ratParity (6,1,1),ratParity (6,3,0),ratParity (7,0,1),ratParity (7,2,0),ratParity (8,1,0),ratParity (9,0,0)],[ratOdd*ratParity (0,0,0),ratOdd*ratParity (0,1,0),ratOdd*ratParity (1,0,0),ratOdd*ratParity (0,0,1),ratOdd*ratParity (0,2,0),ratOdd*ratParity (1,1,0),ratOdd*ratParity (2,0,0),ratOdd*ratParity (0,1,1),ratOdd*ratParity (0,3,0),ratOdd*ratParity (1,0,1),ratOdd*ratParity (1,2,0),ratOdd*ratParity (2,1,0),ratOdd*ratParity (3,0,0),ratOdd*ratParity (0,0,2),ratOdd*ratParity (0,2,1),ratOdd*ratParity (0,4,0),ratOdd*ratParity (1,1,1),ratOdd*ratParity (1,3,0),ratOdd*ratParity (2,0,1),ratOdd*ratParity (2,2,0),ratOdd*ratParity (3,1,0),ratOdd*ratParity (4,0,0),ratOdd*ratParity (0,1,2),ratOdd*ratParity (0,3,1),ratOdd*ratParity (0,5,0),ratOdd*ratParity (1,0,2),ratOdd*ratParity (1,2,1),ratOdd*ratParity (1,4,0),ratOdd*ratParity (2,1,1),ratOdd*ratParity (2,3,0),ratOdd*ratParity (3,0,1),ratOdd*ratParity (3,2,0),ratOdd*ratParity (4,1,0),ratOdd*ratParity (5,0,0),ratOdd*ratParity (0,0,3),ratOdd*ratParity (0,2,2),ratOdd*ratParity (0,4,1),ratOdd*ratParity (0,6,0),ratOdd*ratParity (1,1,2),ratOdd*ratParity (1,3,1),ratOdd*ratParity (1,5,0),ratOdd*ratParity (2,0,2),ratOdd*ratParity (2,2,1),ratOdd*ratParity (2,4,0),ratOdd*ratParity (3,1,1),ratOdd*ratParity (3,3,0),ratOdd*ratParity (4,0,1),ratOdd*ratParity (4,2,0),ratOdd*ratParity (5,1,0),ratOdd*ratParity (6,0,0),ratOdd*ratParity (0,1,3),ratOdd*ratParity (0,3,2),ratOdd*ratParity (0,5,1),ratOdd*ratParity (0,7,0),ratOdd*ratParity (1,0,3),ratOdd*ratParity (1,2,2),ratOdd*ratParity (1,4,1),ratOdd*ratParity (1,6,0),ratOdd*ratParity (2,1,2),ratOdd*ratParity (2,3,1),ratOdd*ratParity (2,5,0),ratOdd*ratParity (3,0,2),ratOdd*ratParity (3,2,1),ratOdd*ratParity (3,4,0),ratOdd*ratParity (4,1,1),ratOdd*ratParity (4,3,0),ratOdd*ratParity (5,0,1),ratOdd*ratParity (5,2,0),ratOdd*ratParity (6,1,0),ratOdd*ratParity (7,0,0),ratOdd*ratParity (0,0,4),ratOdd*ratParity (0,2,3),ratOdd*ratParity (0,4,2),ratOdd*ratParity (0,6,1),ratOdd*ratParity (0,8,0),ratOdd*ratParity (1,1,3),ratOdd*ratParity (1,3,2),ratOdd*ratParity (1,5,1),ratOdd*ratParity (1,7,0),ratOdd*ratParity (2,0,3),ratOdd*ratParity (2,2,2),ratOdd*ratParity (2,4,1),ratOdd*ratParity (2,6,0),ratOdd*ratParity (3,1,2),ratOdd*ratParity (3,3,1),ratOdd*ratParity (3,5,0),ratOdd*ratParity (4,0,2),ratOdd*ratParity (4,2,1),ratOdd*ratParity (4,4,0),ratOdd*ratParity (5,1,1),ratOdd*ratParity (5,3,0),ratOdd*ratParity (6,0,1),ratOdd*ratParity (6,2,0),ratOdd*ratParity (7,1,0),ratOdd*ratParity (8,0,0)]]
  simp only [List.cons.injEq,and_true]
  exact ⟨⟨raw_identity_0220,⟨raw_identity_0221,⟨raw_identity_0222,⟨raw_identity_0223,⟨raw_identity_0224,⟨raw_identity_0225,⟨raw_identity_0226,⟨raw_identity_0227,⟨raw_identity_0228,⟨raw_identity_0229,⟨raw_identity_0230,⟨raw_identity_0231,⟨raw_identity_0232,⟨raw_identity_0233,⟨raw_identity_0234,⟨raw_identity_0235,⟨raw_identity_0236,⟨raw_identity_0237,⟨raw_identity_0238,⟨raw_identity_0239,⟨raw_identity_0240,⟨raw_identity_0241,⟨raw_identity_0255,⟨raw_identity_0256,⟨raw_identity_0257,⟨raw_identity_0258,⟨raw_identity_0259,⟨raw_identity_0260,⟨raw_identity_0261,⟨raw_identity_0262,⟨raw_identity_0263,⟨raw_identity_0264,⟨raw_identity_0265,⟨raw_identity_0266,⟨raw_identity_0276,⟨raw_identity_0277,⟨raw_identity_0278,⟨raw_identity_0279,⟨raw_identity_0280,⟨raw_identity_0281,⟨raw_identity_0282,⟨raw_identity_0283,⟨raw_identity_0284,⟨raw_identity_0285,⟨raw_identity_0286,⟨raw_identity_0287,⟨raw_identity_0288,⟨raw_identity_0289,⟨raw_identity_0290,⟨raw_identity_0291,⟨raw_identity_0304,⟨raw_identity_0305,⟨raw_identity_0306,⟨raw_identity_0307,⟨raw_identity_0308,⟨raw_identity_0309,⟨raw_identity_0310,⟨raw_identity_0311,⟨raw_identity_0312,⟨raw_identity_0313,⟨raw_identity_0314,⟨raw_identity_0315,⟨raw_identity_0316,⟨raw_identity_0317,⟨raw_identity_0318,⟨raw_identity_0319,⟨raw_identity_0320,⟨raw_identity_0321,⟨raw_identity_0322,⟨raw_identity_0323,⟨raw_identity_0340,⟨raw_identity_0341,⟨raw_identity_0342,⟨raw_identity_0343,⟨raw_identity_0344,⟨raw_identity_0345,⟨raw_identity_0346,⟨raw_identity_0347,⟨raw_identity_0348,⟨raw_identity_0349,⟨raw_identity_0350,⟨raw_identity_0351,⟨raw_identity_0352,⟨raw_identity_0353,⟨raw_identity_0354,⟨raw_identity_0355,⟨raw_identity_0356,⟨raw_identity_0357,⟨raw_identity_0358,⟨raw_identity_0359,⟨raw_identity_0360,⟨raw_identity_0361,⟨raw_identity_0362,⟨raw_identity_0363,⟨raw_identity_0364,⟨raw_identity_0385,⟨raw_identity_0386,⟨raw_identity_0387,⟨raw_identity_0388,⟨raw_identity_0389,⟨raw_identity_0390,⟨raw_identity_0391,⟨raw_identity_0392,⟨raw_identity_0393,⟨raw_identity_0394,⟨raw_identity_0395,⟨raw_identity_0396,⟨raw_identity_0397,⟨raw_identity_0398,⟨raw_identity_0399,⟨raw_identity_0400,⟨raw_identity_0401,⟨raw_identity_0402,⟨raw_identity_0403,⟨raw_identity_0404,⟨raw_identity_0405,⟨raw_identity_0406,⟨raw_identity_0407,⟨raw_identity_0408,⟨raw_identity_0409,⟨raw_identity_0410,⟨raw_identity_0411,⟨raw_identity_0412,⟨raw_identity_0413,raw_identity_0414⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩,⟨raw_identity_0242,⟨raw_identity_0243,⟨raw_identity_0244,⟨raw_identity_0245,⟨raw_identity_0246,⟨raw_identity_0247,⟨raw_identity_0248,⟨raw_identity_0249,⟨raw_identity_0250,⟨raw_identity_0251,⟨raw_identity_0252,⟨raw_identity_0253,⟨raw_identity_0254,⟨raw_identity_0267,⟨raw_identity_0268,⟨raw_identity_0269,⟨raw_identity_0270,⟨raw_identity_0271,⟨raw_identity_0272,⟨raw_identity_0273,⟨raw_identity_0274,⟨raw_identity_0275,⟨raw_identity_0292,⟨raw_identity_0293,⟨raw_identity_0294,⟨raw_identity_0295,⟨raw_identity_0296,⟨raw_identity_0297,⟨raw_identity_0298,⟨raw_identity_0299,⟨raw_identity_0300,⟨raw_identity_0301,⟨raw_identity_0302,⟨raw_identity_0303,⟨raw_identity_0324,⟨raw_identity_0325,⟨raw_identity_0326,⟨raw_identity_0327,⟨raw_identity_0328,⟨raw_identity_0329,⟨raw_identity_0330,⟨raw_identity_0331,⟨raw_identity_0332,⟨raw_identity_0333,⟨raw_identity_0334,⟨raw_identity_0335,⟨raw_identity_0336,⟨raw_identity_0337,⟨raw_identity_0338,⟨raw_identity_0339,⟨raw_identity_0365,⟨raw_identity_0366,⟨raw_identity_0367,⟨raw_identity_0368,⟨raw_identity_0369,⟨raw_identity_0370,⟨raw_identity_0371,⟨raw_identity_0372,⟨raw_identity_0373,⟨raw_identity_0374,⟨raw_identity_0375,⟨raw_identity_0376,⟨raw_identity_0377,⟨raw_identity_0378,⟨raw_identity_0379,⟨raw_identity_0380,⟨raw_identity_0381,⟨raw_identity_0382,⟨raw_identity_0383,⟨raw_identity_0384,⟨raw_identity_0415,⟨raw_identity_0416,⟨raw_identity_0417,⟨raw_identity_0418,⟨raw_identity_0419,⟨raw_identity_0420,⟨raw_identity_0421,⟨raw_identity_0422,⟨raw_identity_0423,⟨raw_identity_0424,⟨raw_identity_0425,⟨raw_identity_0426,⟨raw_identity_0427,⟨raw_identity_0428,⟨raw_identity_0429,⟨raw_identity_0430,⟨raw_identity_0431,⟨raw_identity_0432,⟨raw_identity_0433,⟨raw_identity_0434,⟨raw_identity_0435,⟨raw_identity_0436,⟨raw_identity_0437,⟨raw_identity_0438,raw_identity_0439⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem source_catalogue_verified : ∀ i : Fin 12, EntryAgrees (entries i) := by
  intro i
  fin_cases i
  · exact source_entry0
  · exact source_entry1
  · exact source_entry2
  · exact source_entry3
  · exact source_entry4
  · exact source_entry5
  · exact source_entry6
  · exact source_entry7
  · exact source_entry8
  · exact source_entry9
  · exact source_entry10
  · exact source_entry11

end RawCatalogue

theorem kernels_finite_layout_linkage : FiniteLayoutLinkageContract :=
  ⟨RawCatalogue.source_catalogue_verified,RawCatalogue.expectedGroups_map⟩

#check kernels_finite_layout_linkage
#print axioms kernels_finite_layout_linkage

#check FiniteLayoutLinkageContract
#print axioms FiniteLayoutLinkageContract
end Blueprint.Thomson.Finite
