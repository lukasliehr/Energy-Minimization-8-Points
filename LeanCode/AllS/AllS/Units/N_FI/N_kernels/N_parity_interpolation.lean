import AllS.Units.N_FI.N_kernels.N_parity_nodes
import AllS.Units.N_F.N_contact_interpolation
import AllS.Units.N_FI.N_upstream_evaluation.N_S_R_eval

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

abbrev ParityData (odd : Bool) := (i : Fin 4) → Fin (parityFiberSize odd i) → ℝ
abbrev ParityIndex (odd : Bool) := (i : Fin 4) × Fin (parityFiberSize odd i)

def parityFiberPair (odd : Bool) (i : Fin 4) (j : Fin (parityFiberSize odd i)) : Fin 4 × Fin 4 :=
  (parityFiberPairs odd i).get ⟨j.val,by rw [parityFiberPairs_length]; exact j.isLt⟩
def parityIndexLabel (odd : Bool) (r : ParityIndex odd) : Fin 3 → Fin 4 :=
  ![parityFiberLabel odd r.1,(parityFiberPair odd r.1 r.2).1,(parityFiberPair odd r.1 r.2).2]
def parityFiberZ (a : ℝ) (odd : Bool) (i : Fin 4) (j : Fin (parityFiberSize odd i)) : ℝ :=
  contacts a (parityFiberPair odd i j).1+contacts a (parityFiberPair odd i j).2

def parityUExt (a : ℝ) (odd : Bool) (n : ℕ) : ℝ :=
  if hn : n<4 then parityFiberU a odd ⟨n,hn⟩ else 0

def parityNewton (a : ℝ) (odd : Bool) (n : ℕ) : Polynomial ℝ :=
  ∏ j ∈ Finset.range n, (Polynomial.X-Polynomial.C (parityUExt a odd j))
def parityBiEval (p : Poly3) (u z : ℝ) : ℝ := MvPolynomial.eval ![u,z,0] p

def parityCorrection (a : ℝ) (odd : Bool) (V : ParityData odd) (i : Fin 4) (p : Poly3) : Polynomial ℝ :=
  scalarLagrange (parityFiberZ a odd i) (fun j =>
    (V i j-parityBiEval p (parityFiberU a odd i) (parityFiberZ a odd i j))/
      (parityNewton a odd i.val).eval (parityFiberU a odd i))

def parityBiStep (a : ℝ) (odd : Bool) (V : ParityData odd) (i : Fin 4) (p : Poly3) : Poly3 :=
  p+polyLift (parityNewton a odd i.val) (MvPolynomial.X 0)*
    polyLift (parityCorrection a odd V i p) (MvPolynomial.X 1)
def parityBiInterpolant (a : ℝ) (odd : Bool) (V : ParityData odd) : Poly3 :=
  parityBiStep a odd V 3 (parityBiStep a odd V 2 (parityBiStep a odd V 1 (parityBiStep a odd V 0 0)))

def parityEmbed : Poly3 →ₐ[ℝ] Poly3 := MvPolynomial.aeval ![MvPolynomial.X 0,parityZ,0]
def parityInterpolant (a : ℝ) (odd : Bool) (V : ParityData odd) : Poly3 :=
  parityEmbed (parityBiInterpolant a odd V)
def paritySourceData (a : ℝ) (odd : Bool) (t : Tag) : ParityData odd := fun i j =>
  MvPolynomial.eval (contactTripleEval a (parityIndexLabel odd ⟨i,j⟩)) (parityMonomial t)
def parityKernelFeature (odd : Bool) (a : ℝ) (t : Tag) : Poly3 :=
  (if odd then parityOdd else 1)*
    (parityMonomial t-parityInterpolant a odd (paritySourceData a odd t))

def parityBiPivot (t : Tag) : Poly3 := MvPolynomial.X 0^t.1*MvPolynomial.X 1^t.2.1

def ParityInterpolationContract : Prop := ∀ a : ℝ, physical a → ∀ odd,
  (∀ V : ParityData odd, ∀ i j,
    parityBiEval (parityBiInterpolant a odd V) (parityFiberU a odd i) (parityFiberZ a odd i j)=V i j) ∧
  (∀ V : ParityData odd, (parityBiInterpolant a odd V).totalDegree ≤ (if odd then 3 else 4)) ∧
  (∀ V : ParityData odd, ∃ c : Tag → ℝ,
    parityBiInterpolant a odd V =
      ∑ t ∈ (parityPivotTags odd).toFinset, MvPolynomial.C (c t)*parityBiPivot t) ∧
  (∀ t r σ, MvPolynomial.eval (permutedContact a r σ) (parityKernelFeature odd a t)=0)

theorem parityFiberZ_get (a : ℝ) (odd : Bool) (i : Fin 4) (j : Fin (parityFiberSize odd i)) :
    parityFiberZ a odd i j = (parityFiberZList a odd i).get
      ⟨j.val,by simp only [parityFiberZList,List.length_map,parityFiberPairs_length]; exact j.isLt⟩ := by
  simp [parityFiberZ,parityFiberZList,parityFiberPair]

theorem parityFiberZ_injective (a : ℝ) (ha : physical a) (odd : Bool) (i : Fin 4) :
    Function.Injective (parityFiberZ a odd i) := by
  intro j k hjk
  simp only [parityFiberZ_get] at hjk
  have h := (parityFiberZList_nodup a ha odd i).injective_get hjk
  exact Fin.ext (congrArg (fun k : Fin (parityFiberZList a odd i).length => k.val) h)

theorem parityUExt_val (a : ℝ) (odd : Bool) (i : Fin 4) :
    parityUExt a odd i.val=parityFiberU a odd i := by
  simp only [parityUExt,dif_pos i.isLt]

theorem parityNewton_eval (a : ℝ) (odd : Bool) (n : ℕ) (x : ℝ) :
    (parityNewton a odd n).eval x=∏ j ∈ Finset.range n, (x-parityUExt a odd j) := by
  simp [parityNewton,Polynomial.eval_prod]

theorem parityNewton_eval_ne (a : ℝ) (ha : physical a) (odd : Bool) (i : Fin 4) :
    (parityNewton a odd i.val).eval (parityFiberU a odd i) ≠ 0 := by
  rw [parityNewton_eval]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hjlt : j<4 := lt_trans (Finset.mem_range.mp hj) i.isLt
  rw [show parityUExt a odd j=parityFiberU a odd ⟨j,hjlt⟩ from parityUExt_val a odd ⟨j,hjlt⟩]
  exact sub_ne_zero.mpr ((parityFiberU_injective a ha odd).ne (by
    intro he
    have hv := congrArg Fin.val he
    have hh := Finset.mem_range.mp hj
    dsimp at hv
    omega))

theorem parityNewton_eval_zero (a : ℝ) (odd : Bool) (i j : Fin 4) (hij : i<j) :
    (parityNewton a odd j.val).eval (parityFiberU a odd i)=0 := by
  rw [parityNewton_eval]
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hij)
  rw [parityUExt_val,sub_self]

theorem parityBiStep_eval (a : ℝ) (odd : Bool) (V : ParityData odd) (i : Fin 4)
    (p : Poly3) (u z : ℝ) :
    parityBiEval (parityBiStep a odd V i p) u z = parityBiEval p u z+
      (parityNewton a odd i.val).eval u*(parityCorrection a odd V i p).eval z := by
  simp only [parityBiEval,parityBiStep,map_add,map_mul,polyLift_eval,MvPolynomial.eval_X]
  rfl

theorem parityBiStep_current (a : ℝ) (ha : physical a) (odd : Bool) (V : ParityData odd)
    (i : Fin 4) (p : Poly3) (j : Fin (parityFiberSize odd i)) :
    parityBiEval (parityBiStep a odd V i p) (parityFiberU a odd i) (parityFiberZ a odd i j)=V i j := by
  rw [parityBiStep_eval,parityCorrection,
    scalarLagrange_eval _ _ (parityFiberZ_injective a ha odd i)]
  have hn := parityNewton_eval_ne a ha odd i
  field_simp
  ring

theorem parityBiStep_previous (a : ℝ) (odd : Bool) (V : ParityData odd)
    (i k : Fin 4) (hik : i<k) (p : Poly3) (z : ℝ) :
    parityBiEval (parityBiStep a odd V k p) (parityFiberU a odd i) z =
      parityBiEval p (parityFiberU a odd i) z := by
  rw [parityBiStep_eval,parityNewton_eval_zero a odd i k hik,zero_mul,add_zero]

theorem parityBiInterpolant_eval (a : ℝ) (ha : physical a) (odd : Bool) (V : ParityData odd)
    (i : Fin 4) (j : Fin (parityFiberSize odd i)) :
    parityBiEval (parityBiInterpolant a odd V) (parityFiberU a odd i) (parityFiberZ a odd i j)=V i j := by
  unfold parityBiInterpolant
  fin_cases i
  · change parityBiEval (parityBiStep a odd V 3 (parityBiStep a odd V 2
      (parityBiStep a odd V 1 (parityBiStep a odd V 0 0))))
      (parityFiberU a odd 0) (parityFiberZ a odd 0 j)=V 0 j
    rw [parityBiStep_previous a odd V 0 3 (by decide),
      parityBiStep_previous a odd V 0 2 (by decide),
      parityBiStep_previous a odd V 0 1 (by decide),
      parityBiStep_current a ha]
  · change parityBiEval (parityBiStep a odd V 3 (parityBiStep a odd V 2
      (parityBiStep a odd V 1 (parityBiStep a odd V 0 0))))
      (parityFiberU a odd 1) (parityFiberZ a odd 1 j)=V 1 j
    rw [parityBiStep_previous a odd V 1 3 (by decide),
      parityBiStep_previous a odd V 1 2 (by decide),
      parityBiStep_current a ha]
  · change parityBiEval (parityBiStep a odd V 3 (parityBiStep a odd V 2
      (parityBiStep a odd V 1 (parityBiStep a odd V 0 0))))
      (parityFiberU a odd 2) (parityFiberZ a odd 2 j)=V 2 j
    rw [parityBiStep_previous a odd V 2 3 (by decide),
      parityBiStep_current a ha]
  · change parityBiEval (parityBiStep a odd V 3 (parityBiStep a odd V 2
      (parityBiStep a odd V 1 (parityBiStep a odd V 0 0))))
      (parityFiberU a odd 3) (parityFiberZ a odd 3 j)=V 3 j
    rw [parityBiStep_current a ha]

/-- The source pivot synthesis map, with no arbitrary-basis choice. -/
def parityBiSynthesis (odd : Bool) : (Tag → ℝ) →ₗ[ℝ] Poly3 where
  toFun c := ∑ t ∈ (parityPivotTags odd).toFinset, c t • parityBiPivot t
  map_add' c d := by simp [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' c d := by simp [Pi.smul_apply,Finset.smul_sum,smul_smul]

def parityBiRange (odd : Bool) : Submodule ℝ Poly3 := (parityBiSynthesis odd).range

theorem parityBiRange_pivot (odd : Bool) (t : Tag) (ht : t ∈ (parityPivotTags odd).toFinset) :
    parityBiPivot t ∈ parityBiRange odd := by
  classical
  refine ⟨fun u => if u=t then 1 else 0,?_⟩
  change (∑ u ∈ (parityPivotTags odd).toFinset,(if u=t then (1:ℝ) else 0) • parityBiPivot u)=_
  simp [Finset.sum_ite_eq',ht]

set_option maxRecDepth 100000 in
theorem parity_pivot_lower : ∀ odd (i : Fin 4) (r : Fin (i.val+1))
    (j : Fin (parityFiberSize odd i)), ((r.val,j.val,0) : Tag) ∈ (parityPivotTags odd).toFinset := by decide

set_option maxRecDepth 100000 in
theorem parity_pivot_degree_bound : ∀ odd, ∀ t ∈ (parityPivotTags odd).toFinset,
    t.1+t.2.1 ≤ (if odd then 3 else 4) := by decide

theorem parityNewton_natDegree (a : ℝ) (odd : Bool) (n : ℕ) :
    (parityNewton a odd n).natDegree ≤ n := by
  unfold parityNewton
  have h := Polynomial.natDegree_prod_le (Finset.range n)
    (fun j => Polynomial.X-Polynomial.C (parityUExt a odd j))
  simpa using h

theorem polyLift_X_expansion (p : Polynomial ℝ) (i : Fin 3) (n : ℕ) (hp : p.natDegree<n) :
    polyLift p (MvPolynomial.X i)=∑ j ∈ Finset.range n, MvPolynomial.C (p.coeff j)*MvPolynomial.X i^j := by
  exact Polynomial.eval₂_eq_sum_range' MvPolynomial.C hp _

theorem parityBiStep_mem (a : ℝ) (ha : physical a) (odd : Bool) (V : ParityData odd)
    (i : Fin 4) (p : Poly3) (hp : p ∈ parityBiRange odd) : parityBiStep a odd V i p ∈ parityBiRange odd := by
  apply (parityBiRange odd).add_mem hp
  have hN := parityNewton_natDegree a odd i.val
  have hsize : 0<parityFiberSize odd i := by cases odd <;> fin_cases i <;> decide
  have hL : (parityCorrection a odd V i p).natDegree<parityFiberSize odd i := by
    have h := scalarLagrange_natDegree (parityFiberZ a odd i)
      (fun j => (V i j-parityBiEval p (parityFiberU a odd i) (parityFiberZ a odd i j))/
        (parityNewton a odd i.val).eval (parityFiberU a odd i)) (parityFiberZ_injective a ha odd i)
    change (parityCorrection a odd V i p).natDegree ≤ parityFiberSize odd i-1 at h
    omega
  rw [polyLift_X_expansion _ 0 (i.val+1) (by omega),polyLift_X_expansion _ 1 (parityFiberSize odd i) hL,
    Finset.sum_mul]
  apply Submodule.sum_mem
  intro r hr
  rw [Finset.mul_sum]
  apply Submodule.sum_mem
  intro j hj
  have he : (MvPolynomial.C ((parityNewton a odd i.val).coeff r)*MvPolynomial.X 0^r)*
      (MvPolynomial.C ((parityCorrection a odd V i p).coeff j)*MvPolynomial.X 1^j) =
      ((parityNewton a odd i.val).coeff r*(parityCorrection a odd V i p).coeff j) •
        parityBiPivot (r,j,0) := by
    simp only [parityBiPivot,MvPolynomial.C_mul',map_mul]
    simp only [smul_mul_assoc,mul_smul_comm,smul_smul]
    rw [mul_comm ((parityCorrection a odd V i p).coeff j)]
  rw [he]
  apply (parityBiRange odd).smul_mem
  exact parityBiRange_pivot odd _ (parity_pivot_lower odd i
    ⟨r,Finset.mem_range.mp hr⟩ ⟨j,Finset.mem_range.mp hj⟩)

theorem parityBiInterpolant_mem (a : ℝ) (ha : physical a) (odd : Bool) (V : ParityData odd) :
    parityBiInterpolant a odd V ∈ parityBiRange odd := by
  exact parityBiStep_mem a ha odd V 3 _ (parityBiStep_mem a ha odd V 2 _
    (parityBiStep_mem a ha odd V 1 _ (parityBiStep_mem a ha odd V 0 _ (Submodule.zero_mem _))))

theorem parityBiInterpolant_expansion (a : ℝ) (ha : physical a) (odd : Bool) (V : ParityData odd) :
    ∃ c : Tag → ℝ, parityBiInterpolant a odd V =
      ∑ t ∈ (parityPivotTags odd).toFinset,MvPolynomial.C (c t)*parityBiPivot t := by
  obtain ⟨c,hc⟩ := parityBiInterpolant_mem a ha odd V
  refine ⟨c,?_⟩
  simpa only [parityBiSynthesis,LinearMap.coe_mk,AddHom.coe_mk,MvPolynomial.C_mul'] using hc.symm

theorem parityBiInterpolant_degree (a : ℝ) (ha : physical a) (odd : Bool) (V : ParityData odd) :
    (parityBiInterpolant a odd V).totalDegree ≤ (if odd then 3 else 4) := by
  obtain ⟨c,hc⟩ := parityBiInterpolant_expansion a ha odd V
  rw [hc]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro t ht
  apply (polyDegree_C_mul_le _ _).trans
  have hd : (parityBiPivot t).totalDegree ≤ t.1+t.2.1 := by
    exact polyDegree_mul_le _ _ _ _ (by simp) (by simp)
  exact hd.trans (parity_pivot_degree_bound odd t ht)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem parityIndexLabel_image : ∀ odd,
    Finset.univ.image (parityIndexLabel odd)=parityLabelPoints odd := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem parityLabel_canonical_or_swap : ∀ odd (p : Fin 3 → Fin 4),
    p ∈ Finset.univ.biUnion contactLabelOrbit → (odd=true → p 1≠p 2) →
    p ∈ parityLabelPoints odd ∨ (p ∘ Equiv.swap 1 2) ∈ parityLabelPoints odd := by decide

theorem parityEmbed_eval (x : Fin 3 → ℝ) (p : Poly3) :
    MvPolynomial.eval x (parityEmbed p)=parityBiEval p (x 0) (x 1+x 2) := by
  rw [parityEmbed,eval_aeval_poly]
  apply congrArg (fun z : Fin 3 → ℝ => MvPolynomial.eval z p)
  funext i
  fin_cases i <;> simp [parityZ]

theorem parityInterpolant_eval_index (a : ℝ) (ha : physical a) (odd : Bool) (V : ParityData odd)
    (r : ParityIndex odd) :
    MvPolynomial.eval (contactTripleEval a (parityIndexLabel odd r)) (parityInterpolant a odd V)=V r.1 r.2 := by
  rw [parityInterpolant,parityEmbed_eval]
  exact parityBiInterpolant_eval a ha odd V r.1 r.2

theorem parityMonomial_eval_swap (x : Fin 3 → ℝ) (t : Tag) :
    MvPolynomial.eval (x ∘ Equiv.swap 1 2) (parityMonomial t)=MvPolynomial.eval x (parityMonomial t) := by
  simp [parityMonomial,parityZ,parityW,Function.comp_apply,Equiv.swap_apply_def]
  ring

theorem parityInterpolant_eval_swap (a : ℝ) (odd : Bool) (V : ParityData odd) (x : Fin 3 → ℝ) :
    MvPolynomial.eval (x ∘ Equiv.swap 1 2) (parityInterpolant a odd V)=
      MvPolynomial.eval x (parityInterpolant a odd V) := by
  simp only [parityInterpolant,parityEmbed_eval]
  simp [Function.comp_apply,Equiv.swap_apply_def,add_comm]

theorem parityKernel_canonical_residual (a : ℝ) (ha : physical a) (odd : Bool) (t : Tag)
    (p : Fin 3 → Fin 4) (hp : p ∈ parityLabelPoints odd) :
    MvPolynomial.eval (contactTripleEval a p)
      (parityMonomial t-parityInterpolant a odd (paritySourceData a odd t))=0 := by
  rw [← parityIndexLabel_image odd] at hp
  obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hp
  rw [map_sub,parityInterpolant_eval_index a ha]
  simp [paritySourceData]

theorem parityKernelFeature_vanish_label (a : ℝ) (ha : physical a) (odd : Bool) (t : Tag)
    (p : Fin 3 → Fin 4) (hp : p ∈ Finset.univ.biUnion contactLabelOrbit) :
    MvPolynomial.eval (contactTripleEval a p) (parityKernelFeature odd a t)=0 := by
  by_cases hbad : odd=true ∧ p 1=p 2
  · obtain ⟨rfl,he⟩ := hbad
    simp [parityKernelFeature,parityOdd,contactTripleEval,he]
  have hvalid : odd=true → p 1≠p 2 := by tauto
  rw [parityKernelFeature,map_mul]
  have hz : MvPolynomial.eval (contactTripleEval a p)
      (parityMonomial t-parityInterpolant a odd (paritySourceData a odd t))=0 := by
    rcases parityLabel_canonical_or_swap odd p hp hvalid with hc | hc
    · exact parityKernel_canonical_residual a ha odd t p hc
    · have h := parityKernel_canonical_residual a ha odd t (p ∘ Equiv.swap 1 2) hc
      change MvPolynomial.eval (contactTripleEval a p ∘ Equiv.swap 1 2)
        (parityMonomial t-parityInterpolant a odd (paritySourceData a odd t))=0 at h
      simpa only [map_sub,parityMonomial_eval_swap,parityInterpolant_eval_swap] using h
  rw [hz,mul_zero]

theorem parityKernelFeature_vanish (a : ℝ) (ha : physical a) (odd : Bool) (t : Tag)
    (r : Fin 5) (σ : Equiv.Perm (Fin 3)) :
    MvPolynomial.eval (permutedContact a r σ) (parityKernelFeature odd a t)=0 := by
  apply parityKernelFeature_vanish_label a ha odd t (contactRepresentative r ∘ σ)
  apply Finset.mem_biUnion.mpr
  refine ⟨r,Finset.mem_univ _,?_⟩
  exact Finset.mem_image.mpr ⟨σ,Finset.mem_univ _,rfl⟩

theorem parityEmbed_degree (p : Poly3) : (parityEmbed p).totalDegree ≤ p.totalDegree := by
  apply affine_subst_degree
  intro i
  fin_cases i <;> simp
  exact parityZ_degree

theorem parityInterpolant_degree (a : ℝ) (ha : physical a) (odd : Bool) (V : ParityData odd) :
    (parityInterpolant a odd V).totalDegree ≤ (if odd then 3 else 4) :=
  (parityEmbed_degree _).trans (parityBiInterpolant_degree a ha odd V)

theorem kernels_parity_interpolation : ParityInterpolationContract := by
  intro a ha odd
  exact ⟨parityBiInterpolant_eval a ha odd,parityBiInterpolant_degree a ha odd,
    parityBiInterpolant_expansion a ha odd,parityKernelFeature_vanish a ha odd⟩

#check kernels_parity_interpolation
#print axioms kernels_parity_interpolation

#check ParityInterpolationContract
#print axioms ParityInterpolationContract
end Blueprint.Thomson.Finite
