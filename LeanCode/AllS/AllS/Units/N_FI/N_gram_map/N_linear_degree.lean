import AllS.Units.N_FI.N_gram_map.N_family_and_map

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite
open MvPolynomial

set_option maxHeartbeats 0

def GramLinearDegreeContract : Prop :=
  (∀ a d p,∀ V W : GramFamily d,∀ c : ℝ,
    gramPoly a d p (V+c • W)=gramPoly a d p V+c • gramPoly a d p W) ∧
  (∀ a d p,∀ W : GramFamily d,(gramPoly a d p W).IsSymmetric) ∧
  (∀ a,physical a → ∀ d,6≤d → ∀ p,∀ W : GramFamily d,(gramPoly a d p W).totalDegree ≤ 2*d)

theorem reynolds_rename (p : Poly3) (σ : Equiv.Perm (Fin 3)) :
    reynolds (rename σ p)=reynolds p := by
  change (6 : ℝ)⁻¹ • (∑ τ : Equiv.Perm (Fin 3),rename τ (rename σ p))=_
  have hs : (∑ τ : Equiv.Perm (Fin 3),rename τ (rename σ p))=
      ∑ τ : Equiv.Perm (Fin 3),rename τ p := by
    simp only [rename_rename]
    change (∑ τ : Equiv.Perm (Fin 3),rename (τ*σ) p)=_
    exact Equiv.sum_comp (Equiv.mulRight σ) (fun τ : Equiv.Perm (Fin 3) => rename τ p)
  rw [hs]
  rfl

theorem reynolds_isSymmetric (p : Poly3) : (reynolds p).IsSymmetric := by
  intro σ
  change rename σ ((6 : ℝ)⁻¹ • ∑ τ : Equiv.Perm (Fin 3),rename τ p)=_
  rw [map_smul,map_sum]
  have hs : (∑ τ : Equiv.Perm (Fin 3),rename σ (rename τ p))=
      ∑ τ : Equiv.Perm (Fin 3),rename τ p := by
    simp only [rename_rename]
    change (∑ τ : Equiv.Perm (Fin 3),rename (σ*τ) p)=_
    exact Equiv.sum_comp (Equiv.mulLeft σ) (fun τ : Equiv.Perm (Fin 3) => rename τ p)
  rw [hs]
  rfl

theorem symmetric_sum {ι : Type*} (s : Finset ι) (f : ι → Poly3)
    (hf : ∀ i∈s,(f i).IsSymmetric) : (∑ i∈s,f i).IsSymmetric := by
  intro σ
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i hi => hf i hi σ)

theorem rename_repeatSubst (p : Poly3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    rename σ (repeatSubst i p)=repeatSubst (σ i) p := by
  have h : (rename σ).comp (repeatSubst i)=repeatSubst (σ i) := by
    ext j
    fin_cases j <;> simp [repeatSubst]
  exact congrArg (fun f : Poly3 →ₐ[ℝ] Poly3 => f p) h

theorem repeatSum_isSymmetric (p : Poly3) :
    (repeatSubst 0 p+repeatSubst 1 p+repeatSubst 2 p).IsSymmetric := by
  have he : repeatSubst 0 p+repeatSubst 1 p+repeatSubst 2 p=
      ∑ i : Fin 3,repeatSubst i p := by simp [Fin.sum_univ_succ];ring
  rw [he]
  intro σ
  simp only [map_sum,rename_repeatSubst]
  exact Equiv.sum_comp σ (fun i => repeatSubst i p)

theorem kernelRPoly_isSymmetric (k i j : ℕ) : (kernelRPoly k i j).IsSymmetric := by
  have he : kernelRPoly k i j=C 6*kernelSPoly k i j+
      (repeatSubst 0 (kernelSPoly k i j)+repeatSubst 1 (kernelSPoly k i j)+repeatSubst 2 (kernelSPoly k i j))+
      C (if k=0 then (1/7 : ℝ) else 0) := by simp only [kernelRPoly];ring
  rw [he]
  exact (((MvPolynomial.IsSymmetric.C 6).mul (reynolds_isSymmetric _)).add
    (repeatSum_isSymmetric _)).add (MvPolynomial.IsSymmetric.C _)

theorem gramKernel_isSymmetric (a : ℝ) (d : ℕ) (p : MomentPivots d) (b : GramBlock d)
    (i j : Fin (gramBlockDimension d b)) : (gramKernel a d p b i j).IsSymmetric := by
  cases b with
  | inl k =>
    change (momentBilinearKernel a d p k i j).IsSymmetric
    apply symmetric_sum
    intro r hr
    apply symmetric_sum
    intro c hc
    exact (MvPolynomial.IsSymmetric.C _).mul (kernelRPoly_isSymmetric _ _ _)
  | inr b => exact reynolds_isSymmetric _

theorem gramPoly_isSymmetric (a : ℝ) (d : ℕ) (p : MomentPivots d) (W : GramFamily d) :
    (gramPoly a d p W).IsSymmetric := by
  apply symmetric_sum
  intro b hb
  apply symmetric_sum
  intro i hi
  apply symmetric_sum
  intro j hj
  exact (MvPolynomial.IsSymmetric.C _).mul (gramKernel_isSymmetric a d p b i j)

theorem gramPoly_add (a : ℝ) (d : ℕ) (p : MomentPivots d) (V W : GramFamily d) :
    gramPoly a d p (V+W)=gramPoly a d p V+gramPoly a d p W := by
  simp [gramPoly,add_mul,Finset.sum_add_distrib]

theorem gramPoly_smul (a : ℝ) (d : ℕ) (p : MomentPivots d) (W : GramFamily d) (c : ℝ) :
    gramPoly a d p (c • W)=c • gramPoly a d p W := by
  simp [gramPoly,smul_eq_C_mul,Finset.mul_sum,mul_assoc]

theorem scalarFeature_degree (a : ℝ) (ha : physical a) (d : ℕ) (hd : 6≤d)
    (b : ScalarBlockName) (c : Fin 2) (i : Fin (scalarBlockDimension b d)) :
    (scalarFeature b a d c i).totalDegree ≤ scalarBlockAllowance b d := by
  unfold scalarFeature
  cases hg : (scalarBlockFeatures b a d)[c.val]? with
  | none => simp [hg]
  | some g =>
    simp only [hg,Option.getD_some]
    cases hf : g[i.val]? with
    | none => simp [hf]
    | some f =>
      simp only [hf,Option.getD_some]
      exact (scalarBlockFeatures_spec a ha d hd b g (List.mem_of_getElem? hg) f
        (List.mem_of_getElem? hf)).1

def scalarWeightDegree : ScalarBlockName → ℕ
  | .m0Plus | .m0Sign | .m0Standard => 0
  | .m1Even | .m1Odd => 2
  | .mdetPlus | .mdetSign | .mdetStandard => 3

theorem scalarWeightPoly_degree (b : ScalarBlockName) :
    (scalarWeightPoly b).totalDegree ≤ scalarWeightDegree b := by
  have he : edgeWeightPoly.totalDegree ≤ 2 := by
    apply polyDegree_sub_le <;> simp
  have hdet : determinantWeightPoly.totalDegree ≤ 3 := by
    have heq : determinantWeightPoly=1+C 2*(MvPolynomial.X 0*MvPolynomial.X 1*MvPolynomial.X 2)-
        (MvPolynomial.X 0^2+MvPolynomial.X 1^2+MvPolynomial.X 2^2) := by
      simp only [determinantWeightPoly,map_ofNat];ring
    rw [heq]
    apply polyDegree_sub_le
    · apply polyDegree_add_le
      · simp
      · have h := polyDegree_mul_le (MvPolynomial.X 0*MvPolynomial.X 1 : Poly3)
            (MvPolynomial.X 2) 2 1 (by simpa using totalDegree_mul (MvPolynomial.X 0 : Poly3) (MvPolynomial.X 1)) (by simp)
        exact (polyDegree_C_mul_le 2 _).trans h
    · apply polyDegree_add_le
      · apply polyDegree_add_le <;> simp
      · simp
  cases b <;> first | exact he | exact hdet | simp [scalarWeightPoly,scalarWeightDegree]

theorem scalarBilinearKernel_degree (a : ℝ) (ha : physical a) (d : ℕ) (hd : 6≤d)
    (b : ScalarBlockName) (i j : Fin (scalarBlockDimension b d)) :
    (scalarBilinearKernel b a d i j).totalDegree ≤ 2*d := by
  apply (reynolds_degree _).trans
  have hplus := polyDegree_mul_le _ _ _ _ (scalarFeature_degree a ha d hd b 0 i)
    (scalarFeature_degree a ha d hd b 0 j)
  have hminus := polyDegree_mul_le _ _ _ _ (scalarFeature_degree a ha d hd b 1 i)
    (scalarFeature_degree a ha d hd b 1 j)
  have hsum := polyDegree_add_le _ _ _ hplus ((polyDegree_C_mul_le (if scalarBlockStandard b then (1/3 : ℝ) else 0) _).trans hminus)
  have h := polyDegree_mul_le _ _ _ _ (scalarWeightPoly_degree b) hsum
  apply h.trans
  cases b <;> simp only [scalarWeightDegree,scalarBlockAllowance] <;> omega

theorem gramKernel_degree (a : ℝ) (ha : physical a) (d : ℕ) (hd : 6≤d)
    (p : MomentPivots d) (b : GramBlock d) (i j : Fin (gramBlockDimension d b)) :
    (gramKernel a d p b i j).totalDegree ≤ 2*d := by
  cases b with
  | inl k =>
    apply totalDegree_finsetSum_le
    intro r hr
    apply totalDegree_finsetSum_le
    intro c hc
    apply (polyDegree_C_mul_le _ _).trans
    exact (kernelRPoly_degree k.val r.val c.val).trans (by have hr:=r.isLt;have hc:=c.isLt;omega)
  | inr b => exact scalarBilinearKernel_degree a ha d hd b i j

theorem gramPoly_degree (a : ℝ) (ha : physical a) (d : ℕ) (hd : 6≤d)
    (p : MomentPivots d) (W : GramFamily d) : (gramPoly a d p W).totalDegree ≤ 2*d := by
  apply totalDegree_finsetSum_le
  intro b hb
  apply totalDegree_finsetSum_le
  intro i hi
  apply totalDegree_finsetSum_le
  intro j hj
  exact (polyDegree_C_mul_le _ _).trans (gramKernel_degree a ha d hd p b i j)

theorem gram_map_linear_degree : GramLinearDegreeContract := by
  refine ⟨?_,gramPoly_isSymmetric,gramPoly_degree⟩
  intro a d p V W c
  rw [gramPoly_add,gramPoly_smul]

#check gram_map_linear_degree
#print axioms gram_map_linear_degree
end Blueprint.Thomson.Finite
