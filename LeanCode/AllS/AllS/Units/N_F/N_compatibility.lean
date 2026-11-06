import AllS.Units.N_FI.N_compatibility.N_scalar_annihilation
import AllS.Units.N_FI.N_compatibility.N_moment_annihilation
import AllS.Units.N_FI.N_compatibility.N_target_annihilation
import AllS.Units.N_FI.N_compatibility.N_low_values

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite
set_option maxHeartbeats 0

def Compatible (a : ℝ) (D : ℕ) : Submodule ℝ Poly3 :=
  boundedSymmetric D ⊓ LinearMap.ker (L0 a) ⊓ LinearMap.ker (L1 a)

@[simp] theorem mem_Compatible (a : ℝ) (D : ℕ) (f : Poly3) :
    f∈Compatible a D ↔ f.IsSymmetric ∧ f.totalDegree≤D ∧ L0 a f=0 ∧ L1 a f=0 := by
  simp only [Compatible,Submodule.mem_inf,mem_boundedSymmetric,LinearMap.mem_ker]
  tauto

theorem scalarFeature_vanish (a : ℝ) (ha : physical a) (d : ℕ) (hd : 6≤d)
    (b : ScalarBlockName) (c : Fin 2) (i : Fin (scalarBlockDimension b d)) :
    ContactVanishes a (scalarFeature b a d c i) := by
  unfold scalarFeature
  cases hg : (scalarBlockFeatures b a d)[c.val]? with
  | none => simp [hg,ContactVanishes]
  | some g =>
    simp only [hg,Option.getD_some]
    cases hf : g[i.val]? with
    | none => simp [hf,ContactVanishes]
    | some f =>
      simp only [hf,Option.getD_some]
      exact (scalarBlockFeatures_spec a ha d hd b g (List.mem_of_getElem? hg) f
        (List.mem_of_getElem? hf)).2

theorem scalarBilinearKernel_annihilation (a : ℝ) (ha : physical a) (d : ℕ) (hd : 6≤d)
    (b : ScalarBlockName) (i j : Fin (scalarBlockDimension b d)) :
    L0 a (scalarBilinearKernel b a d i j)=0 ∧ L1 a (scalarBilinearKernel b a d i j)=0 := by
  have h0 := compatibility_scalar_annihilation a ha (scalarWeightPoly b) _ _
    (scalarFeature_vanish a ha d hd b 0 i) (scalarFeature_vanish a ha d hd b 0 j)
  have h1 := compatibility_scalar_annihilation a ha
    (scalarWeightPoly b*MvPolynomial.C (if scalarBlockStandard b then (1/3 : ℝ) else 0)) _ _
    (scalarFeature_vanish a ha d hd b 1 i) (scalarFeature_vanish a ha d hd b 1 j)
  have he : scalarBilinearKernel b a d i j=
      reynolds (scalarWeightPoly b*scalarFeature b a d 0 i*scalarFeature b a d 0 j)+
      reynolds ((scalarWeightPoly b*MvPolynomial.C (if scalarBlockStandard b then (1/3 : ℝ) else 0))*
        scalarFeature b a d 1 i*scalarFeature b a d 1 j) := by
    rw [← map_add]
    unfold scalarBilinearKernel
    congr 1
    ring
  rw [he]
  simp only [map_add,h0.1,h0.2,h1.1,h1.2,add_zero,and_self]

theorem gramKernel_annihilation (a : ℝ) (ha : physical a) (d : ℕ) (hl : 6≤d) (hu : d≤9)
    (p : MomentPivots d) (hp : ValidMomentPivots p) (b : GramBlock d)
    (i j : Fin (gramBlockDimension d b)) :
    L0 a (gramKernel a d p b i j)=0 ∧ L1 a (gramKernel a d p b i j)=0 := by
  cases b with
  | inl k => exact compatibility_moment_annihilation a ha d hu p hp k i j
  | inr b => exact scalarBilinearKernel_annihilation a ha d hl b i j

theorem gramPoly_annihilation (a : ℝ) (ha : physical a) (d : ℕ) (hl : 6≤d) (hu : d≤9)
    (p : MomentPivots d) (hp : ValidMomentPivots p) (W : GramFamily d) :
    L0 a (gramPoly a d p W)=0 ∧ L1 a (gramPoly a d p W)=0 := by
  have h0 (b : GramBlock d) (i j : Fin (gramBlockDimension d b)) :=
    (gramKernel_annihilation a ha d hl hu p hp b i j).1
  have h1 (b : GramBlock d) (i j : Fin (gramBlockDimension d b)) :=
    (gramKernel_annihilation a ha d hl hu p hp b i j).2
  simp only [gramPoly,MvPolynomial.C_mul',map_sum,map_smul,h0,h1,smul_zero,Finset.sum_const_zero,and_self]

theorem gramPoly_compatible (a : ℝ) (ha : physical a) (d : ℕ) (hl : 6≤d) (hu : d≤9)
    (p : MomentPivots d) (hp : ValidMomentPivots p) (W : GramFamily d) :
    gramPoly a d p W∈Compatible a (2*d) := by
  rw [mem_Compatible]
  exact ⟨gramPoly_isSymmetric a d p W,gramPoly_degree a ha d hl p W,
    gramPoly_annihilation a ha d hl hu p hp W⟩

theorem compatibility_functionals_independent (a : ℝ) (ha : physical a) (c0 c1 : ℝ)
    (he : c0 • L0 a+c1 • L1 a=0) : c0=0 ∧ c1=0 := by
  have h1 := LinearMap.congr_fun he (1 : Poly3)
  simp only [LinearMap.add_apply,LinearMap.smul_apply,LinearMap.zero_apply,smul_eq_mul,
    low_L0_one,low_L1_one,mul_zero,add_zero] at h1
  have hc0 : c0=0 := by linarith
  have hσ := LinearMap.congr_fun he (sigma^2)
  simp only [LinearMap.add_apply,LinearMap.smul_apply,LinearMap.zero_apply,smul_eq_mul,
    hc0,zero_mul,zero_add,low_L1_sigma_square] at hσ
  have hn : 768*(3*a-1)≠0 := by nlinarith [ha.2]
  exact ⟨hc0,(mul_eq_zero.mp hσ).resolve_right hn⟩

def CoefficientCompatibilityContract : Prop := FamilyFunctionalsContract ∧ ScalarAnnihilationContract ∧
  MomentAnnihilationContract ∧ TargetAnnihilationContract ∧ LowValuesContract ∧
  (∀ a,physical a → ∀ d,6≤d → d≤9 → ∀ p : MomentPivots d,ValidMomentPivots p →
    ∀ W : GramFamily d,gramPoly a d p W∈Compatible a (2*d)) ∧
  (∀ a,physical a → ∀ c0 c1 : ℝ,c0 • L0 a+c1 • L1 a=0 → c0=0 ∧ c1=0)

theorem coefficient_compatibility : CoefficientCompatibilityContract :=
  ⟨compatibility_family_functionals,compatibility_scalar_annihilation,compatibility_moment_annihilation,
    compatibility_target_annihilation,compatibility_low_values,gramPoly_compatible,compatibility_functionals_independent⟩

#check coefficient_compatibility
#print axioms coefficient_compatibility
end Blueprint.Thomson.Finite
