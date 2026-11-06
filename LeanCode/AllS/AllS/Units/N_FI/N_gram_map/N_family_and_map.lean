import AllS.Units.N_F.N_kernels
import AllS.Units.N_F.N_moment_kernels
import AllS.Units.N_FI.N_moment_pos.N_scalar_weights
import Mathlib.Order.Fin.Tuple
import Mathlib.LinearAlgebra.Matrix.Symmetric

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

/-- Scalar blocks are ordered exactly as the mathematical kernel declaration. -/
instance : Fintype ScalarBlockName where
  elems := {.m0Plus,.m0Sign,.m0Standard,.m1Even,.m1Odd,.mdetPlus,.mdetSign,.mdetStandard}
  complete := by intro b;cases b <;> simp

def scalarBlockDimension (b : ScalarBlockName) (d : ℕ) : ℕ :=
  match b with
  | .m0Plus => (freeRows (invariantTagList d).length (invariantPivots d)).length
  | .m0Sign => (freeRows (invariantTagList (d-3)).length (signPivots d)).length
  | .m0Standard => (freeRows (standardTagList d).length (standardPivots d)).length
  | .m1Even => (freeRows (parityTagList (d-1)).length (parityPivots false (d-1))).length
  | .m1Odd => (freeRows (parityTagList (d-1-1)).length (parityPivots true (d-1))).length
  | .mdetPlus => (freeRows (invariantTagList (d-2)).length (invariantPivots (d-2))).length
  | .mdetSign => (freeRows (invariantTagList (d-2-3)).length (signPivots (d-2))).length
  | .mdetStandard => (freeRows (standardTagList (d-2)).length (standardPivots (d-2))).length

def scalarBlockStandard : ScalarBlockName → Bool
  | .m0Standard | .mdetStandard => true
  | _ => false

def scalarWeightPoly : ScalarBlockName → Poly3
  | .m0Plus | .m0Sign | .m0Standard => 1
  | .m1Even | .m1Odd => edgeWeightPoly
  | .mdetPlus | .mdetSign | .mdetStandard => determinantWeightPoly

def scalarFeature (b : ScalarBlockName) (a : ℝ) (d : ℕ) (component : Fin 2)
    (i : Fin (scalarBlockDimension b d)) : Poly3 :=
  (((scalarBlockFeatures b a d)[component.val]?.getD [])[i.val]?).getD 0

def scalarBilinearKernel (b : ScalarBlockName) (a : ℝ) (d : ℕ)
    (i j : Fin (scalarBlockDimension b d)) : Poly3 :=
  reynolds (scalarWeightPoly b*(scalarFeature b a d 0 i*scalarFeature b a d 0 j+
    MvPolynomial.C (if scalarBlockStandard b then (1/3 : ℝ) else 0)*
      (scalarFeature b a d 1 i*scalarFeature b a d 1 j)))

abbrev GramBlock (d : ℕ) := Sum (Fin d) ScalarBlockName

def gramBlockDimension (d : ℕ) : GramBlock d → ℕ
  | .inl k => d-k.val
  | .inr b => scalarBlockDimension b d

abbrev MomentPivots (d : ℕ) := ∀ k : Fin d,Fin (d-k.val+1)

/-- Free rows are ascending, via the order preserving successor-above map. -/
def momentKernelMatrix (a : ℝ) (d : ℕ) (p : MomentPivots d) (k : Fin d) :
    Matrix (Fin (d-k.val+1)) (Fin (d-k.val)) ℝ := fun r i =>
  momentNullspaceColumn (fun r => momentP k.val r.val a) (p k) r (finSuccAboveEquiv (p k) i)

def momentBilinearKernel (a : ℝ) (d : ℕ) (p : MomentPivots d) (k : Fin d)
    (i j : Fin (d-k.val)) : Poly3 :=
  ∑ r : Fin (d-k.val+1),∑ c : Fin (d-k.val+1),
    MvPolynomial.C (momentKernelMatrix a d p k r i*momentKernelMatrix a d p k c j)*
      kernelRPoly k.val r.val c.val

def gramKernel (a : ℝ) (d : ℕ) (p : MomentPivots d) (b : GramBlock d) :
    Matrix (Fin (gramBlockDimension d b)) (Fin (gramBlockDimension d b)) Poly3 :=
  match b with
  | .inl k => momentBilinearKernel a d p k
  | .inr b => scalarBilinearKernel b a d

abbrev GramMatrices (d : ℕ) :=
  ∀ b : GramBlock d,Matrix (Fin (gramBlockDimension d b)) (Fin (gramBlockDimension d b)) ℝ

def gramSymmetricSubmodule (d : ℕ) : Submodule ℝ (GramMatrices d) where
  carrier := {W | ∀ b,(W b).IsSymm}
  zero_mem' := by intro b;exact Matrix.isSymm_zero
  add_mem' := by intro W V hW hV b;exact (hW b).add (hV b)
  smul_mem' := by intro c W hW b;exact (hW b).smul c

/-- A finite product of symmetric physical matrices. There is no square-root-two
normalization in this representation. Zero dimensional blocks are harmless. -/
abbrev GramFamily (d : ℕ) := gramSymmetricSubmodule d

def gramPoly (a : ℝ) (d : ℕ) (p : MomentPivots d) (W : GramFamily d) : Poly3 :=
  ∑ b : GramBlock d,∑ i,∑ j,MvPolynomial.C (W.val b i j)*gramKernel a d p b i j

def GramFamilyMapContract : Prop :=
  (∀ d,∀ W : GramFamily d,∀ b,(W.val b).IsSymm) ∧
  (∀ a d p W,gramPoly a d p W=
    ∑ b : GramBlock d,∑ i,∑ j,MvPolynomial.C (W.val b i j)*gramKernel a d p b i j) ∧
  (∀ a d p k r i,momentKernelMatrix a d p k r i=
    (if r=(p k).succAbove i then 1 else 0)-
      (momentP k.val ((p k).succAbove i).val a/momentP k.val (p k).val a)*
        (if r=p k then 1 else 0))

theorem gram_map_family_and_map : GramFamilyMapContract := by
  refine ⟨fun d W b => W.property b,fun a d p W => rfl,?_⟩
  intro a d p k r i
  rfl

#check gram_map_family_and_map
#print axioms gram_map_family_and_map
end Blueprint.Thomson.Finite
