import ThomsonNegative.Geometry.Base

/-! Generic spherical moment positivity and exact R/S summation. Read-only
source adaptation; provenance in analysis/formalization_geometry/MOMENTS_PROVENANCE.json. -/
noncomputable section

/- Source: N_real_power_recurrence.lean -/

/-! Clean proof port from Energy-Minimization-8-Points,
commit 50d14bc06bd41f61573eb6a36eedb8d00759af8f,
Logarithmic/Thomson8/Kernels.lean:21-24. Target Point is the supplied EuclideanSpace.
No legacy Data, certificate, or fixed-exponent target is imported. -/
open scoped BigOperators InnerProductSpace
namespace ThomsonNegative.Geometry.GenericMoments

theorem real_power_recurrence (w : ℂ) (k : ℕ) : (w ^ (k + 2)).re = 2 * w.re * (w ^ (k + 1)).re - Complex.normSq w * (w ^ k).re := by
  simp only [pow_succ, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

end ThomsonNegative.Geometry.GenericMoments
namespace ThomsonNegative.Geometry
theorem generic_moments_real_power_recurrence (w : ℂ) (k : ℕ) : (w ^ (k + 2)).re = 2 * w.re * (w ^ (k + 1)).re - Complex.normSq w * (w ^ k).re :=
  GenericMoments.real_power_recurrence w k
end ThomsonNegative.Geometry


/- Source: N_kernelQ_complex.lean -/

/-! Clean generic proof port from upstream commit
50d14bc06bd41f61573eb6a36eedb8d00759af8f, Logarithmic/Thomson8.
Source declarations: Kernels.kernelQ, KernelPositivity.sphericalKernel, Kernels.kernelQ_complex.
Only target type aliases and explicit real symEval replace legacy interfaces. -/
open scoped BigOperators InnerProductSpace
open ThomsonNegative.Geometry (Configuration)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThomsonNegative.Geometry.GenericMoments

noncomputable def kernelQ : ℕ → ℝ → ℝ → ℝ → ℝ
  | 0, _,_,_ => 1
  | 1, u,v,t => t-u*v
  | k+2, u,v,t => 2*(t-u*v)*kernelQ (k+1) u v t -
      (1-u^2)*(1-v^2)*kernelQ k u v t

noncomputable def sphericalKernel {ι : Type*} (x : Point) (y : ι → Point) (k : ℕ) :
    Matrix ι ι ℝ := fun i j => kernelQ k ⟪x,y i⟫_ℝ ⟪x,y j⟫_ℝ ⟪y i,y j⟫_ℝ

theorem kernelQ_complex (k : ℕ) (u v t : ℝ) (w : ℂ)
    (hr : w.re=t-u*v) (hn : Complex.normSq w=(1-u^2)*(1-v^2)) :
    kernelQ k u v t = (w^k).re := by
  induction k using Nat.twoStepInduction with
  | zero => simp [kernelQ]
  | one => simpa [kernelQ] using hr.symm
  | more k hk hk1 =>
    rw [kernelQ, hk, hk1, real_power_recurrence, hr, hn]

end ThomsonNegative.Geometry.GenericMoments
namespace ThomsonNegative.Geometry
open GenericMoments
theorem generic_moments_kernelQ_complex (k : ℕ) (u v t : ℝ) (w : ℂ)
    (hr : w.re=t-u*v) (hn : Complex.normSq w=(1-u^2)*(1-v^2)) :
    kernelQ k u v t = (w^k).re :=
  GenericMoments.kernelQ_complex k u v t w hr hn
end ThomsonNegative.Geometry

/- Source: N_sum_swaps.lean -/

/-! Clean generic proof port from upstream commit
50d14bc06bd41f61573eb6a36eedb8d00759af8f, Logarithmic/Thomson8.
Source declarations: TripleSums.Index, TripleSums.tripleSum, TripleSums.offSum, TripleSymmetry.onTriples, TripleSums.tripleSum_swap12, TripleSums.tripleSum_swap23, TripleSums.distinctSum_swap12, TripleSums.distinctSum_swap23.
Only target type aliases and explicit real symEval replace legacy interfaces. -/
open scoped BigOperators InnerProductSpace
open ThomsonNegative.Geometry (Configuration)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThomsonNegative.Geometry.GenericMoments

abbrev Index := Fin 8

noncomputable abbrev distinctSum (f : Fin 8 → Fin 8 → Fin 8 → ℝ) : ℝ := ThomsonNegative.Geometry.DistinctSum f

noncomputable def tripleSum (f : Index → Index → Index → ℝ) : ℝ := ∑ i, ∑ j, ∑ k, f i j k

noncomputable def offSum (f : Index → Index → ℝ) : ℝ := ∑ i, ∑ j, if i≠j then f i j else 0

noncomputable def onTriples (x : Configuration) (f : ℝ → ℝ → ℝ → ℝ)
    (i j k : Index) : ℝ := f ⟪x i,x j⟫_ℝ ⟪x i,x k⟫_ℝ ⟪x j,x k⟫_ℝ

theorem tripleSum_swap12 (f : Index → Index → Index → ℝ) :
    tripleSum (fun i j k => f j i k) = tripleSum f := by
  unfold tripleSum
  rw [Finset.sum_comm]

theorem tripleSum_swap23 (f : Index → Index → Index → ℝ) :
    tripleSum (fun i j k => f i k j) = tripleSum f := by
  unfold tripleSum
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

theorem distinctSum_swap12 (f : Index → Index → Index → ℝ) :
    distinctSum (fun i j k => f j i k) = distinctSum f := by
  unfold distinctSum ThomsonNegative.Geometry.DistinctSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  simp only [ne_comm,and_comm,and_left_comm,and_assoc]

theorem distinctSum_swap23 (f : Index → Index → Index → ℝ) :
    distinctSum (fun i j k => f i k j) = distinctSum f := by
  unfold distinctSum ThomsonNegative.Geometry.DistinctSum
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  simp only [ne_comm,and_comm,and_left_comm,and_assoc]

end ThomsonNegative.Geometry.GenericMoments
namespace ThomsonNegative.Geometry
open GenericMoments
theorem generic_moments_sum_swaps (f : Fin 8 → Fin 8 → Fin 8 → ℝ) :
    tripleSum (fun i j k => f j i k) = tripleSum f ∧
    tripleSum (fun i j k => f i k j) = tripleSum f ∧
    distinctSum (fun i j k => f j i k) = distinctSum f ∧
    distinctSum (fun i j k => f i k j) = distinctSum f := by
  exact ⟨tripleSum_swap12 f, tripleSum_swap23 f, distinctSum_swap12 f, distinctSum_swap23 f⟩
end ThomsonNegative.Geometry

/- Source: N_sum_linearity.lean -/

/-! Clean generic proof port from upstream commit
50d14bc06bd41f61573eb6a36eedb8d00759af8f, Logarithmic/Thomson8.
Source declarations: SumLinearity.distinctSum_add, SumLinearity.distinctSum_mul, SumLinearity.offSum_add, SumLinearity.offSum_mul.
Only target type aliases and explicit real symEval replace legacy interfaces. -/
open scoped BigOperators InnerProductSpace
open ThomsonNegative.Geometry (Configuration)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThomsonNegative.Geometry.GenericMoments

theorem distinctSum_add (f g : Index → Index → Index → ℝ) :
    distinctSum (fun i j k => f i j k+g i j k)=distinctSum f+distinctSum g := by
  simp only [distinctSum, ThomsonNegative.Geometry.DistinctSum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> ring

theorem distinctSum_mul (c : ℝ) (f : Index → Index → Index → ℝ) :
    distinctSum (fun i j k => c*f i j k)=c*distinctSum f := by
  simp [distinctSum, ThomsonNegative.Geometry.DistinctSum,Finset.mul_sum,mul_ite]

theorem offSum_add (f g : Index → Index → ℝ) :
    offSum (fun i j => f i j+g i j)=offSum f+offSum g := by
  simp only [offSum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

theorem offSum_mul (c : ℝ) (f : Index → Index → ℝ) :
    offSum (fun i j => c*f i j)=c*offSum f := by
  simp [offSum,Finset.mul_sum,mul_ite]

end ThomsonNegative.Geometry.GenericMoments
namespace ThomsonNegative.Geometry
open GenericMoments
theorem generic_moments_sum_linearity (f g : Fin 8 → Fin 8 → Fin 8 → ℝ) (p q : Fin 8 → Fin 8 → ℝ) (c : ℝ) :
    distinctSum (fun i j k => f i j k + g i j k) = distinctSum f + distinctSum g ∧
    distinctSum (fun i j k => c * f i j k) = c * distinctSum f ∧
    offSum (fun i j => p i j + q i j) = offSum p + offSum q ∧
    offSum (fun i j => c * p i j) = c * offSum p := by
  exact ⟨distinctSum_add f g, distinctSum_mul c f, offSum_add p q, offSum_mul c p⟩
end ThomsonNegative.Geometry

/- Source: N_index_symmetry.lean -/

/-! Clean generic proof port from upstream commit
50d14bc06bd41f61573eb6a36eedb8d00759af8f, Logarithmic/Thomson8.
Source declarations: TripleSymmetry.indexSym, TripleSymmetry.tripleSum_indexSym, TripleSymmetry.distinctSum_indexSym.
Only target type aliases and explicit real symEval replace legacy interfaces. -/
open scoped BigOperators InnerProductSpace
open ThomsonNegative.Geometry (Configuration)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThomsonNegative.Geometry.GenericMoments

noncomputable def indexSym (f : Index → Index → Index → ℝ) (i j k : Index) : ℝ :=
  (f i j k+f i k j+f j i k+f k i j+f j k i+f k j i)/6

theorem tripleSum_indexSym (f : Index → Index → Index → ℝ) :
    tripleSum (indexSym f)=tripleSum f := by
  have h312 : tripleSum (fun i j k => f k i j)=tripleSum f :=
    (tripleSum_swap23 (fun i j k => f j i k)).trans (tripleSum_swap12 f)
  have h231 : tripleSum (fun i j k => f j k i)=tripleSum f :=
    (tripleSum_swap12 (fun i j k => f i k j)).trans (tripleSum_swap23 f)
  have h321 : tripleSum (fun i j k => f k j i)=tripleSum f :=
    (tripleSum_swap12 (fun i j k => f k i j)).trans h312
  have hsplit : tripleSum (indexSym f) =
      (tripleSum f+tripleSum (fun i j k => f i k j)+tripleSum (fun i j k => f j i k)+
        tripleSum (fun i j k => f k i j)+tripleSum (fun i j k => f j k i)+
        tripleSum (fun i j k => f k j i))/6 := by
    simp only [tripleSum,indexSym]
    simp_rw [← Finset.sum_div,Finset.sum_add_distrib]
  rw [hsplit,tripleSum_swap12 f,tripleSum_swap23 f,h312,h231,h321]
  ring

theorem distinctSum_indexSym (f : Index → Index → Index → ℝ) :
    distinctSum (indexSym f)=distinctSum f := by
  have h312 : distinctSum (fun i j k => f k i j)=distinctSum f :=
    (distinctSum_swap23 (fun i j k => f j i k)).trans (distinctSum_swap12 f)
  have h231 : distinctSum (fun i j k => f j k i)=distinctSum f :=
    (distinctSum_swap12 (fun i j k => f i k j)).trans (distinctSum_swap23 f)
  have h321 : distinctSum (fun i j k => f k j i)=distinctSum f :=
    (distinctSum_swap12 (fun i j k => f k i j)).trans h312
  have hsplit : distinctSum (indexSym f) =
      (distinctSum f+distinctSum (fun i j k => f i k j)+distinctSum (fun i j k => f j i k)+
        distinctSum (fun i j k => f k i j)+distinctSum (fun i j k => f j k i)+
        distinctSum (fun i j k => f k j i))/6 := by
    have he (p : Prop) [Decidable p] (a b c d e g : ℝ) :
        (if p then (a+b+c+d+e+g)/6 else 0) =
          ((if p then a else 0)+(if p then b else 0)+(if p then c else 0)+
            (if p then d else 0)+(if p then e else 0)+(if p then g else 0))/6 := by
      split_ifs <;> ring
    simp only [distinctSum, ThomsonNegative.Geometry.DistinctSum,indexSym,he]
    simp_rw [← Finset.sum_div,Finset.sum_add_distrib]
  rw [hsplit,distinctSum_swap12 f,distinctSum_swap23 f,h312,h231,h321]
  ring

end ThomsonNegative.Geometry.GenericMoments
namespace ThomsonNegative.Geometry
open GenericMoments
theorem generic_moments_index_symmetry (f : Fin 8 → Fin 8 → Fin 8 → ℝ) :
    tripleSum (indexSym f) = tripleSum f ∧ distinctSum (indexSym f) = distinctSum f := by
  exact ⟨tripleSum_indexSym f, distinctSum_indexSym f⟩
end ThomsonNegative.Geometry

/- Source: N_onTriples_symmetry.lean -/

/-! Clean generic proof port from upstream commit
50d14bc06bd41f61573eb6a36eedb8d00759af8f, Logarithmic/Thomson8.
Source declarations: TripleSymmetry.onTriples_sym, TripleSymmetry.tripleSum_sym, TripleSymmetry.distinctSum_sym.
Only target type aliases and explicit real symEval replace legacy interfaces. -/
open scoped BigOperators InnerProductSpace
open ThomsonNegative.Geometry (Configuration)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThomsonNegative.Geometry.GenericMoments

noncomputable def symEval (f : ℝ → ℝ → ℝ → ℝ) (u v t : ℝ) : ℝ :=
  (f u v t + f u t v + f v u t + f t u v + f v t u + f t v u) / 6

theorem onTriples_sym (x : Configuration) (f : ℝ → ℝ → ℝ → ℝ) :
    onTriples x (symEval f) = indexSym (onTriples x f) := by
  funext i j k
  simp only [onTriples,symEval,indexSym,real_inner_comm (x k) (x i),
    real_inner_comm (x j) (x i),real_inner_comm (x k) (x j)]
  ring

theorem tripleSum_sym (x : Configuration) (f : ℝ → ℝ → ℝ → ℝ) :
    tripleSum (onTriples x (symEval f)) = tripleSum (onTriples x f) := by
  rw [onTriples_sym,tripleSum_indexSym]

theorem distinctSum_sym (x : Configuration) (f : ℝ → ℝ → ℝ → ℝ) :
    distinctSum (onTriples x (symEval f)) = distinctSum (onTriples x f) := by
  rw [onTriples_sym,distinctSum_indexSym]

end ThomsonNegative.Geometry.GenericMoments
namespace ThomsonNegative.Geometry
open GenericMoments
theorem generic_moments_onTriples_symmetry (y : Configuration) (f : ℝ → ℝ → ℝ → ℝ) :
    onTriples y (symEval f) = indexSym (onTriples y f) ∧
    tripleSum (onTriples y (symEval f)) = tripleSum (onTriples y f) ∧
    distinctSum (onTriples y (symEval f)) = distinctSum (onTriples y f) := by
  exact ⟨onTriples_sym y f, tripleSum_sym y f, distinctSum_sym y f⟩
end ThomsonNegative.Geometry

/- Source: N_kernel_diagonal.lean -/

/-! Generic all-parameter proof. S/R identities adapt upstream RCounting
(commit50d14bc06bd41f61573eb6a36eedb8d00759af8f); outer products expand
the explicit proved tangent features. No fixed-exponent certificate. -/
open scoped BigOperators InnerProductSpace
open ThomsonNegative.Geometry (Configuration)
namespace ThomsonNegative.Geometry.GenericMoments
noncomputable def Sfun (k a b : ℕ) : ℝ → ℝ → ℝ → ℝ :=
  symEval (fun u v t => u^a * v^b * kernelQ k u v t)

theorem kernelQ_diagonal (k : ℕ) : kernelQ k 1 1 1 = if k=0 then 1 else 0 := by
  induction k using Nat.twoStepInduction with
  | zero => simp [kernelQ]
  | one => simp [kernelQ]
  | more k hk hk1 => simp [kernelQ]

theorem Sfun_diagonal (k a b : ℕ) : Sfun k a b 1 1 1 = if k=0 then 1 else 0 := by
  simp only [Sfun, symEval, one_pow, one_mul, kernelQ_diagonal]
  split_ifs <;> norm_num

end ThomsonNegative.Geometry.GenericMoments
namespace ThomsonNegative.Geometry
open GenericMoments

theorem generic_moments_kernel_diagonal (k a b : ℕ) :
    kernelQ k 1 1 1 = (if k=0 then 1 else 0) ∧
    Sfun k a b 1 1 1 = (if k=0 then 1 else 0) := by
  exact ⟨kernelQ_diagonal k, Sfun_diagonal k a b⟩
end ThomsonNegative.Geometry


/- Source: N_moment_entry.lean -/

/-! Clean generic proof port from upstream commit
50d14bc06bd41f61573eb6a36eedb8d00759af8f, Logarithmic/Thomson8.
Source declarations: MomentMatrices.powerFeatures, MomentMatrices.momentMatrix, MomentMatrices.momentMatrix_entry.
Only target type aliases and explicit real symEval replace legacy interfaces. -/
open scoped BigOperators InnerProductSpace
open ThomsonNegative.Geometry (Configuration)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThomsonNegative.Geometry.GenericMoments

noncomputable def powerFeatures (m : ℕ) (x : Point) (y : Configuration) :
    Matrix (Fin m) Index ℝ := fun a j => ⟪x,y j⟫_ℝ^a.val

noncomputable def momentMatrix (m k : ℕ) (y : Configuration) : Matrix (Fin m) (Fin m) ℝ :=
  ∑ i : Index, powerFeatures m (y i) y * sphericalKernel (y i) y k *
    (powerFeatures m (y i) y).transpose

theorem momentMatrix_entry (m k : ℕ) (y : Configuration) (a b : Fin m) :
    momentMatrix m k y a b = tripleSum (onTriples y (fun u v t => u^a.val*v^b.val*kernelQ k u v t)) := by
  simp only [momentMatrix,Matrix.sum_apply,Matrix.mul_apply,Matrix.transpose_apply,
    powerFeatures,sphericalKernel,tripleSum,onTriples,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  ring

end ThomsonNegative.Geometry.GenericMoments
namespace ThomsonNegative.Geometry
open GenericMoments
theorem generic_moments_moment_entry (m k : ℕ) (y : Configuration) (a b : Fin m) :
    momentMatrix m k y a b = tripleSum (onTriples y (fun u v t => u^a.val*v^b.val*kernelQ k u v t)) :=
  GenericMoments.momentMatrix_entry m k y a b
end ThomsonNegative.Geometry

/- Source: N_pair_count.lean -/

/-! Clean generic proof port from upstream commit
50d14bc06bd41f61573eb6a36eedb8d00759af8f, Logarithmic/Thomson8.
Source declarations: TripleSums.distinctSum_pair, TripleSums.distinctSum_const, SumLinearity.distinctSum_pair13, SumLinearity.distinctSum_pair23.
Only target type aliases and explicit real symEval replace legacy interfaces. -/
open scoped BigOperators InnerProductSpace
open ThomsonNegative.Geometry (Configuration)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThomsonNegative.Geometry.GenericMoments

theorem distinctSum_pair (f : Index → Index → ℝ) :
    distinctSum (fun i j _ => f i j) = 6*offSum f := by
  have h (i j : Index) :
      (∑ k : Index, if i≠j ∧ j≠k ∧ k≠i then f i j else 0) =
        6*(if i≠j then f i j else 0) := by
    fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_succ] <;> ring
  simp only [distinctSum, ThomsonNegative.Geometry.DistinctSum,h,offSum,Finset.mul_sum]

theorem distinctSum_const (c : ℝ) : distinctSum (fun _ _ _ => c) = 336*c := by
  rw [distinctSum_pair]
  simp [offSum,Fin.sum_univ_succ]
  ring

theorem distinctSum_pair13 (f : Index → Index → ℝ) :
    distinctSum (fun i _ k => f i k)=6*offSum f :=
  (distinctSum_swap23 (fun i j _ => f i j)).trans (distinctSum_pair f)

theorem distinctSum_pair23 (f : Index → Index → ℝ) :
    distinctSum (fun _ j k => f j k)=6*offSum f :=
  (distinctSum_swap12 (fun i _ k => f i k)).trans (distinctSum_pair13 f)

end ThomsonNegative.Geometry.GenericMoments
namespace ThomsonNegative.Geometry
open GenericMoments
theorem generic_moments_pair_count (f : Fin 8 → Fin 8 → ℝ) (c : ℝ) :
    distinctSum (fun i j _ => f i j) = 6 * offSum f ∧
    distinctSum (fun i _ k => f i k) = 6 * offSum f ∧
    distinctSum (fun _ j k => f j k) = 6 * offSum f ∧
    distinctSum (fun _ _ _ => c) = 336 * c := by
  exact ⟨distinctSum_pair f, distinctSum_pair13 f, distinctSum_pair23 f, distinctSum_const c⟩
end ThomsonNegative.Geometry

/- Source: N_triple_decomposition.lean -/

/-! Clean generic proof port from upstream commit
50d14bc06bd41f61573eb6a36eedb8d00759af8f, Logarithmic/Thomson8.
Source declarations: TripleSums.tripleSum_decomposition.
Only target type aliases and explicit real symEval replace legacy interfaces. -/
open scoped BigOperators InnerProductSpace
open ThomsonNegative.Geometry (Configuration)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThomsonNegative.Geometry.GenericMoments

theorem tripleSum_decomposition (f : Index → Index → Index → ℝ) :
    tripleSum f = distinctSum f +
      offSum (fun i j => f i i j+f i j i+f j i i) + ∑ i, f i i i := by
  simp only [tripleSum,distinctSum,ThomsonNegative.Geometry.DistinctSum,offSum,Fin.sum_univ_succ]
  norm_num [Fin.succ]
  ring

end ThomsonNegative.Geometry.GenericMoments
namespace ThomsonNegative.Geometry
open GenericMoments
theorem generic_moments_triple_decomposition (f : Index → Index → Index → ℝ) :
    tripleSum f = distinctSum f +
      offSum (fun i j => f i i j+f i j i+f j i i) + ∑ i, f i i i :=
  GenericMoments.tripleSum_decomposition f
end ThomsonNegative.Geometry

/- Source: N_symmetry_counting.lean -/

/-! Clean generic proof port from upstream commit
50d14bc06bd41f61573eb6a36eedb8d00759af8f, Logarithmic/Thomson8.
Source declarations: RCounting.repeated_triple_count.
Only target type aliases and explicit real symEval replace legacy interfaces. -/
open scoped BigOperators InnerProductSpace
open ThomsonNegative.Geometry (Configuration)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThomsonNegative.Geometry.GenericMoments

theorem repeated_triple_count (s : ℝ → ℝ → ℝ → ℝ) (c : ℝ)
    (hs12 : ∀ u v t, s u v t=s v u t) (hs23 : ∀ u v t, s u v t=s u t v)
    (hdiag : s 1 1 1=c) (y : Configuration) (hy : ∀ i, ‖y i‖=1) :
    distinctSum (onTriples y (fun u v t => 6*s u v t+s u u 1+s v v 1+s t t 1+c/7)) =
      6*tripleSum (onTriples y s) := by
  let p : Index → Index → ℝ := fun i j => s ⟪y i,y j⟫_ℝ ⟪y i,y j⟫_ℝ 1
  have hrepeated : (fun i j : Index => onTriples y s i i j +
      onTriples y s i j i+onTriples y s j i i) = fun i j => 3*p i j := by
    funext i j
    simp only [onTriples,real_inner_self_eq_norm_sq,hy,one_pow,real_inner_comm (y j) (y i)]
    rw [hs12 1,hs23 _ 1]
    dsimp [p]
    simp only [real_inner_comm]
    ring
  have hdiagonal : (∑ i : Index, onTriples y s i i i)=8*c := by
    simp [onTriples,real_inner_self_eq_norm_sq,hy,hdiag]
  have hdecomp := tripleSum_decomposition (onTriples y s)
  rw [hrepeated,offSum_mul,hdiagonal] at hdecomp
  have hsplit : onTriples y (fun u v t => 6*s u v t+s u u 1+s v v 1+s t t 1+c/7) =
      fun i j k => 6*onTriples y s i j k+p i j+p i k+p j k+c/7 := rfl
  rw [hsplit,distinctSum_add,distinctSum_add,distinctSum_add,distinctSum_add,
    distinctSum_mul,distinctSum_pair,distinctSum_pair13,distinctSum_pair23,distinctSum_const]
  linarith

end ThomsonNegative.Geometry.GenericMoments
namespace ThomsonNegative.Geometry
open GenericMoments
theorem generic_moments_symmetry_counting (s : ℝ → ℝ → ℝ → ℝ) (c : ℝ)
    (hs12 : ∀ u v t, s u v t=s v u t) (hs23 : ∀ u v t, s u v t=s u t v)
    (hdiag : s 1 1 1=c) (y : Configuration) (hy : ∀ i, ‖y i‖=1) :
    distinctSum (onTriples y (fun u v t => 6*s u v t+s u u 1+s v v 1+s t t 1+c/7)) =
      6*tripleSum (onTriples y s) :=
  GenericMoments.repeated_triple_count s c hs12 hs23 hdiag y hy
end ThomsonNegative.Geometry

/- Source: N_S_R_bridge.lean -/

/-! Generic all-parameter proof. S/R identities adapt upstream RCounting
(commit50d14bc06bd41f61573eb6a36eedb8d00759af8f); outer products expand
the explicit proved tangent features. No fixed-exponent certificate. -/
open scoped BigOperators InnerProductSpace
open ThomsonNegative.Geometry (Configuration)
namespace ThomsonNegative.Geometry.GenericMoments
noncomputable def Rfun (k a b : ℕ) (u v t : ℝ) : ℝ :=
  6 * Sfun k a b u v t + Sfun k a b u u 1 + Sfun k a b v v 1 +
    Sfun k a b t t 1 + (if k=0 then 1 else 0)/7

theorem symEval_swap12 (f : ℝ → ℝ → ℝ → ℝ) (u v t : ℝ) :
    symEval f u v t = symEval f v u t := by unfold symEval; ring

theorem symEval_swap23 (f : ℝ → ℝ → ℝ → ℝ) (u v t : ℝ) :
    symEval f u v t = symEval f u t v := by unfold symEval; ring

theorem momentMatrix_eq_sum_Sfun (m k : ℕ) (y : Configuration) (a b : Fin m) :
    momentMatrix m k y a b = tripleSum (onTriples y (Sfun k a.val b.val)) := by
  rw [momentMatrix_entry]
  exact (tripleSum_sym y (fun u v t => u^a.val * v^b.val * kernelQ k u v t)).symm

theorem sum_Rfun_eq_moment (m k : ℕ) (y : Configuration) (hy : ∀ i, ‖y i‖=1)
    (a b : Fin m) :
    distinctSum (onTriples y (Rfun k a.val b.val)) = 6 * momentMatrix m k y a b := by
  rw [momentMatrix_eq_sum_Sfun]
  unfold Rfun
  apply repeated_triple_count
  · intro u v t
    exact symEval_swap12 _ u v t
  · intro u v t
    exact symEval_swap23 _ u v t
  · exact Sfun_diagonal k a.val b.val
  · exact hy

end ThomsonNegative.Geometry.GenericMoments
namespace ThomsonNegative.Geometry
open GenericMoments

theorem generic_moments_S_R_bridge (m k : ℕ) (y : Configuration)
    (hy : ∀ i, ‖y i‖=1) (a b : Fin m) :
    momentMatrix m k y a b = tripleSum (onTriples y (Sfun k a.val b.val)) ∧
    distinctSum (onTriples y (Rfun k a.val b.val)) = 6 * momentMatrix m k y a b := by
  exact ⟨momentMatrix_eq_sum_Sfun m k y a b, sum_Rfun_eq_moment m k y hy a b⟩
end ThomsonNegative.Geometry


/- Source: N_complex_power_gram.lean -/

/-! Clean proof port from Energy-Minimization-8-Points,
commit 50d14bc06bd41f61573eb6a36eedb8d00759af8f,
Logarithmic/Thomson8/Kernels.lean:35-40. Target Point is the supplied EuclideanSpace.
No legacy Data, certificate, or fixed-exponent target is imported. -/
open scoped BigOperators InnerProductSpace
namespace ThomsonNegative.Geometry.GenericMoments

theorem complex_power_gram (z w : ℂ) (k : ℕ) : ((z * star w) ^ k).re = (z ^ k).re * (w ^ k).re + (z ^ k).im * (w ^ k).im := by
  change ((z * (starRingEnd ℂ) w) ^ k).re = _
  rw [mul_pow, ← map_pow]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

end ThomsonNegative.Geometry.GenericMoments
namespace ThomsonNegative.Geometry
theorem generic_moments_complex_power_gram (z w : ℂ) (k : ℕ) : ((z * star w) ^ k).re = (z ^ k).re * (w ^ k).re + (z ^ k).im * (w ^ k).im :=
  GenericMoments.complex_power_gram z w k
end ThomsonNegative.Geometry


/- Source: N_inner_frame.lean -/

/-! Clean proof port from Energy-Minimization-8-Points,
commit 50d14bc06bd41f61573eb6a36eedb8d00759af8f,
Logarithmic/Thomson8/SphereFrame.lean:24-28. Target Point is the supplied EuclideanSpace.
No legacy Data, certificate, or fixed-exponent target is imported. -/
open scoped BigOperators InnerProductSpace
namespace ThomsonNegative.Geometry.GenericMoments

theorem inner_frame (b : OrthonormalBasis (Fin 3) ℝ Point) (y z : Point) : inner ℝ y z = inner ℝ (b 0) y * inner ℝ (b 0) z + inner ℝ (b 1) y * inner ℝ (b 1) z + inner ℝ (b 2) y * inner ℝ (b 2) z := by
  have h := b.sum_inner_mul_inner y z
  simpa [Fin.sum_univ_succ, real_inner_comm, add_assoc] using h.symm

end ThomsonNegative.Geometry.GenericMoments
namespace ThomsonNegative.Geometry
theorem generic_moments_inner_frame (b : OrthonormalBasis (Fin 3) ℝ Point) (y z : Point) : inner ℝ y z = inner ℝ (b 0) y * inner ℝ (b 0) z + inner ℝ (b 1) y * inner ℝ (b 1) z + inner ℝ (b 2) y * inner ℝ (b 2) z :=
  GenericMoments.inner_frame b y z
end ThomsonNegative.Geometry


/- Source: N_tangent_re.lean -/

/-! Clean generic proof port from upstream commit
50d14bc06bd41f61573eb6a36eedb8d00759af8f, Logarithmic/Thomson8.
Source declarations: SphereFrame.tangentComplex, SphereFrame.tangent_re.
Only target type aliases and explicit real symEval replace legacy interfaces. -/
open scoped BigOperators InnerProductSpace
open ThomsonNegative.Geometry (Configuration)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThomsonNegative.Geometry.GenericMoments

noncomputable def tangentComplex (b : OrthonormalBasis (Fin 3) ℝ Point) (y : Point) : ℂ :=
  ⟨⟪b 1,y⟫_ℝ,⟪b 2,y⟫_ℝ⟩

theorem tangent_re (b : OrthonormalBasis (Fin 3) ℝ Point) (y z : Point) :
    (tangentComplex b y * star (tangentComplex b z)).re =
      ⟪y,z⟫_ℝ - ⟪b 0,y⟫_ℝ * ⟪b 0,z⟫_ℝ := by
  rw [inner_frame b y z]
  simp [tangentComplex,Complex.mul_re,Complex.star_def]
  ring

end ThomsonNegative.Geometry.GenericMoments
namespace ThomsonNegative.Geometry
open GenericMoments
theorem generic_moments_tangent_re (b : OrthonormalBasis (Fin 3) ℝ Point) (y z : Point) :
    (tangentComplex b y * star (tangentComplex b z)).re =
      ⟪y,z⟫_ℝ - ⟪b 0,y⟫_ℝ * ⟪b 0,z⟫_ℝ :=
  GenericMoments.tangent_re b y z
end ThomsonNegative.Geometry

/- Source: N_tangent_normSq.lean -/

/-! Clean generic proof port from upstream commit
50d14bc06bd41f61573eb6a36eedb8d00759af8f, Logarithmic/Thomson8.
Source declarations: SphereFrame.tangent_normSq.
Only target type aliases and explicit real symEval replace legacy interfaces. -/
open scoped BigOperators InnerProductSpace
open ThomsonNegative.Geometry (Configuration)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThomsonNegative.Geometry.GenericMoments

theorem tangent_normSq (b : OrthonormalBasis (Fin 3) ℝ Point) (y : Point) (hy : ‖y‖=1) :
    Complex.normSq (tangentComplex b y) = 1-⟪b 0,y⟫_ℝ^2 := by
  have h := inner_frame b y y
  rw [real_inner_self_eq_norm_sq,hy] at h
  simp [tangentComplex,Complex.normSq_apply]
  nlinarith

end ThomsonNegative.Geometry.GenericMoments
namespace ThomsonNegative.Geometry
open GenericMoments
theorem generic_moments_tangent_normSq (b : OrthonormalBasis (Fin 3) ℝ Point) (y : Point) (hy : ‖y‖=1) :
    Complex.normSq (tangentComplex b y) = 1-⟪b 0,y⟫_ℝ^2 :=
  GenericMoments.tangent_normSq b y hy
end ThomsonNegative.Geometry

/- Source: N_frame_features.lean -/

/-! Clean generic proof port from upstream commit
50d14bc06bd41f61573eb6a36eedb8d00759af8f, Logarithmic/Thomson8.
Source declarations: SphereFrame.spherical_kernel_features.
Only target type aliases and explicit real symEval replace legacy interfaces. -/
open scoped BigOperators InnerProductSpace
open ThomsonNegative.Geometry (Configuration)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThomsonNegative.Geometry.GenericMoments

theorem spherical_kernel_features (b : OrthonormalBasis (Fin 3) ℝ Point)
    (y z : Point) (hy : ‖y‖=1) (hz : ‖z‖=1) (k : ℕ) :
    kernelQ k ⟪b 0,y⟫_ℝ ⟪b 0,z⟫_ℝ ⟪y,z⟫_ℝ =
      ((tangentComplex b y)^k).re*((tangentComplex b z)^k).re +
      ((tangentComplex b y)^k).im*((tangentComplex b z)^k).im := by
  rw [kernelQ_complex k _ _ _ (tangentComplex b y * star (tangentComplex b z))
    (tangent_re b y z)]
  · exact complex_power_gram _ _ _
  · simp [Complex.normSq_mul,Complex.star_def,Complex.normSq_conj,tangent_normSq b y hy,
      tangent_normSq b z hz]

end ThomsonNegative.Geometry.GenericMoments
namespace ThomsonNegative.Geometry
open GenericMoments
theorem generic_moments_frame_features (b : OrthonormalBasis (Fin 3) ℝ Point)
    (y z : Point) (hy : ‖y‖=1) (hz : ‖z‖=1) (k : ℕ) :
    kernelQ k ⟪b 0,y⟫_ℝ ⟪b 0,z⟫_ℝ ⟪y,z⟫_ℝ =
      ((tangentComplex b y)^k).re*((tangentComplex b z)^k).re +
      ((tangentComplex b y)^k).im*((tangentComplex b z)^k).im :=
  GenericMoments.spherical_kernel_features b y z hy hz k
end ThomsonNegative.Geometry

/- Source: N_kernelQ_swap.lean -/

/-! Clean generic proof port from upstream commit
50d14bc06bd41f61573eb6a36eedb8d00759af8f, Logarithmic/Thomson8.
Source declarations: KernelPositivity.kernelQ_swap.
Only target type aliases and explicit real symEval replace legacy interfaces. -/
open scoped BigOperators InnerProductSpace
open ThomsonNegative.Geometry (Configuration)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThomsonNegative.Geometry.GenericMoments

theorem kernelQ_swap (k : ℕ) (u v t : ℝ) : kernelQ k u v t = kernelQ k v u t := by
  induction k using Nat.twoStepInduction with
  | zero => rfl
  | one => simp [kernelQ,mul_comm]
  | more k hk hk1 => simp [kernelQ,hk,hk1,mul_comm,mul_left_comm,mul_assoc]

end ThomsonNegative.Geometry.GenericMoments
namespace ThomsonNegative.Geometry
open GenericMoments
theorem generic_moments_kernelQ_swap (k : ℕ) (u v t : ℝ) : kernelQ k u v t = kernelQ k v u t :=
  GenericMoments.kernelQ_swap k u v t
end ThomsonNegative.Geometry

/- Source: N_two_feature_square.lean -/

/-! Clean proof port from Energy-Minimization-8-Points,
commit 50d14bc06bd41f61573eb6a36eedb8d00759af8f,
Logarithmic/Thomson8/KernelPositivity.lean:8-13. Target Point is the supplied EuclideanSpace.
No legacy Data, certificate, or fixed-exponent target is imported. -/
open scoped BigOperators InnerProductSpace
namespace ThomsonNegative.Geometry.GenericMoments

theorem two_feature_square {ι : Type*} [Fintype ι] (c a b : ι → ℝ) : (∑ i, ∑ j, c i * c j * (a i * a j + b i * b j)) = (∑ i, c i * a i) ^ 2 + (∑ i, c i * b i) ^ 2 := by
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    apply Finset.sum_congr rfl <;> intro j _ <;> ring

end ThomsonNegative.Geometry.GenericMoments
namespace ThomsonNegative.Geometry
theorem generic_moments_two_feature_square {ι : Type*} [Fintype ι] (c a b : ι → ℝ) : (∑ i, ∑ j, c i * c j * (a i * a j + b i * b j)) = (∑ i, c i * a i) ^ 2 + (∑ i, c i * b i) ^ 2 :=
  GenericMoments.two_feature_square c a b
end ThomsonNegative.Geometry


/- Source: N_unit_frame.lean -/

/-! Clean proof port from Energy-Minimization-8-Points,
commit 50d14bc06bd41f61573eb6a36eedb8d00759af8f,
Logarithmic/Thomson8/SphereFrame.lean:8-19. Target Point is the supplied EuclideanSpace.
No legacy Data, certificate, or fixed-exponent target is imported. -/
open scoped BigOperators InnerProductSpace
namespace ThomsonNegative.Geometry.GenericMoments

theorem unit_frame (x : Point) (hx : ‖x‖ = 1) : ∃ b : OrthonormalBasis (Fin 3) ℝ Point, b 0 = x := by
  have hv : Orthonormal ℝ (({0} : Set (Fin 3)).restrict (fun _ => x)) := by
    constructor
    · intro i; exact hx
    · intro i j hij
      exfalso
      apply hij
      apply Subtype.ext
      exact (Set.mem_singleton_iff.mp i.property).trans
        (Set.mem_singleton_iff.mp j.property).symm
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp [Point])
  exact ⟨b, hb 0 (by simp)⟩

end ThomsonNegative.Geometry.GenericMoments
namespace ThomsonNegative.Geometry
theorem generic_moments_unit_frame (x : Point) (hx : ‖x‖ = 1) : ∃ b : OrthonormalBasis (Fin 3) ℝ Point, b 0 = x :=
  GenericMoments.unit_frame x hx
end ThomsonNegative.Geometry


/- Source: N_spherical_kernel_nonneg.lean -/

/-! Clean generic proof port from upstream commit
50d14bc06bd41f61573eb6a36eedb8d00759af8f, Logarithmic/Thomson8.
Source declarations: KernelPositivity.spherical_kernel_nonneg.
Only target type aliases and explicit real symEval replace legacy interfaces. -/
open scoped BigOperators InnerProductSpace
open ThomsonNegative.Geometry (Configuration)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThomsonNegative.Geometry.GenericMoments

theorem spherical_kernel_nonneg {ι : Type*} [Fintype ι] (x : Point) (hx : ‖x‖=1)
    (y : ι → Point) (hy : ∀ i, ‖y i‖=1) (k : ℕ) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i*c j*kernelQ k ⟪x,y i⟫_ℝ ⟪x,y j⟫_ℝ ⟪y i,y j⟫_ℝ := by
  obtain ⟨b,hb⟩ := unit_frame x hx
  simp_rw [←hb,spherical_kernel_features b _ _ (hy _) (hy _)]
  rw [two_feature_square]
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

end ThomsonNegative.Geometry.GenericMoments
namespace ThomsonNegative.Geometry
open GenericMoments
theorem generic_moments_spherical_kernel_nonneg {ι : Type*} [Fintype ι] (x : Point) (hx : ‖x‖=1)
    (y : ι → Point) (hy : ∀ i, ‖y i‖=1) (k : ℕ) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i*c j*kernelQ k ⟪x,y i⟫_ℝ ⟪x,y j⟫_ℝ ⟪y i,y j⟫_ℝ :=
  GenericMoments.spherical_kernel_nonneg x hx y hy k c
end ThomsonNegative.Geometry

/- Source: N_spherical_kernel_psd.lean -/

/-! Clean generic proof port from upstream commit
50d14bc06bd41f61573eb6a36eedb8d00759af8f, Logarithmic/Thomson8.
Source declarations: KernelPositivity.sphericalKernel_symmetric, KernelPositivity.sphericalKernel_posSemidef.
Only target type aliases and explicit real symEval replace legacy interfaces. -/
open scoped BigOperators InnerProductSpace
open ThomsonNegative.Geometry (Configuration)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThomsonNegative.Geometry.GenericMoments

theorem sphericalKernel_symmetric {ι : Type*} (x : Point) (y : ι → Point) (k : ℕ) :
    (sphericalKernel x y k).IsHermitian := by
  ext i j
  simp only [sphericalKernel,Matrix.conjTranspose_apply,star_trivial]
  rw [real_inner_comm (y j) (y i),kernelQ_swap]

theorem sphericalKernel_posSemidef {ι : Type*} [Fintype ι] (x : Point) (hx : ‖x‖=1)
    (y : ι → Point) (hy : ∀ i, ‖y i‖=1) (k : ℕ) :
    (sphericalKernel x y k).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (sphericalKernel_symmetric x y k)
  intro c
  simpa only [sphericalKernel,Matrix.mulVec,dotProduct,star_trivial,Finset.mul_sum,
    mul_assoc,mul_comm,mul_left_comm] using spherical_kernel_nonneg x hx y hy k c

end ThomsonNegative.Geometry.GenericMoments
namespace ThomsonNegative.Geometry
open GenericMoments
theorem generic_moments_spherical_kernel_psd {ι : Type*} [Fintype ι] (x : Point) (hx : ‖x‖=1)
    (y : ι → Point) (hy : ∀ i, ‖y i‖=1) (k : ℕ) :
    (sphericalKernel x y k).PosSemidef :=
  GenericMoments.sphericalKernel_posSemidef x hx y hy k
end ThomsonNegative.Geometry

/- Source: N_matrix_psd.lean -/

/-! Clean generic proof port from upstream commit
50d14bc06bd41f61573eb6a36eedb8d00759af8f, Logarithmic/Thomson8.
Source declarations: MomentMatrices.momentMatrix_posSemidef.
Only target type aliases and explicit real symEval replace legacy interfaces. -/
open scoped BigOperators InnerProductSpace
open ThomsonNegative.Geometry (Configuration)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThomsonNegative.Geometry.GenericMoments

theorem momentMatrix_posSemidef (m k : ℕ) (y : Configuration) (hy : ∀ i, ‖y i‖=1) :
    (momentMatrix m k y).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro i _
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (sphericalKernel_posSemidef (y i) (hy i) y hy k).mul_mul_conjTranspose_same
      (powerFeatures m (y i) y)

end ThomsonNegative.Geometry.GenericMoments
namespace ThomsonNegative.Geometry
open GenericMoments
theorem generic_moments_matrix_psd (m k : ℕ) (y : Configuration) (hy : ∀ i, ‖y i‖=1) :
    (momentMatrix m k y).PosSemidef :=
  GenericMoments.momentMatrix_posSemidef m k y hy
end ThomsonNegative.Geometry

/- Source: N_outer_product_identity.lean -/

/-! Generic all-parameter proof. S/R identities adapt upstream RCounting
(commit50d14bc06bd41f61573eb6a36eedb8d00759af8f); outer products expand
the explicit proved tangent features. No fixed-exponent certificate. -/
open scoped BigOperators InnerProductSpace
open ThomsonNegative.Geometry (Configuration)
namespace ThomsonNegative.Geometry.GenericMoments
noncomputable def realFeature (m k : ℕ) (y : Configuration)
    (b : Index → OrthonormalBasis (Fin 3) ℝ Point) (i : Index) (a : Fin m) : ℝ :=
  ∑ j : Index, (inner ℝ (y i) (y j)) ^ a.val * ((tangentComplex (b i) (y j)) ^ k).re

noncomputable def imagFeature (m k : ℕ) (y : Configuration)
    (b : Index → OrthonormalBasis (Fin 3) ℝ Point) (i : Index) (a : Fin m) : ℝ :=
  ∑ j : Index, (inner ℝ (y i) (y j)) ^ a.val * ((tangentComplex (b i) (y j)) ^ k).im

theorem momentMatrix_outer_products (m k : ℕ) (y : Configuration)
    (hy : ∀ i, ‖y i‖=1) (b : Index → OrthonormalBasis (Fin 3) ℝ Point)
    (hb : ∀ i, b i 0 = y i) :
    momentMatrix m k y = ∑ i : Index, (fun a c =>
      realFeature m k y b i a * realFeature m k y b i c +
      imagFeature m k y b i a * imagFeature m k y b i c) := by
  ext a c
  rw [momentMatrix_entry]
  simp only [tripleSum, onTriples, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hf (j l : Index) :
      kernelQ k (inner ℝ (y i) (y j)) (inner ℝ (y i) (y l)) (inner ℝ (y j) (y l)) =
      ((tangentComplex (b i) (y j))^k).re * ((tangentComplex (b i) (y l))^k).re +
      ((tangentComplex (b i) (y j))^k).im * ((tangentComplex (b i) (y l))^k).im := by
    simpa only [hb i] using spherical_kernel_features (b i) (y j) (y l) (hy j) (hy l) k
  simp_rw [hf]
  simp only [realFeature, imagFeature, mul_add, Finset.sum_add_distrib,
    Finset.sum_mul, Finset.mul_sum]
  congr 1 <;> rw [Finset.sum_comm] <;> apply Finset.sum_congr rfl <;> intro j _ <;>
    apply Finset.sum_congr rfl <;> intro l _ <;> ring

theorem momentMatrix_exists_outer_products (m k : ℕ) (y : Configuration)
    (hy : ∀ i, ‖y i‖=1) :
    ∃ v w : Index → Fin m → ℝ,
      momentMatrix m k y = ∑ i : Index, (fun a c => v i a * v i c + w i a * w i c) := by
  classical
  let b : Index → OrthonormalBasis (Fin 3) ℝ Point :=
    fun i => Classical.choose (unit_frame (y i) (hy i))
  have hb (i : Index) : b i 0 = y i := Classical.choose_spec (unit_frame (y i) (hy i))
  exact ⟨realFeature m k y b, imagFeature m k y b,
    momentMatrix_outer_products m k y hy b hb⟩

end ThomsonNegative.Geometry.GenericMoments
namespace ThomsonNegative.Geometry
open GenericMoments

theorem generic_moments_outer_product_identity (m k : ℕ) (y : Configuration)
    (hy : ∀ i, ‖y i‖=1) :
    ∃ v w : Fin 8 → Fin m → ℝ,
      momentMatrix m k y = ∑ i : Fin 8, (fun a c => v i a * v i c + w i a * w i c) :=
  momentMatrix_exists_outer_products m k y hy
end ThomsonNegative.Geometry


/- Source: N_generic_moments.lean -/

open scoped BigOperators
namespace ThomsonNegative.Geometry.GenericMoments
open ThomsonNegative.Geometry (Configuration)

/-- Complete generic moment contract, including equality-use outer products. -/
def GenericMomentContract : Prop :=
  ∀ (m k : ℕ) (y : Configuration), (∀ i, ‖y i‖ = 1) →
    (momentMatrix m k y).PosSemidef ∧
    (∃ v w : Fin 8 → Fin m → ℝ,
      momentMatrix m k y = ∑ i : Fin 8, (fun a c => v i a * v i c + w i a * w i c)) ∧
    (∀ a b : Fin m,
      momentMatrix m k y a b = tripleSum (onTriples y (Sfun k a.val b.val)) ∧
      distinctSum (onTriples y (Rfun k a.val b.val)) = 6 * momentMatrix m k y a b)

theorem generic_moment_soundness : GenericMomentContract := by
  intro m k y hy
  exact ⟨momentMatrix_posSemidef m k y hy,
    momentMatrix_exists_outer_products m k y hy,
    fun a b => ⟨momentMatrix_eq_sum_Sfun m k y a b,
      sum_Rfun_eq_moment m k y hy a b⟩⟩

end ThomsonNegative.Geometry.GenericMoments
#print axioms ThomsonNegative.Geometry.GenericMoments.generic_moment_soundness
