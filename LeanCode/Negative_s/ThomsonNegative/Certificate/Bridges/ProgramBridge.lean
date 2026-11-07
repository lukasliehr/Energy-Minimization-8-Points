import ThomsonNegative.Certificate.ProgramSound
import ThomsonNegative.Certificate.Bridges.RawBridge
import ThomsonNegative.Certificate.Bridges.TargetCoordinates

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
open ThomsonNegative.Geometry
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

lemma rawSize_layout (b : Block) : RawData.size b.val=rawSize b := by fin_cases b <;> rfl
lemma freeSize_layout (b : Block) : BasisLayout.freeOrder b.val=blockSize b := by fin_cases b <;> rfl
lemma fullRow_layout (r : Fin 68) : BasisLayout.fullRow r.val=(chartIndex r).val := by fin_cases r <;> rfl

lemma matrix_contraction_comm {m n : Nat} (B : Matrix (Fin m) (Fin n) ℝ)
    (W : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin m) (Fin m) ℝ) :
    (∑ r, ∑ s, C r s*(∑ j, (∑ i,B r i*W i j)*B s j))=
      ∑ i, ∑ j,W i j*∑ r, ∑ s,B r i*B s j*C r s := by
  calc
    _ = ∑ r, ∑ s, ∑ i, ∑ j,W i j*(B r i*B s j*C r s) := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro s hs
      simp_rw [Finset.mul_sum,Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ r, ∑ i, ∑ s, ∑ j,W i j*(B r i*B s j*C r s) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ r, ∑ s, ∑ j,W i j*(B r i*B s j*C r s) := by rw [Finset.sum_comm]
    _ = ∑ i, ∑ r, ∑ j, ∑ s,W i j*(B r i*B s j*C r s) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_comm]
    _ = ∑ i, ∑ j, ∑ r, ∑ s,W i j*(B r i*B s j*C r s) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = _ := by simp only [Finset.mul_sum]

theorem imageFunction_block (a : ℝ → ℝ) (W : ℝ → GramFamily)
    (g : Nat → Nat → Nat → ℝ → ℝ)
    (hg : ∀ (b : Block) (i j : Fin (blockSize b)) t,g b.val i.val j.val t=W t b i j)
    (b : Block) (r : Fin 68) (t : ℝ) :
    imageFunction b.val r.val (basisFunction a b.val) (g b.val) t=
      ∑ i, ∑ j,W t b i j*mixedCoefficient (sourceBasis.eval (a t)) b i j (chartIndex r) := by
  unfold imageFunction multiplyFunction
  rw [rawSize_layout,freeSize_layout,fullRow_layout]
  simp only [← Fin.sum_univ_eq_sum_range]
  simp only [basisFunction,← blockBasis_encoded_entry,hg]
  change (∑ u : Fin (rawSize b),∑ v : Fin (rawSize b),
    rawCoefficient b (chartIndex r) u v *
      (∑ j : Fin (blockSize b),(∑ i : Fin (blockSize b),
        blockBasis (sourceBasis.eval (a t)) b u i*W t b i j)*
        blockBasis (sourceBasis.eval (a t)) b v j))=_
  erw [matrix_contraction_comm]
  simp only [mixedCoefficient,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,rawCoefficientVector]

theorem imageFunction_sum (a : ℝ → ℝ) (W : ℝ → GramFamily)
    (g : Nat → Nat → Nat → ℝ → ℝ)
    (hg : ∀ (b : Block) (i j : Fin (blockSize b)) t,g b.val i.val j.val t=W t b i j)
    (r : Fin 68) (t : ℝ) :
    (∑ b ∈ Finset.range 8,imageFunction b r.val (basisFunction a b) (g b) t)=
      retain (coefficientMap (a t) (W t)) r := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp_rw [imageFunction_block a W g hg]
  rfl

def targetNumerator (r : Fin 68) : Int :=
  signedNumerator ((TargetData.entry r.val).2.1,(TargetData.entry r.val).2.2,3)

lemma targetPower_row : ∀ (n : Fin 8) (r : Fin 68),
    sparseCoefficient (targetPowerEntry n) (chartIndex r)=
      if n.val=(TargetData.entry r.val).1 then targetNumerator r else 0 := by decide +kernel

theorem targetFunction_retained (H : Polynomial ℝ) (e : ℝ) (r : Fin 68) (t : ℝ) :
    targetFunction (fun n _ => H.coeff n) r.val t=retain (targetCoefficients H e) r := by
  have hn : chartIndex r≠0 := chartIndex_ne_zero r
  simp only [targetFunction,qval_signedNumerator]
  change (targetNumerator r:ℝ)/3*H.coeff (TargetData.entry r.val).1=_
  simp only [retain,targetCoefficients,Pi.sub_apply,Pi.smul_apply,Finset.sum_apply,
    smul_eq_mul,targetPowerVector,targetPower_row,Int.cast_ite,Int.cast_zero]
  simp only [Pi.single_apply,hn,if_false,mul_zero,sub_zero]
  by_cases hz : (TargetData.entry r.val).2.2=0
  · have hc : targetNumerator r=0 := by simp [targetNumerator,signedNumerator,hz]
    simp [hc]
  · have hd := target_degree_lt r.val r.isLt hz
    have he (n : Fin 8) : (n.val=(TargetData.entry r.val).1) ↔ n=⟨_,hd⟩ := by
      constructor
      · intro h; exact Fin.ext h
      · intro h; exact congrArg Fin.val h
    simp only [he,ite_mul,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    ring

theorem targetFunction_physical (H : Polynomial ℝ) (hH : H.degree<8) (e : ℝ) :
    physicalSynthesize (targetCoefficients H e)=centeredPolynomial H e ∧
    ∀ r : Fin 68, targetFunction (fun n _ => H.coeff n) r.val 0=
      retain (targetCoefficients H e) r :=
  ⟨targetCoefficients_physical H hH e,fun r => targetFunction_retained H e r 0⟩

theorem residualFunction_retained (a e : ℝ → ℝ) (H : ℝ → Polynomial ℝ)
    (W : ℝ → GramFamily) (g : Nat → Nat → Nat → ℝ → ℝ)
    (hg : ∀ (b : Block) (i j : Fin (blockSize b)) t,g b.val i.val j.val t=W t b i j)
    (r : Fin 68) (t : ℝ) :
    targetFunction (fun n t => (H t).coeff n) r.val t-
        (∑ b ∈ Finset.range 8,imageFunction b r.val (basisFunction a b) (g b) t)=
      retain (targetCoefficients (H t) (e t)-coefficientMap (a t) (W t)) r := by
  change targetFunction (fun n _ => (H t).coeff n) r.val t-_= _
  rw [targetFunction_retained (H t) (e t),imageFunction_sum a W g hg]
  rfl

#print axioms imageFunction_sum
#print axioms targetFunction_retained
#print axioms residualFunction_retained
end ThomsonNegative.Certificate.Bridges
