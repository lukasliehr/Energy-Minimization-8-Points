import ThomsonNegative.Certificate.MatrixCellSound

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Finalization
open ThomsonNegative.Certificate

def factorSquare (n : Nat) (F : FactorData) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => F.square i.val j.val

def gramValueMatrix (n degree count : Nat) (K : FactorData) (F : Nat → FactorData)
    (t : ℝ) : Matrix (Fin n) (Fin n) ℝ := fun i j => gramValue degree count K F t i.val j.val

lemma factorSquare_eq_matrix (n : Nat) (F : FactorData) (hF : F.order=n) :
    factorSquare n F=F.matrix n*(F.matrix n).transpose := by
  ext i j
  simp only [factorSquare,FactorData.square,hF,Matrix.mul_apply,Matrix.transpose_apply,
    FactorData.matrix]
  exact (Fin.sum_univ_eq_sum_range (fun k => F.eval i.val k*F.eval j.val k) n).symm

lemma gramValue_split (n degree count : Nat) (K : FactorData) (F : Nat → FactorData)
    (t : ℝ) (hK : K.order=n) :
    gramValueMatrix n degree count K F t=
      (1/2:ℝ) • (K.matrix n*(K.matrix n).transpose)+
        ∑ r ∈ Finset.range count,bernsteinWeight degree r t • factorSquare n (F r) := by
  rw [← factorSquare_eq_matrix n K hK]
  ext i j
  simp [gramValueMatrix,gramValue,factorSquare,Matrix.smul_apply,Matrix.add_apply,Matrix.sum_apply,smul_eq_mul]

lemma bernstein_remainder_psd (n degree count : Nat) (F : Nat → FactorData)
    (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    (∑ r ∈ Finset.range count,bernsteinWeight degree r t • factorSquare n (F r)).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro r hr
  exact (factor_square_psd n (F r)).smul (Reduction.bernstein_weight_nonneg degree r t ht)

theorem floor_correction_posDef {n : Nat} (K J Δ : Matrix (Fin n) (Fin n) ℝ)
    (hKJ : K*J=1) (hΔ : ∀i j,Δ i j=Δ j i)
    (w : Fin n → ℝ) (hw : ∀i,0<w i)
    (hrow : ∀i,∑ j,|(J*Δ*J.transpose) i j| *w j/w i≤(1/3:ℝ)) :
    ((1/2:ℝ) • (K*K.transpose)+Δ).PosDef := by
  have h := Reduction.corrected_block_of_inverse (r := 0) (k := 0) K J Δ hKJ hΔ w hw
    (1/3) (1/2) hrow (by norm_num) (fun _ : Fin 0 => 0)
    (fun i => Fin.elim0 i) (fun i : Fin 0 => Fin.elim0 i)
  simpa using h

theorem gramValue_correction_posDef {n degree count : Nat} (K J : FactorData)
    (F : Nat → FactorData) (Δ : Matrix (Fin n) (Fin n) ℝ)
    (hK : K.order=n) (hKJ : K.matrix n*J.matrix n=1)
    (hΔ : ∀i j,Δ i j=Δ j i) (w : Fin n → ℝ) (hw : ∀i,0<w i)
    (hrow : ∀i,∑ j,|(J.matrix n*Δ*(J.matrix n).transpose) i j| *w j/w i≤(1/3:ℝ))
    (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    (gramValueMatrix n degree count K F t+Δ).PosDef := by
  have hf := floor_correction_posDef (K.matrix n) (J.matrix n) Δ hKJ hΔ w hw hrow
  have hp := hf.posSemidef_add (bernstein_remainder_psd n degree count F t ht)
  rw [gramValue_split n degree count K F t hK]
  convert hp using 1
  abel

#print axioms gramValue_correction_posDef
end ThomsonNegative.Finalization
