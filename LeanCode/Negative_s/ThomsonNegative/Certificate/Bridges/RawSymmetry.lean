import ThomsonNegative.Certificate.Bridges.RawMoment

noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
open ThomsonNegative.Geometry.GenericMoments

lemma kernelS_index_symm (k i j : Nat) (u v t : ℝ) : Sfun k i j u v t=Sfun k j i u v t := by
  simp only [Sfun,symEval]
  rw [kernelQ_swap k v u t,kernelQ_swap k t u v,kernelQ_swap k t v u]
  ring

lemma kernelRPolynomial_index_symm (k i j : Nat) : kernelRPolynomial k i j=kernelRPolynomial k j i := by
  apply MvPolynomial.funext
  intro x
  simp only [kernelRPolynomial_eval,Rfun,kernelS_index_symm k i j]

lemma rawPlusPolynomial_symm (i j : Fin 16) : rawPlusPolynomial i j=rawPlusPolynomial j i := by
  unfold rawPlusPolynomial
  rw [mul_comm]

lemma rawStandardPolynomial_symm (i j : Fin 18) : rawStandardPolynomial i j=rawStandardPolynomial j i := by
  unfold rawStandardPolynomial
  congr 1
  ring

end ThomsonNegative.Certificate.Bridges
