import Coulomb8.SOSPositivity

namespace Coulomb8
open scoped BigOperators

theorem old_S_symmetric (k i j : ℕ) (u v t : ℝ) :
    (Thomson8.Block.S k i j).eval u v t=(Thomson8.Block.S k j i).eval u v t := by
  simp only [Thomson8.S_eval,Thomson8.Poly.symEval]
  rw [Thomson8.kernelQ_swap k v u t,Thomson8.kernelQ_swap k t u v,
    Thomson8.kernelQ_swap k t v u]
  ring

theorem R_symmetric (k i j : ℕ) (u v t : ℝ) :
    (Block.R k i j).eval u v t=(Block.R k j i).eval u v t := by
  simp only [R_eval_bridge,Thomson8.R_eval]
  rw [old_S_symmetric k i j u v t,old_S_symmetric k i j u u 1,
    old_S_symmetric k i j v v 1,old_S_symmetric k i j t t 1]

theorem Block.column_symmetric (b : Block) (i j : ℕ) (u v t : ℝ) :
    (b.column i j).eval u v t=(b.column j i).eval u v t := by
  cases hm : b.moment
  · rw [sos_column_eval b hm,sos_column_eval b hm]
    congr 1
    funext u v t
    ring
  · rw [moment_column_eval b hm,moment_column_eval b hm,Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro c hc
    rw [R_symmetric b.k c a]
    ring

end Coulomb8

#print axioms Coulomb8.Block.column_symmetric
