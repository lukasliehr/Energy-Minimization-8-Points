import Coulomb8.NodeArithmetic

set_option maxHeartbeats 0

namespace Coulomb8
open Thomson8

def nodeBox : Fin 4 → Box := ![NodeArithmetic.b0,NodeArithmetic.b6,NodeArithmetic.b11,NodeArithmetic.b13]

theorem nodeBox_contains (i : Fin 4) : (nodeBox i).Contains (nodes a i) := by
  fin_cases i
  · change NodeArithmetic.b0.Contains _
    convert NodeArithmetic.h0 using 1
    norm_num [nodes,nodeA,nodeB,nodeC,nodeD,q,NodeArithmetic.v0,NodeArithmetic.v1,NodeArithmetic.v2,NodeArithmetic.v3,NodeArithmetic.v4,NodeArithmetic.v5,NodeArithmetic.v6,NodeArithmetic.v7,NodeArithmetic.v8,NodeArithmetic.v9,NodeArithmetic.v10,NodeArithmetic.v11,NodeArithmetic.v12,NodeArithmetic.v13,div_eq_mul_inv] <;> ring_nf
  · change NodeArithmetic.b6.Contains _
    convert NodeArithmetic.h6 using 1
    norm_num [nodes,nodeA,nodeB,nodeC,nodeD,q,NodeArithmetic.v0,NodeArithmetic.v1,NodeArithmetic.v2,NodeArithmetic.v3,NodeArithmetic.v4,NodeArithmetic.v5,NodeArithmetic.v6,NodeArithmetic.v7,NodeArithmetic.v8,NodeArithmetic.v9,NodeArithmetic.v10,NodeArithmetic.v11,NodeArithmetic.v12,NodeArithmetic.v13,div_eq_mul_inv] <;> ring_nf
  · change NodeArithmetic.b11.Contains _
    convert NodeArithmetic.h11 using 1
    norm_num [nodes,nodeA,nodeB,nodeC,nodeD,q,NodeArithmetic.v0,NodeArithmetic.v1,NodeArithmetic.v2,NodeArithmetic.v3,NodeArithmetic.v4,NodeArithmetic.v5,NodeArithmetic.v6,NodeArithmetic.v7,NodeArithmetic.v8,NodeArithmetic.v9,NodeArithmetic.v10,NodeArithmetic.v11,NodeArithmetic.v12,NodeArithmetic.v13,div_eq_mul_inv] <;> ring_nf
  · change NodeArithmetic.b13.Contains _
    convert NodeArithmetic.h13 using 1
    norm_num [nodes,nodeA,nodeB,nodeC,nodeD,q,NodeArithmetic.v0,NodeArithmetic.v1,NodeArithmetic.v2,NodeArithmetic.v3,NodeArithmetic.v4,NodeArithmetic.v5,NodeArithmetic.v6,NodeArithmetic.v7,NodeArithmetic.v8,NodeArithmetic.v9,NodeArithmetic.v10,NodeArithmetic.v11,NodeArithmetic.v12,NodeArithmetic.v13,div_eq_mul_inv] <;> ring_nf

theorem nodes_interior (i : Fin 4) : -1 < nodes a i ∧ nodes a i < 1 := by
  have hb : (-1 : ℚ) < (nodeBox i).lo ∧ (nodeBox i).hi < 1 := by
    fin_cases i <;> decide +kernel
  have h := nodeBox_contains i
  constructor
  · have hl : (-1 : ℝ) < (nodeBox i).lo := by exact_mod_cast hb.1
    exact hl.trans_le h.1
  · have hu : ((nodeBox i).hi : ℝ) < 1 := by exact_mod_cast hb.2
    exact h.2.trans_lt hu

theorem node_difference_check (i j : Fin 4) (hij : i ≠ j) :
    (Box.sub (nodeBox i) (nodeBox j)).separated := by
  fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel

theorem nodes_injective : Function.Injective (nodes a) := by
  intro i j h
  by_contra hij
  have hn := Box.nonzero_of_contains (Box.contains_sub (nodeBox_contains i) (nodeBox_contains j))
    (node_difference_check i j hij)
  exact hn (sub_eq_zero.mpr h)

theorem node_sum_check (i j : Fin 4) :
    (Box.add (nodeBox i) (nodeBox j)).separated := by
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem nodes_no_opposites (i j : Fin 4) : nodes a i+nodes a j ≠ 0 :=
  Box.nonzero_of_contains (Box.contains_add (nodeBox_contains i) (nodeBox_contains j))
    (node_sum_check i j)

end Coulomb8

#print axioms Coulomb8.nodes_interior
#print axioms Coulomb8.nodes_injective
#print axioms Coulomb8.nodes_no_opposites
