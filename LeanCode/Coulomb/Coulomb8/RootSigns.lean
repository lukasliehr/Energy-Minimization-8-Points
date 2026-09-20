import Coulomb8.RootArithmetic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8
open Thomson8

theorem F_left_enclosed : RootArithmetic.b34.Contains (F (leftEndpoint : ℝ)) := by
  convert RootArithmetic.h34 using 1
  norm_num [F,dMinus,dPlus,q,leftEndpoint,RootArithmetic.v0,RootArithmetic.v1,RootArithmetic.v2,RootArithmetic.v3,RootArithmetic.v4,RootArithmetic.v5,RootArithmetic.v6,RootArithmetic.v7,RootArithmetic.v8,RootArithmetic.v9,RootArithmetic.v10,RootArithmetic.v11,RootArithmetic.v12,RootArithmetic.v13,RootArithmetic.v14,RootArithmetic.v15,RootArithmetic.v16,RootArithmetic.v17,RootArithmetic.v18,RootArithmetic.v19,RootArithmetic.v20,RootArithmetic.v21,RootArithmetic.v22,RootArithmetic.v23,RootArithmetic.v24,RootArithmetic.v25,RootArithmetic.v26,RootArithmetic.v27,RootArithmetic.v28,RootArithmetic.v29,RootArithmetic.v30,RootArithmetic.v31,RootArithmetic.v32,RootArithmetic.v33,RootArithmetic.v34,RootArithmetic.v35,RootArithmetic.v36,RootArithmetic.v37,RootArithmetic.v38,RootArithmetic.v39,RootArithmetic.v40,RootArithmetic.v41,RootArithmetic.v42,RootArithmetic.v43,RootArithmetic.v44,RootArithmetic.v45,RootArithmetic.v46,RootArithmetic.v47,RootArithmetic.v48,RootArithmetic.v49,RootArithmetic.v50,RootArithmetic.v51,RootArithmetic.v52,RootArithmetic.v53,RootArithmetic.v54,RootArithmetic.v55,RootArithmetic.v56,div_eq_mul_inv] <;> ring_nf

theorem F_right_enclosed : RootArithmetic.b56.Contains (F (rightEndpoint : ℝ)) := by
  convert RootArithmetic.h56 using 1
  norm_num [F,dMinus,dPlus,q,rightEndpoint,RootArithmetic.v0,RootArithmetic.v1,RootArithmetic.v2,RootArithmetic.v3,RootArithmetic.v4,RootArithmetic.v5,RootArithmetic.v6,RootArithmetic.v7,RootArithmetic.v8,RootArithmetic.v9,RootArithmetic.v10,RootArithmetic.v11,RootArithmetic.v12,RootArithmetic.v13,RootArithmetic.v14,RootArithmetic.v15,RootArithmetic.v16,RootArithmetic.v17,RootArithmetic.v18,RootArithmetic.v19,RootArithmetic.v20,RootArithmetic.v21,RootArithmetic.v22,RootArithmetic.v23,RootArithmetic.v24,RootArithmetic.v25,RootArithmetic.v26,RootArithmetic.v27,RootArithmetic.v28,RootArithmetic.v29,RootArithmetic.v30,RootArithmetic.v31,RootArithmetic.v32,RootArithmetic.v33,RootArithmetic.v34,RootArithmetic.v35,RootArithmetic.v36,RootArithmetic.v37,RootArithmetic.v38,RootArithmetic.v39,RootArithmetic.v40,RootArithmetic.v41,RootArithmetic.v42,RootArithmetic.v43,RootArithmetic.v44,RootArithmetic.v45,RootArithmetic.v46,RootArithmetic.v47,RootArithmetic.v48,RootArithmetic.v49,RootArithmetic.v50,RootArithmetic.v51,RootArithmetic.v52,RootArithmetic.v53,RootArithmetic.v54,RootArithmetic.v55,RootArithmetic.v56,div_eq_mul_inv] <;> ring_nf

theorem F_left_negative : F (leftEndpoint : ℝ) < 0 :=
  Box.negative_of_contains F_left_enclosed (by decide +kernel)
theorem F_right_positive : 0 < F (rightEndpoint : ℝ) :=
  Box.positive_of_contains F_right_enclosed (by decide +kernel)

end Coulomb8

#print axioms Coulomb8.F_left_negative
#print axioms Coulomb8.F_right_positive
