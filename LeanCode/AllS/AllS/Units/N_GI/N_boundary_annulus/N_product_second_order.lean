import Mathlib

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem product_one_add_second_order {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (u : ι → ℝ) (hu : ∀i∈s,0≤u i) :
    1+(∑i∈s,u i)+((∑i∈s,u i)^2-(∑i∈s,(u i)^2))/2≤ s.prod (fun i=>1+u i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hua : 0≤u a := hu a (Finset.mem_insert_self _ _)
    have hus : ∀i∈s,0≤u i := fun i hi=>hu i (Finset.mem_insert_of_mem hi)
    have hi := ih hus
    have hq := Finset.sum_sq_le_sq_sum_of_nonneg hus
    have hm := mul_le_mul_of_nonneg_left hi (by linarith : 0≤1+u a)
    have hrem := mul_nonneg hua (sub_nonneg.mpr hq)
    simp only [Finset.sum_insert ha,Finset.prod_insert ha]
    nlinarith [hm,hrem]

#print axioms product_one_add_second_order
end Blueprint.Thomson.Tail.Implementation
