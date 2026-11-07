import AllS.Units.N_F.N_definitions

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite

def StandardMetricContract : Prop := ∀ x y : Fin 3 → ℝ,
  (∑ i,x i)=0 → (∑ i,y i)=0 →
  x 0*y 0+(x 1-x 2)*(y 1-y 2)/3 = (2/3 : ℝ)*∑ i,x i*y i

theorem kernels_standard_metric : StandardMetricContract := by
  intro x y hx hy
  simp [Fin.sum_univ_succ] at hx hy ⊢
  have hx2 : x 2 = -x 0-x 1 := by simpa using (show x 2 = -x 0-x 1 by linarith [hx])
  have hy2 : y 2 = -y 0-y 1 := by simpa using (show y 2 = -y 0-y 1 by linarith [hy])
  rw [hx2,hy2]
  ring

#check kernels_standard_metric
#print axioms kernels_standard_metric
#check StandardMetricContract
#print axioms StandardMetricContract
end Blueprint.Thomson.Finite
