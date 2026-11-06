import ThomsonNegative.Certificate.Correction.q01.LayoutSound
import ThomsonNegative.Certificate.Correction.q03.LayoutSound
import ThomsonNegative.Certificate.Correction.q05.LayoutSound
import ThomsonNegative.Certificate.Correction.q07.LayoutSound
import ThomsonNegative.Certificate.Correction.q09.LayoutSound
import ThomsonNegative.Certificate.Cells.q01.Metrics
import ThomsonNegative.Certificate.Cells.q03.Metrics
import ThomsonNegative.Certificate.Cells.q05.Metrics
import ThomsonNegative.Certificate.Cells.q07.Metrics
import ThomsonNegative.Certificate.Cells.q09.Metrics

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Certificate.Correction.Cells
open ThomsonNegative.Compact.Packed
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def physicalBlock (b : Fin 4) : Fin 8 := match b.val with
  | 0 => 0
  | 1 => 1
  | 2 => 6
  | _ => 7
noncomputable def residual (c : Fin 5) : ℕ → TM := match c.val with
  | 0 => Correction.q01.residual
  | 1 => Correction.q03.residual
  | 2 => Correction.q05.residual
  | 3 => Correction.q07.residual
  | 4 => Correction.q09.residual
  | _ => Correction.q01.residual
noncomputable def metric (c : Fin 5) (b : Fin 4) : FactorData := match c.val,b.val with
  | 0, 0 => ThomsonNegative.Certificate.Cells.q01.metric0
  | 0, 1 => ThomsonNegative.Certificate.Cells.q01.metric1
  | 0, 2 => ThomsonNegative.Certificate.Cells.q01.metric6
  | 0, 3 => ThomsonNegative.Certificate.Cells.q01.metric7
  | 1, 0 => ThomsonNegative.Certificate.Cells.q03.metric0
  | 1, 1 => ThomsonNegative.Certificate.Cells.q03.metric1
  | 1, 2 => ThomsonNegative.Certificate.Cells.q03.metric6
  | 1, 3 => ThomsonNegative.Certificate.Cells.q03.metric7
  | 2, 0 => ThomsonNegative.Certificate.Cells.q05.metric0
  | 2, 1 => ThomsonNegative.Certificate.Cells.q05.metric1
  | 2, 2 => ThomsonNegative.Certificate.Cells.q05.metric6
  | 2, 3 => ThomsonNegative.Certificate.Cells.q05.metric7
  | 3, 0 => ThomsonNegative.Certificate.Cells.q07.metric0
  | 3, 1 => ThomsonNegative.Certificate.Cells.q07.metric1
  | 3, 2 => ThomsonNegative.Certificate.Cells.q07.metric6
  | 3, 3 => ThomsonNegative.Certificate.Cells.q07.metric7
  | 4, 0 => ThomsonNegative.Certificate.Cells.q09.metric0
  | 4, 1 => ThomsonNegative.Certificate.Cells.q09.metric1
  | 4, 2 => ThomsonNegative.Certificate.Cells.q09.metric6
  | 4, 3 => ThomsonNegative.Certificate.Cells.q09.metric7
  | _, _ => ThomsonNegative.Certificate.Cells.q01.metric0
noncomputable def inverse (c : Fin 5) (b : Fin 4) : FactorData := match c.val,b.val with
  | 0, 0 => ThomsonNegative.Certificate.Cells.q01.inverse0
  | 0, 1 => ThomsonNegative.Certificate.Cells.q01.inverse1
  | 0, 2 => ThomsonNegative.Certificate.Cells.q01.inverse6
  | 0, 3 => ThomsonNegative.Certificate.Cells.q01.inverse7
  | 1, 0 => ThomsonNegative.Certificate.Cells.q03.inverse0
  | 1, 1 => ThomsonNegative.Certificate.Cells.q03.inverse1
  | 1, 2 => ThomsonNegative.Certificate.Cells.q03.inverse6
  | 1, 3 => ThomsonNegative.Certificate.Cells.q03.inverse7
  | 2, 0 => ThomsonNegative.Certificate.Cells.q05.inverse0
  | 2, 1 => ThomsonNegative.Certificate.Cells.q05.inverse1
  | 2, 2 => ThomsonNegative.Certificate.Cells.q05.inverse6
  | 2, 3 => ThomsonNegative.Certificate.Cells.q05.inverse7
  | 3, 0 => ThomsonNegative.Certificate.Cells.q07.inverse0
  | 3, 1 => ThomsonNegative.Certificate.Cells.q07.inverse1
  | 3, 2 => ThomsonNegative.Certificate.Cells.q07.inverse6
  | 3, 3 => ThomsonNegative.Certificate.Cells.q07.inverse7
  | 4, 0 => ThomsonNegative.Certificate.Cells.q09.inverse0
  | 4, 1 => ThomsonNegative.Certificate.Cells.q09.inverse1
  | 4, 2 => ThomsonNegative.Certificate.Cells.q09.inverse6
  | 4, 3 => ThomsonNegative.Certificate.Cells.q09.inverse7
  | _, _ => ThomsonNegative.Certificate.Cells.q01.inverse0
noncomputable def weight (c : Fin 5) (b : Fin 4) : ℕ → ℕ := match c.val,b.val with
  | 0, 0 => Correction.q01.weight0
  | 0, 1 => Correction.q01.weight1
  | 0, 2 => Correction.q01.weight6
  | 0, 3 => Correction.q01.weight7
  | 1, 0 => Correction.q03.weight0
  | 1, 1 => Correction.q03.weight1
  | 1, 2 => Correction.q03.weight6
  | 1, 3 => Correction.q03.weight7
  | 2, 0 => Correction.q05.weight0
  | 2, 1 => Correction.q05.weight1
  | 2, 2 => Correction.q05.weight6
  | 2, 3 => Correction.q05.weight7
  | 3, 0 => Correction.q07.weight0
  | 3, 1 => Correction.q07.weight1
  | 3, 2 => Correction.q07.weight6
  | 3, 3 => Correction.q07.weight7
  | 4, 0 => Correction.q09.weight0
  | 4, 1 => Correction.q09.weight1
  | 4, 2 => Correction.q09.weight6
  | 4, 3 => Correction.q09.weight7
  | _, _ => Correction.q01.weight0
def heightArgument (c : Fin 5) (t : ℝ) : ℝ := Compact.Target.ScalarCells.heightFunction c t-83/256
/-- Uniform finite-certificate interface. Every numeric premise has been
kernel checked; callers supply only the actual residual enclosure. -/
theorem certified_floor (c : Fin 5) (b : Fin 4) (f : ℝ → Fin 68 → ℝ)
    (hf : ∀ j : Fin 68,Encl sourceContext (residual c j) (fun t => f t j))
    (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    (∀ i : Fin (Source.blockSize (physicalBlock b)),0<(weight c b i:ℝ)) ∧
    (∀ i : Fin (Source.blockSize (physicalBlock b)),
      ∑ j : Fin (Source.blockSize (physicalBlock b)),
        |((inverse c b).matrix (Source.blockSize (physicalBlock b)) *
          Source.blockLinear (heightArgument c t) (physicalBlock b) (f t) *
          ((inverse c b).matrix (Source.blockSize (physicalBlock b))).transpose) i j| *
        (weight c b j:ℝ)/(weight c b i:ℝ)≤(1:ℝ)/3) := by
  fin_cases c <;> fin_cases b
  · have h := Correction.q01.correction0_floor f hf t ht
    rw [Correction.q01.correction0_shared] at h
    exact h
  · have h := Correction.q01.correction1_floor f hf t ht
    rw [Correction.q01.correction1_shared] at h
    exact h
  · have h := Correction.q01.correction6_floor f hf t ht
    rw [Correction.q01.correction6_shared] at h
    exact h
  · have h := Correction.q01.correction7_floor f hf t ht
    rw [Correction.q01.correction7_shared] at h
    exact h
  · have h := Correction.q03.correction0_floor f hf t ht
    rw [Correction.q03.correction0_shared] at h
    exact h
  · have h := Correction.q03.correction1_floor f hf t ht
    rw [Correction.q03.correction1_shared] at h
    exact h
  · have h := Correction.q03.correction6_floor f hf t ht
    rw [Correction.q03.correction6_shared] at h
    exact h
  · have h := Correction.q03.correction7_floor f hf t ht
    rw [Correction.q03.correction7_shared] at h
    exact h
  · have h := Correction.q05.correction0_floor f hf t ht
    rw [Correction.q05.correction0_shared] at h
    exact h
  · have h := Correction.q05.correction1_floor f hf t ht
    rw [Correction.q05.correction1_shared] at h
    exact h
  · have h := Correction.q05.correction6_floor f hf t ht
    rw [Correction.q05.correction6_shared] at h
    exact h
  · have h := Correction.q05.correction7_floor f hf t ht
    rw [Correction.q05.correction7_shared] at h
    exact h
  · have h := Correction.q07.correction0_floor f hf t ht
    rw [Correction.q07.correction0_shared] at h
    exact h
  · have h := Correction.q07.correction1_floor f hf t ht
    rw [Correction.q07.correction1_shared] at h
    exact h
  · have h := Correction.q07.correction6_floor f hf t ht
    rw [Correction.q07.correction6_shared] at h
    exact h
  · have h := Correction.q07.correction7_floor f hf t ht
    rw [Correction.q07.correction7_shared] at h
    exact h
  · have h := Correction.q09.correction0_floor f hf t ht
    rw [Correction.q09.correction0_shared] at h
    exact h
  · have h := Correction.q09.correction1_floor f hf t ht
    rw [Correction.q09.correction1_shared] at h
    exact h
  · have h := Correction.q09.correction6_floor f hf t ht
    rw [Correction.q09.correction6_shared] at h
    exact h
  · have h := Correction.q09.correction7_floor f hf t ht
    rw [Correction.q09.correction7_shared] at h
    exact h
theorem metric_order (c : Fin 5) (b : Fin 4) : (metric c b).order=Source.blockSize (physicalBlock b) := by
  fin_cases c <;> fin_cases b <;> rfl
theorem inverse_order (c : Fin 5) (b : Fin 4) : (inverse c b).order=Source.blockSize (physicalBlock b) := by
  fin_cases c <;> fin_cases b <;> rfl
theorem metric_inverse_gate (c : Fin 5) (b : Fin 4) :
    inverseCheck (Source.blockSize (physicalBlock b)) (metric c b) (inverse c b)=true := by
  fin_cases c <;> fin_cases b
  · have h := ThomsonNegative.Certificate.Cells.q01.metric_gate_pass
    simp only [ThomsonNegative.Certificate.Cells.q01.metricGate,Bool.and_eq_true] at h
    exact h.1.1.1
  · have h := ThomsonNegative.Certificate.Cells.q01.metric_gate_pass
    simp only [ThomsonNegative.Certificate.Cells.q01.metricGate,Bool.and_eq_true] at h
    exact h.1.1.2
  · have h := ThomsonNegative.Certificate.Cells.q01.metric_gate_pass
    simp only [ThomsonNegative.Certificate.Cells.q01.metricGate,Bool.and_eq_true] at h
    exact h.1.2
  · have h := ThomsonNegative.Certificate.Cells.q01.metric_gate_pass
    simp only [ThomsonNegative.Certificate.Cells.q01.metricGate,Bool.and_eq_true] at h
    exact h.2
  · have h := ThomsonNegative.Certificate.Cells.q03.metric_gate_pass
    simp only [ThomsonNegative.Certificate.Cells.q03.metricGate,Bool.and_eq_true] at h
    exact h.1.1.1
  · have h := ThomsonNegative.Certificate.Cells.q03.metric_gate_pass
    simp only [ThomsonNegative.Certificate.Cells.q03.metricGate,Bool.and_eq_true] at h
    exact h.1.1.2
  · have h := ThomsonNegative.Certificate.Cells.q03.metric_gate_pass
    simp only [ThomsonNegative.Certificate.Cells.q03.metricGate,Bool.and_eq_true] at h
    exact h.1.2
  · have h := ThomsonNegative.Certificate.Cells.q03.metric_gate_pass
    simp only [ThomsonNegative.Certificate.Cells.q03.metricGate,Bool.and_eq_true] at h
    exact h.2
  · have h := ThomsonNegative.Certificate.Cells.q05.metric_gate_pass
    simp only [ThomsonNegative.Certificate.Cells.q05.metricGate,Bool.and_eq_true] at h
    exact h.1.1.1
  · have h := ThomsonNegative.Certificate.Cells.q05.metric_gate_pass
    simp only [ThomsonNegative.Certificate.Cells.q05.metricGate,Bool.and_eq_true] at h
    exact h.1.1.2
  · have h := ThomsonNegative.Certificate.Cells.q05.metric_gate_pass
    simp only [ThomsonNegative.Certificate.Cells.q05.metricGate,Bool.and_eq_true] at h
    exact h.1.2
  · have h := ThomsonNegative.Certificate.Cells.q05.metric_gate_pass
    simp only [ThomsonNegative.Certificate.Cells.q05.metricGate,Bool.and_eq_true] at h
    exact h.2
  · have h := ThomsonNegative.Certificate.Cells.q07.metric_gate_pass
    simp only [ThomsonNegative.Certificate.Cells.q07.metricGate,Bool.and_eq_true] at h
    exact h.1.1.1
  · have h := ThomsonNegative.Certificate.Cells.q07.metric_gate_pass
    simp only [ThomsonNegative.Certificate.Cells.q07.metricGate,Bool.and_eq_true] at h
    exact h.1.1.2
  · have h := ThomsonNegative.Certificate.Cells.q07.metric_gate_pass
    simp only [ThomsonNegative.Certificate.Cells.q07.metricGate,Bool.and_eq_true] at h
    exact h.1.2
  · have h := ThomsonNegative.Certificate.Cells.q07.metric_gate_pass
    simp only [ThomsonNegative.Certificate.Cells.q07.metricGate,Bool.and_eq_true] at h
    exact h.2
  · have h := ThomsonNegative.Certificate.Cells.q09.metric_gate_pass
    simp only [ThomsonNegative.Certificate.Cells.q09.metricGate,Bool.and_eq_true] at h
    exact h.1.1.1
  · have h := ThomsonNegative.Certificate.Cells.q09.metric_gate_pass
    simp only [ThomsonNegative.Certificate.Cells.q09.metricGate,Bool.and_eq_true] at h
    exact h.1.1.2
  · have h := ThomsonNegative.Certificate.Cells.q09.metric_gate_pass
    simp only [ThomsonNegative.Certificate.Cells.q09.metricGate,Bool.and_eq_true] at h
    exact h.1.2
  · have h := ThomsonNegative.Certificate.Cells.q09.metric_gate_pass
    simp only [ThomsonNegative.Certificate.Cells.q09.metricGate,Bool.and_eq_true] at h
    exact h.2
theorem metric_inverse (c : Fin 5) (b : Fin 4) :
    (metric c b).matrix (Source.blockSize (physicalBlock b)) *
      (inverse c b).matrix (Source.blockSize (physicalBlock b))=1 :=
  inverseCheck_sound _ _ _ (metric_inverse_gate c b)
#print axioms metric_inverse
#print axioms certified_floor
end ThomsonNegative.Certificate.Correction.Cells
