import ThomsonNegative.Compact.Target.CellSound
import ThomsonNegative.Compact.Target.Cells.Q01
import ThomsonNegative.Compact.Target.Cells.Q03
import ThomsonNegative.Compact.Target.Cells.Q05
import ThomsonNegative.Compact.Target.Cells.Q07
import ThomsonNegative.Compact.Target.Cells.Q09

/-! Uniform checked scalar interface for the five closed parameter cells.
At interior q values, the extended semantic height and polynomial are the
stationary height and the concrete degree-seven Hermite polynomial. -/
noncomputable section
namespace ThomsonNegative.Compact.Target.ScalarCells
open ThomsonNegative.Compact.Packed

def data : Fin 5 → Cells.Data :=
  ![Cells.Q01.data,Cells.Q03.data,Cells.Q05.data,Cells.Q07.data,Cells.Q09.data]
def parameter (i : Fin 5) : ℝ → ℝ := Cells.parameter (data i)
def proposed (i : Fin 5) : ℝ → ℝ := Cells.proposed (data i)
def heightCheckpoint (i : Fin 5) : TM := (data i).heightCheckpoint
def coefficientCheckpoint (i : Fin 5) (j : Fin 8) : TM :=
  (data i).coefficientCheckpoints.getD j.val zeroTM
def heightFunction (i : Fin 5) : ℝ → ℝ := Cells.heightFunction (data i)
def polynomialFunction (i : Fin 5) : ℝ → Polynomial ℝ := Cells.polynomialFunction (data i)

theorem checked (i : Fin 5) : Cells.gate (data i)=true := by
  fin_cases i
  · exact Cells.Q01.checked
  · exact Cells.Q03.checked
  · exact Cells.Q05.checked
  · exact Cells.Q07.checked
  · exact Cells.Q09.checked

theorem data_center (i : Fin 5) : (data i).centerNumerator=2*i.val+1 := by
  fin_cases i <;> rfl

theorem parameter_formula (i : Fin 5) (t : ℝ) :
    parameter i t=(2*(i.val:ℝ)+1+t)/10 := by
  unfold parameter Cells.parameter
  rw [data_center]
  push_cast
  ring

theorem parameter_domain (i : Fin 5) (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    parameter i t ∈ Set.Icc (0:ℝ) 1 := Cells.parameter_domain (data i) (checked i) t ht

theorem height_encl (i : Fin 5) :
    Encl Cells.context (heightCheckpoint i) (heightFunction i) :=
  Cells.height_encl (data i) (checked i)

theorem coefficient_encl (i : Fin 5) (j : Fin 8) :
    Encl Cells.context (coefficientCheckpoint i j) (fun t => (polynomialFunction i t).coeff j.val) :=
  Cells.coefficient_encl (data i) (checked i) j.val j.isLt

theorem height_range (i : Fin 5) (t : ℝ) (ht : t ∈ Set.Icc (-1:ℝ) 1) :
    heightFunction i t ∈ Set.Ioo (5/16:ℝ) (1/3) :=
  Cells.height_range (data i) (checked i) t ht

theorem interior_bridge (i : Fin 5) (t : ℝ) (hq : parameter i t ∈ Set.Ioo (0:ℝ) 1) :
    heightFunction i t=aStar (2*parameter i t-2) ∧
    polynomialFunction i t=Geometry.hermiteH7 (parameter i t)
      (sourceContact (aStar (2*parameter i t-2))) :=
  Cells.interior_bridge (data i) t hq

theorem parameter_on_cell (i : Fin 5) (q : ℝ)
    (hq : q ∈ Set.Icc ((i.val:ℝ)/5) (((i.val:ℝ)+1)/5)) :
    ∃ t ∈ Set.Icc (-1:ℝ) 1, parameter i t=q := by
  refine ⟨10*q-(2*(i.val:ℝ)+1),?_,?_⟩
  · constructor <;> linarith [hq.1,hq.2]
  · rw [parameter_formula]; ring

/-- Exact closed cover, with an explicit inverse affine parameterization. -/
theorem cover (q : ℝ) (hq : q ∈ Set.Icc (0:ℝ) 1) :
    ∃ i : Fin 5, ∃ t ∈ Set.Icc (-1:ℝ) 1, parameter i t=q := by
  by_cases h0 : q≤1/5
  · exact ⟨0,parameter_on_cell 0 q ⟨by simpa using hq.1,by simpa using h0⟩⟩
  by_cases h1 : q≤2/5
  · refine ⟨1,parameter_on_cell 1 q ⟨?_,?_⟩⟩ <;> norm_num <;> linarith
  by_cases h2 : q≤3/5
  · refine ⟨2,parameter_on_cell 2 q ⟨?_,?_⟩⟩ <;> norm_num <;> linarith
  by_cases h3 : q≤4/5
  · refine ⟨3,parameter_on_cell 3 q ⟨?_,?_⟩⟩ <;> norm_num <;> linarith
  · refine ⟨4,parameter_on_cell 4 q ⟨?_,?_⟩⟩ <;> norm_num <;> linarith [hq.2]

#print axioms height_encl
#print axioms coefficient_encl
#print axioms interior_bridge
#print axioms cover
end ThomsonNegative.Compact.Target.ScalarCells
