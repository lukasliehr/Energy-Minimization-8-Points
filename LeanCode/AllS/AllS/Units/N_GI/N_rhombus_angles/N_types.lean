import AllS.Units.N_GI.N_rhombus_angles.N_triangle_incidence

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem rhombus_angles_equal_type (α : ℝ) (θ : Fin 1 → ℝ)
    (hsum : 3*α + ∑ j, θ j = 2*Real.pi) (j : Fin 1) :
    θ j = 2*Real.pi - 3*α := by
  have hj : j=0 := Subsingleton.elim _ _
  rw [hj]
  simp only [Fin.sum_univ_one] at hsum
  linarith

theorem rhombus_angles_high_type (α : ℝ) (θ : Fin 2 → ℝ)
    (hθ : ∀ j, θ j < 2*α) (hsum : α + ∑ j, θ j = 2*Real.pi) (j : Fin 2) :
    2*Real.pi - 3*α < θ j := by
  have h0 := hθ 0
  have h1 := hθ 1
  simp only [Fin.sum_univ_two] at hsum
  have hj : j=0 ∨ j=1 := by fin_cases j <;> decide
  rcases hj with rfl | rfl <;> linarith

theorem rhombus_angles_low_type (t q : ℕ) (α : ℝ) (θ : Fin q → ℝ)
    (hdegree : t+q=4) (ht : t≤2)
    (hθ : ∀ j, α < θ j) (hsum : (t:ℝ)*α + ∑ j, θ j = 2*Real.pi) (j : Fin q) :
    θ j < 2*Real.pi - 3*α := by
  interval_cases t
  · have hq : q=4 := by omega
    subst q
    have h0 := hθ 0
    have h1 := hθ 1
    have h2 := hθ 2
    have h3 := hθ 3
    simp only [Nat.cast_zero, zero_mul, zero_add, Fin.sum_univ_four] at hsum
    have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by fin_cases j <;> decide
    rcases hj with rfl | rfl | rfl | rfl <;> linarith
  · have hq : q=3 := by omega
    subst q
    have h0 := hθ 0
    have h1 := hθ 1
    have h2 := hθ 2
    simp only [Nat.cast_one, one_mul, Fin.sum_univ_three] at hsum
    have hj : j=0 ∨ j=1 ∨ j=2 := by fin_cases j <;> decide
    rcases hj with rfl | rfl | rfl <;> linarith
  · have hq : q=2 := by omega
    subst q
    have h0 := hθ 0
    have h1 := hθ 1
    simp only [Nat.cast_ofNat, Fin.sum_univ_two] at hsum
    have hj : j=0 ∨ j=1 := by fin_cases j <;> decide
    rcases hj with rfl | rfl <;> linarith

#print axioms rhombus_angles_equal_type
#print axioms rhombus_angles_high_type
#print axioms rhombus_angles_low_type

end Blueprint.Thomson.Tail.Implementation

namespace Blueprint.Thomson.Tail.Implementation

theorem rhombus_angles_types (t q : ℕ) (α : ℝ) (θ : Fin q → ℝ)
    (hθ : ∀ j, θ j ∈ Set.Ioo α (2*α))
    (hsum : (t:ℝ)*α + ∑ j, θ j = 2*Real.pi) :
    (t+q=4 → t=3 → ∀ j, θ j = 2*Real.pi-3*α) ∧
    (t+q=4 → t≤2 → ∀ j, θ j < 2*Real.pi-3*α) ∧
    (t+q=3 → t=1 → ∀ j, 2*Real.pi-3*α < θ j) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hdeg ht
    subst t
    have hq : q=1 := by omega
    subst q
    exact rhombus_angles_equal_type α θ (by simpa using hsum)
  · intro hdeg ht
    exact rhombus_angles_low_type t q α θ hdeg ht (fun j => (hθ j).1) hsum
  · intro hdeg ht
    subst t
    have hq : q=2 := by omega
    subst q
    exact rhombus_angles_high_type α θ (fun j => (hθ j).2) (by simpa using hsum)

#print axioms rhombus_angles_types
end Blueprint.Thomson.Tail.Implementation
