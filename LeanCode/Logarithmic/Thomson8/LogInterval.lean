import Thomson8.LogBound

namespace Thomson8

noncomputable def horner (cs : List ℚ) (z : ℝ) : ℝ :=
  match cs with
  | [] => 0
  | c::cs => (c : ℝ)+z*horner cs z

theorem horner_range (n : ℕ) (f : ℕ → ℚ) (z : ℝ) :
    horner ((List.range n).map f) z = ∑ j ∈ Finset.range n, (f j : ℝ)*z^j := by
  induction n generalizing f with
  | zero => simp [horner]
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [horner, Function.comp_def]
    rw [ih]
    rw [Finset.sum_range_succ']
    simp only [pow_zero, mul_one, Finset.mul_sum]
    rw [add_comm (f 0 : ℝ)]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_succ]
    ring

namespace Box

def horner (cs : List ℚ) (b : Box) : Box :=
  match cs with
  | [] => exact 0
  | c::cs => add (rational c) (times b (horner cs b))

theorem contains_horner {b : Box} {z : ℝ} (hz : b.Contains z) (cs : List ℚ) :
    (horner cs b).Contains (Thomson8.horner cs z) := by
  induction cs with
  | nil => simpa [horner, Thomson8.horner] using exact_contains 0
  | cons c cs ih =>
    exact contains_add (contains_rational c) (contains_times hz ih)

def taylor (n : ℕ) (b : Box) : Box :=
  horner ((List.range (n+1)).map fun j : ℕ => (-1 : ℚ)^(j+1)/(j : ℚ)) b

theorem contains_taylor {b : Box} {z : ℝ} (hz : b.Contains z) (n : ℕ) :
    (taylor n b).Contains (logTaylor n z) := by
  have h := contains_horner hz ((List.range (n+1)).map fun j : ℕ => (-1 : ℚ)^(j+1)/(j : ℚ))
  rw [horner_range] at h
  simpa [logTaylor, taylor, mul_div_assoc, div_mul_eq_mul_div] using h

def logError (n : ℕ) : ℚ := 2*((3/5 : ℚ)^(n+1)*(1-3/5 : ℚ)⁻¹/(n+1))

def logOfTransform (n : ℕ) (b : Box) : Box :=
  add (sub (taylor n b) (taylor n (neg b))) ⟨-logError n,logError n⟩

theorem contains_logOfTransform {b : Box} {z : ℝ} (hb : b.Contains z)
    (hz : |z| ≤ 3/5) (n : ℕ) :
    (logOfTransform n b).Contains (Real.log ((1+z)/(1-z))) := by
  have h₁ := contains_sub (contains_taylor hb n) (contains_taylor (contains_neg hb) n)
  have h₂ := log_ratio_bound n hz
  have herr : (⟨-logError n,logError n⟩ : Box).Contains
      (Real.log ((1+z)/(1-z)) - logApprox n z) := by
    rw [abs_le] at h₂
    simpa [Contains,logError] using h₂
  have h := contains_add h₁ herr
  convert h using 1 <;> simp [logOfTransform,logApprox]

end Box
end Thomson8
