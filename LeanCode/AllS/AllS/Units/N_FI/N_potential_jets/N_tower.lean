import AllS.Units.N_F.N_definitions
import Blueprint.FiniteDefinitions
import Blueprint.FiniteJetPilot
import Blueprint.Target

noncomputable section
open scoped BigOperators Topology
open Real
namespace Blueprint.Thomson.Finite

def jetCoeff (s : ℝ) (m : ℕ) : ℝ :=
  ∏ j ∈ Finset.range m, (s + 2 * ((j : ℝ) + 1))

def potentialJet (s : ℝ) : ℕ → ℝ → ℝ
  | 0 => phi s
  | m+1 => fun t => jetCoeff s m * (2-2*t)^(-1-(m : ℝ)-s/2)

@[simp] theorem jetCoeff_zero (s : ℝ) : jetCoeff s 0 = 1 := by simp [jetCoeff]

@[simp] theorem jetCoeff_succ (s : ℝ) (m : ℕ) :
    jetCoeff s (m+1) = jetCoeff s m * (s+2*((m : ℝ)+1)) := by
  simp [jetCoeff, Finset.prod_range_succ]

@[simp] theorem potentialJet_zero (s t : ℝ) : potentialJet s 0 t = phi s t := rfl

@[simp] theorem potentialJet_one (s t : ℝ) :
    potentialJet s 1 t = (2-2*t)^(-1-s/2) := by simp [potentialJet]

theorem jetCoeff_pos (s : ℝ) (hs : 0 ≤ s) (m : ℕ) : 0 < jetCoeff s m := by
  apply Finset.prod_pos
  intro j hj
  have : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  linarith

theorem hasDerivAt_potentialJet (s t : ℝ) (m : ℕ) (hs : 0 ≤ s) (ht : t < 1) :
    HasDerivAt (potentialJet s m) (potentialJet s (m+1) t) t := by
  cases m with
  | zero =>
    change HasDerivAt (phi s) (potentialJet s 1 t) t
    rw [potentialJet_one]
    exact hasDerivAt_phi s t hs ht
  | succ m =>
    have hb : 0 < 2-2*t := by linarith
    have hd : HasDerivAt (fun x : ℝ => 2-2*x) (-2) t := by
      convert! (hasDerivAt_const t (2 : ℝ)).sub ((hasDerivAt_id t).const_mul 2) using 1 <;> norm_num
    have h := (hd.rpow_const (p := -1-(m : ℝ)-s/2) (Or.inl hb.ne')).const_mul (jetCoeff s m)
    convert! h using 1
    · simp only [potentialJet, jetCoeff_succ, Nat.cast_add, Nat.cast_one]
      have he : -1-((m : ℝ)+1)-s/2 = -1-(m : ℝ)-s/2-1 := by ring
      rw [he]
      ring

theorem potentialJet_pos (s t : ℝ) (m : ℕ) (hs : 0 ≤ s) (ht : t < 1)
    (hm : 0 < m) : 0 < potentialJet s m t := by
  cases m with
  | zero => omega
  | succ m =>
    exact mul_pos (jetCoeff_pos s hs m) (Real.rpow_pos_of_pos (by linarith) _)

theorem potential_jets_tower (s t : ℝ) (m : ℕ) (hs : 0 ≤ s) (ht : t < 1) :
    HasDerivAt (potentialJet s m) (potentialJet s (m+1) t) t ∧
    ContinuousAt (potentialJet s m) t ∧
    (0 < m → 0 < potentialJet s m t) := by
  exact ⟨hasDerivAt_potentialJet s t m hs ht,
    (hasDerivAt_potentialJet s t m hs ht).continuousAt,
    potentialJet_pos s t m hs ht⟩

theorem jetCoeff_product (s : ℝ) (m : ℕ) :
    jetCoeff s m = 2^m * ∏ j ∈ Finset.range m, (s/2+(j : ℝ)+1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [jetCoeff_succ, Finset.prod_range_succ, pow_succ, ih]
    ring

theorem potential_value_factor (s t : ℝ) :
    1+s*phi s t = (2-2*t)^(-s/2) := by
  by_cases hs : s = 0
  · subst s
    simp
  · simp only [phi, if_neg hs]
    field_simp
    ring

theorem potentialJet_closed (s t : ℝ) (m : ℕ) (ht : t < 1) :
    potentialJet s (m+1) t =
      2^m * (∏ j ∈ Finset.range m, (s/2+(j : ℝ)+1)) *
        (2-2*t)^(-((m : ℝ)+1)) * (1+s*phi s t) := by
  have hb : 0 < 2-2*t := by linarith
  rw [potentialJet, jetCoeff_product, potential_value_factor, mul_assoc,
    ← Real.rpow_add hb]
  have he : -1-(m : ℝ)-s/2 = -((m : ℝ)+1)+(-s/2) := by ring
  rw [he]

theorem potentialJet_recurrence (s t : ℝ) (m : ℕ) (ht : t < 1) :
    potentialJet s (m+2) t =
      (2*(s/2+(m : ℝ)+1)/(2-2*t)) * potentialJet s (m+1) t := by
  have hb : 0 < 2-2*t := by linarith
  have he : -1-((m+1 : ℕ) : ℝ)-s/2 = -1+(-1-(m : ℝ)-s/2) := by push_cast; ring
  simp only [potentialJet, jetCoeff_succ]
  rw [he, Real.rpow_add hb, Real.rpow_neg_one]
  ring

theorem iteratedDeriv_phi_eq_potentialJet (s : ℝ) (hs : 0 ≤ s) (m : ℕ)
    (t : ℝ) (ht : t < 1) : iteratedDeriv m (phi s) t = potentialJet s m t := by
  induction m generalizing t with
  | zero => rfl
  | succ m ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv m (phi s) =ᶠ[𝓝 t] potentialJet s m := by
      filter_upwards [isOpen_Iio.mem_nhds ht] with x hx
      exact ih x hx
    rw [he.deriv_eq]
    exact (hasDerivAt_potentialJet s t m hs ht).deriv

#print axioms iteratedDeriv_phi_eq_potentialJet
#check potential_jets_tower
#print axioms potential_jets_tower
#check potentialJet_closed
#print axioms potentialJet_closed
#check potentialJet_recurrence
#print axioms potentialJet_recurrence
end Blueprint.Thomson.Finite
