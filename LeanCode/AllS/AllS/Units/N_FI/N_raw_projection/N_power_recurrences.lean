import AllS.Units.N_F.N_sympoly

noncomputable section
namespace Blueprint.Thomson.Finite

/-- The two Newton power sums used by the exact retained-coordinate tensors. -/
def rawPowerSum (n : ℕ) : Poly3 :=
  MvPolynomial.X 0^n+MvPolynomial.X 1^n+MvPolynomial.X 2^n
def rawPairPowerSum (n : ℕ) : Poly3 :=
  (MvPolynomial.X 0*MvPolynomial.X 1)^n+
    (MvPolynomial.X 0*MvPolynomial.X 2)^n+(MvPolynomial.X 1*MvPolynomial.X 2)^n

theorem rawPowerSum_initial :
    rawPowerSum 0=3 ∧ rawPowerSum 1=sigma ∧ rawPowerSum 2=sigma^2-2*e2 := by
  refine ⟨?_,?_,?_⟩ <;> simp [rawPowerSum,sigma,e2] <;> ring

theorem rawPairPowerSum_initial :
    rawPairPowerSum 0=3 ∧ rawPairPowerSum 1=e2 ∧
      rawPairPowerSum 2=e2^2-2*sigma*e3 := by
  refine ⟨?_,?_,?_⟩ <;> simp [rawPairPowerSum,sigma,e2,e3] <;> ring

theorem rawPowerSum_recurrence (n : ℕ) :
    rawPowerSum (n+3)=sigma*rawPowerSum (n+2)-e2*rawPowerSum (n+1)+e3*rawPowerSum n := by
  simp only [rawPowerSum,sigma,e2,e3,pow_add]
  ring

theorem rawPairPowerSum_recurrence (n : ℕ) :
    rawPairPowerSum (n+3)=e2*rawPairPowerSum (n+2)-
      sigma*e3*rawPairPowerSum (n+1)+e3^2*rawPairPowerSum n := by
  simp only [rawPairPowerSum,sigma,e2,e3,pow_add,mul_pow]
  ring

def RawPowerRecurrencesContract : Prop :=
  (rawPowerSum 0=3 ∧ rawPowerSum 1=sigma ∧ rawPowerSum 2=sigma^2-2*e2) ∧
  (rawPairPowerSum 0=3 ∧ rawPairPowerSum 1=e2 ∧ rawPairPowerSum 2=e2^2-2*sigma*e3) ∧
  ∀ n : ℕ,3≤n →
    rawPowerSum n=sigma*rawPowerSum (n-1)-e2*rawPowerSum (n-2)+e3*rawPowerSum (n-3) ∧
    rawPairPowerSum n=e2*rawPairPowerSum (n-1)-
      sigma*e3*rawPairPowerSum (n-2)+e3^2*rawPairPowerSum (n-3)

theorem raw_projection_power_recurrences : RawPowerRecurrencesContract := by
  refine ⟨rawPowerSum_initial,rawPairPowerSum_initial,?_⟩
  intro n hn
  obtain ⟨m,rfl⟩ : ∃ m,n=m+3 := ⟨n-3,by omega⟩
  simpa using And.intro (rawPowerSum_recurrence m) (rawPairPowerSum_recurrence m)

#print axioms raw_projection_power_recurrences
end Blueprint.Thomson.Finite
