import AllS.Units.N_FI.N_certificate.N_typed_contract
import AllS.Units.N_F.N_geometry

noncomputable section
namespace Blueprint.Thomson.Finite

def polyPairEnergy (H : Polynomial ℝ) (Y : Configuration) : ℝ :=
  PairSum (fun i j => H.eval (inner ℝ (Y i) (Y j)))

theorem univariateLift_eval (x : Fin 3 → ℝ) (i : Fin 3) (H : Polynomial ℝ) :
    MvPolynomial.eval x (univariateLift i H)=H.eval (x i) := by
  unfold univariateLift
  induction H using Polynomial.induction_on' with
  | add H K hH hK => simp only [map_add,hH,hK,Polynomial.eval_add]
  | monomial n c => simp [univariateLift,Polynomial.aeval_monomial]

theorem averagedPolynomial_eval (x : Fin 3 → ℝ) (H : Polynomial ℝ) :
    MvPolynomial.eval x (averagedPolynomial H)=(H.eval (x 0)+H.eval (x 1)+H.eval (x 2))/3 := by
  simp [averagedPolynomial,univariateLift_eval]
  ring

theorem centeredPolynomial_eval (x : Fin 3 → ℝ) (H : Polynomial ℝ) (e : ℝ) :
    MvPolynomial.eval x (centeredPolynomial H e)=
      (H.eval (x 0)+H.eval (x 1)+H.eval (x 2))/3-e/28 := by
  simp [centeredPolynomial,averagedPolynomial_eval]

theorem PairSum_const (c : ℝ) : PairSum (fun _ _ => c)=28*c := by
  have h := PairSum_mul c (fun _ _ => 1)
  simpa only [mul_one,PairSum_one,mul_comm] using h

theorem polyPairEnergy_affine (H : Polynomial ℝ) (Y : Configuration) (β c : ℝ) :
    polyPairEnergy (Polynomial.C β*H+Polynomial.C c) Y=β*polyPairEnergy H Y+28*c := by
  simp only [polyPairEnergy,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
  rw [PairSum_add,PairSum_mul,PairSum_const]

theorem centeredPolynomial_affine (H : Polynomial ℝ) (e β c : ℝ) :
    centeredPolynomial (Polynomial.C β*H+Polynomial.C c) (β*e+28*c)=
      MvPolynomial.C β*centeredPolynomial H e := by
  apply MvPolynomial.funext
  intro x
  simp only [centeredPolynomial_eval,map_mul,MvPolynomial.eval_C,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
  ring

def BalancedTargetContract : Prop := ∀ H Halt : Polynomial ℝ,∀ β c : ℝ,
  Halt=Polynomial.C β*H+Polynomial.C c → ∀ Y : Configuration,
    polyPairEnergy Halt Y=β*polyPairEnergy H Y+28*c ∧
    centeredPolynomial Halt (polyPairEnergy Halt Y)=
      MvPolynomial.C β*centeredPolynomial H (polyPairEnergy H Y)

theorem certificate_balanced_target : BalancedTargetContract := by
  intro H Halt β c h Y
  subst Halt
  exact ⟨polyPairEnergy_affine H Y β c,by rw [polyPairEnergy_affine,centeredPolynomial_affine]⟩

#check certificate_balanced_target
#print axioms certificate_balanced_target
end Blueprint.Thomson.Finite
