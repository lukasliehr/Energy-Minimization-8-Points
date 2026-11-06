import AllS.Units.N_GI.N_constants.N_weights
import AllS.Units.N_GI.N_boundary_basis.N_fourier_basis
import AllS.Units.N_GI.N_contact_taylor.N_exact_expansion

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def balancedD : ℝ := log contactKappa/(contactKappa+1)
def balancedLambda : ℝ := exp (-contactKappa*balancedD)
def balancedZ (e : ContactIndex) : ℝ := if e.2=0 then contactKappa*balancedD else -balancedD
def balancedZNorm : ℝ := √(8*contactKappa*(contactKappa+1)*balancedD^2)
def balancedRefNorm : ℝ := balancedD/√(2*packingHeight*(1-packingHeight))
def balancedReference : TangentCoordinates :=
  (balancedD/(4*packingZHeight*packingRadius)) • boundaryRaw 0

theorem balancedD_pos : 0<balancedD := by
  have hκ : 1<contactKappa := by rw [contactKappa_formula]; linarith [Real.sqrt_pos.mpr (show (0:ℝ)<2 by norm_num)]
  exact div_pos (Real.log_pos hκ) (by linarith)

theorem balancedZ_mean : (∑ e : ContactIndex, contactWeight e*balancedZ e)=0 := by
  simp [Fintype.sum_prod_type,Fin.sum_univ_succ,balancedZ,contactWeight]

theorem balancedZ_square : (∑ e : ContactIndex, contactWeight e*(balancedZ e)^2)=balancedZNorm^2 := by
  rw [balancedZNorm,Real.sq_sqrt (by have hκ := (contactWeight_ge_one (0,1)); simp [contactWeight] at hκ; positivity)]
  simp [Fintype.sum_prod_type,Fin.sum_univ_succ,balancedZ,contactWeight]
  ring

theorem balancedZ_exponential (e : ContactIndex) :
    balancedLambda*contactWeight e*exp (balancedZ e)=1 := by
  have hκ : 0<contactKappa := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (contactWeight_ge_one (0,1))
  have hd : (contactKappa+1)*balancedD=log contactKappa := by
    unfold balancedD
    field_simp
  rcases e with ⟨i,k⟩
  fin_cases k
  · simp only [contactWeight,balancedZ,Prod.snd,Fin.zero_eta,ite_true,balancedLambda,mul_one]
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  · have he : -contactKappa*balancedD-balancedD= -log contactKappa := by nlinarith [hd]
    simp only [contactWeight,balancedZ,Prod.snd,show (1:Fin 2)≠0 by decide,ite_false,balancedLambda]
    calc
      _ = contactKappa*exp (-contactKappa*balancedD-balancedD) := by rw [Real.exp_sub]; simp [Real.exp_neg]; ring
      _ = 1 := by rw [he,Real.exp_neg,Real.exp_log hκ]; field_simp

#print axioms balancedZ_exponential
end Blueprint.Thomson.Tail.Implementation
