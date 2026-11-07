import AllS.Units.N_GI.N_disphenoid.N_coordinates

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem disphenoid_assemble (A B : Fin 4 → Point) (c : ℝ) (hc : 0<c)
    (hAunit : ∀i,‖A i‖=1) (hBunit : ∀i,‖B i‖=1)
    (hAinj : Function.Injective A) (hBinj : Function.Injective B)
    (hcross : ∀i j,i≠j → inner ℝ (A i) (B j)=c)
    (hmatched : ∀i,inner ℝ (A i) (B i)≤c) :
    ∃ (e : Fin 3 → Point) (x : Fin 3 → ℝ),Orthonormal ℝ e ∧ (∀k,0<x k) ∧
      (∀i,A i=∑k,(cubeSign i k*x k) • e k) ∧
      (∀i,B i=∑k,(-c*cubeSign i k/x k) • e k) ∧
      (∑k,(x k)^2)=1 ∧ c^2*(∑k,1/(x k)^2)=1 :=
  disphenoid_coordinates A B c hc hAunit hBunit hAinj hBinj hcross hmatched

#print axioms disphenoid_assemble
end Blueprint.Thomson.Tail.Implementation
