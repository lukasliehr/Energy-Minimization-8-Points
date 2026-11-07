import AllS.Units.N_GI.N_contact_spectrum.N_contact_rows
import AllS.Units.N_GI.N_boundary_basis.N_basis_of_slice

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def contactGram (w : ℝ) (q v : TangentCoordinates) : ℝ :=
  ∑ e : ContactIndex, (if e.2=0 then 1 else w)*contactLinear q e.1 (contactNext e)*contactLinear v e.1 (contactNext e)

def contactRawVector (j : Fin 13) : TangentCoordinates := boundaryRaw (boundaryBasisIndex j)

def contactGramDiagonal (w : ℝ) : Fin 13 → ℝ :=
  ![128*packingRadius^2*packingHeight*(contactKappa^2+w),
    32*packingRadius^2*((1-√2/2)/2+w),32*packingRadius^2*((1-√2/2)/2+w),
    32*packingRadius^2*packingHeight*(contactKappa^2*(1+√2/2)+w),
    32*packingRadius^2*packingHeight*(contactKappa^2*(1+√2/2)+w),
    32*packingRadius^2*(1/2+2*w),32*packingRadius^2*(1/2+2*w),
    32*packingRadius^2*packingHeight*contactKappa^2,32*packingRadius^2*packingHeight*contactKappa^2,
    32*packingRadius^2*(1+packingHeight)^2*((1+√2/2)/2+w),
    32*packingRadius^2*(1+packingHeight)^2*((1+√2/2)/2+w),
    64*packingRadius^2,128*packingRadius^2*packingHeight*w]

def contactGramMixed1 (w : ℝ) : ℝ := 32*packingRadius^2*packingZHeight*(w-contactKappa/2)
def contactGramMixed2 : ℝ := -32*packingRadius^2*packingZHeight*contactKappa/√2

def contactGramEntry (w : ℝ) (j k : Fin 13) : ℝ :=
  if j=k then contactGramDiagonal w j
  else if (j=1 ∧ k=4) ∨ (j=4 ∧ k=1) then contactGramMixed1 w
  else if (j=2 ∧ k=3) ∨ (j=3 ∧ k=2) then -contactGramMixed1 w
  else if (j=5 ∧ k=8) ∨ (j=8 ∧ k=5) then contactGramMixed2
  else if (j=6 ∧ k=7) ∨ (j=7 ∧ k=6) then -contactGramMixed2 else 0

end Blueprint.Thomson.Tail.Implementation
