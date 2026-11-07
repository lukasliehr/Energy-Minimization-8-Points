import AllS.Units.N_GI.N_signed_mean.N_real_fourier
import AllS.Units.N_GI.N_signed_mean.N_edge_forms

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def meanPartner : Fin 8 → Fin 8 := ![0,2,1,4,3,6,5,7]
def meanSinSign : Fin 8 → ℝ := ![0,1,-1,1,-1,1,-1,0]
def meanBetaFactor : Fin 8 → ℝ := ![0,3+√2,3+√2,√2,√2,-(1+√2),-(1+√2),0]
def meanPhiEigen : Fin 8 → ℝ := ![0,√2-1,√2-1,√2,√2,√2+1,√2+1,2*√2]
def meanMeridianEigen : Fin 8 → ℝ :=
  ![0,(-3+13*√2)/7,(-3+13*√2)/7,(12+11*√2)/7,(12+11*√2)/7,
    (3+√2)/7,(3+√2)/7,(-24+6*√2)/7]
def meanRadialFactor : Fin 8 → ℝ :=
  ![0,1+√2,1+√2,2+√2,2+√2,-(1+√2),-(1+√2),-2*(2+√2)]
def meanDEigen : Fin 8 → ℝ :=
  ![0,(-4+8*√2)/7,(-4+8*√2)/7,(2+10*√2)/7,(2+10*√2)/7,
    (4+6*√2)/7,(4+6*√2)/7,(-4+8*√2)/7]

def meanHEntry (j k : Fin 8 × Fin 2) : ℝ :=
  if j=k then meanScalarWeight j.1*(if j.2=0 then meanPhiEigen j.1 else meanMeridianEigen j.1)
  else if j.1=meanPartner k.1 ∧ j.2≠k.2 then
    meanScalarWeight j.1*packingZHeight*meanBetaFactor j.1*meanSinSign j.1*(if j.2=0 then 1 else -1)
  else 0

def meanBEntry (j : Fin 8 × Fin 2) (k : Fin 8) : ℝ :=
  if j.2=0 then
    if k=meanPartner j.1 then -meanScalarWeight j.1*packingRadius*meanBetaFactor j.1*meanSinSign j.1 else 0
  else if k=j.1 then meanScalarWeight j.1*packingZHeight*packingRadius*meanRadialFactor j.1 else 0

def meanDEntry (j k : Fin 8) : ℝ := if j=k then meanScalarWeight j*meanDEigen j else 0

end Blueprint.Thomson.Tail.Implementation
