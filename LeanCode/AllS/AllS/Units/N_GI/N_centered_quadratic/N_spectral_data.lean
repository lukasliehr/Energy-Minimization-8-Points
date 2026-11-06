import AllS.Units.N_GI.N_centered_quadratic.N_projected_form

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def centeredPhiEigen : Fin 8 → ℝ :=
  ![(139+107*√2)/196,(1370-157*√2)/784,(1370-157*√2)/784,
    (677+102*√2)/392,(677+102*√2)/392,(1058+537*√2)/784,(1058+537*√2)/784,(446+25*√2)/196]
def centeredMeridianEigen : Fin 8 → ℝ :=
  ![(4+√2)/2,(15714+1689*√2)/5488,(15714+1689*√2)/5488,
    (6845+2620*√2)/2744,(6845+2620*√2)/2744,(10282+4027*√2)/5488,(10282+4027*√2)/5488,(2721-556*√2)/1372]
def centeredBetaFactor : Fin 8 → ℝ :=
  ![0,(386+607*√2)/784,(386+607*√2)/784,(237-89*√2)/392,(237-89*√2)/392,
    (-438-181*√2)/784,(-438-181*√2)/784,0]
def centeredQEntry (j k : Fin 8 × Fin 2) : ℝ :=
  if j=k then meanScalarWeight j.1*(if j.2=0 then centeredPhiEigen j.1 else centeredMeridianEigen j.1)
  else if j.1=meanPartner k.1 ∧ j.2≠k.2 then
    meanScalarWeight j.1*packingZHeight*centeredBetaFactor j.1*meanSinSign j.1*(if j.2=0 then 1 else -1)
  else 0

end Blueprint.Thomson.Tail.Implementation
