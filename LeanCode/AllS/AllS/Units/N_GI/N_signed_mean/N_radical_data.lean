import AllS.Units.N_GI.N_signed_mean.N_radical_arithmetic

namespace Blueprint.Thomson.Tail.Implementation

def meanBlockAData : Fin 8 → Fin 2 → Fin 2 → MeanRadical :=
![![![![(829/200),0,0,0],![0,0,0,0]],![![0,0,0,0],![(829/200),0,0,0]]],![![![(1029/200),-1,0,0],![0,0,-3,-1]],![![0,0,-3,-1],![(6403/1400),(-13/7),0,0]]],![![![(1029/200),-1,0,0],![0,0,3,1]],![![0,0,3,1],![(6403/1400),(-13/7),0,0]]],![![![(829/200),-1,0,0],![0,0,0,-1]],![![0,0,0,-1],![(3403/1400),(-11/7),0,0]]],![![![(829/200),-1,0,0],![0,0,0,1]],![![0,0,0,1],![(3403/1400),(-11/7),0,0]]],![![![(629/200),-1,0,0],![0,0,1,1]],![![0,0,1,1],![(5203/1400),(-1/7),0,0]]],![![![(629/200),-1,0,0],![0,0,-1,-1]],![![0,0,-1,-1],![(5203/1400),(-1/7),0,0]]],![![![(829/200),-2,0,0],![0,0,0,0]],![![0,0,0,0],![(10603/1400),(-6/7),0,0]]]]

def meanRadicalOne : MeanRadical := ![1,0,0,0]
def meanRadicalId (i j : Fin 4) : MeanRadical := if i=j then meanRadicalOne else 0

def meanPairAData (u v : Fin 8) : Fin 4 → Fin 4 → MeanRadical :=
  let A := meanBlockAData u
  let B := meanBlockAData v
  ![![A 0 0+B 0 0,B 0 1,A 0 1,0],
    ![B 1 0,A 0 0+B 1 1,0,A 0 1],
    ![A 1 0,0,A 1 1+B 0 0,B 0 1],
    ![0,A 1 0,B 1 0,A 1 1+B 1 1]]
end Blueprint.Thomson.Tail.Implementation
