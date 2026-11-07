import AllS.Units.N_GI.N_nearest_chart.N_tangent

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def boundaryCos2 : Fin 8 → ℝ := ![1,0,-1,0,1,0,-1,0]
def boundarySin2 : Fin 8 → ℝ := ![0,1,0,-1,0,1,0,-1]
def boundaryCos3 (i : Fin 8) : ℝ := layerSign i*angularCos i
def boundarySin3 (i : Fin 8) : ℝ := -layerSign i*angularSin i

def boundaryRawPair (k : Fin 16) (i : Fin 8) : Fin 2 → ℝ :=
  (![![0,1],![angularCos i,0],![angularSin i,0],![0,angularCos i],![0,angularSin i],
     ![boundaryCos2 i,0],![boundarySin2 i,0],![0,boundaryCos2 i],![0,boundarySin2 i],
     ![boundarySin3 i,packingZHeight*boundaryCos3 i],
     ![boundaryCos3 i,-packingZHeight*boundarySin3 i],
     ![layerSign i,0],![0,layerSign i],
     ![-packingZHeight*boundaryCos3 i,-boundarySin3 i],
     ![packingZHeight*boundarySin3 i,-boundaryCos3 i],![packingRadius,0]] : Fin 16 → Fin 2 → ℝ) k

def boundaryRaw (k : Fin 16) : TangentCoordinates := WithLp.toLp 2 (fun ij=>boundaryRawPair k ij.1 ij.2)

def boundaryWeight : Fin 16 → ℝ :=
  ![8,4,4,4,4,4,4,4,4,4*(1+packingZHeight^2),4*(1+packingZHeight^2),8,8,
    4*(1+packingZHeight^2),4*(1+packingZHeight^2),8*packingRadius^2]

def boundaryNormalized (k : Fin 16) : TangentCoordinates :=
  (√(boundaryWeight k))⁻¹ • boundaryRaw k

def boundaryRotationIndex (j : Fin 3) : Fin 16 := ⟨13+j.val,by omega⟩
def boundaryBasisIndex (j : Fin 13) : Fin 16 := ⟨j.val,by omega⟩
def boundaryRotation (j : Fin 3) : TangentCoordinates := boundaryRaw (boundaryRotationIndex j)
def boundaryFourier (j : Fin 13) : TangentCoordinates := boundaryNormalized (boundaryBasisIndex j)

end Blueprint.Thomson.Tail.Implementation
