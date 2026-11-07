import Blueprint.Tail
import Lean_Code.CrossAlgebra

/-! Exact finite coordinates for the paper's orthographic rotation slice.
The angular tables are the values of cosine/sine at i*pi/4, in cyclicIndex order.
This module defines the common objects; the nearest-chart units prove their
geometric and analytic properties. No local-minimum or CAP fact is assumed. -/
noncomputable section
open Real
open SquareAntiprismVerification (crossVec crossVec_smul_right)
namespace Blueprint.Thomson.Tail

def packingRadius : ℝ := √(1-packingHeight)
def packingZHeight : ℝ := √packingHeight

def angularCos : Fin 8 → ℝ := ![1,1/√2,0,-(1/√2),-1,-(1/√2),0,1/√2]
def angularSin : Fin 8 → ℝ := ![0,1/√2,1,1/√2,0,-(1/√2),-1,-(1/√2)]
def layerSign : Fin 8 → ℝ := ![1,-1,1,-1,1,-1,1,-1]

def azimuthFrame (i : Fin 8) : Point := !₂[-angularSin i,angularCos i,0]
def meridianFrame (i : Fin 8) : Point :=
  !₂[-packingZHeight*angularCos i,-packingZHeight*angularSin i,layerSign i*packingRadius]

def tangentVector (q : TangentCoordinates) (i : Fin 8) : Point :=
  q (i,0) • azimuthFrame i+q (i,1) • meridianFrame i

def rotationVector (q : TangentCoordinates) : Point :=
  ∑ i, crossVec (packingReference i) (tangentVector q i)

theorem crossVec_add_right (x y z : Point) : crossVec x (y+z)=crossVec x y+crossVec x z := by
  ext i
  fin_cases i <;> simp [crossVec] <;> ring

theorem tangentVector_add (q v : TangentCoordinates) (i : Fin 8) :
    tangentVector (q+v) i=tangentVector q i+tangentVector v i := by
  simp only [tangentVector,PiLp.add_apply,add_smul]
  module

theorem tangentVector_smul (c : ℝ) (q : TangentCoordinates) (i : Fin 8) :
    tangentVector (c • q) i=c • tangentVector q i := by
  simp only [tangentVector,PiLp.smul_apply,smul_eq_mul]
  module

def rotationLinearMap : TangentCoordinates →ₗ[ℝ] Point where
  toFun := rotationVector
  map_add' q v := by simp only [rotationVector,tangentVector_add,crossVec_add_right,Finset.sum_add_distrib]
  map_smul' c q := by
    simp only [rotationVector,tangentVector_smul,crossVec_smul_right,Finset.smul_sum,RingHom.id_apply]

def rotationSlice : Submodule ℝ TangentCoordinates := rotationLinearMap.ker

def orthographicChart (q : TangentCoordinates) (i : Fin 8) : Point :=
  √(1-‖tangentVector q i‖^2) • packingReference i+tangentVector q i

#print axioms rotationLinearMap
end Blueprint.Thomson.Tail
