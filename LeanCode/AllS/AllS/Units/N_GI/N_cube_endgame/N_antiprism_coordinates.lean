import AllS.Units.N_GI.N_cube_endgame.N_antiprism_radicals
import AllS.Units.N_FI.N_congruence.N_isometry

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def cubeCanonicalPoint (v : CubeVertex) : Point :=
  if v.1=0 then !₂[cubeSign v.2 0*cubeU,cubeSign v.2 1*cubeL,cubeSign v.2 2*cubeH]
  else !₂[-cubeSign v.2 0*cubeL,-cubeSign v.2 1*cubeU,-cubeSign v.2 2*cubeH]

def cubeHorizontalFrame : Fin 3 → Point :=
  ![!₂[cubeU/cubeR,cubeL/cubeR,0],!₂[-cubeL/cubeR,cubeU/cubeR,0],!₂[0,0,1]]

def cubeModelLabel : Fin 8 → CubeVertex :=
  ![(0,0),(1,1),(0,3),(1,2),(1,3),(0,2),(1,0),(0,1)]

def cubeModelLabelEquiv : Fin 8 ≃ CubeVertex := Equiv.ofBijective cubeModelLabel (by decide)

theorem cubeHorizontalFrame_orthonormal : Orthonormal ℝ cubeHorizontalFrame := by
  obtain ⟨hu,hl,hh,hr,hprod,hsum,hminus,hplus,huDiv,hlDiv,hhDiv⟩ := antiprism_cube_radicals
  rw [orthonormal_iff_ite]
  intro i j
  rw [PiLp.inner_apply]
  fin_cases i <;> fin_cases j <;> norm_num [cubeHorizontalFrame,Fin.sum_univ_succ]
  all_goals field_simp [hr.ne'] <;> nlinarith [hsum]

theorem cubeCanonicalPoint_isometry (e : Fin 3 → Point) (U : Point ≃ₗᵢ[ℝ] Point)
    (hU : ∀x,U x=∑k,x k • e k) (v : CubeVertex) :
    U (cubeCanonicalPoint v)=cubeVertexModel e packingHeight antiprismCubeQ v := by
  obtain ⟨v,i⟩ := v
  obtain ⟨_,_,_,_,_,_,_,_,huDiv,hlDiv,hhDiv⟩ := antiprism_cube_radicals
  have huD (z : ℝ) : -packingHeight*z/cubeU=(-z)*cubeL := by calc
    _=(-z)*(packingHeight/cubeU) := by ring
    _=(-z)*cubeL := by rw [huDiv]
  have hlD (z : ℝ) : -packingHeight*z/cubeL=(-z)*cubeU := by calc
    _=(-z)*(packingHeight/cubeL) := by ring
    _=(-z)*cubeU := by rw [hlDiv]
  have hhD (z : ℝ) : -packingHeight*z/cubeH=(-z)*cubeH := by calc
    _=(-z)*(packingHeight/cubeH) := by ring
    _=(-z)*cubeH := by rw [hhDiv]
  fin_cases v
  · change U (!₂[cubeSign i 0*cubeU,cubeSign i 1*cubeL,cubeSign i 2*cubeH])=cubeModelA e antiprismCubeQ i
    rw [hU,Fin.sum_univ_three,cubeModelA,Fin.sum_univ_three]
    rfl
  · change U (!₂[-cubeSign i 0*cubeL,-cubeSign i 1*cubeU,-cubeSign i 2*cubeH])=cubeModelB e packingHeight antiprismCubeQ i
    rw [hU,Fin.sum_univ_three,cubeModelB,Fin.sum_univ_three]
    change (-cubeSign i 0*cubeL) • e 0+(-cubeSign i 1*cubeU) • e 1+(-cubeSign i 2*cubeH) • e 2=
      (-packingHeight*cubeSign i 0/cubeU) • e 0+(-packingHeight*cubeSign i 1/cubeL) • e 1+
        (-packingHeight*cubeSign i 2/cubeH) • e 2
    rw [huD,hlD,hhD]

theorem cube_antiprism_coordinate_isometry (U : Point ≃ₗᵢ[ℝ] Point)
    (hU : ∀x,U x=∑k,x k • cubeHorizontalFrame k) (i : Fin 8) :
    U (X packingHeight i)=cubeCanonicalPoint (cubeModelLabel i) := by
  obtain ⟨_,_,_,hr,_,_,hm,hp,_,_,_⟩ := antiprism_cube_radicals
  have hspos : 0<√(2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hm' := (div_eq_iff hspos.ne').mp hm
  have hp' := (div_eq_iff hspos.ne').mp hp
  have hX : X packingHeight=
    ![!₂[cubeR,0,cubeH],!₂[0,cubeR,cubeH],!₂[-cubeR,0,cubeH],!₂[0,-cubeR,cubeH],
      !₂[cubeR/√2,cubeR/√2,-cubeH],!₂[-(cubeR/√2),cubeR/√2,-cubeH],
      !₂[-(cubeR/√2),-(cubeR/√2),-cubeH],!₂[cubeR/√2,-(cubeR/√2),-cubeH]] := rfl
  rw [hU,hX]
  fin_cases i <;> ext k <;> fin_cases k <;>
    simp [cubeHorizontalFrame,cubeCanonicalPoint,cubeModelLabel,cubeSign,Fin.sum_univ_succ]
  all_goals field_simp [hr.ne',hspos.ne'] <;> nlinarith [hm',hp']

#print axioms cube_antiprism_coordinate_isometry
end Blueprint.Thomson.Tail.Implementation
