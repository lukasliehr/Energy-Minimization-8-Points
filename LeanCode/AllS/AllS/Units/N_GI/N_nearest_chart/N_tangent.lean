import AllS.Units.N_GI.N_nearest_chart.N_frame
import Lean_Code.ChartInverse

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem localFrame_inner (i : Fin 8) (j k : Fin 3) :
    inner ℝ (localFrame i j) (localFrame i k)=if j=k then 1 else 0 :=
  orthonormal_iff_ite.mp (localFrame_orthonormal i) j k

theorem packingReference_norm (i : Fin 8) : ‖packingReference i‖=1 := by
  have h := localFrame_inner i 0 0
  change inner ℝ (packingReference i) (packingReference i)=(1:ℝ) at h
  rw [real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (packingReference i)]

def localOrthonormalBasis (i : Fin 8) : OrthonormalBasis (Fin 3) ℝ Point :=
  let b := basisOfOrthonormalOfCardEqFinrank (localFrame_orthonormal i) (by simp [Point])
  b.toOrthonormalBasis (by simpa [b] using localFrame_orthonormal i)

theorem localFrame_expand (i : Fin 8) (y : Point) :
    y=inner ℝ (packingReference i) y • packingReference i+
      inner ℝ (azimuthFrame i) y • azimuthFrame i+inner ℝ (meridianFrame i) y • meridianFrame i := by
  have he := (localOrthonormalBasis i).sum_repr' y
  have hb : (localOrthonormalBasis i : Fin 3 → Point)=localFrame i := by simp [localOrthonormalBasis]
  rw [hb] at he
  simpa [localFrame,Fin.sum_univ_succ,add_assoc] using he.symm

theorem tangentVector_orthogonal (q : TangentCoordinates) (i : Fin 8) :
    inner ℝ (tangentVector q i) (packingReference i)=0 := by
  have hf : inner ℝ (azimuthFrame i) (packingReference i)=0 := localFrame_inner i 1 0
  have hg : inner ℝ (meridianFrame i) (packingReference i)=0 := localFrame_inner i 2 0
  simp [tangentVector,inner_add_left,inner_smul_left,hf,hg]

theorem tangentVector_norm_sq (q : TangentCoordinates) (i : Fin 8) :
    ‖tangentVector q i‖^2=(q (i,0))^2+(q (i,1))^2 := by
  have hf : inner ℝ (azimuthFrame i) (azimuthFrame i)=1 := localFrame_inner i 1 1
  have hg : inner ℝ (meridianFrame i) (meridianFrame i)=1 := localFrame_inner i 2 2
  have hfg : inner ℝ (azimuthFrame i) (meridianFrame i)=0 := localFrame_inner i 1 2
  have hgf : inner ℝ (meridianFrame i) (azimuthFrame i)=0 := localFrame_inner i 2 1
  rw [← real_inner_self_eq_norm_sq]
  simp only [tangentVector,inner_add_left,inner_add_right,inner_smul_left,inner_smul_right,
    starRingEnd_apply,star_trivial,hf,hg,hfg,hgf]
  ring

theorem tangentVector_sum_norm_sq (q : TangentCoordinates) :
    (∑ i, ‖tangentVector q i‖^2)=‖q‖^2 := by
  simp_rw [tangentVector_norm_sq]
  simp [EuclideanSpace.norm_sq_eq,Fintype.sum_prod_type,Fin.sum_univ_two]

theorem tangentVector_norm_le (q : TangentCoordinates) (i : Fin 8) : ‖tangentVector q i‖ ≤ ‖q‖ := by
  have h := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 8))) => sq_nonneg ‖tangentVector q j‖) (Finset.mem_univ i)
  rw [tangentVector_sum_norm_sq] at h
  nlinarith [norm_nonneg (tangentVector q i),norm_nonneg q]

def inverseCoordinates (Y : Fin 8 → Point) : TangentCoordinates :=
  WithLp.toLp 2 (fun ij => if ij.2=0 then inner ℝ (azimuthFrame ij.1) (Y ij.1)
    else inner ℝ (meridianFrame ij.1) (Y ij.1))

theorem inverseCoordinates_tangent (Y : Fin 8 → Point) (i : Fin 8) :
    tangentVector (inverseCoordinates Y) i=SquareAntiprismVerification.inverseSphereChart (packingReference i) (Y i) := by
  have he := localFrame_expand i (Y i)
  dsimp [tangentVector,inverseCoordinates,SquareAntiprismVerification.inverseSphereChart]
  rw [real_inner_comm (Y i) (packingReference i)] at he
  calc
    _ = (inner ℝ (Y i) (packingReference i) • packingReference i+
      inner ℝ (azimuthFrame i) (Y i) • azimuthFrame i+inner ℝ (meridianFrame i) (Y i) • meridianFrame i)-
      inner ℝ (Y i) (packingReference i) • packingReference i := by module
    _ = _ := congrArg (fun z : Point => z-inner ℝ (Y i) (packingReference i) • packingReference i) he.symm

#print axioms inverseCoordinates_tangent
#print axioms tangentVector_sum_norm_sq
end Blueprint.Thomson.Tail.Implementation
