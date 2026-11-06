import ThomsonNegative.Structure.Concrete.Symmetry
import ThomsonNegative.Structure.Factored.HighData
import ThomsonNegative.Certificate.Correction.SourceLayout

noncomputable section
open scoped BigOperators
namespace ThomsonNegative.Structure.Concrete
open ThomsonNegative.Certificate.Bridges

def repairBlock : Fin 68 → Block := ![0,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,6,7,7,7,7,7,7]

def repairRow : Fin 68 → Nat := ![0,0,0,0,0,0,1,1,1,1,1,4,5,0,1,2,2,4,0,0,0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,1,1,1,2,2,2,2,2,3,3,3,3,3,4,4,6,6,6,6,6,7,7,7,8,8,9,10,0,0,0,1,3,4]

def repairCol : Fin 68 → Nat := ![0,1,2,3,4,5,1,2,3,4,5,5,5,0,2,2,3,4,0,1,2,3,4,5,6,7,8,9,10,1,2,3,4,5,6,7,8,9,2,3,5,6,7,3,6,7,8,9,6,8,6,7,8,9,10,7,9,10,8,10,10,10,0,7,8,8,3,8]

theorem repairRow_lt : ∀ k : Fin 68, repairRow k<blockSize (repairBlock k) := by decide +kernel
theorem repairCol_lt : ∀ k : Fin 68, repairCol k<blockSize (repairBlock k) := by decide +kernel
def repairRowFin (k : Fin 68) : Fin (blockSize (repairBlock k)) := ⟨repairRow k,repairRow_lt k⟩
def repairColFin (k : Fin 68) : Fin (blockSize (repairBlock k)) := ⟨repairCol k,repairCol_lt k⟩

theorem repairCoordinate_agrees : ∀ k : Fin 68,
    Factored.HighData.repairCoordinate k.val=((repairBlock k).val,repairRow k,repairCol k) := by decide +kernel

theorem sourceRepairCoordinate_agrees : ∀ k : Fin 68,
    ThomsonNegative.Certificate.Correction.Source.repairCoordinate k.val=
      ((repairBlock k).val,repairRow k,repairCol k) := by decide +kernel

def gramUnit (b : Block) (i j : Fin (blockSize b)) : GramFamily :=
  Pi.single b (Matrix.single i j 1)

theorem coefficientMap_gramUnit (a : ℝ) (b : Block) (i j : Fin (blockSize b)) :
    coefficientMap a (gramUnit b i j)=mixedCoefficient (sourceBasis.eval a) b i j := by
  classical
  change (∑ b', ∑ r, ∑ s, gramUnit b i j b' r s •
    mixedCoefficient (sourceBasis.eval a) b' r s)=_
  rw [Finset.sum_eq_single b]
  · simp [gramUnit,Matrix.single_apply,ite_and,eq_comm]
  · intro b' hb' hne
    have hz : gramUnit b i j b'=0 := Pi.single_eq_of_ne hne _
    simp only [hz,Matrix.zero_apply,zero_smul,Finset.sum_const_zero]
  · simp

theorem gramUnit_entry (b : Block) (i j : Fin (blockSize b))
    (b' : Block) (r s : Fin (blockSize b')) :
    gramUnit b i j b' r s=if b'=b ∧ r.val=i.val ∧ s.val=j.val then 1 else 0 := by
  classical
  by_cases hb : b'=b
  · subst b'
    simp [gramUnit,Matrix.single_apply,Fin.ext_iff,eq_comm,and_comm]
  · simp [gramUnit,Pi.single_apply,hb]

def repairUnit (k : Fin 68) : GramFamily :=
  gramUnit (repairBlock k) (repairRowFin k) (repairColFin k)+
    if repairRow k=repairCol k then 0 else
      gramUnit (repairBlock k) (repairColFin k) (repairRowFin k)

def repairMultiplicity (k : Fin 68) : ℝ := if repairRow k=repairCol k then 1 else 2

theorem coefficientMap_repairUnit (a : ℝ) (k : Fin 68) :
    coefficientMap a (repairUnit k)=repairMultiplicity k •
      mixedCoefficient (sourceBasis.eval a) (repairBlock k) (repairRowFin k) (repairColFin k) := by
  rw [repairUnit,map_add,coefficientMap_gramUnit]
  by_cases h : repairRow k=repairCol k
  · simp [h,repairMultiplicity]
  · simp only [h,if_false,coefficientMap_gramUnit,mixedCoefficient_symm,
      repairMultiplicity,two_smul]

def unitMask (k : Fin 68) (b : Block) (i j : Fin (blockSize b)) : Nat :=
  if b=repairBlock k ∧ ((i.val=repairRow k ∧ j.val=repairCol k) ∨
      (i.val=repairCol k ∧ j.val=repairRow k)) then 1 else 0

theorem repairUnit_entry (k : Fin 68) (b : Block) (i j : Fin (blockSize b)) :
    repairUnit k b i j=(unitMask k b i j:ℝ) := by
  simp only [repairUnit,Pi.add_apply,Matrix.add_apply,gramUnit_entry,repairRowFin,repairColFin,unitMask]
  simp only [apply_ite,Pi.zero_apply,Matrix.zero_apply,gramUnit_entry,repairRowFin,repairColFin]
  split_ifs <;> simp_all [gramUnit_entry] <;> aesop

theorem unitMask_source : ∀ (k : Fin 68) (b : Block) (i j : Fin (blockSize b)),
    unitMask k b i j=
      if ThomsonNegative.Certificate.Correction.Source.blockIndex b.val i.val j.val=k.val then 1 else 0 := by
  decide +kernel

def insertRepair : ChartSpace →ₗ[ℝ] GramFamily where
  toFun x := ∑ k, x k • repairUnit k
  map_add' x y := by simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' c x := by simp only [Pi.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum,RingHom.id_apply]

theorem insertRepair_entry (x : ChartSpace) (b : Block) (i j : Fin (blockSize b)) :
    insertRepair x b i j=
      if h : ThomsonNegative.Certificate.Correction.Source.blockIndex b.val i.val j.val<68 then
        x ⟨_,h⟩ else 0 := by
  classical
  change (∑ k, x k • repairUnit k) b i j=_
  simp only [Finset.sum_apply,Matrix.sum_apply,Pi.smul_apply,Matrix.smul_apply,smul_eq_mul,
    repairUnit_entry,unitMask_source,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,mul_ite,mul_one,mul_zero]
  by_cases h : ThomsonNegative.Certificate.Correction.Source.blockIndex b.val i.val j.val<68
  · rw [dif_pos h]
    have he (k : Fin 68) :
        (ThomsonNegative.Certificate.Correction.Source.blockIndex b.val i.val j.val=k.val) ↔
          k=⟨_,h⟩ := by simp [Fin.ext_iff,eq_comm]
    simp_rw [he]
    simp
  · rw [dif_neg h]
    apply Finset.sum_eq_zero
    intro k hk
    rw [if_neg (by intro he;have hi:=k.isLt;omega)]

#print axioms insertRepair_entry
end ThomsonNegative.Structure.Concrete
