import AllS.Units.N_AI.N_fixed_tables.D18.OperatorDefinitions
import AllS.Units.N_AI.N_fixed_tables.GramEntrySupport

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP.FixedTables.D18
open Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Names in the exact fixed-table output order, interpreted as actual Gram blocks. -/
def insertionBlockName : GramBlock 9 → String
  | .inl k => !["F0","F1","F2","F3","F4","F5","F6","F7","F8"] k
  | .inr .m0Plus => "M0_plus"
  | .inr .m0Sign => "M0_sign"
  | .inr .m0Standard => "M0_standard"
  | .inr .m1Even => "M1_even"
  | .inr .m1Odd => "M1_odd"
  | .inr .mdetPlus => "Mdet_plus"
  | .inr .mdetSign => "Mdet_sign"
  | .inr .mdetStandard => "Mdet_standard"

def outputEntry (j : Fin 272) (name : String) (r c : ℕ) : ℝ :=
  if name=(outputCoordinates j).1 ∧
    ((r=(outputCoordinates j).2.1 ∧ c=(outputCoordinates j).2.2) ∨
     (r=(outputCoordinates j).2.2 ∧ c=(outputCoordinates j).2.1)) then 1 else 0

theorem outputEntry_symm (j : Fin 272) (name : String) (r c : ℕ) :
    outputEntry j name c r=outputEntry j name r c := by
  simp only [outputEntry,and_comm,or_comm]

def insertionUnit (j : Fin 272) : GramFamily 9 :=
  ⟨fun b r c => outputEntry j (insertionBlockName b) r.val c.val,
    fun b => by ext r c; exact outputEntry_symm j (insertionBlockName b) r.val c.val⟩

/-- Linear insertion of the table's 272 physical symmetric Gram coordinates. -/
def insertionLinear : (Fin 272 → ℝ) →ₗ[ℝ] GramFamily 9 where
  toFun v := ∑ j,v j • insertionUnit j
  map_add' v w := by simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' x v := by simp only [Pi.smul_apply,smul_smul,Finset.smul_sum,RingHom.id_apply,smul_eq_mul]

theorem insertionLinear_apply (v : Fin 272 → ℝ) :
    insertionLinear v=∑ j,v j • insertionUnit j := rfl

theorem insertionLinear_entry (v : Fin 272 → ℝ) (b : GramBlock 9)
    (r c : Fin (gramBlockDimension 9 b)) :
    (insertionLinear v).val b r c=
      ∑ j,v j*outputEntry j (insertionBlockName b) r.val c.val :=
  fixedGramCombination_apply insertionUnit v b r c

theorem outputCoordinates_active : ∀ j : Fin 272,
    (outputCoordinates j).1="F0" ∨ (outputCoordinates j).1="F1" ∨
    (outputCoordinates j).1="M0_plus" ∨ (outputCoordinates j).1="M0_standard" := by
  decide +kernel

theorem insertionLinear_inactive (v : Fin 272 → ℝ) (b : GramBlock 9)
    (h0 : insertionBlockName b≠"F0") (h1 : insertionBlockName b≠"F1")
    (hp : insertionBlockName b≠"M0_plus") (hs : insertionBlockName b≠"M0_standard") :
    (insertionLinear v).val b=0 := by
  ext r c
  rw [insertionLinear_entry]
  apply Finset.sum_eq_zero
  intro j hj
  have h : insertionBlockName b≠(outputCoordinates j).1 := by
    rcases outputCoordinates_active j with h|h|h|h
    · exact h ▸ h0
    · exact h ▸ h1
    · exact h ▸ hp
    · exact h ▸ hs
  simp [outputEntry,h]

theorem insertionBlockName_injective : Function.Injective insertionBlockName := by
  decide +kernel

theorem insertionUnit_eq_fixed (k : Fin 272) (b : GramBlock 9)
    (i j : Fin (gramBlockDimension 9 b))
    (h : outputCoordinates k=(insertionBlockName b,i.val,j.val)) :
    insertionUnit k=fixedGramUnit b i j := by
  apply Subtype.ext
  funext c r s
  by_cases hc : c=b
  · subst c
    rw [fixedGramUnit_same_block_apply]
    change outputEntry k (insertionBlockName b) r.val s.val=_
    simp only [outputEntry,h,true_and,Fin.ext_iff]
  · rw [fixedGramUnit_other_block b c i j hc]
    have hn : insertionBlockName c≠insertionBlockName b :=
      fun he => hc (insertionBlockName_injective he)
    change outputEntry k (insertionBlockName c) r.val s.val=0
    simp [outputEntry,h,hn]

/-- The actual rational inverse, as a real linear map for shared residual expansions. -/
def inverseLinear (a : ℝ) : (Fin 272 → ℝ) →ₗ[ℝ] (Fin 272 → ℝ) where
  toFun r := (inverseMatrix a).mulVec r
  map_add' v w := Matrix.mulVec_add _ v w
  map_smul' x v := Matrix.mulVec_smul _ x v

def correctionLinear (a : ℝ) : (Fin 272 → ℝ) →ₗ[ℝ] GramFamily 9 :=
  insertionLinear.comp (inverseLinear a)

theorem correctionLinear_apply (a : ℝ) (r : Fin 272 → ℝ) :
    correctionLinear a r=insertionLinear ((inverseMatrix a).mulVec r) := rfl

#print axioms insertionUnit_eq_fixed
#print axioms correctionLinear_apply
#print axioms insertionLinear_entry
#print axioms insertionLinear_inactive
end Blueprint.CAP.FixedTables.D18
