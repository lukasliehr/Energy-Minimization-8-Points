import AllS.Units.N_GI.N_contact_spectrum.N_gram_row_00
import AllS.Units.N_GI.N_contact_spectrum.N_gram_row_01
import AllS.Units.N_GI.N_contact_spectrum.N_gram_row_02
import AllS.Units.N_GI.N_contact_spectrum.N_gram_row_03
import AllS.Units.N_GI.N_contact_spectrum.N_gram_row_04
import AllS.Units.N_GI.N_contact_spectrum.N_gram_row_05
import AllS.Units.N_GI.N_contact_spectrum.N_gram_row_06
import AllS.Units.N_GI.N_contact_spectrum.N_gram_row_07
import AllS.Units.N_GI.N_contact_spectrum.N_gram_row_08
import AllS.Units.N_GI.N_contact_spectrum.N_gram_row_09
import AllS.Units.N_GI.N_contact_spectrum.N_gram_row_10
import AllS.Units.N_GI.N_contact_spectrum.N_gram_row_11
import AllS.Units.N_GI.N_contact_spectrum.N_gram_row_12
import AllS.Units.N_GI.N_contact_spectrum.N_synthesis

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem contactGram_raw (w : ℝ) (j k : Fin 13) :
    contactGram w (contactRawVector j) (contactRawVector k)=contactGramEntry w j k := by
  fin_cases j
  · exact contactGram_raw_row_0 w k
  · exact contactGram_raw_row_1 w k
  · exact contactGram_raw_row_2 w k
  · exact contactGram_raw_row_3 w k
  · exact contactGram_raw_row_4 w k
  · exact contactGram_raw_row_5 w k
  · exact contactGram_raw_row_6 w k
  · exact contactGram_raw_row_7 w k
  · exact contactGram_raw_row_8 w k
  · exact contactGram_raw_row_9 w k
  · exact contactGram_raw_row_10 w k
  · exact contactGram_raw_row_11 w k
  · exact contactGram_raw_row_12 w k

def contactBlockValue (a d b x y : ℝ) : ℝ := a*x^2+2*b*x*y+d*y^2

def contactBlockSum (w : ℝ) (x : Fin 13 → ℝ) : ℝ :=
    contactGramDiagonal w 0*(x 0)^2+
    contactBlockValue (contactGramDiagonal w 1) (contactGramDiagonal w 3) (contactGramMixed1 w) (x 1) (x 4)+
    contactBlockValue (contactGramDiagonal w 1) (contactGramDiagonal w 3) (-contactGramMixed1 w) (x 2) (x 3)+
    contactBlockValue (contactGramDiagonal w 5) (contactGramDiagonal w 7) contactGramMixed2 (x 5) (x 8)+
    contactBlockValue (contactGramDiagonal w 5) (contactGramDiagonal w 7) (-contactGramMixed2) (x 6) (x 7)+
    contactGramDiagonal w 9*((x 9)^2+(x 10)^2)+
    contactGramDiagonal w 11*(x 11)^2+contactGramDiagonal w 12*(x 12)^2

def contactRawNormSquare (x : Fin 13 → ℝ) : ℝ :=
    8*(x 0)^2+4*((x 1)^2+(x 2)^2+(x 3)^2+(x 4)^2+(x 5)^2+(x 6)^2+(x 7)^2+(x 8)^2)+
    4*(1+packingHeight)*((x 9)^2+(x 10)^2)+8*((x 11)^2+(x 12)^2)

theorem contactGram_block_sum (w : ℝ) (x : Fin 13 → ℝ) :
    contactGram w (contactRawSynthesis x) (contactRawSynthesis x)=contactBlockSum w x := by
  rw [contactGram_synthesis]
  simp_rw [contactGram_raw]
  norm_num [Fin.sum_univ_succ,Fin.succ,Fin.instOfNat,Fin.ofNat,contactGramEntry,contactBlockSum,contactBlockValue,contactGramDiagonal]
  dsimp
  ring

theorem contactRawSynthesis_norm_formula (x : Fin 13 → ℝ) :
    ‖contactRawSynthesis x‖^2=contactRawNormSquare x := by
  rw [contactRawSynthesis_norm_sq]
  have hH := packing_parameters.2.2.1
  norm_num [Fin.sum_univ_succ,Fin.succ,Fin.instOfNat,Fin.ofNat,boundaryWeight,boundaryBasisIndex,contactRawNormSquare,hH]
  dsimp
  ring

#print axioms contactGram_block_sum
end Blueprint.Thomson.Tail.Implementation
