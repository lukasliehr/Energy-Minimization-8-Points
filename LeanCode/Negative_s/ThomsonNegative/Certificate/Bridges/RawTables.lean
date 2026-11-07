import ThomsonNegative.Certificate.Bridges.RawMoment
import ThomsonNegative.Certificate.Bridges.RawSynthesis
import ThomsonNegative.Certificate.Bridges.PowerTables
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000
@[simp] theorem fullTag_000 : fullTag (0:Fin 102)=(0,0,0) := rfl
@[simp] theorem fullTag_001 : fullTag (1:Fin 102)=(1,0,0) := rfl
@[simp] theorem fullTag_002 : fullTag (2:Fin 102)=(0,1,0) := rfl
@[simp] theorem fullTag_003 : fullTag (3:Fin 102)=(2,0,0) := rfl
@[simp] theorem fullTag_004 : fullTag (4:Fin 102)=(0,0,1) := rfl
@[simp] theorem fullTag_005 : fullTag (5:Fin 102)=(1,1,0) := rfl
@[simp] theorem fullTag_006 : fullTag (6:Fin 102)=(3,0,0) := rfl
@[simp] theorem fullTag_007 : fullTag (7:Fin 102)=(0,2,0) := rfl
@[simp] theorem fullTag_008 : fullTag (8:Fin 102)=(1,0,1) := rfl
@[simp] theorem fullTag_009 : fullTag (9:Fin 102)=(2,1,0) := rfl
@[simp] theorem fullTag_010 : fullTag (10:Fin 102)=(4,0,0) := rfl
@[simp] theorem fullTag_011 : fullTag (11:Fin 102)=(0,1,1) := rfl
@[simp] theorem fullTag_012 : fullTag (12:Fin 102)=(1,2,0) := rfl
@[simp] theorem fullTag_013 : fullTag (13:Fin 102)=(2,0,1) := rfl
@[simp] theorem fullTag_014 : fullTag (14:Fin 102)=(3,1,0) := rfl
@[simp] theorem fullTag_015 : fullTag (15:Fin 102)=(5,0,0) := rfl
@[simp] theorem fullTag_016 : fullTag (16:Fin 102)=(0,0,2) := rfl
@[simp] theorem fullTag_017 : fullTag (17:Fin 102)=(0,3,0) := rfl
@[simp] theorem fullTag_018 : fullTag (18:Fin 102)=(1,1,1) := rfl
@[simp] theorem fullTag_019 : fullTag (19:Fin 102)=(2,2,0) := rfl
@[simp] theorem fullTag_020 : fullTag (20:Fin 102)=(3,0,1) := rfl
@[simp] theorem fullTag_021 : fullTag (21:Fin 102)=(4,1,0) := rfl
@[simp] theorem fullTag_022 : fullTag (22:Fin 102)=(6,0,0) := rfl
@[simp] theorem fullTag_023 : fullTag (23:Fin 102)=(0,2,1) := rfl
@[simp] theorem fullTag_024 : fullTag (24:Fin 102)=(1,0,2) := rfl
@[simp] theorem fullTag_025 : fullTag (25:Fin 102)=(1,3,0) := rfl
@[simp] theorem fullTag_026 : fullTag (26:Fin 102)=(2,1,1) := rfl
@[simp] theorem fullTag_027 : fullTag (27:Fin 102)=(3,2,0) := rfl
@[simp] theorem fullTag_028 : fullTag (28:Fin 102)=(4,0,1) := rfl
@[simp] theorem fullTag_029 : fullTag (29:Fin 102)=(5,1,0) := rfl
@[simp] theorem fullTag_030 : fullTag (30:Fin 102)=(7,0,0) := rfl
@[simp] theorem fullTag_031 : fullTag (31:Fin 102)=(0,1,2) := rfl
@[simp] theorem fullTag_032 : fullTag (32:Fin 102)=(0,4,0) := rfl
@[simp] theorem fullTag_033 : fullTag (33:Fin 102)=(1,2,1) := rfl
@[simp] theorem fullTag_034 : fullTag (34:Fin 102)=(2,0,2) := rfl
@[simp] theorem fullTag_035 : fullTag (35:Fin 102)=(2,3,0) := rfl
@[simp] theorem fullTag_036 : fullTag (36:Fin 102)=(3,1,1) := rfl
@[simp] theorem fullTag_037 : fullTag (37:Fin 102)=(4,2,0) := rfl
@[simp] theorem fullTag_038 : fullTag (38:Fin 102)=(5,0,1) := rfl
@[simp] theorem fullTag_039 : fullTag (39:Fin 102)=(6,1,0) := rfl
@[simp] theorem fullTag_040 : fullTag (40:Fin 102)=(8,0,0) := rfl
@[simp] theorem fullTag_041 : fullTag (41:Fin 102)=(0,0,3) := rfl
@[simp] theorem fullTag_042 : fullTag (42:Fin 102)=(0,3,1) := rfl
@[simp] theorem fullTag_043 : fullTag (43:Fin 102)=(1,1,2) := rfl
@[simp] theorem fullTag_044 : fullTag (44:Fin 102)=(1,4,0) := rfl
@[simp] theorem fullTag_045 : fullTag (45:Fin 102)=(2,2,1) := rfl
@[simp] theorem fullTag_046 : fullTag (46:Fin 102)=(3,0,2) := rfl
@[simp] theorem fullTag_047 : fullTag (47:Fin 102)=(3,3,0) := rfl
@[simp] theorem fullTag_048 : fullTag (48:Fin 102)=(4,1,1) := rfl
@[simp] theorem fullTag_049 : fullTag (49:Fin 102)=(5,2,0) := rfl
@[simp] theorem fullTag_050 : fullTag (50:Fin 102)=(6,0,1) := rfl
@[simp] theorem fullTag_051 : fullTag (51:Fin 102)=(7,1,0) := rfl
@[simp] theorem fullTag_052 : fullTag (52:Fin 102)=(9,0,0) := rfl
@[simp] theorem fullTag_053 : fullTag (53:Fin 102)=(0,2,2) := rfl
@[simp] theorem fullTag_054 : fullTag (54:Fin 102)=(0,5,0) := rfl
@[simp] theorem fullTag_055 : fullTag (55:Fin 102)=(1,0,3) := rfl
@[simp] theorem fullTag_056 : fullTag (56:Fin 102)=(1,3,1) := rfl
@[simp] theorem fullTag_057 : fullTag (57:Fin 102)=(2,1,2) := rfl
@[simp] theorem fullTag_058 : fullTag (58:Fin 102)=(2,4,0) := rfl
@[simp] theorem fullTag_059 : fullTag (59:Fin 102)=(3,2,1) := rfl
@[simp] theorem fullTag_060 : fullTag (60:Fin 102)=(4,0,2) := rfl
@[simp] theorem fullTag_061 : fullTag (61:Fin 102)=(4,3,0) := rfl
@[simp] theorem fullTag_062 : fullTag (62:Fin 102)=(5,1,1) := rfl
@[simp] theorem fullTag_063 : fullTag (63:Fin 102)=(6,2,0) := rfl
@[simp] theorem fullTag_064 : fullTag (64:Fin 102)=(7,0,1) := rfl
@[simp] theorem fullTag_065 : fullTag (65:Fin 102)=(8,1,0) := rfl
@[simp] theorem fullTag_066 : fullTag (66:Fin 102)=(10,0,0) := rfl
@[simp] theorem fullTag_067 : fullTag (67:Fin 102)=(0,1,3) := rfl
@[simp] theorem fullTag_068 : fullTag (68:Fin 102)=(0,4,1) := rfl
@[simp] theorem fullTag_069 : fullTag (69:Fin 102)=(1,2,2) := rfl
@[simp] theorem fullTag_070 : fullTag (70:Fin 102)=(1,5,0) := rfl
@[simp] theorem fullTag_071 : fullTag (71:Fin 102)=(2,0,3) := rfl
@[simp] theorem fullTag_072 : fullTag (72:Fin 102)=(2,3,1) := rfl
@[simp] theorem fullTag_073 : fullTag (73:Fin 102)=(3,1,2) := rfl
@[simp] theorem fullTag_074 : fullTag (74:Fin 102)=(3,4,0) := rfl
@[simp] theorem fullTag_075 : fullTag (75:Fin 102)=(4,2,1) := rfl
@[simp] theorem fullTag_076 : fullTag (76:Fin 102)=(5,0,2) := rfl
@[simp] theorem fullTag_077 : fullTag (77:Fin 102)=(5,3,0) := rfl
@[simp] theorem fullTag_078 : fullTag (78:Fin 102)=(6,1,1) := rfl
@[simp] theorem fullTag_079 : fullTag (79:Fin 102)=(7,2,0) := rfl
@[simp] theorem fullTag_080 : fullTag (80:Fin 102)=(8,0,1) := rfl
@[simp] theorem fullTag_081 : fullTag (81:Fin 102)=(9,1,0) := rfl
@[simp] theorem fullTag_082 : fullTag (82:Fin 102)=(11,0,0) := rfl
@[simp] theorem fullTag_083 : fullTag (83:Fin 102)=(0,0,4) := rfl
@[simp] theorem fullTag_084 : fullTag (84:Fin 102)=(0,3,2) := rfl
@[simp] theorem fullTag_085 : fullTag (85:Fin 102)=(0,6,0) := rfl
@[simp] theorem fullTag_086 : fullTag (86:Fin 102)=(1,1,3) := rfl
@[simp] theorem fullTag_087 : fullTag (87:Fin 102)=(1,4,1) := rfl
@[simp] theorem fullTag_088 : fullTag (88:Fin 102)=(2,2,2) := rfl
@[simp] theorem fullTag_089 : fullTag (89:Fin 102)=(2,5,0) := rfl
@[simp] theorem fullTag_090 : fullTag (90:Fin 102)=(3,0,3) := rfl
@[simp] theorem fullTag_091 : fullTag (91:Fin 102)=(3,3,1) := rfl
@[simp] theorem fullTag_092 : fullTag (92:Fin 102)=(4,1,2) := rfl
@[simp] theorem fullTag_093 : fullTag (93:Fin 102)=(4,4,0) := rfl
@[simp] theorem fullTag_094 : fullTag (94:Fin 102)=(5,2,1) := rfl
@[simp] theorem fullTag_095 : fullTag (95:Fin 102)=(6,0,2) := rfl
@[simp] theorem fullTag_096 : fullTag (96:Fin 102)=(6,3,0) := rfl
@[simp] theorem fullTag_097 : fullTag (97:Fin 102)=(7,1,1) := rfl
@[simp] theorem fullTag_098 : fullTag (98:Fin 102)=(8,2,0) := rfl
@[simp] theorem fullTag_099 : fullTag (99:Fin 102)=(9,0,1) := rfl
@[simp] theorem fullTag_100 : fullTag (100:Fin 102)=(10,1,0) := rfl
@[simp] theorem fullTag_101 : fullTag (101:Fin 102)=(12,0,0) := rfl
def qTerms0 : List RawTerm := [(1,(0,0,0))]
theorem qTerms0_eq : termsPolynomial 0 0 qTerms0=kernelQPolynomial 0 := by
  apply MvPolynomial.funext
  intro x
  simp [qTerms0,termsPolynomial,termPolynomial,kernelQPolynomial] <;> ring
def qTerms1 : List RawTerm := [(1,(0,0,1)),(-1,(1,1,0))]
theorem qTerms1_eq : termsPolynomial 0 0 qTerms1=kernelQPolynomial 1 := by
  apply MvPolynomial.funext
  intro x
  simp [qTerms1,termsPolynomial,termPolynomial,kernelQPolynomial] <;> ring
def qTerms2 : List RawTerm := [(-1,(0,0,0)),(2,(0,0,2)),(1,(0,2,0)),(-4,(1,1,1)),(1,(2,0,0)),(1,(2,2,0))]
theorem qTerms2_eq : termsPolynomial 0 0 qTerms2=kernelQPolynomial 2 := by
  apply MvPolynomial.funext
  intro x
  simp [qTerms2,termsPolynomial,termPolynomial,kernelQPolynomial] <;> ring
def qTerms3 : List RawTerm := [(-3,(0,0,1)),(4,(0,0,3)),(3,(0,2,1)),(3,(1,1,0)),(-12,(1,1,2)),(-3,(1,3,0)),(3,(2,0,1)),(9,(2,2,1)),(-3,(3,1,0)),(-1,(3,3,0))]
theorem qTerms3_eq : termsPolynomial 0 0 qTerms3=kernelQPolynomial 3 := by
  apply MvPolynomial.funext
  intro x
  simp [qTerms3,termsPolynomial,termPolynomial,kernelQPolynomial] <;> ring
def qTerms4 : List RawTerm := [(1,(0,0,0)),(-8,(0,0,2)),(8,(0,0,4)),(-2,(0,2,0)),(8,(0,2,2)),(1,(0,4,0)),(16,(1,1,1)),(-32,(1,1,3)),(-16,(1,3,1)),(-2,(2,0,0)),(8,(2,0,2)),(-4,(2,2,0)),(40,(2,2,2)),(6,(2,4,0)),(-16,(3,1,1)),(-16,(3,3,1)),(1,(4,0,0)),(6,(4,2,0)),(1,(4,4,0))]
theorem qTerms4_eq : termsPolynomial 0 0 qTerms4=kernelQPolynomial 4 := by
  apply MvPolynomial.funext
  intro x
  simp [qTerms4,termsPolynomial,termPolynomial,kernelQPolynomial] <;> ring
def qTerms5 : List RawTerm := [(5,(0,0,1)),(-20,(0,0,3)),(16,(0,0,5)),(-10,(0,2,1)),(20,(0,2,3)),(5,(0,4,1)),(-5,(1,1,0)),(60,(1,1,2)),(-80,(1,1,4)),(10,(1,3,0)),(-60,(1,3,2)),(-5,(1,5,0)),(-10,(2,0,1)),(20,(2,0,3)),(-40,(2,2,1)),(140,(2,2,3)),(50,(2,4,1)),(10,(3,1,0)),(-60,(3,1,2)),(-100,(3,3,2)),(-10,(3,5,0)),(5,(4,0,1)),(50,(4,2,1)),(25,(4,4,1)),(-5,(5,1,0)),(-10,(5,3,0)),(-1,(5,5,0))]
theorem qTerms5_eq : termsPolynomial 0 0 qTerms5=kernelQPolynomial 5 := by
  apply MvPolynomial.funext
  intro x
  simp [qTerms5,termsPolynomial,termPolynomial,kernelQPolynomial] <;> ring
end ThomsonNegative.Certificate.Bridges
