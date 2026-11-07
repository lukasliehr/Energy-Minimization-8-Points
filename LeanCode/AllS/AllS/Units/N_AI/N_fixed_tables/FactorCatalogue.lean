import AllS.Units.N_AI.N_fixed_tables.DenominatorSupport
noncomputable section
namespace Blueprint.CAP.FixedTableDenominators
open Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
def factor00 : List ℚ := [(0:ℚ),(1:ℚ)]
theorem factor00_nonzero (a : ℝ) (ha : physical a) : evalRationalList factor00 a≠0 := by
  have hl : (13/50:ℝ)<a := lt_trans packing_endpoint_bounds.1 ha.1
  have hu : a<(1/3:ℝ) := ha.2
  let t : ℝ := (150*a-39)/11
  have ht : 0<t := by dsimp [t];linarith
  have ht1 : 0<1-t := by dsimp [t];linarith
  have he : (1:ℝ)*evalRationalList factor00 a=(13/50:ℝ)*t^0*(1-t)^1+(1/3:ℝ)*t^1*(1-t)^0 := by
    norm_num [factor00,evalRationalList]
    dsimp [t]
    ring
  have hp : 0<(1:ℝ)*evalRationalList factor00 a := by rw [he];positivity
  intro hz
  rw [hz,mul_zero] at hp
  exact (lt_irrefl 0) hp
#print axioms factor00_nonzero
def factor01 : List ℚ := [(-3:ℚ),(21:ℚ),(-45:ℚ),(35:ℚ)]
theorem factor01_nonzero (a : ℝ) (ha : physical a) : evalRationalList factor01 a≠0 := by
  have hl : (13/50:ℝ)<a := lt_trans packing_endpoint_bounds.1 ha.1
  have hu : a<(1/3:ℝ) := ha.2
  let t : ℝ := (150*a-39)/11
  have ht : 0<t := by dsimp [t];linarith
  have ht1 : 0<1-t := by dsimp [t];linarith
  have he : (1:ℝ)*evalRationalList factor01 a=(829/25000:ℝ)*t^0*(1-t)^3+(111/250:ℝ)*t^1*(1-t)^2+(52/75:ℝ)*t^2*(1-t)^1+(8/27:ℝ)*t^3*(1-t)^0 := by
    norm_num [factor01,evalRationalList]
    dsimp [t]
    ring
  have hp : 0<(1:ℝ)*evalRationalList factor01 a := by rw [he];positivity
  intro hz
  rw [hz,mul_zero] at hp
  exact (lt_irrefl 0) hp
#print axioms factor01_nonzero
def factor02 : List ℚ := [(1:ℚ),(-84:ℚ),(1794:ℚ),(-19684:ℚ),(141983:ℚ),(-783016:ℚ),(3545180:ℚ),(-12904040:ℚ),(35253007:ℚ),(-67080708:ℚ),(81406786:ℚ),(-54042548:ℚ),(13170609:ℚ)]
theorem factor02_nonzero (a : ℝ) (ha : physical a) : evalRationalList factor02 a≠0 := by
  have hl : (13/50:ℝ)<a := lt_trans packing_endpoint_bounds.1 ha.1
  have hu : a<(1/3:ℝ) := ha.2
  let t : ℝ := (150*a-39)/11
  have ht : 0<t := by dsimp [t];linarith
  have ht1 : 0<1-t := by dsimp [t];linarith
  have he : (1:ℝ)*evalRationalList factor02 a=(1014204673741582129/244140625000000000000:ℝ)*t^0*(1-t)^12+(52158368748700573/915527343750000000:ℝ)*t^1*(1-t)^11+(2483428231301897/6866455078125000:ℝ)*t^2*(1-t)^10+(2311137248312101/1647949218750000:ℝ)*t^3*(1-t)^9+(81165991737457/21972656250000:ℝ)*t^4*(1-t)^8+(1146633618988/164794921875:ℝ)*t^5*(1-t)^7+(341866662808/35595703125:ℝ)*t^6*(1-t)^6+(208710226208/21357421875:ℝ)*t^7*(1-t)^5+(18575782192/2562890625:ℝ)*t^8*(1-t)^4+(389154304/102515625:ℝ)*t^9*(1-t)^3+(48637952/36905625:ℝ)*t^10*(1-t)^2+(1183744/4428675:ℝ)*t^11*(1-t)^1+(4096/177147:ℝ)*t^12*(1-t)^0 := by
    norm_num [factor02,evalRationalList]
    dsimp [t]
    ring
  have hp : 0<(1:ℝ)*evalRationalList factor02 a := by rw [he];positivity
  intro hz
  rw [hz,mul_zero] at hp
  exact (lt_irrefl 0) hp
#print axioms factor02_nonzero
def factor03 : List ℚ := [(-1:ℚ),(3:ℚ)]
theorem factor03_nonzero (a : ℝ) (ha : physical a) : evalRationalList factor03 a≠0 := by
  have hl : (13/50:ℝ)<a := lt_trans packing_endpoint_bounds.1 ha.1
  have hu : a<(1/3:ℝ) := ha.2
  let t : ℝ := (150*a-39)/11
  have ht : 0<t := by dsimp [t];linarith
  have ht1 : 0<1-t := by dsimp [t];linarith
  have he : (-1:ℝ)*evalRationalList factor03 a=(11/50:ℝ)*t^0*(1-t)^1 := by
    norm_num [factor03,evalRationalList]
    dsimp [t]
    ring
  have hp : 0<(-1:ℝ)*evalRationalList factor03 a := by rw [he];positivity
  intro hz
  rw [hz,mul_zero] at hp
  exact (lt_irrefl 0) hp
#print axioms factor03_nonzero
def factor04 : List ℚ := [(1:ℚ),(-10:ℚ),(17:ℚ)]
theorem factor04_nonzero (a : ℝ) (ha : physical a) : evalRationalList factor04 a≠0 := by
  have hl : (13/50:ℝ)<a := lt_trans packing_endpoint_bounds.1 ha.1
  have hu : a<(1/3:ℝ) := ha.2
  let t : ℝ := (150*a-39)/11
  have ht : 0<t := by dsimp [t];linarith
  have ht1 : 0<1-t := by dsimp [t];linarith
  have he : (-1:ℝ)*evalRationalList factor04 a=(1127/2500:ℝ)*t^0*(1-t)^2+(74/75:ℝ)*t^1*(1-t)^1+(4/9:ℝ)*t^2*(1-t)^0 := by
    norm_num [factor04,evalRationalList]
    dsimp [t]
    ring
  have hp : 0<(-1:ℝ)*evalRationalList factor04 a := by rw [he];positivity
  intro hz
  rw [hz,mul_zero] at hp
  exact (lt_irrefl 0) hp
#print axioms factor04_nonzero
def factor05 : List ℚ := [(-1:ℚ),(-6:ℚ),(23:ℚ)]
theorem factor05_nonzero (a : ℝ) (ha : physical a) : evalRationalList factor05 a≠0 := by
  have hl : (13/50:ℝ)<a := lt_trans packing_endpoint_bounds.1 ha.1
  have hu : a<(1/3:ℝ) := ha.2
  let t : ℝ := (150*a-39)/11
  have ht : 0<t := by dsimp [t];linarith
  have ht1 : 0<1-t := by dsimp [t];linarith
  have he : (-1:ℝ)*evalRationalList factor05 a=(2513/2500:ℝ)*t^0*(1-t)^2+(118/75:ℝ)*t^1*(1-t)^1+(4/9:ℝ)*t^2*(1-t)^0 := by
    norm_num [factor05,evalRationalList]
    dsimp [t]
    ring
  have hp : 0<(-1:ℝ)*evalRationalList factor05 a := by rw [he];positivity
  intro hz
  rw [hz,mul_zero] at hp
  exact (lt_irrefl 0) hp
#print axioms factor05_nonzero
def factor06 : List ℚ := [(-1:ℚ),(0:ℚ),(78:ℚ),(-408:ℚ),(587:ℚ)]
theorem factor06_nonzero (a : ℝ) (ha : physical a) : evalRationalList factor06 a≠0 := by
  have hl : (13/50:ℝ)<a := lt_trans packing_endpoint_bounds.1 ha.1
  have hu : a<(1/3:ℝ) := ha.2
  let t : ℝ := (150*a-39)/11
  have ht : 0<t := by dsimp [t];linarith
  have ht1 : 0<1-t := by dsimp [t];linarith
  have he : (-1:ℝ)*evalRationalList factor06 a=(1348493/6250000:ℝ)*t^0*(1-t)^4+(87193/93750:ℝ)*t^1*(1-t)^3+(942/625:ℝ)*t^2*(1-t)^2+(136/135:ℝ)*t^3*(1-t)^1+(16/81:ℝ)*t^4*(1-t)^0 := by
    norm_num [factor06,evalRationalList]
    dsimp [t]
    ring
  have hp : 0<(-1:ℝ)*evalRationalList factor06 a := by rw [he];positivity
  intro hz
  rw [hz,mul_zero] at hp
  exact (lt_irrefl 0) hp
#print axioms factor06_nonzero
def factor07 : List ℚ := [(-1:ℚ),(5:ℚ)]
theorem factor07_nonzero (a : ℝ) (ha : physical a) : evalRationalList factor07 a≠0 := by
  have hl : (13/50:ℝ)<a := lt_trans packing_endpoint_bounds.1 ha.1
  have hu : a<(1/3:ℝ) := ha.2
  let t : ℝ := (150*a-39)/11
  have ht : 0<t := by dsimp [t];linarith
  have ht1 : 0<1-t := by dsimp [t];linarith
  have he : (1:ℝ)*evalRationalList factor07 a=(3/10:ℝ)*t^0*(1-t)^1+(2/3:ℝ)*t^1*(1-t)^0 := by
    norm_num [factor07,evalRationalList]
    dsimp [t]
    ring
  have hp : 0<(1:ℝ)*evalRationalList factor07 a := by rw [he];positivity
  intro hz
  rw [hz,mul_zero] at hp
  exact (lt_irrefl 0) hp
#print axioms factor07_nonzero
def factor08 : List ℚ := [(-1:ℚ),(2:ℚ),(7:ℚ)]
theorem factor08_nonzero (a : ℝ) (ha : physical a) : evalRationalList factor08 a≠0 := by
  have hp := (contact_order_packing_bounds a ha.1 ha.2).2
  have he : evalRationalList factor08 a=7*a^2+2*a-1 := by norm_num [factor08,evalRationalList];ring
  rw [he]
  exact ne_of_gt hp
#print axioms factor08_nonzero
def factor09 : List ℚ := [(-1:ℚ),(1:ℚ)]
theorem factor09_nonzero (a : ℝ) (ha : physical a) : evalRationalList factor09 a≠0 := by
  have hl : (13/50:ℝ)<a := lt_trans packing_endpoint_bounds.1 ha.1
  have hu : a<(1/3:ℝ) := ha.2
  let t : ℝ := (150*a-39)/11
  have ht : 0<t := by dsimp [t];linarith
  have ht1 : 0<1-t := by dsimp [t];linarith
  have he : (-1:ℝ)*evalRationalList factor09 a=(37/50:ℝ)*t^0*(1-t)^1+(2/3:ℝ)*t^1*(1-t)^0 := by
    norm_num [factor09,evalRationalList]
    dsimp [t]
    ring
  have hp : 0<(-1:ℝ)*evalRationalList factor09 a := by rw [he];positivity
  intro hz
  rw [hz,mul_zero] at hp
  exact (lt_irrefl 0) hp
#print axioms factor09_nonzero
end Blueprint.CAP.FixedTableDenominators
