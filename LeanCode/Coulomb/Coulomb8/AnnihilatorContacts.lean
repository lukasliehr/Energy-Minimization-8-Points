import Coulomb8.AnnihilatorData
import Coulomb8.ContactEnergy

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Coulomb8.Annihilators
open scoped BigOperators

def pureIndex (j : Fin 12) : Fin 102 := ⟨j.val+1,by omega⟩

theorem qpow2 : q^2=2 := q_sq

theorem qpow3 : q^3=2*q := by
  calc q^3=q^1*q^2 := by ring
       _ = _ := by simp only [q_sq]; ring

theorem qpow4 : q^4=4 := by
  calc q^4=q^2*q^2 := by ring
       _ = _ := by simp only [q_sq,qpow2]; ring

theorem qpow5 : q^5=4*q := by
  calc q^5=q^3*q^2 := by ring
       _ = _ := by simp only [q_sq,qpow3]; ring

theorem qpow6 : q^6=8 := by
  calc q^6=q^4*q^2 := by ring
       _ = _ := by simp only [q_sq,qpow4]; ring

theorem qpow7 : q^7=8*q := by
  calc q^7=q^5*q^2 := by ring
       _ = _ := by simp only [q_sq,qpow5]; ring

theorem qpow8 : q^8=16 := by
  calc q^8=q^6*q^2 := by ring
       _ = _ := by simp only [q_sq,qpow6]; ring

theorem qpow9 : q^9=16*q := by
  calc q^9=q^7*q^2 := by ring
       _ = _ := by simp only [q_sq,qpow7]; ring

theorem qpow10 : q^10=32 := by
  calc q^10=q^8*q^2 := by ring
       _ = _ := by simp only [q_sq,qpow8]; ring

theorem qpow11 : q^11=32*q := by
  calc q^11=q^9*q^2 := by ring
       _ = _ := by simp only [q_sq,qpow9]; ring

theorem qpow12 : q^12=64 := by
  calc q^12=q^10*q^2 := by ring
       _ = _ := by simp only [q_sq,qpow10]; ring

theorem pure0_1 : L0 1=
    36*∑ i, contactCounts i*nodes a i^1 := by
  simp only [Fin.sum_univ_succ]

  change IP.eval [-288]/2=36*(8*(nodeA a^1)+(4*(nodeB a^1)+(8*(nodeC a^1)+(8*(nodeD a^1)+0))))
  simp only [nodeA,nodeB,nodeC_polynomial,nodeD_polynomial,IP.eval,IP.evalAt]
  push_cast
  ring_nf
  all_goals simp only [qpow2,qpow3,qpow4,qpow5,qpow6,qpow7,qpow8,qpow9,qpow10,qpow11,qpow12]
  all_goals ring

theorem pure1_1 : L1 1=
    36*∑ i, contactCounts i*1*nodes a i^0*nodeSlopes i := by
  simp only [Fin.sum_univ_succ]

  change IP.eval []=36*(8*1*(nodeA a^0)*1+(4*1*(nodeB a^0)*2+(8*1*(nodeC a^0)*(-1-q/2)+(8*1*(nodeD a^0)*(-1+q/2)+0))))
  simp only [nodeA,nodeB,nodeC_polynomial,nodeD_polynomial,IP.eval,IP.evalAt]
  push_cast
  ring_nf
  all_goals simp only [qpow2,qpow3,qpow4,qpow5,qpow6,qpow7,qpow8,qpow9,qpow10,qpow11,qpow12]
  all_goals ring

theorem pure0_2 : L0 2=
    36*∑ i, contactCounts i*nodes a i^2 := by
  simp only [Fin.sum_univ_succ]

  change IP.eval [864,-2304,3456]/2=36*(8*(nodeA a^2)+(4*(nodeB a^2)+(8*(nodeC a^2)+(8*(nodeD a^2)+0))))
  simp only [nodeA,nodeB,nodeC_polynomial,nodeD_polynomial,IP.eval,IP.evalAt]
  push_cast
  ring_nf
  all_goals simp only [qpow2,qpow3,qpow4,qpow5,qpow6,qpow7,qpow8,qpow9,qpow10,qpow11,qpow12]
  all_goals ring

theorem pure1_2 : L1 2=
    36*∑ i, contactCounts i*2*nodes a i^1*nodeSlopes i := by
  simp only [Fin.sum_univ_succ]

  change IP.eval [-1152,3456]=36*(8*2*(nodeA a^1)*1+(4*2*(nodeB a^1)*2+(8*2*(nodeC a^1)*(-1-q/2)+(8*2*(nodeD a^1)*(-1+q/2)+0))))
  simp only [nodeA,nodeB,nodeC_polynomial,nodeD_polynomial,IP.eval,IP.evalAt]
  push_cast
  ring_nf
  all_goals simp only [qpow2,qpow3,qpow4,qpow5,qpow6,qpow7,qpow8,qpow9,qpow10,qpow11,qpow12]
  all_goals ring

theorem pure0_3 : L0 3=
    36*∑ i, contactCounts i*nodes a i^3 := by
  simp only [Fin.sum_univ_succ]

  change IP.eval [-288]/2=36*(8*(nodeA a^3)+(4*(nodeB a^3)+(8*(nodeC a^3)+(8*(nodeD a^3)+0))))
  simp only [nodeA,nodeB,nodeC_polynomial,nodeD_polynomial,IP.eval,IP.evalAt]
  push_cast
  ring_nf
  all_goals simp only [qpow2,qpow3,qpow4,qpow5,qpow6,qpow7,qpow8,qpow9,qpow10,qpow11,qpow12]
  all_goals ring

theorem pure1_3 : L1 3=
    36*∑ i, contactCounts i*3*nodes a i^2*nodeSlopes i := by
  simp only [Fin.sum_univ_succ]

  change IP.eval []=36*(8*3*(nodeA a^2)*1+(4*3*(nodeB a^2)*2+(8*3*(nodeC a^2)*(-1-q/2)+(8*3*(nodeD a^2)*(-1+q/2)+0))))
  simp only [nodeA,nodeB,nodeC_polynomial,nodeD_polynomial,IP.eval,IP.evalAt]
  push_cast
  ring_nf
  all_goals simp only [qpow2,qpow3,qpow4,qpow5,qpow6,qpow7,qpow8,qpow9,qpow10,qpow11,qpow12]
  all_goals ring

theorem pure0_4 : L0 4=
    36*∑ i, contactCounts i*nodes a i^4 := by
  simp only [Fin.sum_univ_succ]

  change IP.eval [576,-3456,12096,-17280,10080]/2=36*(8*(nodeA a^4)+(4*(nodeB a^4)+(8*(nodeC a^4)+(8*(nodeD a^4)+0))))
  simp only [nodeA,nodeB,nodeC_polynomial,nodeD_polynomial,IP.eval,IP.evalAt]
  push_cast
  ring_nf
  all_goals simp only [qpow2,qpow3,qpow4,qpow5,qpow6,qpow7,qpow8,qpow9,qpow10,qpow11,qpow12]
  all_goals ring

theorem pure1_4 : L1 4=
    36*∑ i, contactCounts i*4*nodes a i^3*nodeSlopes i := by
  simp only [Fin.sum_univ_succ]

  change IP.eval [-1728,12096,-25920,20160]=36*(8*4*(nodeA a^3)*1+(4*4*(nodeB a^3)*2+(8*4*(nodeC a^3)*(-1-q/2)+(8*4*(nodeD a^3)*(-1+q/2)+0))))
  simp only [nodeA,nodeB,nodeC_polynomial,nodeD_polynomial,IP.eval,IP.evalAt]
  push_cast
  ring_nf
  all_goals simp only [qpow2,qpow3,qpow4,qpow5,qpow6,qpow7,qpow8,qpow9,qpow10,qpow11,qpow12]
  all_goals ring

theorem pure0_5 : L0 5=
    36*∑ i, contactCounts i*nodes a i^5 := by
  simp only [Fin.sum_univ_succ]

  change IP.eval [-288,1440,-5760,8640,-5760,1440]/2=36*(8*(nodeA a^5)+(4*(nodeB a^5)+(8*(nodeC a^5)+(8*(nodeD a^5)+0))))
  simp only [nodeA,nodeB,nodeC_polynomial,nodeD_polynomial,IP.eval,IP.evalAt]
  push_cast
  ring_nf
  all_goals simp only [qpow2,qpow3,qpow4,qpow5,qpow6,qpow7,qpow8,qpow9,qpow10,qpow11,qpow12]
  all_goals ring

theorem pure1_5 : L1 5=
    36*∑ i, contactCounts i*5*nodes a i^4*nodeSlopes i := by
  simp only [Fin.sum_univ_succ]

  change IP.eval [720,-5760,12960,-11520,3600]=36*(8*5*(nodeA a^4)*1+(4*5*(nodeB a^4)*2+(8*5*(nodeC a^4)*(-1-q/2)+(8*5*(nodeD a^4)*(-1+q/2)+0))))
  simp only [nodeA,nodeB,nodeC_polynomial,nodeD_polynomial,IP.eval,IP.evalAt]
  push_cast
  ring_nf
  all_goals simp only [qpow2,qpow3,qpow4,qpow5,qpow6,qpow7,qpow8,qpow9,qpow10,qpow11,qpow12]
  all_goals ring

theorem pure0_6 : L0 6=
    36*∑ i, contactCounts i*nodes a i^6 := by
  simp only [Fin.sum_univ_succ]

  change IP.eval [432,-4320,23760,-66240,105840,-90720,33264]/2=36*(8*(nodeA a^6)+(4*(nodeB a^6)+(8*(nodeC a^6)+(8*(nodeD a^6)+0))))
  simp only [nodeA,nodeB,nodeC_polynomial,nodeD_polynomial,IP.eval,IP.evalAt]
  push_cast
  ring_nf
  all_goals simp only [qpow2,qpow3,qpow4,qpow5,qpow6,qpow7,qpow8,qpow9,qpow10,qpow11,qpow12]
  all_goals ring

theorem pure1_6 : L1 6=
    36*∑ i, contactCounts i*6*nodes a i^5*nodeSlopes i := by
  simp only [Fin.sum_univ_succ]

  change IP.eval [-2160,23760,-99360,211680,-226800,99792]=36*(8*6*(nodeA a^5)*1+(4*6*(nodeB a^5)*2+(8*6*(nodeC a^5)*(-1-q/2)+(8*6*(nodeD a^5)*(-1+q/2)+0))))
  simp only [nodeA,nodeB,nodeC_polynomial,nodeD_polynomial,IP.eval,IP.evalAt]
  push_cast
  ring_nf
  all_goals simp only [qpow2,qpow3,qpow4,qpow5,qpow6,qpow7,qpow8,qpow9,qpow10,qpow11,qpow12]
  all_goals ring

theorem pure0_7 : L0 7=
    36*∑ i, contactCounts i*nodes a i^7 := by
  simp only [Fin.sum_univ_succ]

  change IP.eval [-288,3024,-18144,55440,-100800,105840,-58464,13104]/2=36*(8*(nodeA a^7)+(4*(nodeB a^7)+(8*(nodeC a^7)+(8*(nodeD a^7)+0))))
  simp only [nodeA,nodeB,nodeC_polynomial,nodeD_polynomial,IP.eval,IP.evalAt]
  push_cast
  ring_nf
  all_goals simp only [qpow2,qpow3,qpow4,qpow5,qpow6,qpow7,qpow8,qpow9,qpow10,qpow11,qpow12]
  all_goals ring

theorem pure1_7 : L1 7=
    36*∑ i, contactCounts i*7*nodes a i^6*nodeSlopes i := by
  simp only [Fin.sum_univ_succ]

  change IP.eval [1512,-18144,83160,-201600,264600,-175392,45864]=36*(8*7*(nodeA a^6)*1+(4*7*(nodeB a^6)*2+(8*7*(nodeC a^6)*(-1-q/2)+(8*7*(nodeD a^6)*(-1+q/2)+0))))
  simp only [nodeA,nodeB,nodeC_polynomial,nodeD_polynomial,IP.eval,IP.evalAt]
  push_cast
  ring_nf
  all_goals simp only [qpow2,qpow3,qpow4,qpow5,qpow6,qpow7,qpow8,qpow9,qpow10,qpow11,qpow12]
  all_goals ring

theorem pure0_8 : L0 8=
    36*∑ i, contactCounts i*nodes a i^8 := by
  simp only [Fin.sum_univ_succ]

  change IP.eval [360,-5184,38304,-157248,408240,-681408,715680,-432576,115848]/2=36*(8*(nodeA a^8)+(4*(nodeB a^8)+(8*(nodeC a^8)+(8*(nodeD a^8)+0))))
  simp only [nodeA,nodeB,nodeC_polynomial,nodeD_polynomial,IP.eval,IP.evalAt]
  push_cast
  ring_nf
  all_goals simp only [qpow2,qpow3,qpow4,qpow5,qpow6,qpow7,qpow8,qpow9,qpow10,qpow11,qpow12]
  all_goals ring

theorem pure1_8 : L1 8=
    36*∑ i, contactCounts i*8*nodes a i^7*nodeSlopes i := by
  simp only [Fin.sum_univ_succ]

  change IP.eval [-2592,38304,-235872,816480,-1703520,2147040,-1514016,463392]=36*(8*8*(nodeA a^7)*1+(4*8*(nodeB a^7)*2+(8*8*(nodeC a^7)*(-1-q/2)+(8*8*(nodeD a^7)*(-1+q/2)+0))))
  simp only [nodeA,nodeB,nodeC_polynomial,nodeD_polynomial,IP.eval,IP.evalAt]
  push_cast
  ring_nf
  all_goals simp only [qpow2,qpow3,qpow4,qpow5,qpow6,qpow7,qpow8,qpow9,qpow10,qpow11,qpow12]
  all_goals ring

theorem pure0_9 : L0 9=
    36*∑ i, contactCounts i*nodes a i^9 := by
  simp only [Fin.sum_univ_succ]

  change IP.eval [-288,4536,-36288,163296,-471744,898128,-1124928,889056,-399168,77112]/2=36*(8*(nodeA a^9)+(4*(nodeB a^9)+(8*(nodeC a^9)+(8*(nodeD a^9)+0))))
  simp only [nodeA,nodeB,nodeC_polynomial,nodeD_polynomial,IP.eval,IP.evalAt]
  push_cast
  ring_nf
  all_goals simp only [qpow2,qpow3,qpow4,qpow5,qpow6,qpow7,qpow8,qpow9,qpow10,qpow11,qpow12]
  all_goals ring

theorem pure1_9 : L1 9=
    36*∑ i, contactCounts i*9*nodes a i^8*nodeSlopes i := by
  simp only [Fin.sum_univ_succ]

  change IP.eval [2268,-36288,244944,-943488,2245320,-3374784,3111696,-1596672,347004]=36*(8*9*(nodeA a^8)*1+(4*9*(nodeB a^8)*2+(8*9*(nodeC a^8)*(-1-q/2)+(8*9*(nodeD a^8)*(-1+q/2)+0))))
  simp only [nodeA,nodeB,nodeC_polynomial,nodeD_polynomial,IP.eval,IP.evalAt]
  push_cast
  ring_nf
  all_goals simp only [qpow2,qpow3,qpow4,qpow5,qpow6,qpow7,qpow8,qpow9,qpow10,qpow11,qpow12]
  all_goals ring

theorem pure0_10 : L0 10=
    36*∑ i, contactCounts i*nodes a i^10 := by
  simp only [Fin.sum_univ_succ]

  change IP.eval [324,-6120,56700,-306720,1096200,-2694384,4619160,-5456160,4252500,-1976040,416556]/2=36*(8*(nodeA a^10)+(4*(nodeB a^10)+(8*(nodeC a^10)+(8*(nodeD a^10)+0))))
  simp only [nodeA,nodeB,nodeC_polynomial,nodeD_polynomial,IP.eval,IP.evalAt]
  push_cast
  ring_nf
  all_goals simp only [qpow2,qpow3,qpow4,qpow5,qpow6,qpow7,qpow8,qpow9,qpow10,qpow11,qpow12]
  all_goals ring

theorem pure1_10 : L1 10=
    36*∑ i, contactCounts i*10*nodes a i^9*nodeSlopes i := by
  simp only [Fin.sum_univ_succ]

  change IP.eval [-3060,56700,-460080,2192400,-6735960,13857480,-19096560,17010000,-8892180,2082780]=36*(8*10*(nodeA a^9)*1+(4*10*(nodeB a^9)*2+(8*10*(nodeC a^9)*(-1-q/2)+(8*10*(nodeD a^9)*(-1+q/2)+0))))
  simp only [nodeA,nodeB,nodeC_polynomial,nodeD_polynomial,IP.eval,IP.evalAt]
  push_cast
  ring_nf
  all_goals simp only [qpow2,qpow3,qpow4,qpow5,qpow6,qpow7,qpow8,qpow9,qpow10,qpow11,qpow12]
  all_goals ring

theorem pure0_11 : L0 11=
    36*∑ i, contactCounts i*nodes a i^11 := by
  simp only [Fin.sum_univ_succ]

  change IP.eval [-288,5940,-59400,350460,-1378080,3775464,-7351344,10157400,-9741600,6159780,-2302344,383724]/2=36*(8*(nodeA a^11)+(4*(nodeB a^11)+(8*(nodeC a^11)+(8*(nodeD a^11)+0))))
  simp only [nodeA,nodeB,nodeC_polynomial,nodeD_polynomial,IP.eval,IP.evalAt]
  push_cast
  ring_nf
  all_goals simp only [qpow2,qpow3,qpow4,qpow5,qpow6,qpow7,qpow8,qpow9,qpow10,qpow11,qpow12]
  all_goals ring

theorem pure1_11 : L1 11=
    36*∑ i, contactCounts i*11*nodes a i^10*nodeSlopes i := by
  simp only [Fin.sum_univ_succ]

  change IP.eval [2970,-59400,525690,-2756160,9438660,-22054032,35550900,-38966400,27719010,-11511720,2110482]=36*(8*11*(nodeA a^10)*1+(4*11*(nodeB a^10)*2+(8*11*(nodeC a^10)*(-1-q/2)+(8*11*(nodeD a^10)*(-1+q/2)+0))))
  simp only [nodeA,nodeB,nodeC_polynomial,nodeD_polynomial,IP.eval,IP.evalAt]
  push_cast
  ring_nf
  all_goals simp only [qpow2,qpow3,qpow4,qpow5,qpow6,qpow7,qpow8,qpow9,qpow10,qpow11,qpow12]
  all_goals ring

theorem pure0_12 : L0 12=
    36*∑ i, contactCounts i*nodes a i^12 := by
  simp only [Fin.sum_univ_succ]

  change IP.eval [306,-7128,79596,-534600,2432430,-7883568,18677736,-32603472,41636430,-37956600,23459436,-8831592,1533042]/2=36*(8*(nodeA a^12)+(4*(nodeB a^12)+(8*(nodeC a^12)+(8*(nodeD a^12)+0))))
  simp only [nodeA,nodeB,nodeC_polynomial,nodeD_polynomial,IP.eval,IP.evalAt]
  push_cast
  ring_nf
  all_goals simp only [qpow2,qpow3,qpow4,qpow5,qpow6,qpow7,qpow8,qpow9,qpow10,qpow11,qpow12]
  all_goals ring

theorem pure1_12 : L1 12=
    36*∑ i, contactCounts i*12*nodes a i^11*nodeSlopes i := by
  simp only [Fin.sum_univ_succ]

  change IP.eval [-3564,79596,-801900,4864860,-19708920,56033208,-114112152,166545720,-170804700,117297180,-48573756,9198252]=36*(8*12*(nodeA a^11)*1+(4*12*(nodeB a^11)*2+(8*12*(nodeC a^11)*(-1-q/2)+(8*12*(nodeD a^11)*(-1+q/2)+0))))
  simp only [nodeA,nodeB,nodeC_polynomial,nodeD_polynomial,IP.eval,IP.evalAt]
  push_cast
  ring_nf
  all_goals simp only [qpow2,qpow3,qpow4,qpow5,qpow6,qpow7,qpow8,qpow9,qpow10,qpow11,qpow12]
  all_goals ring

theorem pure0 (j : Fin 12) : L0 (pureIndex j)=
    36*∑ i, contactCounts i*nodes a i^(j.val+1) := by
  fin_cases j
  · exact pure0_1
  · exact pure0_2
  · exact pure0_3
  · exact pure0_4
  · exact pure0_5
  · exact pure0_6
  · exact pure0_7
  · exact pure0_8
  · exact pure0_9
  · exact pure0_10
  · exact pure0_11
  · exact pure0_12

theorem pure1 (j : Fin 12) : L1 (pureIndex j)=
    36*∑ i, contactCounts i*(j.val+1)*nodes a i^j.val*nodeSlopes i := by
  fin_cases j
  · convert pure1_1 using 1 <;> norm_num [pureIndex] <;> rfl
  · convert pure1_2 using 1 <;> norm_num [pureIndex] <;> rfl
  · convert pure1_3 using 1 <;> norm_num [pureIndex] <;> rfl
  · convert pure1_4 using 1 <;> norm_num [pureIndex] <;> rfl
  · convert pure1_5 using 1 <;> norm_num [pureIndex] <;> rfl
  · convert pure1_6 using 1 <;> norm_num [pureIndex] <;> rfl
  · convert pure1_7 using 1 <;> norm_num [pureIndex] <;> rfl
  · convert pure1_8 using 1 <;> norm_num [pureIndex] <;> rfl
  · convert pure1_9 using 1 <;> norm_num [pureIndex] <;> rfl
  · convert pure1_10 using 1 <;> norm_num [pureIndex] <;> rfl
  · convert pure1_11 using 1 <;> norm_num [pureIndex] <;> rfl
  · convert pure1_12 using 1 <;> norm_num [pureIndex] <;> rfl

theorem constant0 : L0 0=336 := by norm_num [L0,l0,IP.eval,IP.evalAt]
theorem constant1 : L1 0=0 := by rfl
theorem quadratic1 : L1 2=1152*(3*a-1) := by
  change IP.eval [-1152,3456]=1152*(3*a-1)
  norm_num [IP.eval,IP.evalAt]; ring
theorem quadratic1_nonzero : L1 2 ≠ 0 := by
  rw [quadratic1]
  have h := a_lt_third
  intro he; nlinarith

end Coulomb8.Annihilators
