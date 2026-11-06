import ThomsonNegative.Certificate.Bridges.FunctionalBasic
noncomputable section
namespace ThomsonNegative.Certificate.Bridges
open ThomsonNegative.Structure
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
theorem functionalRow080_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 80)=[8,96,-1264,10144,-52224,190400,-540288,1262464,-2373632,3251136,-2769792,1075488] := by decide +kernel
theorem functionalRow080_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 80)=[96,-2528,30432,-208896,952000,-3241728,8837248,-18989056,29260224,-27697920,11830368] := by decide +kernel
theorem functionalRow080_den : Factored.FunctionalData.denominator 80=1 := by decide +kernel
theorem functionalRow080_polynomial : familyPolynomial (invariantMonomial (fullTag (80:Fin 102)))=functionalPolynomial 80 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (80:Fin 102)=(8,0,1) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow080_decode,functionalRow080_den]
  norm_num [functionalRow080_decode,functionalRow080_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow080_derivative : (functionalPolynomial (80:Fin 102)).derivative=functionalSlopePolynomial 80 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow080_decode,functionalRow080_slope_decode,functionalRow080_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow080_decode,functionalRow080_slope_decode,functionalRow080_den,integerPolynomial] <;> ring

theorem functionalRow081_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 81)=[8,-1184,10960,-44256,53760,409920,-2932608,10317312,-23053824,33039168,-27823744,10496928] := by decide +kernel
theorem functionalRow081_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 81)=[-1184,21920,-132768,215040,2049600,-17595648,72221184,-184430592,297352512,-278237440,115466208] := by decide +kernel
theorem functionalRow081_den : Factored.FunctionalData.denominator 81=1 := by decide +kernel
theorem functionalRow081_polynomial : familyPolynomial (invariantMonomial (fullTag (81:Fin 102)))=functionalPolynomial 81 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (81:Fin 102)=(9,1,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow081_decode,functionalRow081_den]
  norm_num [functionalRow081_decode,functionalRow081_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow081_derivative : (functionalPolynomial (81:Fin 102)).derivative=functionalSlopePolynomial 81 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow081_decode,functionalRow081_slope_decode,functionalRow081_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow081_decode,functionalRow081_slope_decode,functionalRow081_den,integerPolynomial] <;> ring

theorem functionalRow082_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 82)=[-24,-5280,49280,-211200,337920,1360128,-10999296,38206080,-82199040,112891680,-91437632,33424512] := by decide +kernel
theorem functionalRow082_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 82)=[-5280,98560,-633600,1351680,6800640,-65995776,267442560,-657592320,1016025120,-914376320,367669632] := by decide +kernel
theorem functionalRow082_den : Factored.FunctionalData.denominator 82=1 := by decide +kernel
theorem functionalRow082_polynomial : familyPolynomial (invariantMonomial (fullTag (82:Fin 102)))=functionalPolynomial 82 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (82:Fin 102)=(11,0,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow082_decode,functionalRow082_den]
  norm_num [functionalRow082_decode,functionalRow082_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow082_derivative : (functionalPolynomial (82:Fin 102)).derivative=functionalSlopePolynomial 82 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow082_decode,functionalRow082_slope_decode,functionalRow082_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow082_decode,functionalRow082_slope_decode,functionalRow082_den,integerPolynomial] <;> ring

theorem functionalRow083_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 83)=[1,-16,108,-392,792,-760,12,344,917,-2680,3072,-2064,722] := by decide +kernel
theorem functionalRow083_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 83)=[-16,216,-1176,3168,-3800,72,2408,7336,-24120,30720,-22704,8664] := by decide +kernel
theorem functionalRow083_den : Factored.FunctionalData.denominator 83=1 := by decide +kernel
theorem functionalRow083_polynomial : familyPolynomial (invariantMonomial (fullTag (83:Fin 102)))=functionalPolynomial 83 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (83:Fin 102)=(0,0,4) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow083_decode,functionalRow083_den]
  norm_num [functionalRow083_decode,functionalRow083_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow083_derivative : (functionalPolynomial (83:Fin 102)).derivative=functionalSlopePolynomial 83 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow083_decode,functionalRow083_slope_decode,functionalRow083_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow083_decode,functionalRow083_slope_decode,functionalRow083_den,integerPolynomial] <;> ring

theorem functionalRow084_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 84)=[-1,26,-295,1916,-7834,20812,-35446,35392,-12605,-14806,24909,-18316,6584] := by decide +kernel
theorem functionalRow084_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 84)=[26,-590,5748,-31336,104060,-212676,247744,-100840,-133254,249090,-201476,79008] := by decide +kernel
theorem functionalRow084_den : Factored.FunctionalData.denominator 84=2 := by decide +kernel
theorem functionalRow084_polynomial : familyPolynomial (invariantMonomial (fullTag (84:Fin 102)))=functionalPolynomial 84 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (84:Fin 102)=(0,3,2) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow084_decode,functionalRow084_den]
  norm_num [functionalRow084_decode,functionalRow084_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow084_derivative : (functionalPolynomial (84:Fin 102)).derivative=functionalSlopePolynomial 84 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow084_decode,functionalRow084_slope_decode,functionalRow084_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow084_decode,functionalRow084_slope_decode,functionalRow084_den,integerPolynomial] <;> ring

theorem functionalRow085_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 85)=[3,-60,714,-6020,36405,-157560,491692,-1124136,1931325,-2563020,2603754,-1807956,618379] := by decide +kernel
theorem functionalRow085_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 85)=[-60,1428,-18060,145620,-787800,2950152,-7868952,15450600,-23067180,26037540,-19887516,7420548] := by decide +kernel
theorem functionalRow085_den : Factored.FunctionalData.denominator 85=4 := by decide +kernel
theorem functionalRow085_polynomial : familyPolynomial (invariantMonomial (fullTag (85:Fin 102)))=functionalPolynomial 85 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (85:Fin 102)=(0,6,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow085_decode,functionalRow085_den]
  norm_num [functionalRow085_decode,functionalRow085_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow085_derivative : (functionalPolynomial (85:Fin 102)).derivative=functionalSlopePolynomial 85 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow085_decode,functionalRow085_slope_decode,functionalRow085_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow085_decode,functionalRow085_slope_decode,functionalRow085_den,integerPolynomial] <;> ring

theorem functionalRow086_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 86)=[1,-18,136,-556,1288,-1512,140,2052,-2603,794,1812,-2936,1522] := by decide +kernel
theorem functionalRow086_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 86)=[-18,272,-1668,5152,-7560,840,14364,-20824,7146,18120,-32296,18264] := by decide +kernel
theorem functionalRow086_den : Factored.FunctionalData.denominator 86=1 := by decide +kernel
theorem functionalRow086_polynomial : familyPolynomial (invariantMonomial (fullTag (86:Fin 102)))=functionalPolynomial 86 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (86:Fin 102)=(1,1,3) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow086_decode,functionalRow086_den]
  norm_num [functionalRow086_decode,functionalRow086_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow086_derivative : (functionalPolynomial (86:Fin 102)).derivative=functionalSlopePolynomial 86 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow086_decode,functionalRow086_slope_decode,functionalRow086_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow086_decode,functionalRow086_slope_decode,functionalRow086_den,integerPolynomial] <;> ring

theorem functionalRow087_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 87)=[-1,28,-347,2454,-10906,31776,-60814,70580,-24141,-84140,192185,-192794,79912] := by decide +kernel
theorem functionalRow087_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 87)=[28,-694,7362,-43624,158880,-364884,494060,-193128,-757260,1921850,-2120734,958944] := by decide +kernel
theorem functionalRow087_den : Factored.FunctionalData.denominator 87=2 := by decide +kernel
theorem functionalRow087_polynomial : familyPolynomial (invariantMonomial (fullTag (87:Fin 102)))=functionalPolynomial 87 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (87:Fin 102)=(1,4,1) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow087_decode,functionalRow087_den]
  norm_num [functionalRow087_decode,functionalRow087_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow087_derivative : (functionalPolynomial (87:Fin 102)).derivative=functionalSlopePolynomial 87 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow087_decode,functionalRow087_slope_decode,functionalRow087_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow087_decode,functionalRow087_slope_decode,functionalRow087_den,integerPolynomial] <;> ring

theorem functionalRow088_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 88)=[1,-20,170,-788,2178,-3656,3568,-2168,3825,-13412,27390,-29300,12908] := by decide +kernel
theorem functionalRow088_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 88)=[-20,340,-2364,8712,-18280,21408,-15176,30600,-120708,273900,-322300,154896] := by decide +kernel
theorem functionalRow088_den : Factored.FunctionalData.denominator 88=1 := by decide +kernel
theorem functionalRow088_polynomial : familyPolynomial (invariantMonomial (fullTag (88:Fin 102)))=functionalPolynomial 88 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (88:Fin 102)=(2,2,2) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow088_decode,functionalRow088_den]
  norm_num [functionalRow088_decode,functionalRow088_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow088_derivative : (functionalPolynomial (88:Fin 102)).derivative=functionalSlopePolynomial 88 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow088_decode,functionalRow088_slope_decode,functionalRow088_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow088_decode,functionalRow088_slope_decode,functionalRow088_den,integerPolynomial] <;> ring

theorem functionalRow089_decode : Exact.recCoeffs (Factored.FunctionalData.numerator 89)=[1,6,-283,2760,-14380,46660,-92046,56664,301505,-1178170,2111641,-1999216,799754] := by decide +kernel
theorem functionalRow089_slope_decode : Exact.recCoeffs (Factored.FunctionalData.slopeNumerator 89)=[6,-566,8280,-57520,233300,-552276,396648,2412040,-10603530,21116410,-21991376,9597048] := by decide +kernel
theorem functionalRow089_den : Factored.FunctionalData.denominator 89=2 := by decide +kernel
theorem functionalRow089_polynomial : familyPolynomial (invariantMonomial (fullTag (89:Fin 102)))=functionalPolynomial 89 := by
  apply Polynomial.funext
  intro a
  rw [show fullTag (89:Fin 102)=(2,5,0) from rfl,familyPolynomial_invariant_eval]
  simp only [functionalPolynomial,Fin.val_natCast,Nat.reduceMod,Polynomial.eval_mul,Polynomial.eval_C,integerPolynomial_eval,
    functionalRow089_decode,functionalRow089_den]
  norm_num [functionalRow089_decode,functionalRow089_den,orbitCount,orbitSigma,orbitE2,orbitE3,Fin.sum_univ_succ,Packed.evalZ,Packed.horner] <;>
    ring_nf <;> norm_num <;> ring

theorem functionalRow089_derivative : (functionalPolynomial (89:Fin 102)).derivative=functionalSlopePolynomial 89 := by
  simp only [functionalPolynomial,functionalSlopePolynomial,Fin.val_natCast,Nat.reduceMod,functionalRow089_decode,functionalRow089_slope_decode,functionalRow089_den]
  apply Polynomial.funext
  intro a
  norm_num [functionalRow089_decode,functionalRow089_slope_decode,functionalRow089_den,integerPolynomial] <;> ring

end ThomsonNegative.Certificate.Bridges
