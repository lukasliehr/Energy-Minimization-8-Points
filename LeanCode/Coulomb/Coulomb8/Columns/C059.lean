import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C059

def r0 : ℚ := { num := 9, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -45, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 351, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -81, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 495, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 27, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -243, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 9, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -3, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 15, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -63, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 291, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -405, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := 21, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 1, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -5, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 45, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -67, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 37, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := -217, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := 357, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := -71, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := 25, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 9, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := 99, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := -141, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := 153, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 57, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -17, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 23, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -79, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 79, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -197, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 151, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -61, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -3, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -5, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -7, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 13, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -17, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 79, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -47, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 109, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 1, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -1, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -9, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 1, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 1, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -5, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 45, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -61, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := -145, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 261, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -77, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 49, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -3, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -21, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 9, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -7, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -199, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 155, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := -63, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := 5, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := -11, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := 7, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 11, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := 59, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 81, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,0,r0,r1,r2,r3,r4,r5,r6,r7,r7],[0,r8,r9,r10,r11,r12,42,-15,r1,r13],[r14,r15,r16,r17,r18,r19,r20,r21,r22],[0,r23,r17,r24,r25,r26,r27,r28],[r8,r29,r30,r31,r32,r33,r34],[0,r35,3,r36,r37,r9],[r38,r39,r40,r41,r42],[0,0,r43,r44],[r35,2,r45],[],[r46],[],[],[r47,r48,r49,r50,28,r51,r52,r53,r54],[0,0,r46,r55,r9,r56,r57,r58],[r8,r29,r30,r31,r59,r60,r61],[],[r46,r48,r62,r63,r64],[],[],[],[],[],[],[0,0,0,0,r43,-1,r43],[0,0,r35,r65,r39,r7],[],[0,0,r43,r44],[],[],[],[],[],[r23,-6,r66,-18,r67],[],[r35,2,r45],[],[],[],[],[],[],[],[],[],[r43],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,0,r0,r1,r2,r3,r4,r5,r6,r7,r7]),(⟨0,0,1⟩,[0,r8,r9,r10,r11,r12,42,-15,r1,r13]),(⟨0,0,2⟩,[r14,r15,r16,r17,r18,r19,r20,r21,r22]),(⟨0,0,3⟩,[0,r23,r17,r24,r25,r26,r27,r28]),(⟨0,0,4⟩,[r8,r29,r30,r31,r32,r33,r34]),(⟨0,0,5⟩,[0,r35,3,r36,r37,r9]),(⟨0,0,6⟩,[r38,r39,r40,r41,r42]),(⟨0,0,7⟩,[0,0,r43,r44]),(⟨0,0,8⟩,[r35,2,r45]),(⟨0,0,10⟩,[r46]),(⟨0,1,0⟩,[0,r8,r9,r10,r11,r12,42,-15,r1,r13]),(⟨0,1,1⟩,[r47,r48,r49,r50,28,r51,r52,r53,r54]),(⟨0,1,2⟩,[0,0,r46,r55,r9,r56,r57,r58]),(⟨0,1,3⟩,[r8,r29,r30,r31,r59,r60,r61]),(⟨0,1,5⟩,[r46,r48,r62,r63,r64]),(⟨0,2,0⟩,[r14,r15,r16,r17,r18,r19,r20,r21,r22]),(⟨0,2,1⟩,[0,0,r46,r55,r9,r56,r57,r58]),(⟨0,2,2⟩,[0,0,0,0,r43,-1,r43]),(⟨0,2,3⟩,[0,0,r35,r65,r39,r7]),(⟨0,2,5⟩,[0,0,r43,r44]),(⟨0,3,0⟩,[0,r23,r17,r24,r25,r26,r27,r28]),(⟨0,3,1⟩,[r8,r29,r30,r31,r59,r60,r61]),(⟨0,3,2⟩,[0,0,r35,r65,r39,r7]),(⟨0,3,3⟩,[r23,-6,r66,-18,r67]),(⟨0,3,5⟩,[r35,2,r45]),(⟨0,4,0⟩,[r8,r29,r30,r31,r32,r33,r34]),(⟨0,5,0⟩,[0,r35,3,r36,r37,r9]),(⟨0,5,1⟩,[r46,r48,r62,r63,r64]),(⟨0,5,2⟩,[0,0,r43,r44]),(⟨0,5,3⟩,[r35,2,r45]),(⟨0,5,5⟩,[r43]),(⟨0,6,0⟩,[r38,r39,r40,r41,r42]),(⟨0,7,0⟩,[0,0,r43,r44]),(⟨0,8,0⟩,[r35,2,r45]),(⟨0,10,0⟩,[r46]),(⟨1,0,0⟩,[0,r8,r9,r10,r11,r12,42,-15,r1,r13]),(⟨1,0,1⟩,[r47,r48,r49,r50,28,r51,r52,r53,r54]),(⟨1,0,2⟩,[0,0,r46,r55,r9,r56,r57,r58]),(⟨1,0,3⟩,[r8,r29,r30,r31,r59,r60,r61]),(⟨1,0,5⟩,[r46,r48,r62,r63,r64]),(⟨1,1,0⟩,[r47,r48,r49,r50,28,r51,r52,r53,r54]),(⟨1,2,0⟩,[0,0,r46,r55,r9,r56,r57,r58]),(⟨1,3,0⟩,[r8,r29,r30,r31,r59,r60,r61]),(⟨1,5,0⟩,[r46,r48,r62,r63,r64]),(⟨2,0,0⟩,[r14,r15,r16,r17,r18,r19,r20,r21,r22]),(⟨2,0,1⟩,[0,0,r46,r55,r9,r56,r57,r58]),(⟨2,0,2⟩,[0,0,0,0,r43,-1,r43]),(⟨2,0,3⟩,[0,0,r35,r65,r39,r7]),(⟨2,0,5⟩,[0,0,r43,r44]),(⟨2,1,0⟩,[0,0,r46,r55,r9,r56,r57,r58]),(⟨2,2,0⟩,[0,0,0,0,r43,-1,r43]),(⟨2,3,0⟩,[0,0,r35,r65,r39,r7]),(⟨2,5,0⟩,[0,0,r43,r44]),(⟨3,0,0⟩,[0,r23,r17,r24,r25,r26,r27,r28]),(⟨3,0,1⟩,[r8,r29,r30,r31,r59,r60,r61]),(⟨3,0,2⟩,[0,0,r35,r65,r39,r7]),(⟨3,0,3⟩,[r23,-6,r66,-18,r67]),(⟨3,0,5⟩,[r35,2,r45]),(⟨3,1,0⟩,[r8,r29,r30,r31,r59,r60,r61]),(⟨3,2,0⟩,[0,0,r35,r65,r39,r7]),(⟨3,3,0⟩,[r23,-6,r66,-18,r67]),(⟨3,5,0⟩,[r35,2,r45]),(⟨4,0,0⟩,[r8,r29,r30,r31,r32,r33,r34]),(⟨5,0,0⟩,[0,r35,3,r36,r37,r9]),(⟨5,0,1⟩,[r46,r48,r62,r63,r64]),(⟨5,0,2⟩,[0,0,r43,r44]),(⟨5,0,3⟩,[r35,2,r45]),(⟨5,0,5⟩,[r43]),(⟨5,1,0⟩,[r46,r48,r62,r63,r64]),(⟨5,2,0⟩,[0,0,r43,r44]),(⟨5,3,0⟩,[r35,2,r45]),(⟨5,5,0⟩,[r43]),(⟨6,0,0⟩,[r38,r39,r40,r41,r42]),(⟨7,0,0⟩,[0,0,r43,r44]),(⟨8,0,0⟩,[r35,2,r45]),(⟨10,0,0⟩,[r46])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,-3,15,-21,3,6]),(⟨0,0,1⟩,[1,-5,10,-11,7]),(⟨0,0,2⟩,[0,0,2,-2]),(⟨0,0,3⟩,[-3,8,-9]),(⟨0,0,5⟩,[2]),(⟨0,1,0⟩,[1,-5,10,-11,7]),(⟨0,2,0⟩,[0,0,2,-2]),(⟨0,3,0⟩,[-3,8,-9]),(⟨0,5,0⟩,[2]),(⟨1,0,0⟩,[1,-5,10,-11,7]),(⟨2,0,0⟩,[0,0,2,-2]),(⟨3,0,0⟩,[-3,8,-9]),(⟨5,0,0⟩,[2])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[0,-3,15,-21,3,6]),(⟨0,0,1⟩,[1,-5,10,-11,7]),(⟨0,0,2⟩,[0,0,2,-2]),(⟨0,0,3⟩,[-3,8,-9]),(⟨0,0,5⟩,[2]),(⟨0,1,0⟩,[1,-5,10,-11,7]),(⟨0,2,0⟩,[0,0,2,-2]),(⟨0,3,0⟩,[-3,8,-9]),(⟨0,5,0⟩,[2]),(⟨1,0,0⟩,[1,-5,10,-11,7]),(⟨2,0,0⟩,[0,0,2,-2]),(⟨3,0,0⟩,[-3,8,-9]),(⟨5,0,0⟩,[2])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 1 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r46) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 1 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r46) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨5,0,0⟩,[2])]

noncomputable def partial12 : Poly := [(⟨5,0,0⟩,[0,-6,30,-42,6,12]),(⟨5,0,1⟩,[2,-10,20,-22,14]),(⟨5,0,2⟩,[0,0,4,-4]),(⟨5,0,3⟩,[-6,16,-18]),(⟨5,0,5⟩,[4]),(⟨5,1,0⟩,[2,-10,20,-22,14]),(⟨5,2,0⟩,[0,0,4,-4]),(⟨5,3,0⟩,[-6,16,-18]),(⟨5,5,0⟩,[4]),(⟨6,0,0⟩,[2,-10,20,-22,14]),(⟨7,0,0⟩,[0,0,4,-4]),(⟨8,0,0⟩,[-6,16,-18]),(⟨10,0,0⟩,[4])]


theorem partial_checked12 :
    (Poly.add (Poly.add (Poly.mul chunk12 sourceRight) partial13)
      (Poly.scale (K.ofRat (-1)) partial12)).isZero := by decide +kernel

theorem partial_sound12 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 12)
      sourceRight).eval u v t=partial12.eval u v t := by
  change (Poly.mul (chunk12++(sourceLeft.drop 13))
    sourceRight).eval u v t=partial12.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound13 partial_checked12 u v t


noncomputable def chunk8 : Poly := [(⟨0,5,0⟩,[2]),(⟨1,0,0⟩,[1,-5,10,-11,7]),(⟨2,0,0⟩,[0,0,2,-2]),(⟨3,0,0⟩,[-3,8,-9])]

noncomputable def partial8 : Poly := [(⟨0,5,0⟩,[0,-6,30,-42,6,12]),(⟨0,5,1⟩,[2,-10,20,-22,14]),(⟨0,5,2⟩,[0,0,4,-4]),(⟨0,5,3⟩,[-6,16,-18]),(⟨0,5,5⟩,[4]),(⟨0,6,0⟩,[2,-10,20,-22,14]),(⟨0,7,0⟩,[0,0,4,-4]),(⟨0,8,0⟩,[-6,16,-18]),(⟨0,10,0⟩,[4]),(⟨1,0,0⟩,[0,-3,30,-126,291,-405,336,-120,-45,42]),(⟨1,0,1⟩,[1,-10,45,-122,224,-290,261,-154,49]),(⟨1,0,2⟩,[0,0,2,-12,30,-42,36,-14]),(⟨1,0,3⟩,[-3,23,-79,158,-199,155,-63]),(⟨1,0,5⟩,[2,-10,20,-22,14]),(⟨1,1,0⟩,[1,-10,45,-122,224,-290,261,-154,49]),(⟨1,2,0⟩,[0,0,2,-12,30,-42,36,-14]),(⟨1,3,0⟩,[-3,23,-79,158,-199,155,-63]),(⟨1,5,0⟩,[4,-20,40,-44,28]),(⟨2,0,0⟩,[1,-10,45,-128,260,-362,309,-148,37]),(⟨2,0,1⟩,[0,0,2,-12,30,-42,36,-14]),(⟨2,0,2⟩,[0,0,0,0,4,-8,4]),(⟨2,0,3⟩,[0,0,-6,22,-34,18]),(⟨2,0,5⟩,[0,0,4,-4]),(⟨2,1,0⟩,[0,0,2,-12,30,-42,36,-14]),(⟨2,2,0⟩,[0,0,0,0,4,-8,4]),(⟨2,3,0⟩,[0,0,-6,22,-34,18]),(⟨2,5,0⟩,[0,0,8,-8]),(⟨3,0,0⟩,[0,9,-65,186,-252,111,93,-82]),(⟨3,0,1⟩,[-3,23,-79,158,-199,155,-63]),(⟨3,0,2⟩,[0,0,-6,22,-34,18]),(⟨3,0,3⟩,[9,-48,118,-144,81]),(⟨3,0,5⟩,[-6,16,-18]),(⟨3,1,0⟩,[-3,23,-79,158,-199,155,-63]),(⟨3,2,0⟩,[0,0,-6,22,-34,18]),(⟨3,3,0⟩,[9,-48,118,-144,81]),(⟨3,5,0⟩,[-12,32,-36]),(⟨4,0,0⟩,[-6,46,-158,316,-394,302,-122]),(⟨5,0,0⟩,[0,-6,18,2,-62,48]),(⟨5,0,1⟩,[2,-10,20,-22,14]),(⟨5,0,2⟩,[0,0,4,-4]),(⟨5,0,3⟩,[-6,16,-18]),(⟨5,0,5⟩,[4]),(⟨5,1,0⟩,[2,-10,20,-22,14]),(⟨5,2,0⟩,[0,0,4,-4]),(⟨5,3,0⟩,[-6,16,-18]),(⟨5,5,0⟩,[8]),(⟨6,0,0⟩,[13,-68,158,-188,109]),(⟨7,0,0⟩,[0,0,8,-8]),(⟨8,0,0⟩,[-12,32,-36]),(⟨10,0,0⟩,[4])]


theorem partial_checked8 :
    (Poly.add (Poly.add (Poly.mul chunk8 sourceRight) partial12)
      (Poly.scale (K.ofRat (-1)) partial8)).isZero := by decide +kernel

theorem partial_sound8 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 8)
      sourceRight).eval u v t=partial8.eval u v t := by
  change (Poly.mul (chunk8++(sourceLeft.drop 12))
    sourceRight).eval u v t=partial8.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound12 partial_checked8 u v t


noncomputable def chunk4 : Poly := [(⟨0,0,5⟩,[2]),(⟨0,1,0⟩,[1,-5,10,-11,7]),(⟨0,2,0⟩,[0,0,2,-2]),(⟨0,3,0⟩,[-3,8,-9])]

noncomputable def partial4 : Poly := [(⟨0,0,5⟩,[0,-6,30,-42,6,12]),(⟨0,0,6⟩,[2,-10,20,-22,14]),(⟨0,0,7⟩,[0,0,4,-4]),(⟨0,0,8⟩,[-6,16,-18]),(⟨0,0,10⟩,[4]),(⟨0,1,0⟩,[0,-3,30,-126,291,-405,336,-120,-45,42]),(⟨0,1,1⟩,[1,-10,45,-122,224,-290,261,-154,49]),(⟨0,1,2⟩,[0,0,2,-12,30,-42,36,-14]),(⟨0,1,3⟩,[-3,23,-79,158,-199,155,-63]),(⟨0,1,5⟩,[4,-20,40,-44,28]),(⟨0,2,0⟩,[1,-10,45,-128,260,-362,309,-148,37]),(⟨0,2,1⟩,[0,0,2,-12,30,-42,36,-14]),(⟨0,2,2⟩,[0,0,0,0,4,-8,4]),(⟨0,2,3⟩,[0,0,-6,22,-34,18]),(⟨0,2,5⟩,[0,0,8,-8]),(⟨0,3,0⟩,[0,9,-65,186,-252,111,93,-82]),(⟨0,3,1⟩,[-3,23,-79,158,-199,155,-63]),(⟨0,3,2⟩,[0,0,-6,22,-34,18]),(⟨0,3,3⟩,[9,-48,118,-144,81]),(⟨0,3,5⟩,[-12,32,-36]),(⟨0,4,0⟩,[-6,46,-158,316,-394,302,-122]),(⟨0,5,0⟩,[0,-6,18,2,-62,48]),(⟨0,5,1⟩,[2,-10,20,-22,14]),(⟨0,5,2⟩,[0,0,4,-4]),(⟨0,5,3⟩,[-6,16,-18]),(⟨0,5,5⟩,[8]),(⟨0,6,0⟩,[13,-68,158,-188,109]),(⟨0,7,0⟩,[0,0,8,-8]),(⟨0,8,0⟩,[-12,32,-36]),(⟨0,10,0⟩,[4]),(⟨1,0,0⟩,[0,-3,30,-126,291,-405,336,-120,-45,42]),(⟨1,0,1⟩,[1,-10,45,-122,224,-290,261,-154,49]),(⟨1,0,2⟩,[0,0,2,-12,30,-42,36,-14]),(⟨1,0,3⟩,[-3,23,-79,158,-199,155,-63]),(⟨1,0,5⟩,[4,-20,40,-44,28]),(⟨1,1,0⟩,[2,-20,90,-244,448,-580,522,-308,98]),(⟨1,2,0⟩,[0,0,4,-24,60,-84,72,-28]),(⟨1,3,0⟩,[-6,46,-158,316,-398,310,-126]),(⟨1,5,0⟩,[4,-20,40,-44,28]),(⟨2,0,0⟩,[1,-10,45,-128,260,-362,309,-148,37]),(⟨2,0,1⟩,[0,0,2,-12,30,-42,36,-14]),(⟨2,0,2⟩,[0,0,0,0,4,-8,4]),(⟨2,0,3⟩,[0,0,-6,22,-34,18]),(⟨2,0,5⟩,[0,0,8,-8]),(⟨2,1,0⟩,[0,0,4,-24,60,-84,72,-28]),(⟨2,2,0⟩,[0,0,0,0,8,-16,8]),(⟨2,3,0⟩,[0,0,-12,44,-68,36]),(⟨2,5,0⟩,[0,0,8,-8]),(⟨3,0,0⟩,[0,9,-65,186,-252,111,93,-82]),(⟨3,0,1⟩,[-3,23,-79,158,-199,155,-63]),(⟨3,0,2⟩,[0,0,-6,22,-34,18]),(⟨3,0,3⟩,[9,-48,118,-144,81]),(⟨3,0,5⟩,[-12,32,-36]),(⟨3,1,0⟩,[-6,46,-158,316,-398,310,-126]),(⟨3,2,0⟩,[0,0,-12,44,-68,36]),(⟨3,3,0⟩,[18,-96,236,-288,162]),(⟨3,5,0⟩,[-12,32,-36]),(⟨4,0,0⟩,[-6,46,-158,316,-394,302,-122]),(⟨5,0,0⟩,[0,-6,18,2,-62,48]),(⟨5,0,1⟩,[2,-10,20,-22,14]),(⟨5,0,2⟩,[0,0,4,-4]),(⟨5,0,3⟩,[-6,16,-18]),(⟨5,0,5⟩,[8]),(⟨5,1,0⟩,[4,-20,40,-44,28]),(⟨5,2,0⟩,[0,0,8,-8]),(⟨5,3,0⟩,[-12,32,-36]),(⟨5,5,0⟩,[8]),(⟨6,0,0⟩,[13,-68,158,-188,109]),(⟨7,0,0⟩,[0,0,8,-8]),(⟨8,0,0⟩,[-12,32,-36]),(⟨10,0,0⟩,[4])]


theorem partial_checked4 :
    (Poly.add (Poly.add (Poly.mul chunk4 sourceRight) partial8)
      (Poly.scale (K.ofRat (-1)) partial4)).isZero := by decide +kernel

theorem partial_sound4 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 4)
      sourceRight).eval u v t=partial4.eval u v t := by
  change (Poly.mul (chunk4++(sourceLeft.drop 8))
    sourceRight).eval u v t=partial4.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound8 partial_checked4 u v t


noncomputable def chunk0 : Poly := [(⟨0,0,0⟩,[0,-3,15,-21,3,6]),(⟨0,0,1⟩,[1,-5,10,-11,7]),(⟨0,0,2⟩,[0,0,2,-2]),(⟨0,0,3⟩,[-3,8,-9])]

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,0,9,-90,351,-648,495,54,-243,36,36]),(⟨0,0,1⟩,[0,-6,60,-252,582,-810,672,-240,-90,84]),(⟨0,0,2⟩,[1,-10,45,-134,296,-434,357,-142,25]),(⟨0,0,3⟩,[0,18,-134,396,-564,306,114,-136]),(⟨0,0,4⟩,[-6,46,-158,316,-394,302,-122]),(⟨0,0,5⟩,[0,-12,48,-40,-56,60]),(⟨0,0,6⟩,[13,-68,158,-188,109]),(⟨0,0,7⟩,[0,0,8,-8]),(⟨0,0,8⟩,[-12,32,-36]),(⟨0,0,10⟩,[4]),(⟨0,1,0⟩,[0,-6,60,-252,582,-810,672,-240,-90,84]),(⟨0,1,1⟩,[2,-20,90,-244,448,-580,522,-308,98]),(⟨0,1,2⟩,[0,0,4,-24,60,-84,72,-28]),(⟨0,1,3⟩,[-6,46,-158,316,-398,310,-126]),(⟨0,1,5⟩,[4,-20,40,-44,28]),(⟨0,2,0⟩,[1,-10,45,-134,296,-434,357,-142,25]),(⟨0,2,1⟩,[0,0,4,-24,60,-84,72,-28]),(⟨0,2,2⟩,[0,0,0,0,8,-16,8]),(⟨0,2,3⟩,[0,0,-12,44,-68,36]),(⟨0,2,5⟩,[0,0,8,-8]),(⟨0,3,0⟩,[0,18,-134,396,-564,306,114,-136]),(⟨0,3,1⟩,[-6,46,-158,316,-398,310,-126]),(⟨0,3,2⟩,[0,0,-12,44,-68,36]),(⟨0,3,3⟩,[18,-96,236,-288,162]),(⟨0,3,5⟩,[-12,32,-36]),(⟨0,4,0⟩,[-6,46,-158,316,-394,302,-122]),(⟨0,5,0⟩,[0,-12,48,-40,-56,60]),(⟨0,5,1⟩,[4,-20,40,-44,28]),(⟨0,5,2⟩,[0,0,8,-8]),(⟨0,5,3⟩,[-12,32,-36]),(⟨0,5,5⟩,[8]),(⟨0,6,0⟩,[13,-68,158,-188,109]),(⟨0,7,0⟩,[0,0,8,-8]),(⟨0,8,0⟩,[-12,32,-36]),(⟨0,10,0⟩,[4]),(⟨1,0,0⟩,[0,-6,60,-252,582,-810,672,-240,-90,84]),(⟨1,0,1⟩,[2,-20,90,-244,448,-580,522,-308,98]),(⟨1,0,2⟩,[0,0,4,-24,60,-84,72,-28]),(⟨1,0,3⟩,[-6,46,-158,316,-398,310,-126]),(⟨1,0,5⟩,[4,-20,40,-44,28]),(⟨1,1,0⟩,[2,-20,90,-244,448,-580,522,-308,98]),(⟨1,2,0⟩,[0,0,4,-24,60,-84,72,-28]),(⟨1,3,0⟩,[-6,46,-158,316,-398,310,-126]),(⟨1,5,0⟩,[4,-20,40,-44,28]),(⟨2,0,0⟩,[1,-10,45,-134,296,-434,357,-142,25]),(⟨2,0,1⟩,[0,0,4,-24,60,-84,72,-28]),(⟨2,0,2⟩,[0,0,0,0,8,-16,8]),(⟨2,0,3⟩,[0,0,-12,44,-68,36]),(⟨2,0,5⟩,[0,0,8,-8]),(⟨2,1,0⟩,[0,0,4,-24,60,-84,72,-28]),(⟨2,2,0⟩,[0,0,0,0,8,-16,8]),(⟨2,3,0⟩,[0,0,-12,44,-68,36]),(⟨2,5,0⟩,[0,0,8,-8]),(⟨3,0,0⟩,[0,18,-134,396,-564,306,114,-136]),(⟨3,0,1⟩,[-6,46,-158,316,-398,310,-126]),(⟨3,0,2⟩,[0,0,-12,44,-68,36]),(⟨3,0,3⟩,[18,-96,236,-288,162]),(⟨3,0,5⟩,[-12,32,-36]),(⟨3,1,0⟩,[-6,46,-158,316,-398,310,-126]),(⟨3,2,0⟩,[0,0,-12,44,-68,36]),(⟨3,3,0⟩,[18,-96,236,-288,162]),(⟨3,5,0⟩,[-12,32,-36]),(⟨4,0,0⟩,[-6,46,-158,316,-394,302,-122]),(⟨5,0,0⟩,[0,-12,48,-40,-56,60]),(⟨5,0,1⟩,[4,-20,40,-44,28]),(⟨5,0,2⟩,[0,0,8,-8]),(⟨5,0,3⟩,[-12,32,-36]),(⟨5,0,5⟩,[8]),(⟨5,1,0⟩,[4,-20,40,-44,28]),(⟨5,2,0⟩,[0,0,8,-8]),(⟨5,3,0⟩,[-12,32,-36]),(⟨5,5,0⟩,[8]),(⟨6,0,0⟩,[13,-68,158,-188,109]),(⟨7,0,0⟩,[0,0,8,-8]),(⟨8,0,0⟩,[-12,32,-36]),(⟨10,0,0⟩,[4])]


theorem partial_checked0 :
    (Poly.add (Poly.add (Poly.mul chunk0 sourceRight) partial4)
      (Poly.scale (K.ofRat (-1)) partial0)).isZero := by decide +kernel

theorem partial_sound0 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 0)
      sourceRight).eval u v t=partial0.eval u v t := by
  change (Poly.mul (chunk0++(sourceLeft.drop 4))
    sourceRight).eval u v t=partial0.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound4 partial_checked0 u v t


theorem weighted_checked :
    (Poly.add (Poly.scale (K.ofRat r14) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 1 1).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r46*r46 : ℚ)=r14 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 1 1 r46 r46 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 1=1 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 1 1).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C059

#print axioms Coulomb8.Columns.C059.sound
