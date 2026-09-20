import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C045

def r0 : ℚ := { num := 9, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -9, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 99, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -45, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -63, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 27, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 9, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -3, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 27, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 81, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -111, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -9, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 15, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := 1, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 91, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := 359, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := -21, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -59, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 1, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 3, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -17, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 77, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -47, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := -3, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := 7, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := -37, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := 53, den := 16, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := -1, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := 5, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 1, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -3, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 1, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -5, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 43, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -25, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 131, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 25, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 9, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := -19, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := 83, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -35, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -1, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 3, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -7, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 7, den := 2, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 5, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -9, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 49, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -11, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := -7, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,0,r0,r1,r2,r3,r4,r5,r6],[0,r7,r8,-12,r9,r10,r11,r12],[r13,-1,r14,-16,r15,r16,r17],[r18,r7,r19,r20,r21,r22],[r23,r24,r25,r6,r26],[r27,r28,-5,3],[0,r29,r30],[r29,r27],[r31],[],[],[],[],[r18,r32,r33,r34,r35,r3,r36],[r18,r11,r37,r38,r39,r40],[r41,r42,r43,r44,r32],[r41,r45,r46,r45],[],[],[],[],[],[],[],[r18,-1,r12,-7,r47],[r41,r45,r48,r24],[r41,1,r49],[],[],[],[],[],[],[r29,-1,r29],[r29,r27],[],[],[],[],[],[r29],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,0,r0,r1,r2,r3,r4,r5,r6]),(⟨0,0,1⟩,[0,r7,r8,-12,r9,r10,r11,r12]),(⟨0,0,2⟩,[r13,-1,r14,-16,r15,r16,r17]),(⟨0,0,3⟩,[r18,r7,r19,r20,r21,r22]),(⟨0,0,4⟩,[r23,r24,r25,r6,r26]),(⟨0,0,5⟩,[r27,r28,-5,3]),(⟨0,0,6⟩,[0,r29,r30]),(⟨0,0,7⟩,[r29,r27]),(⟨0,0,8⟩,[r31]),(⟨0,1,0⟩,[0,r7,r8,-12,r9,r10,r11,r12]),(⟨0,1,1⟩,[r18,r32,r33,r34,r35,r3,r36]),(⟨0,1,2⟩,[r18,r11,r37,r38,r39,r40]),(⟨0,1,3⟩,[r41,r42,r43,r44,r32]),(⟨0,1,4⟩,[r41,r45,r46,r45]),(⟨0,2,0⟩,[r13,-1,r14,-16,r15,r16,r17]),(⟨0,2,1⟩,[r18,r11,r37,r38,r39,r40]),(⟨0,2,2⟩,[r18,-1,r12,-7,r47]),(⟨0,2,3⟩,[r41,r45,r48,r24]),(⟨0,2,4⟩,[r41,1,r49]),(⟨0,3,0⟩,[r18,r7,r19,r20,r21,r22]),(⟨0,3,1⟩,[r41,r42,r43,r44,r32]),(⟨0,3,2⟩,[r41,r45,r48,r24]),(⟨0,3,3⟩,[r29,-1,r29]),(⟨0,3,4⟩,[r29,r27]),(⟨0,4,0⟩,[r23,r24,r25,r6,r26]),(⟨0,4,1⟩,[r41,r45,r46,r45]),(⟨0,4,2⟩,[r41,1,r49]),(⟨0,4,3⟩,[r29,r27]),(⟨0,4,4⟩,[r29]),(⟨0,5,0⟩,[r27,r28,-5,3]),(⟨0,6,0⟩,[0,r29,r30]),(⟨0,7,0⟩,[r29,r27]),(⟨0,8,0⟩,[r31]),(⟨1,0,0⟩,[0,r7,r8,-12,r9,r10,r11,r12]),(⟨1,0,1⟩,[r18,r32,r33,r34,r35,r3,r36]),(⟨1,0,2⟩,[r18,r11,r37,r38,r39,r40]),(⟨1,0,3⟩,[r41,r42,r43,r44,r32]),(⟨1,0,4⟩,[r41,r45,r46,r45]),(⟨1,1,0⟩,[r18,r32,r33,r34,r35,r3,r36]),(⟨1,2,0⟩,[r18,r11,r37,r38,r39,r40]),(⟨1,3,0⟩,[r41,r42,r43,r44,r32]),(⟨1,4,0⟩,[r41,r45,r46,r45]),(⟨2,0,0⟩,[r13,-1,r14,-16,r15,r16,r17]),(⟨2,0,1⟩,[r18,r11,r37,r38,r39,r40]),(⟨2,0,2⟩,[r18,-1,r12,-7,r47]),(⟨2,0,3⟩,[r41,r45,r48,r24]),(⟨2,0,4⟩,[r41,1,r49]),(⟨2,1,0⟩,[r18,r11,r37,r38,r39,r40]),(⟨2,2,0⟩,[r18,-1,r12,-7,r47]),(⟨2,3,0⟩,[r41,r45,r48,r24]),(⟨2,4,0⟩,[r41,1,r49]),(⟨3,0,0⟩,[r18,r7,r19,r20,r21,r22]),(⟨3,0,1⟩,[r41,r42,r43,r44,r32]),(⟨3,0,2⟩,[r41,r45,r48,r24]),(⟨3,0,3⟩,[r29,-1,r29]),(⟨3,0,4⟩,[r29,r27]),(⟨3,1,0⟩,[r41,r42,r43,r44,r32]),(⟨3,2,0⟩,[r41,r45,r48,r24]),(⟨3,3,0⟩,[r29,-1,r29]),(⟨3,4,0⟩,[r29,r27]),(⟨4,0,0⟩,[r23,r24,r25,r6,r26]),(⟨4,0,1⟩,[r41,r45,r46,r45]),(⟨4,0,2⟩,[r41,1,r49]),(⟨4,0,3⟩,[r29,r27]),(⟨4,0,4⟩,[r29]),(⟨4,1,0⟩,[r41,r45,r46,r45]),(⟨4,2,0⟩,[r41,1,r49]),(⟨4,3,0⟩,[r29,r27]),(⟨4,4,0⟩,[r29]),(⟨5,0,0⟩,[r27,r28,-5,3]),(⟨6,0,0⟩,[0,r29,r30]),(⟨7,0,0⟩,[r29,r27]),(⟨8,0,0⟩,[r31])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,3,-12,9,6]),(⟨0,0,1⟩,[-1,5,-9,5]),(⟨0,0,2⟩,[-1,4,-7]),(⟨0,0,3⟩,[2,-2]),(⟨0,0,4⟩,[2]),(⟨0,1,0⟩,[-1,5,-9,5]),(⟨0,2,0⟩,[-1,4,-7]),(⟨0,3,0⟩,[2,-2]),(⟨0,4,0⟩,[2]),(⟨1,0,0⟩,[-1,5,-9,5]),(⟨2,0,0⟩,[-1,4,-7]),(⟨3,0,0⟩,[2,-2]),(⟨4,0,0⟩,[2])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[0,3,-12,9,6]),(⟨0,0,1⟩,[-1,5,-9,5]),(⟨0,0,2⟩,[-1,4,-7]),(⟨0,0,3⟩,[2,-2]),(⟨0,0,4⟩,[2]),(⟨0,1,0⟩,[-1,5,-9,5]),(⟨0,2,0⟩,[-1,4,-7]),(⟨0,3,0⟩,[2,-2]),(⟨0,4,0⟩,[2]),(⟨1,0,0⟩,[-1,5,-9,5]),(⟨2,0,0⟩,[-1,4,-7]),(⟨3,0,0⟩,[2,-2]),(⟨4,0,0⟩,[2])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 0 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r31) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 0 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r31) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨4,0,0⟩,[2])]

noncomputable def partial12 : Poly := [(⟨4,0,0⟩,[0,6,-24,18,12]),(⟨4,0,1⟩,[-2,10,-18,10]),(⟨4,0,2⟩,[-2,8,-14]),(⟨4,0,3⟩,[4,-4]),(⟨4,0,4⟩,[4]),(⟨4,1,0⟩,[-2,10,-18,10]),(⟨4,2,0⟩,[-2,8,-14]),(⟨4,3,0⟩,[4,-4]),(⟨4,4,0⟩,[4]),(⟨5,0,0⟩,[-2,10,-18,10]),(⟨6,0,0⟩,[-2,8,-14]),(⟨7,0,0⟩,[4,-4]),(⟨8,0,0⟩,[4])]


theorem partial_checked12 :
    (Poly.add (Poly.add (Poly.mul chunk12 sourceRight) partial13)
      (Poly.scale (K.ofRat (-1)) partial12)).isZero := by decide +kernel

theorem partial_sound12 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 12)
      sourceRight).eval u v t=partial12.eval u v t := by
  change (Poly.mul (chunk12++(sourceLeft.drop 13))
    sourceRight).eval u v t=partial12.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound13 partial_checked12 u v t


noncomputable def chunk8 : Poly := [(⟨0,4,0⟩,[2]),(⟨1,0,0⟩,[-1,5,-9,5]),(⟨2,0,0⟩,[-1,4,-7]),(⟨3,0,0⟩,[2,-2])]

noncomputable def partial8 : Poly := [(⟨0,4,0⟩,[0,6,-24,18,12]),(⟨0,4,1⟩,[-2,10,-18,10]),(⟨0,4,2⟩,[-2,8,-14]),(⟨0,4,3⟩,[4,-4]),(⟨0,4,4⟩,[4]),(⟨0,5,0⟩,[-2,10,-18,10]),(⟨0,6,0⟩,[-2,8,-14]),(⟨0,7,0⟩,[4,-4]),(⟨0,8,0⟩,[4]),(⟨1,0,0⟩,[0,-3,27,-96,162,-111,-9,30]),(⟨1,0,1⟩,[1,-10,43,-100,131,-90,25]),(⟨1,0,2⟩,[1,-9,36,-76,83,-35]),(⟨1,0,3⟩,[-2,12,-28,28,-10]),(⟨1,0,4⟩,[-2,10,-18,10]),(⟨1,1,0⟩,[1,-10,43,-100,131,-90,25]),(⟨1,2,0⟩,[1,-9,36,-76,83,-35]),(⟨1,3,0⟩,[-2,12,-28,28,-10]),(⟨1,4,0⟩,[-4,20,-36,20]),(⟨2,0,0⟩,[1,-13,67,-178,245,-129,-17]),(⟨2,0,1⟩,[1,-9,36,-76,83,-35]),(⟨2,0,2⟩,[1,-8,30,-56,49]),(⟨2,0,3⟩,[-2,10,-22,14]),(⟨2,0,4⟩,[-2,8,-14]),(⟨2,1,0⟩,[1,-9,36,-76,83,-35]),(⟨2,2,0⟩,[1,-8,30,-56,49]),(⟨2,3,0⟩,[-2,10,-22,14]),(⟨2,4,0⟩,[-4,16,-28]),(⟨3,0,0⟩,[2,-12,42,-110,160,-82]),(⟨3,0,1⟩,[-2,12,-28,28,-10]),(⟨3,0,2⟩,[-2,10,-22,14]),(⟨3,0,3⟩,[4,-8,4]),(⟨3,0,4⟩,[4,-4]),(⟨3,1,0⟩,[-2,12,-28,28,-10]),(⟨3,2,0⟩,[-2,10,-22,14]),(⟨3,3,0⟩,[4,-8,4]),(⟨3,4,0⟩,[8,-8]),(⟨4,0,0⟩,[-3,22,-50,18,41]),(⟨4,0,1⟩,[-2,10,-18,10]),(⟨4,0,2⟩,[-2,8,-14]),(⟨4,0,3⟩,[4,-4]),(⟨4,0,4⟩,[4]),(⟨4,1,0⟩,[-2,10,-18,10]),(⟨4,2,0⟩,[-2,8,-14]),(⟨4,3,0⟩,[4,-4]),(⟨4,4,0⟩,[8]),(⟨5,0,0⟩,[-8,40,-80,48]),(⟨6,0,0⟩,[0,8,-24]),(⟨7,0,0⟩,[8,-8]),(⟨8,0,0⟩,[4])]


theorem partial_checked8 :
    (Poly.add (Poly.add (Poly.mul chunk8 sourceRight) partial12)
      (Poly.scale (K.ofRat (-1)) partial8)).isZero := by decide +kernel

theorem partial_sound8 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 8)
      sourceRight).eval u v t=partial8.eval u v t := by
  change (Poly.mul (chunk8++(sourceLeft.drop 12))
    sourceRight).eval u v t=partial8.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound12 partial_checked8 u v t


noncomputable def chunk4 : Poly := [(⟨0,0,4⟩,[2]),(⟨0,1,0⟩,[-1,5,-9,5]),(⟨0,2,0⟩,[-1,4,-7]),(⟨0,3,0⟩,[2,-2])]

noncomputable def partial4 : Poly := [(⟨0,0,4⟩,[0,6,-24,18,12]),(⟨0,0,5⟩,[-2,10,-18,10]),(⟨0,0,6⟩,[-2,8,-14]),(⟨0,0,7⟩,[4,-4]),(⟨0,0,8⟩,[4]),(⟨0,1,0⟩,[0,-3,27,-96,162,-111,-9,30]),(⟨0,1,1⟩,[1,-10,43,-100,131,-90,25]),(⟨0,1,2⟩,[1,-9,36,-76,83,-35]),(⟨0,1,3⟩,[-2,12,-28,28,-10]),(⟨0,1,4⟩,[-4,20,-36,20]),(⟨0,2,0⟩,[1,-13,67,-178,245,-129,-17]),(⟨0,2,1⟩,[1,-9,36,-76,83,-35]),(⟨0,2,2⟩,[1,-8,30,-56,49]),(⟨0,2,3⟩,[-2,10,-22,14]),(⟨0,2,4⟩,[-4,16,-28]),(⟨0,3,0⟩,[2,-12,42,-110,160,-82]),(⟨0,3,1⟩,[-2,12,-28,28,-10]),(⟨0,3,2⟩,[-2,10,-22,14]),(⟨0,3,3⟩,[4,-8,4]),(⟨0,3,4⟩,[8,-8]),(⟨0,4,0⟩,[-3,22,-50,18,41]),(⟨0,4,1⟩,[-2,10,-18,10]),(⟨0,4,2⟩,[-2,8,-14]),(⟨0,4,3⟩,[4,-4]),(⟨0,4,4⟩,[8]),(⟨0,5,0⟩,[-8,40,-80,48]),(⟨0,6,0⟩,[0,8,-24]),(⟨0,7,0⟩,[8,-8]),(⟨0,8,0⟩,[4]),(⟨1,0,0⟩,[0,-3,27,-96,162,-111,-9,30]),(⟨1,0,1⟩,[1,-10,43,-100,131,-90,25]),(⟨1,0,2⟩,[1,-9,36,-76,83,-35]),(⟨1,0,3⟩,[-2,12,-28,28,-10]),(⟨1,0,4⟩,[-4,20,-36,20]),(⟨1,1,0⟩,[2,-20,86,-200,262,-180,50]),(⟨1,2,0⟩,[2,-18,72,-152,166,-70]),(⟨1,3,0⟩,[-4,24,-56,56,-20]),(⟨1,4,0⟩,[-4,20,-36,20]),(⟨2,0,0⟩,[1,-13,67,-178,245,-129,-17]),(⟨2,0,1⟩,[1,-9,36,-76,83,-35]),(⟨2,0,2⟩,[1,-8,30,-56,49]),(⟨2,0,3⟩,[-2,10,-22,14]),(⟨2,0,4⟩,[-4,16,-28]),(⟨2,1,0⟩,[2,-18,72,-152,166,-70]),(⟨2,2,0⟩,[2,-16,60,-112,98]),(⟨2,3,0⟩,[-4,20,-44,28]),(⟨2,4,0⟩,[-4,16,-28]),(⟨3,0,0⟩,[2,-12,42,-110,160,-82]),(⟨3,0,1⟩,[-2,12,-28,28,-10]),(⟨3,0,2⟩,[-2,10,-22,14]),(⟨3,0,3⟩,[4,-8,4]),(⟨3,0,4⟩,[8,-8]),(⟨3,1,0⟩,[-4,24,-56,56,-20]),(⟨3,2,0⟩,[-4,20,-44,28]),(⟨3,3,0⟩,[8,-16,8]),(⟨3,4,0⟩,[8,-8]),(⟨4,0,0⟩,[-3,22,-50,18,41]),(⟨4,0,1⟩,[-2,10,-18,10]),(⟨4,0,2⟩,[-2,8,-14]),(⟨4,0,3⟩,[4,-4]),(⟨4,0,4⟩,[8]),(⟨4,1,0⟩,[-4,20,-36,20]),(⟨4,2,0⟩,[-4,16,-28]),(⟨4,3,0⟩,[8,-8]),(⟨4,4,0⟩,[8]),(⟨5,0,0⟩,[-8,40,-80,48]),(⟨6,0,0⟩,[0,8,-24]),(⟨7,0,0⟩,[8,-8]),(⟨8,0,0⟩,[4])]


theorem partial_checked4 :
    (Poly.add (Poly.add (Poly.mul chunk4 sourceRight) partial8)
      (Poly.scale (K.ofRat (-1)) partial4)).isZero := by decide +kernel

theorem partial_sound4 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 4)
      sourceRight).eval u v t=partial4.eval u v t := by
  change (Poly.mul (chunk4++(sourceLeft.drop 8))
    sourceRight).eval u v t=partial4.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound8 partial_checked4 u v t


noncomputable def chunk0 : Poly := [(⟨0,0,0⟩,[0,3,-12,9,6]),(⟨0,0,1⟩,[-1,5,-9,5]),(⟨0,0,2⟩,[-1,4,-7]),(⟨0,0,3⟩,[2,-2])]

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,0,9,-72,198,-180,-63,108,36]),(⟨0,0,1⟩,[0,-6,54,-192,324,-222,-18,60]),(⟨0,0,2⟩,[1,-16,91,-256,359,-168,-59]),(⟨0,0,3⟩,[2,-6,12,-68,154,-94]),(⟨0,0,4⟩,[-3,28,-74,36,53]),(⟨0,0,5⟩,[-8,40,-80,48]),(⟨0,0,6⟩,[0,8,-24]),(⟨0,0,7⟩,[8,-8]),(⟨0,0,8⟩,[4]),(⟨0,1,0⟩,[0,-6,54,-192,324,-222,-18,60]),(⟨0,1,1⟩,[2,-20,86,-200,262,-180,50]),(⟨0,1,2⟩,[2,-18,72,-152,166,-70]),(⟨0,1,3⟩,[-4,24,-56,56,-20]),(⟨0,1,4⟩,[-4,20,-36,20]),(⟨0,2,0⟩,[1,-16,91,-256,359,-168,-59]),(⟨0,2,1⟩,[2,-18,72,-152,166,-70]),(⟨0,2,2⟩,[2,-16,60,-112,98]),(⟨0,2,3⟩,[-4,20,-44,28]),(⟨0,2,4⟩,[-4,16,-28]),(⟨0,3,0⟩,[2,-6,12,-68,154,-94]),(⟨0,3,1⟩,[-4,24,-56,56,-20]),(⟨0,3,2⟩,[-4,20,-44,28]),(⟨0,3,3⟩,[8,-16,8]),(⟨0,3,4⟩,[8,-8]),(⟨0,4,0⟩,[-3,28,-74,36,53]),(⟨0,4,1⟩,[-4,20,-36,20]),(⟨0,4,2⟩,[-4,16,-28]),(⟨0,4,3⟩,[8,-8]),(⟨0,4,4⟩,[8]),(⟨0,5,0⟩,[-8,40,-80,48]),(⟨0,6,0⟩,[0,8,-24]),(⟨0,7,0⟩,[8,-8]),(⟨0,8,0⟩,[4]),(⟨1,0,0⟩,[0,-6,54,-192,324,-222,-18,60]),(⟨1,0,1⟩,[2,-20,86,-200,262,-180,50]),(⟨1,0,2⟩,[2,-18,72,-152,166,-70]),(⟨1,0,3⟩,[-4,24,-56,56,-20]),(⟨1,0,4⟩,[-4,20,-36,20]),(⟨1,1,0⟩,[2,-20,86,-200,262,-180,50]),(⟨1,2,0⟩,[2,-18,72,-152,166,-70]),(⟨1,3,0⟩,[-4,24,-56,56,-20]),(⟨1,4,0⟩,[-4,20,-36,20]),(⟨2,0,0⟩,[1,-16,91,-256,359,-168,-59]),(⟨2,0,1⟩,[2,-18,72,-152,166,-70]),(⟨2,0,2⟩,[2,-16,60,-112,98]),(⟨2,0,3⟩,[-4,20,-44,28]),(⟨2,0,4⟩,[-4,16,-28]),(⟨2,1,0⟩,[2,-18,72,-152,166,-70]),(⟨2,2,0⟩,[2,-16,60,-112,98]),(⟨2,3,0⟩,[-4,20,-44,28]),(⟨2,4,0⟩,[-4,16,-28]),(⟨3,0,0⟩,[2,-6,12,-68,154,-94]),(⟨3,0,1⟩,[-4,24,-56,56,-20]),(⟨3,0,2⟩,[-4,20,-44,28]),(⟨3,0,3⟩,[8,-16,8]),(⟨3,0,4⟩,[8,-8]),(⟨3,1,0⟩,[-4,24,-56,56,-20]),(⟨3,2,0⟩,[-4,20,-44,28]),(⟨3,3,0⟩,[8,-16,8]),(⟨3,4,0⟩,[8,-8]),(⟨4,0,0⟩,[-3,28,-74,36,53]),(⟨4,0,1⟩,[-4,20,-36,20]),(⟨4,0,2⟩,[-4,16,-28]),(⟨4,0,3⟩,[8,-8]),(⟨4,0,4⟩,[8]),(⟨4,1,0⟩,[-4,20,-36,20]),(⟨4,2,0⟩,[-4,16,-28]),(⟨4,3,0⟩,[8,-8]),(⟨4,4,0⟩,[8]),(⟨5,0,0⟩,[-8,40,-80,48]),(⟨6,0,0⟩,[0,8,-24]),(⟨7,0,0⟩,[8,-8]),(⟨8,0,0⟩,[4])]


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
    (Poly.add (Poly.scale (K.ofRat r13) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 0 0).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r31*r31 : ℚ)=r13 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 0 0 r31 r31 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 0=0 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 0 0).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C045

#print axioms Coulomb8.Columns.C045.sound
