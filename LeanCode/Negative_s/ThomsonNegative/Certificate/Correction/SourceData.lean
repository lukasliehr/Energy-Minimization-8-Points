import ThomsonNegative.Certificate.Correction.SourceData00
import ThomsonNegative.Certificate.Correction.SourceData01
import ThomsonNegative.Certificate.Correction.SourceData02
import ThomsonNegative.Certificate.Correction.SourceData03
import ThomsonNegative.Certificate.Correction.SourceData04
import ThomsonNegative.Certificate.Correction.SourceData05
import ThomsonNegative.Certificate.Correction.SourceData06
import ThomsonNegative.Certificate.Correction.SourceData07
import ThomsonNegative.Certificate.Correction.SourceData08
import ThomsonNegative.Certificate.Correction.SourceData09
import ThomsonNegative.Certificate.Correction.SourceData10
import ThomsonNegative.Certificate.Correction.SourceData11
import ThomsonNegative.Certificate.Correction.SourceData12
import ThomsonNegative.Certificate.Correction.SourceData13
import ThomsonNegative.Certificate.Correction.SourceData14
import ThomsonNegative.Certificate.Correction.SourceData15
import ThomsonNegative.Certificate.Correction.SourceData16

namespace ThomsonNegative.Certificate.Correction.Source
open ThomsonNegative.Structure.Exact

noncomputable def rowNumerator : Nat → Nat → Nat
  | 0 => r0n
  | 1 => r1n
  | 2 => r2n
  | 3 => r3n
  | 4 => r4n
  | 5 => r5n
  | 6 => r6n
  | 7 => r7n
  | 8 => r8n
  | 9 => r9n
  | 10 => r10n
  | 11 => r11n
  | 12 => r12n
  | 13 => r13n
  | 14 => r14n
  | 15 => r15n
  | 16 => r16n
  | 17 => r17n
  | 18 => r18n
  | 19 => r19n
  | 20 => r20n
  | 21 => r21n
  | 22 => r22n
  | 23 => r23n
  | 24 => r24n
  | 25 => r25n
  | 26 => r26n
  | 27 => r27n
  | 28 => r28n
  | 29 => r29n
  | 30 => r30n
  | 31 => r31n
  | 32 => r32n
  | 33 => r33n
  | 34 => r34n
  | 35 => r35n
  | 36 => r36n
  | 37 => r37n
  | 38 => r38n
  | 39 => r39n
  | 40 => r40n
  | 41 => r41n
  | 42 => r42n
  | 43 => r43n
  | 44 => r44n
  | 45 => r45n
  | 46 => r46n
  | 47 => r47n
  | 48 => r48n
  | 49 => r49n
  | 50 => r50n
  | 51 => r51n
  | 52 => r52n
  | 53 => r53n
  | 54 => r54n
  | 55 => r55n
  | 56 => r56n
  | 57 => r57n
  | 58 => r58n
  | 59 => r59n
  | 60 => r60n
  | 61 => r61n
  | 62 => r62n
  | 63 => r63n
  | 64 => r64n
  | 65 => r65n
  | 66 => r66n
  | 67 => r67n
  | _ => fun _ => 0x100000

noncomputable def rowDenominator : Nat → Nat
  | 0 => r0d
  | 1 => r1d
  | 2 => r2d
  | 3 => r3d
  | 4 => r4d
  | 5 => r5d
  | 6 => r6d
  | 7 => r7d
  | 8 => r8d
  | 9 => r9d
  | 10 => r10d
  | 11 => r11d
  | 12 => r12d
  | 13 => r13d
  | 14 => r14d
  | 15 => r15d
  | 16 => r16d
  | 17 => r17d
  | 18 => r18d
  | 19 => r19d
  | 20 => r20d
  | 21 => r21d
  | 22 => r22d
  | 23 => r23d
  | 24 => r24d
  | 25 => r25d
  | 26 => r26d
  | 27 => r27d
  | 28 => r28d
  | 29 => r29d
  | 30 => r30d
  | 31 => r31d
  | 32 => r32d
  | 33 => r33d
  | 34 => r34d
  | 35 => r35d
  | 36 => r36d
  | 37 => r37d
  | 38 => r38d
  | 39 => r39d
  | 40 => r40d
  | 41 => r41d
  | 42 => r42d
  | 43 => r43d
  | 44 => r44d
  | 45 => r45d
  | 46 => r46d
  | 47 => r47d
  | 48 => r48d
  | 49 => r49d
  | 50 => r50d
  | 51 => r51d
  | 52 => r52d
  | 53 => r53d
  | 54 => r54d
  | 55 => r55d
  | 56 => r56d
  | 57 => r57d
  | 58 => r58d
  | 59 => r59d
  | 60 => r60d
  | 61 => r61d
  | 62 => r62d
  | 63 => r63d
  | 64 => r64d
  | 65 => r65d
  | 66 => r66d
  | 67 => r67d
  | _ => 0x300201000

def repairCoordinate : Nat → Nat × Nat × Nat
  | 0 => (0, 0, 0)
  | 1 => (0, 0, 1)
  | 2 => (0, 0, 2)
  | 3 => (0, 0, 3)
  | 4 => (0, 0, 4)
  | 5 => (0, 0, 5)
  | 6 => (0, 1, 1)
  | 7 => (0, 1, 2)
  | 8 => (0, 1, 3)
  | 9 => (0, 1, 4)
  | 10 => (0, 1, 5)
  | 11 => (0, 4, 5)
  | 12 => (0, 5, 5)
  | 13 => (1, 0, 0)
  | 14 => (1, 1, 2)
  | 15 => (1, 2, 2)
  | 16 => (1, 2, 3)
  | 17 => (1, 4, 4)
  | 18 => (6, 0, 0)
  | 19 => (6, 0, 1)
  | 20 => (6, 0, 2)
  | 21 => (6, 0, 3)
  | 22 => (6, 0, 4)
  | 23 => (6, 0, 5)
  | 24 => (6, 0, 6)
  | 25 => (6, 0, 7)
  | 26 => (6, 0, 8)
  | 27 => (6, 0, 9)
  | 28 => (6, 0, 10)
  | 29 => (6, 1, 1)
  | 30 => (6, 1, 2)
  | 31 => (6, 1, 3)
  | 32 => (6, 1, 4)
  | 33 => (6, 1, 5)
  | 34 => (6, 1, 6)
  | 35 => (6, 1, 7)
  | 36 => (6, 1, 8)
  | 37 => (6, 1, 9)
  | 38 => (6, 2, 2)
  | 39 => (6, 2, 3)
  | 40 => (6, 2, 5)
  | 41 => (6, 2, 6)
  | 42 => (6, 2, 7)
  | 43 => (6, 3, 3)
  | 44 => (6, 3, 6)
  | 45 => (6, 3, 7)
  | 46 => (6, 3, 8)
  | 47 => (6, 3, 9)
  | 48 => (6, 4, 6)
  | 49 => (6, 4, 8)
  | 50 => (6, 6, 6)
  | 51 => (6, 6, 7)
  | 52 => (6, 6, 8)
  | 53 => (6, 6, 9)
  | 54 => (6, 6, 10)
  | 55 => (6, 7, 7)
  | 56 => (6, 7, 9)
  | 57 => (6, 7, 10)
  | 58 => (6, 8, 8)
  | 59 => (6, 8, 10)
  | 60 => (6, 9, 10)
  | 61 => (6, 10, 10)
  | 62 => (7, 0, 0)
  | 63 => (7, 0, 7)
  | 64 => (7, 0, 8)
  | 65 => (7, 1, 8)
  | 66 => (7, 3, 3)
  | 67 => (7, 4, 8)
  | _ => (8,0,0)

def inputCoordinate : Nat → Nat × Nat × Nat
  | 0 => (1, 0, 0)
  | 1 => (0, 1, 0)
  | 2 => (0, 0, 1)
  | 3 => (1, 1, 0)
  | 4 => (3, 0, 0)
  | 5 => (0, 2, 0)
  | 6 => (1, 0, 1)
  | 7 => (2, 1, 0)
  | 8 => (4, 0, 0)
  | 9 => (0, 1, 1)
  | 10 => (1, 2, 0)
  | 11 => (2, 0, 1)
  | 12 => (3, 1, 0)
  | 13 => (5, 0, 0)
  | 14 => (0, 0, 2)
  | 15 => (0, 3, 0)
  | 16 => (1, 1, 1)
  | 17 => (2, 2, 0)
  | 18 => (3, 0, 1)
  | 19 => (4, 1, 0)
  | 20 => (6, 0, 0)
  | 21 => (0, 2, 1)
  | 22 => (1, 0, 2)
  | 23 => (1, 3, 0)
  | 24 => (2, 1, 1)
  | 25 => (3, 2, 0)
  | 26 => (4, 0, 1)
  | 27 => (5, 1, 0)
  | 28 => (7, 0, 0)
  | 29 => (0, 1, 2)
  | 30 => (0, 4, 0)
  | 31 => (1, 2, 1)
  | 32 => (2, 0, 2)
  | 33 => (2, 3, 0)
  | 34 => (3, 1, 1)
  | 35 => (4, 2, 0)
  | 36 => (5, 0, 1)
  | 37 => (6, 1, 0)
  | 38 => (8, 0, 0)
  | 39 => (0, 0, 3)
  | 40 => (0, 3, 1)
  | 41 => (1, 1, 2)
  | 42 => (1, 4, 0)
  | 43 => (2, 2, 1)
  | 44 => (3, 0, 2)
  | 45 => (3, 3, 0)
  | 46 => (4, 1, 1)
  | 47 => (5, 2, 0)
  | 48 => (6, 0, 1)
  | 49 => (7, 1, 0)
  | 50 => (9, 0, 0)
  | 51 => (0, 2, 2)
  | 52 => (0, 5, 0)
  | 53 => (1, 0, 3)
  | 54 => (1, 3, 1)
  | 55 => (2, 1, 2)
  | 56 => (2, 4, 0)
  | 57 => (3, 2, 1)
  | 58 => (4, 0, 2)
  | 59 => (4, 3, 0)
  | 60 => (5, 1, 1)
  | 61 => (6, 2, 0)
  | 62 => (7, 0, 1)
  | 63 => (8, 1, 0)
  | 64 => (10, 0, 0)
  | 65 => (11, 0, 0)
  | 66 => (12, 0, 0)
  | 67 => (0, 4, 1)
  | _ => (0,0,0)

end ThomsonNegative.Certificate.Correction.Source
