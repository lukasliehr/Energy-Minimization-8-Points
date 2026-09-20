import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C064

def r0 : ℚ := { num := 384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -9120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 92256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -537408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 2057280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -799488, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 1617792, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -998208, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 2442048, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -8559456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -902880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 134784, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -285312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 448, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -34400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 227840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -1028096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 3369792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := -8363328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := 15996352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := -23044352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := 23062400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := -13326688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := 2156864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 161152, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -4064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 20768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -133568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 689728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -334912, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 5517376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -9197856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 10021472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -6094688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 1655712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 32, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -1664, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 104416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -536448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 1820928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -4436352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 8093824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -10644096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 8618976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -2774784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -595808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -672, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 6976, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -38720, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 974464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -2520064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 4844096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -951744, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 833824, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -367712, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 13376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := -91904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := 47808, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := -786368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := 185152, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := -1410560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := 680384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 243616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 6400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -51840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 212096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -573952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 1147392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -1518208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 1040512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := 320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := -4864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := 23616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := -7168, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := 73152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := -59648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -6848, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 15616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -40192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 84608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -123008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 128, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -27008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := 180416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := -109696, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := 2348032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -5687040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 11188096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -16572480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 2357376, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := -9947008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := 434752, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -3232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 26016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -116992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 340224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -641600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 627968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 180224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -1449120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 1986528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := -154464, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 48512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -265856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 947008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -2459584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 4763776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -6523264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 5666336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -357152, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := -1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := 22528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := -99840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := 122880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := 192000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -653312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 1856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -17088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 4544, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := -216000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := 443584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -645440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 69568, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := 1024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := -12288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := 30720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 36864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -5888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 3840, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := -19456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -177920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 569600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -36608, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := 41472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := 26752, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := -608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := 1536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := -9856, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 220160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -416320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 482816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -194944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := -19456, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := 445344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 3328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := -1536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 39680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := 704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -10496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 48576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -80896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 25152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 103680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -26432, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 3072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -7680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := -9216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := 9088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := -69504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := 38528, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 201088, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -1745536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := 1107072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -1536, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := 153600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := -53760, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 30720, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := 830976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := -2113536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := 342528, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -13312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 6144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := 6144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := -158720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := -12800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := 4480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -2560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := -69248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := 176128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := -28544, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 9984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := -4608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -4608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 119040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -5632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 24960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -30720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := -48000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := 163328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := 192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := -4560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := 46128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := -268704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := 1028640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -399744, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := 808896, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := -499104, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := 1221024, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := -4279728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := -451440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := 67392, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := -142656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := 224, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -17200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 113920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := -514048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 1684896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -4181664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := 7998176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := -11522176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := 11531200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -6663344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 1078432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := 80576, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := -16, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := 304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := -2032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := 10384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := -66784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := 344864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := -167456, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := 2758688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := -4598928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := 5010736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := -3047344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := 827856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := 16, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := -832, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := 52208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -268224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := 910464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -2218176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := 4046912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := -5322048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := 4309488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := -1387392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := -297904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := 80, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := -336, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := 3488, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := -19360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := 487232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := -1260032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := 2422048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := -475872, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := 416912, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := -183856, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 6688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -45952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := 23904, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := -393184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := 92576, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -705280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := 340192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := 121808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := 3200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := -25920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := 106048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := -286976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := 573696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := -759104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := 520256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := -2432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := 11808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := -3584, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := 36576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := -29824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := -3424, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := 64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := -192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := 7808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := -20096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := 42304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := -61504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := 64, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -13504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := 90208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -54848, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 1174016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -2843520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 5594048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -8286240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := 1178688, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := -4973504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := 217376, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := -1616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := 13008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := -58496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := 170112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -320800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := 313984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := 90112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -724560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 993264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -77232, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 24256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -132928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 473504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -1229792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 2381888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := -3261632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 2833168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -178576, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := 11264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := -49920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := 61440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := 96000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := -326656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := 928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := -8544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := 2272, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -108000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 221792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -322720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 34784, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := 512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := -6144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := 15360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 18432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -2944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 1920, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -9728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := -88960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := 284800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := -18304, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := 20736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := 13376, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := -304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := 768, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := -4928, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := 110080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := -208160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := 241408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := -97472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := -9728, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := 222672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := 1664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := -768, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := 19840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := 352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := -5248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := 24288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := -40448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := 12576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := 51840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := -13216, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := -3840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := -192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := 4544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := -34752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := 19264, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := 100544, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := -872768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := 553536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := 768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := -768, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := 76800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := -26880, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := 15360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := 415488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := -1056768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := 171264, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := -6656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := 3072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := -79360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := -6400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := 2240, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := -1280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := -34624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := 88064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := -14272, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := 4992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := -2304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := -2304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := 59520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := -2816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := 12480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := -15360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := -24000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := 81664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 1, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := 1, den := 476, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12],[r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25],[r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37],[r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48],[r49,r50,r51,r52,r53,r54,r55,r56,r57,r58],[r59,r60,r61,r62,r63,r64,r65,r66,r67],[r68,r69,r70,r71,r72,r73,r74,r75],[r76,r77,r78,r79,r80,r81,r82],[r83,r84,r85,r86,r87,r88],[],[],[],[],[r89,r90,r91,r92,r93,r94,r95,r96,r97,r98,r99,r100],[r49,r101,r102,r103,r104,r105,r106,r107,r108,r109,r110],[r49,r50,r111,r112,r113,r114,r115,r116,r117,r118],[0,0,r119,r120,r121,r122,r123,r124,4608],[r89,r125,r126,r127,r128,r129,r130,r131],[0,0,r132,r133,r134,r135,-1024],[],[],[],[],[],[0,r0,r136,r137,r138,r139,r140,r141,r142,r143],[r144,r145,r146,r147,r148,r149,r150,r151,r152],[0,0,r68,r153,r154,r119,r155,-256],[r156,r157,r158,r159,r160,r161,r162],[],[r68,r163,r164,r165,256],[],[],[],[r166,r167,r168,r169,-6016,r170,r171,r172],[],[r83,r84,r85,r86,r87,r88],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,0,r173,r174,r175,r176,r177,r178,r179,r180,-10752],[0,0,0,0,r132,r181,r182,r183,r184,1024],[0,0,r119,r120,r121,r122,r123,r124,4608],[],[0,0,r132,r133,r134,r135,-1024],[],[],[],[],[],[r13,r90,r185,r186,r187,r188,r189,r190,896],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,0,r191,r192,r193,r194,r195,-768],[r0,r196,r197,r198,r199,r200,-1152],[],[r68,r163,r164,r165,256],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,r201,r202,r203,r204,r205,r206,r207,r208,r209,r210,r211,r212,r213]),(⟨0,0,1⟩,[r89,r214,r215,r216,r217,r218,r219,r220,r221,r222,r223,r224,r225]),(⟨0,0,2⟩,[r226,r227,r228,r229,r230,r231,r232,r233,r234,r235,r236,r237]),(⟨0,0,3⟩,[r238,r239,r240,r241,r242,r243,r244,r245,r246,r247,r248]),(⟨0,0,4⟩,[r249,r250,r251,r252,r253,r254,r255,r256,r257,r258]),(⟨0,0,5⟩,[r259,r260,r261,r262,r263,r264,r265,r266,r267]),(⟨0,0,6⟩,[r13,r268,r269,r270,r271,r272,r273,r274]),(⟨0,0,7⟩,[r49,r275,r276,r277,r278,r279,r280]),(⟨0,0,8⟩,[r281,r282,r283,r284,r285,r286]),(⟨0,1,0⟩,[r89,r214,r215,r216,r217,r218,r219,r220,r221,r222,r223,r224,r225]),(⟨0,1,1⟩,[r26,r287,r288,r289,r290,r291,r292,r293,r294,r295,r296,r297]),(⟨0,1,2⟩,[r249,r298,r299,r300,r301,r302,r303,r304,r305,r306,r307]),(⟨0,1,3⟩,[r249,r250,r308,r309,r310,r311,r312,r313,r314,r315]),(⟨0,1,4⟩,[0,0,r191,r316,r317,r318,r319,r320,2304]),(⟨0,1,5⟩,[r26,r321,r322,r323,r324,r325,r326,r327]),(⟨0,1,6⟩,[0,0,r328,r329,r330,r331,-512]),(⟨0,2,0⟩,[r226,r227,r228,r229,r230,r231,r232,r233,r234,r235,r236,r237]),(⟨0,2,1⟩,[r249,r298,r299,r300,r301,r302,r303,r304,r305,r306,r307]),(⟨0,2,2⟩,[0,r201,r332,r333,r334,r335,r336,r337,r338,r339]),(⟨0,2,3⟩,[r340,r341,r342,r343,r344,r345,r346,r347,r348]),(⟨0,2,4⟩,[0,0,r13,r349,r350,r191,r351,-128]),(⟨0,2,5⟩,[r352,r353,r354,r355,r356,r357,r358]),(⟨0,2,7⟩,[r13,r173,r359,r194,128]),(⟨0,3,0⟩,[r238,r239,r240,r241,r242,r243,r244,r245,r246,r247,r248]),(⟨0,3,1⟩,[r249,r250,r308,r309,r310,r311,r312,r313,r314,r315]),(⟨0,3,2⟩,[r340,r341,r342,r343,r344,r345,r346,r347,r348]),(⟨0,3,3⟩,[r360,r361,r362,r363,-3008,r364,r365,r366]),(⟨0,3,5⟩,[r281,r282,r283,r284,r285,r286]),(⟨0,4,0⟩,[r249,r250,r251,r252,r253,r254,r255,r256,r257,r258]),(⟨0,4,1⟩,[0,0,r191,r316,r317,r318,r319,r320,2304]),(⟨0,4,2⟩,[0,0,r13,r349,r350,r191,r351,-128]),(⟨0,5,0⟩,[r259,r260,r261,r262,r263,r264,r265,r266,r267]),(⟨0,5,1⟩,[r26,r321,r322,r323,r324,r325,r326,r327]),(⟨0,5,2⟩,[r352,r353,r354,r355,r356,r357,r358]),(⟨0,5,3⟩,[r281,r282,r283,r284,r285,r286]),(⟨0,6,0⟩,[r13,r268,r269,r270,r271,r272,r273,r274]),(⟨0,6,1⟩,[0,0,r328,r329,r330,r331,-512]),(⟨0,7,0⟩,[r49,r275,r276,r277,r278,r279,r280]),(⟨0,7,2⟩,[r13,r173,r359,r194,128]),(⟨0,8,0⟩,[r281,r282,r283,r284,r285,r286]),(⟨1,0,0⟩,[r89,r214,r215,r216,r217,r218,r219,r220,r221,r222,r223,r224,r225]),(⟨1,0,1⟩,[r26,r287,r288,r289,r290,r291,r292,r293,r294,r295,r296,r297]),(⟨1,0,2⟩,[r249,r298,r299,r300,r301,r302,r303,r304,r305,r306,r307]),(⟨1,0,3⟩,[r249,r250,r308,r309,r310,r311,r312,r313,r314,r315]),(⟨1,0,4⟩,[0,0,r191,r316,r317,r318,r319,r320,2304]),(⟨1,0,5⟩,[r26,r321,r322,r323,r324,r325,r326,r327]),(⟨1,0,6⟩,[0,0,r328,r329,r330,r331,-512]),(⟨1,1,0⟩,[r26,r287,r288,r289,r290,r291,r292,r293,r294,r295,r296,r297]),(⟨1,1,1⟩,[0,0,r367,r368,r369,r370,r371,r372,r373,r374,-5376]),(⟨1,1,2⟩,[0,0,0,0,r328,r375,r376,r163,r377,512]),(⟨1,1,3⟩,[0,0,r191,r316,r317,r318,r319,r320,2304]),(⟨1,1,5⟩,[0,0,r328,r329,r330,r331,-512]),(⟨1,2,0⟩,[r249,r298,r299,r300,r301,r302,r303,r304,r305,r306,r307]),(⟨1,2,1⟩,[0,0,0,0,r328,r375,r376,r163,r377,512]),(⟨1,2,2⟩,[r89,r287,r378,r379,r380,r381,r382,r383,448]),(⟨1,3,0⟩,[r249,r250,r308,r309,r310,r311,r312,r313,r314,r315]),(⟨1,3,1⟩,[0,0,r191,r316,r317,r318,r319,r320,2304]),(⟨1,4,0⟩,[0,0,r191,r316,r317,r318,r319,r320,2304]),(⟨1,5,0⟩,[r26,r321,r322,r323,r324,r325,r326,r327]),(⟨1,5,1⟩,[0,0,r328,r329,r330,r331,-512]),(⟨1,6,0⟩,[0,0,r328,r329,r330,r331,-512]),(⟨2,0,0⟩,[r226,r227,r228,r229,r230,r231,r232,r233,r234,r235,r236,r237]),(⟨2,0,1⟩,[r249,r298,r299,r300,r301,r302,r303,r304,r305,r306,r307]),(⟨2,0,2⟩,[0,r201,r332,r333,r334,r335,r336,r337,r338,r339]),(⟨2,0,3⟩,[r340,r341,r342,r343,r344,r345,r346,r347,r348]),(⟨2,0,4⟩,[0,0,r13,r349,r350,r191,r351,-128]),(⟨2,0,5⟩,[r352,r353,r354,r355,r356,r357,r358]),(⟨2,0,7⟩,[r13,r173,r359,r194,128]),(⟨2,1,0⟩,[r249,r298,r299,r300,r301,r302,r303,r304,r305,r306,r307]),(⟨2,1,1⟩,[0,0,0,0,r328,r375,r376,r163,r377,512]),(⟨2,1,2⟩,[r89,r287,r378,r379,r380,r381,r382,r383,448]),(⟨2,2,0⟩,[0,r201,r332,r333,r334,r335,r336,r337,r338,r339]),(⟨2,2,1⟩,[r89,r287,r378,r379,r380,r381,r382,r383,448]),(⟨2,2,2⟩,[0,0,r166,r384,r385,r386,r387,-384]),(⟨2,2,3⟩,[r201,r388,r389,r390,r391,r392,-576]),(⟨2,2,5⟩,[r13,r173,r359,r194,128]),(⟨2,3,0⟩,[r340,r341,r342,r343,r344,r345,r346,r347,r348]),(⟨2,3,2⟩,[r201,r388,r389,r390,r391,r392,-576]),(⟨2,4,0⟩,[0,0,r13,r349,r350,r191,r351,-128]),(⟨2,5,0⟩,[r352,r353,r354,r355,r356,r357,r358]),(⟨2,5,2⟩,[r13,r173,r359,r194,128]),(⟨2,7,0⟩,[r13,r173,r359,r194,128]),(⟨3,0,0⟩,[r238,r239,r240,r241,r242,r243,r244,r245,r246,r247,r248]),(⟨3,0,1⟩,[r249,r250,r308,r309,r310,r311,r312,r313,r314,r315]),(⟨3,0,2⟩,[r340,r341,r342,r343,r344,r345,r346,r347,r348]),(⟨3,0,3⟩,[r360,r361,r362,r363,-3008,r364,r365,r366]),(⟨3,0,5⟩,[r281,r282,r283,r284,r285,r286]),(⟨3,1,0⟩,[r249,r250,r308,r309,r310,r311,r312,r313,r314,r315]),(⟨3,1,1⟩,[0,0,r191,r316,r317,r318,r319,r320,2304]),(⟨3,2,0⟩,[r340,r341,r342,r343,r344,r345,r346,r347,r348]),(⟨3,2,2⟩,[r201,r388,r389,r390,r391,r392,-576]),(⟨3,3,0⟩,[r360,r361,r362,r363,-3008,r364,r365,r366]),(⟨3,5,0⟩,[r281,r282,r283,r284,r285,r286]),(⟨4,0,0⟩,[r249,r250,r251,r252,r253,r254,r255,r256,r257,r258]),(⟨4,0,1⟩,[0,0,r191,r316,r317,r318,r319,r320,2304]),(⟨4,0,2⟩,[0,0,r13,r349,r350,r191,r351,-128]),(⟨4,1,0⟩,[0,0,r191,r316,r317,r318,r319,r320,2304]),(⟨4,2,0⟩,[0,0,r13,r349,r350,r191,r351,-128]),(⟨5,0,0⟩,[r259,r260,r261,r262,r263,r264,r265,r266,r267]),(⟨5,0,1⟩,[r26,r321,r322,r323,r324,r325,r326,r327]),(⟨5,0,2⟩,[r352,r353,r354,r355,r356,r357,r358]),(⟨5,0,3⟩,[r281,r282,r283,r284,r285,r286]),(⟨5,1,0⟩,[r26,r321,r322,r323,r324,r325,r326,r327]),(⟨5,1,1⟩,[0,0,r328,r329,r330,r331,-512]),(⟨5,2,0⟩,[r352,r353,r354,r355,r356,r357,r358]),(⟨5,2,2⟩,[r13,r173,r359,r194,128]),(⟨5,3,0⟩,[r281,r282,r283,r284,r285,r286]),(⟨6,0,0⟩,[r13,r268,r269,r270,r271,r272,r273,r274]),(⟨6,0,1⟩,[0,0,r328,r329,r330,r331,-512]),(⟨6,1,0⟩,[0,0,r328,r329,r330,r331,-512]),(⟨7,0,0⟩,[r49,r275,r276,r277,r278,r279,r280]),(⟨7,0,2⟩,[r13,r173,r359,r194,128]),(⟨7,2,0⟩,[r13,r173,r359,r194,128]),(⟨8,0,0⟩,[r281,r282,r283,r284,r285,r286])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,-3,15,-21,3,6]),(⟨0,0,1⟩,[1,-5,10,-11,7]),(⟨0,0,2⟩,[0,0,2,-2]),(⟨0,0,3⟩,[-3,8,-9]),(⟨0,0,5⟩,[2]),(⟨0,1,0⟩,[1,-5,10,-11,7]),(⟨0,2,0⟩,[0,0,2,-2]),(⟨0,3,0⟩,[-3,8,-9]),(⟨0,5,0⟩,[2]),(⟨1,0,0⟩,[1,-5,10,-11,7]),(⟨2,0,0⟩,[0,0,2,-2]),(⟨3,0,0⟩,[-3,8,-9]),(⟨5,0,0⟩,[2])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[-256,4800,-35712,145856,-387968,744000,-1039488,811328,-95104]),(⟨0,0,1⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨0,0,2⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨0,0,3⟩,[128,-2688,15616,-40192,84608,-123008]),(⟨0,1,0⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨0,1,1⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨0,2,0⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨0,2,2⟩,[-256,3072,-7680,-9216,30464]),(⟨0,3,0⟩,[128,-2688,15616,-40192,84608,-123008]),(⟨1,0,0⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨1,0,1⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨1,1,0⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨2,0,0⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨2,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨2,2,0⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[128,-2688,15616,-40192,84608,-123008])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 1 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r393) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 6 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r394) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨5,0,0⟩,[2])]

noncomputable def partial12 : Poly := [(⟨5,0,0⟩,[-512,9600,-71424,291712,-775936,1488000,-2078976,1622656,-190208]),(⟨5,0,1⟩,[-128,3712,-34176,154496,-432000,887168,-1290880,973952]),(⟨5,0,2⟩,[640,-9728,47232,-100352,146304,-119296,-95872]),(⟨5,0,3⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨5,1,0⟩,[-128,3712,-34176,154496,-432000,887168,-1290880,973952]),(⟨5,1,1⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨5,2,0⟩,[640,-9728,47232,-100352,146304,-119296,-95872]),(⟨5,2,2⟩,[-512,6144,-15360,-18432,60928]),(⟨5,3,0⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨6,0,0⟩,[-128,3712,-34176,154496,-432000,887168,-1290880,973952]),(⟨6,0,1⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨6,1,0⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨7,0,0⟩,[640,-9728,47232,-100352,146304,-119296,-95872]),(⟨7,0,2⟩,[-512,6144,-15360,-18432,60928]),(⟨7,2,0⟩,[-512,6144,-15360,-18432,60928]),(⟨8,0,0⟩,[256,-5376,31232,-80384,169216,-246016])]


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

noncomputable def partial8 : Poly := [(⟨0,5,0⟩,[-512,9600,-71424,291712,-775936,1488000,-2078976,1622656,-190208]),(⟨0,5,1⟩,[-128,3712,-34176,154496,-432000,887168,-1290880,973952]),(⟨0,5,2⟩,[640,-9728,47232,-100352,146304,-119296,-95872]),(⟨0,5,3⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨0,6,0⟩,[-128,3712,-34176,154496,-432000,887168,-1290880,973952]),(⟨0,6,1⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨0,7,0⟩,[640,-9728,47232,-100352,146304,-119296,-95872]),(⟨0,7,2⟩,[-512,6144,-15360,-18432,60928]),(⟨0,8,0⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨1,0,0⟩,[-256,6080,-62272,375232,-1528960,4568832,-10493568,18737408,-25446400,25231168,-17152064,6725440,-665728]),(⟨1,0,1⟩,[-64,2176,-27008,181952,-793984,2497024,-5992704,11066752,-15280704,15074688,-9874816,3408832]),(⟨1,0,2⟩,[320,-6464,51136,-220416,615936,-1220992,1699072,-1512704,688832,109760,-335552]),(⟨1,0,3⟩,[128,-3328,30336,-146560,472192,-1138560,2012544,-2442112,1945344,-861056]),(⟨1,1,0⟩,[-64,2176,-27008,181952,-793984,2497024,-5992704,11066752,-15280704,15074688,-9874816,3408832]),(⟨1,1,1⟩,[0,0,1024,-17408,102400,-250880,143360,553984,-1409024,1598464,-852992]),(⟨1,2,0⟩,[320,-6464,51136,-220416,615936,-1220992,1699072,-1512704,688832,109760,-335552]),(⟨1,2,2⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨1,3,0⟩,[128,-3328,30336,-146560,472192,-1138560,2012544,-2442112,1945344,-861056]),(⟨1,5,0⟩,[-128,3712,-34176,154496,-432000,887168,-1290880,973952]),(⟨1,5,1⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨1,6,0⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨2,0,0⟩,[-64,2176,-27520,192064,-875008,2860160,-7060352,13330688,-18847680,18776320,-11687680,3599040]),(⟨2,0,1⟩,[0,0,896,-13568,64512,-62208,-443136,1873152,-3587072,3863296,-1826944]),(⟨2,0,2⟩,[0,0,640,-10368,56960,-147584,246656,-265600,23424,95872]),(⟨2,0,3⟩,[0,0,256,-5632,36608,-111616,249600,-415232,246016]),(⟨2,1,0⟩,[0,0,896,-13568,64512,-62208,-443136,1873152,-3587072,3863296,-1826944]),(⟨2,1,1⟩,[0,0,0,0,2048,-26624,86016,12288,-317440,243712]),(⟨2,2,0⟩,[0,0,640,-10368,56960,-147584,246656,-265600,23424,95872]),(⟨2,2,2⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨2,3,0⟩,[0,0,256,-5632,36608,-111616,249600,-415232,246016]),(⟨2,5,0⟩,[640,-9728,47232,-100352,146304,-119296,-95872]),(⟨2,5,2⟩,[-512,6144,-15360,-18432,60928]),(⟨2,7,0⟩,[-512,6144,-15360,-18432,60928]),(⟨3,0,0⟩,[1088,-22912,198848,-983040,3230208,-7680768,13674752,-17639424,14642112,-5688192,-453568]),(⟨3,0,1⟩,[192,-6080,66688,-385152,1421824,-3780608,7515008,-10604416,9387328,-4139072]),(⟨3,0,2⟩,[-1216,21504,-138240,445952,-869248,1077248,-639488,-246272,644672]),(⟨3,0,3⟩,[-384,9088,-69504,269696,-715904,1407616,-1745536,1107072]),(⟨3,1,0⟩,[192,-6080,66688,-385152,1421824,-3780608,7515008,-10604416,9387328,-4139072]),(⟨3,1,1⟩,[0,0,-3072,45056,-199680,245760,384000,-1306624,1096704]),(⟨3,2,0⟩,[-1216,21504,-138240,445952,-869248,1077248,-639488,-246272,644672]),(⟨3,2,2⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨3,3,0⟩,[-384,9088,-69504,269696,-715904,1407616,-1745536,1107072]),(⟨3,5,0⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨4,0,0⟩,[320,-9408,97664,-542080,1948928,-5040128,9688192,-13324416,11673536,-5147968]),(⟨4,0,1⟩,[0,0,-3072,45056,-199680,245760,384000,-1306624,1096704]),(⟨4,0,2⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨4,1,0⟩,[0,0,-3072,45056,-199680,245760,384000,-1306624,1096704]),(⟨4,2,0⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨5,0,0⟩,[-1472,26752,-183808,669312,-1572736,2592128,-2821120,1360768,487232]),(⟨5,0,1⟩,[-128,3712,-34176,154496,-432000,887168,-1290880,973952]),(⟨5,0,2⟩,[1408,-20992,97152,-161792,50304,207360,-370048]),(⟨5,0,3⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨5,1,0⟩,[-128,3712,-34176,154496,-432000,887168,-1290880,973952]),(⟨5,1,1⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨5,2,0⟩,[1408,-20992,97152,-161792,50304,207360,-370048]),(⟨5,2,2⟩,[-512,6144,-15360,-18432,60928]),(⟨5,3,0⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨6,0,0⟩,[-512,12800,-103680,424192,-1147904,2294784,-3036416,2081024]),(⟨6,0,1⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨6,1,0⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨7,0,0⟩,[640,-9728,47232,-100352,146304,-119296,-95872]),(⟨7,0,2⟩,[-512,6144,-15360,-18432,60928]),(⟨7,2,0⟩,[-512,6144,-15360,-18432,60928]),(⟨8,0,0⟩,[256,-5376,31232,-80384,169216,-246016])]


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

noncomputable def partial4 : Poly := [(⟨0,0,5⟩,[-512,9600,-71424,291712,-775936,1488000,-2078976,1622656,-190208]),(⟨0,0,6⟩,[-128,3712,-34176,154496,-432000,887168,-1290880,973952]),(⟨0,0,7⟩,[640,-9728,47232,-100352,146304,-119296,-95872]),(⟨0,0,8⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨0,1,0⟩,[-256,6080,-62272,375232,-1528960,4568832,-10493568,18737408,-25446400,25231168,-17152064,6725440,-665728]),(⟨0,1,1⟩,[-64,2176,-27008,181952,-793984,2497024,-5992704,11066752,-15280704,15074688,-9874816,3408832]),(⟨0,1,2⟩,[320,-6464,51136,-220416,615936,-1220992,1699072,-1512704,688832,109760,-335552]),(⟨0,1,3⟩,[128,-3328,30336,-146560,472192,-1138560,2012544,-2442112,1945344,-861056]),(⟨0,1,5⟩,[-128,3712,-34176,154496,-432000,887168,-1290880,973952]),(⟨0,1,6⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨0,2,0⟩,[-64,2176,-27520,192064,-875008,2860160,-7060352,13330688,-18847680,18776320,-11687680,3599040]),(⟨0,2,1⟩,[0,0,896,-13568,64512,-62208,-443136,1873152,-3587072,3863296,-1826944]),(⟨0,2,2⟩,[0,0,640,-10368,56960,-147584,246656,-265600,23424,95872]),(⟨0,2,3⟩,[0,0,256,-5632,36608,-111616,249600,-415232,246016]),(⟨0,2,5⟩,[640,-9728,47232,-100352,146304,-119296,-95872]),(⟨0,2,7⟩,[-512,6144,-15360,-18432,60928]),(⟨0,3,0⟩,[1088,-22912,198848,-983040,3230208,-7680768,13674752,-17639424,14642112,-5688192,-453568]),(⟨0,3,1⟩,[192,-6080,66688,-385152,1421824,-3780608,7515008,-10604416,9387328,-4139072]),(⟨0,3,2⟩,[-1216,21504,-138240,445952,-869248,1077248,-639488,-246272,644672]),(⟨0,3,3⟩,[-384,9088,-69504,269696,-715904,1407616,-1745536,1107072]),(⟨0,3,5⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨0,4,0⟩,[320,-9408,97664,-542080,1948928,-5040128,9688192,-13324416,11673536,-5147968]),(⟨0,4,1⟩,[0,0,-3072,45056,-199680,245760,384000,-1306624,1096704]),(⟨0,4,2⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨0,5,0⟩,[-1472,26752,-183808,669312,-1572736,2592128,-2821120,1360768,487232]),(⟨0,5,1⟩,[-128,3712,-34176,154496,-432000,887168,-1290880,973952]),(⟨0,5,2⟩,[1408,-20992,97152,-161792,50304,207360,-370048]),(⟨0,5,3⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨0,6,0⟩,[-512,12800,-103680,424192,-1147904,2294784,-3036416,2081024]),(⟨0,6,1⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨0,7,0⟩,[640,-9728,47232,-100352,146304,-119296,-95872]),(⟨0,7,2⟩,[-512,6144,-15360,-18432,60928]),(⟨0,8,0⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨1,0,0⟩,[-256,6080,-62272,375232,-1528960,4568832,-10493568,18737408,-25446400,25231168,-17152064,6725440,-665728]),(⟨1,0,1⟩,[-64,2176,-27008,181952,-793984,2497024,-5992704,11066752,-15280704,15074688,-9874816,3408832]),(⟨1,0,2⟩,[320,-6464,51136,-220416,615936,-1220992,1699072,-1512704,688832,109760,-335552]),(⟨1,0,3⟩,[128,-3328,30336,-146560,472192,-1138560,2012544,-2442112,1945344,-861056]),(⟨1,0,5⟩,[-128,3712,-34176,154496,-432000,887168,-1290880,973952]),(⟨1,0,6⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨1,1,0⟩,[-128,4352,-54016,363904,-1587968,4994048,-11985408,22133504,-30561408,30149376,-19749632,6817664]),(⟨1,1,1⟩,[0,0,2048,-34816,204800,-501760,286720,1107968,-2818048,3196928,-1705984]),(⟨1,1,5⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨1,2,0⟩,[320,-6464,52032,-233984,680448,-1283200,1255936,360448,-2898240,3973056,-2162496]),(⟨1,2,1⟩,[0,0,0,0,2048,-26624,86016,12288,-317440,243712]),(⟨1,2,2⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨1,3,0⟩,[320,-9408,97024,-531712,1894016,-4919168,9527552,-13046528,11332672,-5000128]),(⟨1,3,1⟩,[0,0,-3072,45056,-199680,245760,384000,-1306624,1096704]),(⟨1,4,0⟩,[0,0,-3072,45056,-199680,245760,384000,-1306624,1096704]),(⟨1,5,0⟩,[-128,3712,-34176,154496,-432000,887168,-1290880,973952]),(⟨1,5,1⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨1,6,0⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨2,0,0⟩,[-64,2176,-27520,192064,-875008,2860160,-7060352,13330688,-18847680,18776320,-11687680,3599040]),(⟨2,0,1⟩,[0,0,896,-13568,64512,-62208,-443136,1873152,-3587072,3863296,-1826944]),(⟨2,0,2⟩,[0,0,640,-10368,56960,-147584,246656,-265600,23424,95872]),(⟨2,0,3⟩,[0,0,256,-5632,36608,-111616,249600,-415232,246016]),(⟨2,0,5⟩,[640,-9728,47232,-100352,146304,-119296,-95872]),(⟨2,0,7⟩,[-512,6144,-15360,-18432,60928]),(⟨2,1,0⟩,[320,-6464,52032,-233984,680448,-1283200,1255936,360448,-2898240,3973056,-2162496]),(⟨2,1,1⟩,[0,0,0,0,2048,-26624,86016,12288,-317440,243712]),(⟨2,1,2⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨2,2,0⟩,[0,0,1280,-20736,113920,-295168,493312,-531200,46848,191744]),(⟨2,2,2⟩,[0,0,-1024,13312,-43008,-6144,158720,-121856]),(⟨2,2,5⟩,[-512,6144,-15360,-18432,60928]),(⟨2,3,0⟩,[-1216,21504,-137984,440320,-832640,965632,-389888,-661504,890688]),(⟨2,3,2⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨2,4,0⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨2,5,0⟩,[1408,-20992,97152,-161792,50304,207360,-370048]),(⟨2,5,2⟩,[-512,6144,-15360,-18432,60928]),(⟨2,7,0⟩,[-512,6144,-15360,-18432,60928]),(⟨3,0,0⟩,[1088,-22912,198848,-983040,3230208,-7680768,13674752,-17639424,14642112,-5688192,-453568]),(⟨3,0,1⟩,[192,-6080,66688,-385152,1421824,-3780608,7515008,-10604416,9387328,-4139072]),(⟨3,0,2⟩,[-1216,21504,-138240,445952,-869248,1077248,-639488,-246272,644672]),(⟨3,0,3⟩,[-384,9088,-69504,269696,-715904,1407616,-1745536,1107072]),(⟨3,0,5⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨3,1,0⟩,[320,-9408,97024,-531712,1894016,-4919168,9527552,-13046528,11332672,-5000128]),(⟨3,1,1⟩,[0,0,-3072,45056,-199680,245760,384000,-1306624,1096704]),(⟨3,2,0⟩,[-1216,21504,-137984,440320,-832640,965632,-389888,-661504,890688]),(⟨3,2,2⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨3,3,0⟩,[-768,18176,-139008,539392,-1431808,2815232,-3491072,2214144]),(⟨3,5,0⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨4,0,0⟩,[320,-9408,97664,-542080,1948928,-5040128,9688192,-13324416,11673536,-5147968]),(⟨4,0,1⟩,[0,0,-3072,45056,-199680,245760,384000,-1306624,1096704]),(⟨4,0,2⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨4,1,0⟩,[0,0,-3072,45056,-199680,245760,384000,-1306624,1096704]),(⟨4,2,0⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨5,0,0⟩,[-1472,26752,-183808,669312,-1572736,2592128,-2821120,1360768,487232]),(⟨5,0,1⟩,[-128,3712,-34176,154496,-432000,887168,-1290880,973952]),(⟨5,0,2⟩,[1408,-20992,97152,-161792,50304,207360,-370048]),(⟨5,0,3⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨5,1,0⟩,[-128,3712,-34176,154496,-432000,887168,-1290880,973952]),(⟨5,1,1⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨5,2,0⟩,[1408,-20992,97152,-161792,50304,207360,-370048]),(⟨5,2,2⟩,[-512,6144,-15360,-18432,60928]),(⟨5,3,0⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨6,0,0⟩,[-512,12800,-103680,424192,-1147904,2294784,-3036416,2081024]),(⟨6,0,1⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨6,1,0⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨7,0,0⟩,[640,-9728,47232,-100352,146304,-119296,-95872]),(⟨7,0,2⟩,[-512,6144,-15360,-18432,60928]),(⟨7,2,0⟩,[-512,6144,-15360,-18432,60928]),(⟨8,0,0⟩,[256,-5376,31232,-80384,169216,-246016])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,768,-18240,184512,-1074816,4114560,-11192832,22649088,-33939072,34188672,-17118912,-1805760,4582656,-570624]),(⟨0,0,1⟩,[-256,6272,-68800,455680,-2056192,6739584,-16726656,31992704,-46088704,46124800,-26653376,4313728,2256128]),(⟨0,0,2⟩,[-64,1216,-8128,41536,-267136,1379456,-4688768,11034752,-18395712,20042944,-12189376,3311424]),(⟨0,0,3⟩,[1088,-23296,208832,-1072896,3641856,-8872704,16187648,-21288192,17237952,-5549568,-1191616]),(⟨0,0,4⟩,[320,-9408,97664,-542080,1948928,-5040128,9688192,-13324416,11673536,-5147968]),(⟨0,0,5⟩,[-1472,26752,-183808,669312,-1572736,2592128,-2821120,1360768,487232]),(⟨0,0,6⟩,[-512,12800,-103680,424192,-1147904,2294784,-3036416,2081024]),(⟨0,0,7⟩,[640,-9728,47232,-100352,146304,-119296,-95872]),(⟨0,0,8⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨0,1,0⟩,[-256,6272,-68800,455680,-2056192,6739584,-16726656,31992704,-46088704,46124800,-26653376,4313728,2256128]),(⟨0,1,1⟩,[-128,4352,-54016,360832,-1535744,4696064,-11374080,22376192,-33144960,33003264,-19894016,6086528]),(⟨0,1,2⟩,[320,-6464,52032,-233984,680448,-1283200,1255936,360448,-2898240,3973056,-2162496]),(⟨0,1,3⟩,[320,-9408,97024,-531712,1894016,-4919168,9527552,-13046528,11332672,-5000128]),(⟨0,1,4⟩,[0,0,-3072,45056,-199680,245760,384000,-1306624,1096704]),(⟨0,1,5⟩,[-128,3712,-34176,154496,-432000,887168,-1290880,973952]),(⟨0,1,6⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨0,2,0⟩,[-64,1216,-8128,41536,-267136,1379456,-4688768,11034752,-18395712,20042944,-12189376,3311424]),(⟨0,2,1⟩,[320,-6464,52032,-233984,680448,-1283200,1255936,360448,-2898240,3973056,-2162496]),(⟨0,2,2⟩,[0,768,-11776,53760,-38912,-355840,1139200,-1244672,82944,374528]),(⟨0,2,3⟩,[-1216,21504,-137984,440320,-832640,965632,-389888,-661504,890688]),(⟨0,2,4⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨0,2,5⟩,[1408,-20992,97152,-161792,50304,207360,-370048]),(⟨0,2,7⟩,[-512,6144,-15360,-18432,60928]),(⟨0,3,0⟩,[1088,-23296,208832,-1072896,3641856,-8872704,16187648,-21288192,17237952,-5549568,-1191616]),(⟨0,3,1⟩,[320,-9408,97024,-531712,1894016,-4919168,9527552,-13046528,11332672,-5000128]),(⟨0,3,2⟩,[-1216,21504,-137984,440320,-832640,965632,-389888,-661504,890688]),(⟨0,3,3⟩,[-768,18176,-139008,539392,-1431808,2815232,-3491072,2214144]),(⟨0,3,5⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨0,4,0⟩,[320,-9408,97664,-542080,1948928,-5040128,9688192,-13324416,11673536,-5147968]),(⟨0,4,1⟩,[0,0,-3072,45056,-199680,245760,384000,-1306624,1096704]),(⟨0,4,2⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨0,5,0⟩,[-1472,26752,-183808,669312,-1572736,2592128,-2821120,1360768,487232]),(⟨0,5,1⟩,[-128,3712,-34176,154496,-432000,887168,-1290880,973952]),(⟨0,5,2⟩,[1408,-20992,97152,-161792,50304,207360,-370048]),(⟨0,5,3⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨0,6,0⟩,[-512,12800,-103680,424192,-1147904,2294784,-3036416,2081024]),(⟨0,6,1⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨0,7,0⟩,[640,-9728,47232,-100352,146304,-119296,-95872]),(⟨0,7,2⟩,[-512,6144,-15360,-18432,60928]),(⟨0,8,0⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨1,0,0⟩,[-256,6272,-68800,455680,-2056192,6739584,-16726656,31992704,-46088704,46124800,-26653376,4313728,2256128]),(⟨1,0,1⟩,[-128,4352,-54016,360832,-1535744,4696064,-11374080,22376192,-33144960,33003264,-19894016,6086528]),(⟨1,0,2⟩,[320,-6464,52032,-233984,680448,-1283200,1255936,360448,-2898240,3973056,-2162496]),(⟨1,0,3⟩,[320,-9408,97024,-531712,1894016,-4919168,9527552,-13046528,11332672,-5000128]),(⟨1,0,4⟩,[0,0,-3072,45056,-199680,245760,384000,-1306624,1096704]),(⟨1,0,5⟩,[-128,3712,-34176,154496,-432000,887168,-1290880,973952]),(⟨1,0,6⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨1,1,0⟩,[-128,4352,-54016,360832,-1535744,4696064,-11374080,22376192,-33144960,33003264,-19894016,6086528]),(⟨1,1,1⟩,[0,0,3072,-52224,307200,-752640,430080,1661952,-4227072,4795392,-2558976]),(⟨1,1,2⟩,[0,0,0,0,2048,-26624,86016,12288,-317440,243712]),(⟨1,1,3⟩,[0,0,-3072,45056,-199680,245760,384000,-1306624,1096704]),(⟨1,1,5⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨1,2,0⟩,[320,-6464,52032,-233984,680448,-1283200,1255936,360448,-2898240,3973056,-2162496]),(⟨1,2,1⟩,[0,0,0,0,2048,-26624,86016,12288,-317440,243712]),(⟨1,2,2⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨1,3,0⟩,[320,-9408,97024,-531712,1894016,-4919168,9527552,-13046528,11332672,-5000128]),(⟨1,3,1⟩,[0,0,-3072,45056,-199680,245760,384000,-1306624,1096704]),(⟨1,4,0⟩,[0,0,-3072,45056,-199680,245760,384000,-1306624,1096704]),(⟨1,5,0⟩,[-128,3712,-34176,154496,-432000,887168,-1290880,973952]),(⟨1,5,1⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨1,6,0⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨2,0,0⟩,[-64,1216,-8128,41536,-267136,1379456,-4688768,11034752,-18395712,20042944,-12189376,3311424]),(⟨2,0,1⟩,[320,-6464,52032,-233984,680448,-1283200,1255936,360448,-2898240,3973056,-2162496]),(⟨2,0,2⟩,[0,768,-11776,53760,-38912,-355840,1139200,-1244672,82944,374528]),(⟨2,0,3⟩,[-1216,21504,-137984,440320,-832640,965632,-389888,-661504,890688]),(⟨2,0,4⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨2,0,5⟩,[1408,-20992,97152,-161792,50304,207360,-370048]),(⟨2,0,7⟩,[-512,6144,-15360,-18432,60928]),(⟨2,1,0⟩,[320,-6464,52032,-233984,680448,-1283200,1255936,360448,-2898240,3973056,-2162496]),(⟨2,1,1⟩,[0,0,0,0,2048,-26624,86016,12288,-317440,243712]),(⟨2,1,2⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨2,2,0⟩,[0,768,-11776,53760,-38912,-355840,1139200,-1244672,82944,374528]),(⟨2,2,1⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨2,2,2⟩,[0,0,-1536,19968,-64512,-9216,238080,-182784]),(⟨2,2,3⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨2,2,5⟩,[-512,6144,-15360,-18432,60928]),(⟨2,3,0⟩,[-1216,21504,-137984,440320,-832640,965632,-389888,-661504,890688]),(⟨2,3,2⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨2,4,0⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨2,5,0⟩,[1408,-20992,97152,-161792,50304,207360,-370048]),(⟨2,5,2⟩,[-512,6144,-15360,-18432,60928]),(⟨2,7,0⟩,[-512,6144,-15360,-18432,60928]),(⟨3,0,0⟩,[1088,-23296,208832,-1072896,3641856,-8872704,16187648,-21288192,17237952,-5549568,-1191616]),(⟨3,0,1⟩,[320,-9408,97024,-531712,1894016,-4919168,9527552,-13046528,11332672,-5000128]),(⟨3,0,2⟩,[-1216,21504,-137984,440320,-832640,965632,-389888,-661504,890688]),(⟨3,0,3⟩,[-768,18176,-139008,539392,-1431808,2815232,-3491072,2214144]),(⟨3,0,5⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨3,1,0⟩,[320,-9408,97024,-531712,1894016,-4919168,9527552,-13046528,11332672,-5000128]),(⟨3,1,1⟩,[0,0,-3072,45056,-199680,245760,384000,-1306624,1096704]),(⟨3,2,0⟩,[-1216,21504,-137984,440320,-832640,965632,-389888,-661504,890688]),(⟨3,2,2⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨3,3,0⟩,[-768,18176,-139008,539392,-1431808,2815232,-3491072,2214144]),(⟨3,5,0⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨4,0,0⟩,[320,-9408,97664,-542080,1948928,-5040128,9688192,-13324416,11673536,-5147968]),(⟨4,0,1⟩,[0,0,-3072,45056,-199680,245760,384000,-1306624,1096704]),(⟨4,0,2⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨4,1,0⟩,[0,0,-3072,45056,-199680,245760,384000,-1306624,1096704]),(⟨4,2,0⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨5,0,0⟩,[-1472,26752,-183808,669312,-1572736,2592128,-2821120,1360768,487232]),(⟨5,0,1⟩,[-128,3712,-34176,154496,-432000,887168,-1290880,973952]),(⟨5,0,2⟩,[1408,-20992,97152,-161792,50304,207360,-370048]),(⟨5,0,3⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨5,1,0⟩,[-128,3712,-34176,154496,-432000,887168,-1290880,973952]),(⟨5,1,1⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨5,2,0⟩,[1408,-20992,97152,-161792,50304,207360,-370048]),(⟨5,2,2⟩,[-512,6144,-15360,-18432,60928]),(⟨5,3,0⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨6,0,0⟩,[-512,12800,-103680,424192,-1147904,2294784,-3036416,2081024]),(⟨6,0,1⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨6,1,0⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨7,0,0⟩,[640,-9728,47232,-100352,146304,-119296,-95872]),(⟨7,0,2⟩,[-512,6144,-15360,-18432,60928]),(⟨7,2,0⟩,[-512,6144,-15360,-18432,60928]),(⟨8,0,0⟩,[256,-5376,31232,-80384,169216,-246016])]


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
    (Poly.add (Poly.scale (K.ofRat r395) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 1 6).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r393*r394 : ℚ)=r395 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 1 6 r393 r394 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 1=6 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 1 6).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C064

#print axioms Coulomb8.Columns.C064.sound
