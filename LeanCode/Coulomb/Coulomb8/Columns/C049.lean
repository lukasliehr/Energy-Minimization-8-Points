import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C049

def r0 : ℚ := { num := -576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 14400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -20928, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 790656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -2459712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 256128, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -3706944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 8832, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 1659264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -341952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -34176, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -5568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := 67072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := -438528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := 1718336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 5911488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -4168704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 244736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 1013440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -3904, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -8768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 11648, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -24832, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 1396352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -3044864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 238464, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -149504, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -48640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 65728, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 8832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -78976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 342656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -728064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 522624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 465792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := -623232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -13952, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -1152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 23872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -185856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 100800, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -1387648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 1241024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -167168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -26816, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -40640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 186112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -23616, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 304000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 7744, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -1920, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 73728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -135936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 51456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -6656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 4864, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -49664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := -384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := 576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := -1792, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := 110720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := -538752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := 1604352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := -2930048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 2958208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -1136512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -170304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := -4736, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 1216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -9152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 40448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -136384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 359168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := 407808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 37120, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -62272, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 6976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -77696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 310848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -629120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 42176, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -560256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 50688, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := -3392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 23104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -84544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 24768, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -131520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -121920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 28864, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -2816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 13248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := -24576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 15616, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := -128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := 1664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := -768, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 19840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -3840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -4608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 7936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -61312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 229120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -444544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := 52992, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 2688, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -12544, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 3648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -6784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 32960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := -111232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := 96448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := 4992, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := -6400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := 33024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := -3072, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 1792, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := 128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -1280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := -3200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := 59904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := -174208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := 11008, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := -14464, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := 2048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := -12032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 33280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -29824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := -2560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -3840, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := 6144, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -226176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 24192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := 493824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := -1628160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 272832, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := 1152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := -7936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := 28800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := -56192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := 21888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 24320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := -61824, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -4096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := 22272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := -50688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := 20224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 158720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := -329472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 7808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -13824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 2432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := 8960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := -1024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 320, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := -1536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 6656, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := 3328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := -1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := 39680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 7200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := -10464, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := 395328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := -1229856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := 128064, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -1853472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 4416, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := 829632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := -170976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := -17088, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := 96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -2784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := 33536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -219264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 859168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := 2955744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := -2084352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := 122368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := 506720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := -1952, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -4384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 5824, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -12416, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := 698176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := -1522432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := 119232, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := -74752, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := -24320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 32864, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := 4416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -39488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := 171328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := -364032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := 261312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := 232896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := -311616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := -6976, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 11936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -92928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := 50400, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := -693824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := 620512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := -83584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -13408, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := -96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := -20320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := 93056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := -11808, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := 152000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 3872, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 36864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := -67968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := 25728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := -3328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := 2432, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := -24832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := -192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := 288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := -896, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := 55360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -269376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 802176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := -1465024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := 1479104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := -568256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -85152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := -2368, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := -32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := 608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := -4576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := -68192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := 179584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := 203904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := 18560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := -31136, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := 3488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := -38848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := 155424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := -314560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := 21088, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := -280128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := 25344, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := -1696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := 11552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := -42272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := 12384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := -65760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -60960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := 14432, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := -1408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := 6624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := -12288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := -480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := 7808, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := 832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 9920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := -1920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := -2304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := 3968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := -30656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := 114560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := -222272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := 26496, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := 1344, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := -6272, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := 32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := -64, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := 1824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := 16480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := -55616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := 48224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := 2496, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := 16512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := -1536, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := 896, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := -640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -1600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := 29952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := -87104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := 5504, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := -7232, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := 1024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := -6016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := 16640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -14912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := -1280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := 3072, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -113088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 12096, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := 246912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := -814080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := 136416, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := -3968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -28096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 10944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := 12160, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := -30912, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -2048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := 11136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := -25344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := 10112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := 79360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := -164736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := 3904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := -6912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := 4480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 160, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := 3328, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 1, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := 1, den := 476, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10],[0,r11,r12,r13,r14,r15,-34816,r16,r17,r18,r19,r20],[0,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30],[0,r31,r32,r33,r34,r35,r36,r37,r38,r39],[0,r40,r41,r42,r43,r44,r45,r46,r47],[0,r48,r49,r50,r51,r52,r53,r54],[0,r55,r56,r57,r58,r59,128],[0,r21,r60,r61,r62,r63],[],[],[],[],[],[0,r64,r65,r66,r67,r68,r69,r70,r71,r72,r73],[r74,r75,r76,r77,r78,r79,-5056,r80,r81,r82],[r74,r21,r83,r84,r85,r86,r87,r88,r89],[r11,r90,r91,r92,r93,r94,r95,r96],[r11,r97,r98,r99,r100,r101,-1344],[r102,r103,r104,r105,r106,-128],[r102,r107,r108,r109,128],[],[],[],[],[0,r31,r110,r111,r112,r113,r114,r115,r116],[r117,r118,r119,r120,r121,r122,r123,r124],[0,r21,r125,r126,r127,r49,r128],[],[],[],[],[],[],[r129,r130,r131,r132,r133,r134,r135],[r102,r136,r137,r138,r139,r140],[r102,r107,r108,r109,128],[],[],[],[],[],[],[],[],[],[],[],[],[],[r48,r119,r141,r142,r143,r144,r145,r146,r147,-6720],[r74,r148,r149,r150,r151,r152,r153,r154,3136],[r155,r156,r157,r158,r159,r160,r161,1536],[r129,r162,r163,r164,r165,r166,-896],[],[],[],[],[],[],[],[r117,r167,r168,r169,r90,r170,-448],[],[],[],[],[],[],[r171,r172,r169,r173,r174,-256],[r102,r107,r108,r109,128],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,0,r175,r176,r177,r178,r179,r180,r181,r182,r183,r184,r185]),(⟨0,0,1⟩,[0,r186,r187,r188,r189,r190,-17408,r191,r192,r193,r194,r195]),(⟨0,0,2⟩,[0,r11,r196,r197,r198,r199,r200,r201,r202,r203,r204]),(⟨0,0,3⟩,[0,r48,r205,r206,r207,r208,r209,r210,r211,r212]),(⟨0,0,4⟩,[0,r0,r213,r214,r215,r216,r217,r218,r219]),(⟨0,0,5⟩,[0,r220,r221,r222,r223,r224,r225,r226]),(⟨0,0,6⟩,[0,r21,r227,r228,r229,r230,64]),(⟨0,0,7⟩,[0,r11,r231,r232,r233,r234]),(⟨0,1,0⟩,[0,r186,r187,r188,r189,r190,-17408,r191,r192,r193,r194,r195]),(⟨0,1,1⟩,[0,r235,r236,r237,r238,r239,r240,r241,r242,r243,r244]),(⟨0,1,2⟩,[r245,r246,r247,r159,r248,r249,-2528,r250,r251,r252]),(⟨0,1,3⟩,[r245,r11,r253,r254,r255,r256,r257,r258,r259]),(⟨0,1,4⟩,[r186,r260,r261,r262,r263,r264,r265,r266]),(⟨0,1,5⟩,[r186,r267,r268,r269,r270,r271,-672]),(⟨0,1,6⟩,[r74,r272,r63,r31,r273,-64]),(⟨0,1,7⟩,[r74,r55,r274,r275,64]),(⟨0,2,0⟩,[0,r11,r196,r197,r198,r199,r200,r201,r202,r203,r204]),(⟨0,2,1⟩,[r245,r246,r247,r159,r248,r249,-2528,r250,r251,r252]),(⟨0,2,2⟩,[0,r48,r276,r277,r278,r279,r280,r281,r282]),(⟨0,2,3⟩,[r283,r284,r285,r90,r286,r287,r288,r289]),(⟨0,2,4⟩,[0,r11,r131,r290,r291,r221,r292]),(⟨0,3,0⟩,[0,r48,r205,r206,r207,r208,r209,r210,r211,r212]),(⟨0,3,1⟩,[r245,r11,r253,r254,r255,r256,r257,r258,r259]),(⟨0,3,2⟩,[r283,r284,r285,r90,r286,r287,r288,r289]),(⟨0,3,3⟩,[r117,r293,r294,r295,r296,r297,r298]),(⟨0,3,4⟩,[r74,r299,r300,r301,r302,r303]),(⟨0,3,5⟩,[r74,r55,r274,r275,64]),(⟨0,4,0⟩,[0,r0,r213,r214,r215,r216,r217,r218,r219]),(⟨0,4,1⟩,[r186,r260,r261,r262,r263,r264,r265,r266]),(⟨0,4,2⟩,[0,r11,r131,r290,r291,r221,r292]),(⟨0,4,3⟩,[r74,r299,r300,r301,r302,r303]),(⟨0,5,0⟩,[0,r220,r221,r222,r223,r224,r225,r226]),(⟨0,5,1⟩,[r186,r267,r268,r269,r270,r271,-672]),(⟨0,5,3⟩,[r74,r55,r274,r275,64]),(⟨0,6,0⟩,[0,r21,r227,r228,r229,r230,64]),(⟨0,6,1⟩,[r74,r272,r63,r31,r273,-64]),(⟨0,7,0⟩,[0,r11,r231,r232,r233,r234]),(⟨0,7,1⟩,[r74,r55,r274,r275,64]),(⟨1,0,0⟩,[0,r186,r187,r188,r189,r190,-17408,r191,r192,r193,r194,r195]),(⟨1,0,1⟩,[0,r235,r236,r237,r238,r239,r240,r241,r242,r243,r244]),(⟨1,0,2⟩,[r245,r246,r247,r159,r248,r249,-2528,r250,r251,r252]),(⟨1,0,3⟩,[r245,r11,r253,r254,r255,r256,r257,r258,r259]),(⟨1,0,4⟩,[r186,r260,r261,r262,r263,r264,r265,r266]),(⟨1,0,5⟩,[r186,r267,r268,r269,r270,r271,-672]),(⟨1,0,6⟩,[r74,r272,r63,r31,r273,-64]),(⟨1,0,7⟩,[r74,r55,r274,r275,64]),(⟨1,1,0⟩,[0,r235,r236,r237,r238,r239,r240,r241,r242,r243,r244]),(⟨1,1,1⟩,[r220,r285,r56,r304,r305,r306,r307,r308,r309,-3360]),(⟨1,1,2⟩,[r245,r64,r310,r1,r311,r312,r313,r314,1568]),(⟨1,1,3⟩,[r129,r315,r316,r317,r318,r319,r320,768]),(⟨1,1,4⟩,[r117,r118,r321,r322,r75,r323,-448]),(⟨1,2,0⟩,[r245,r246,r247,r159,r248,r249,-2528,r250,r251,r252]),(⟨1,2,1⟩,[r245,r64,r310,r1,r311,r312,r313,r314,1568]),(⟨1,2,3⟩,[r283,r324,r325,r104,r260,r326,-224]),(⟨1,3,0⟩,[r245,r11,r253,r254,r255,r256,r257,r258,r259]),(⟨1,3,1⟩,[r129,r315,r316,r317,r318,r319,r320,768]),(⟨1,3,2⟩,[r283,r324,r325,r104,r260,r326,-224]),(⟨1,3,3⟩,[r102,r103,r104,r105,r106,-128]),(⟨1,3,4⟩,[r74,r55,r274,r275,64]),(⟨1,4,0⟩,[r186,r260,r261,r262,r263,r264,r265,r266]),(⟨1,4,1⟩,[r117,r118,r321,r322,r75,r323,-448]),(⟨1,4,3⟩,[r74,r55,r274,r275,64]),(⟨1,5,0⟩,[r186,r267,r268,r269,r270,r271,-672]),(⟨1,6,0⟩,[r74,r272,r63,r31,r273,-64]),(⟨1,7,0⟩,[r74,r55,r274,r275,64]),(⟨2,0,0⟩,[0,r11,r196,r197,r198,r199,r200,r201,r202,r203,r204]),(⟨2,0,1⟩,[r245,r246,r247,r159,r248,r249,-2528,r250,r251,r252]),(⟨2,0,2⟩,[0,r48,r276,r277,r278,r279,r280,r281,r282]),(⟨2,0,3⟩,[r283,r284,r285,r90,r286,r287,r288,r289]),(⟨2,0,4⟩,[0,r11,r131,r290,r291,r221,r292]),(⟨2,1,0⟩,[r245,r246,r247,r159,r248,r249,-2528,r250,r251,r252]),(⟨2,1,1⟩,[r245,r64,r310,r1,r311,r312,r313,r314,1568]),(⟨2,1,3⟩,[r283,r324,r325,r104,r260,r326,-224]),(⟨2,2,0⟩,[0,r48,r276,r277,r278,r279,r280,r281,r282]),(⟨2,3,0⟩,[r283,r284,r285,r90,r286,r287,r288,r289]),(⟨2,3,1⟩,[r283,r324,r325,r104,r260,r326,-224]),(⟨2,4,0⟩,[0,r11,r131,r290,r291,r221,r292]),(⟨3,0,0⟩,[0,r48,r205,r206,r207,r208,r209,r210,r211,r212]),(⟨3,0,1⟩,[r245,r11,r253,r254,r255,r256,r257,r258,r259]),(⟨3,0,2⟩,[r283,r284,r285,r90,r286,r287,r288,r289]),(⟨3,0,3⟩,[r117,r293,r294,r295,r296,r297,r298]),(⟨3,0,4⟩,[r74,r299,r300,r301,r302,r303]),(⟨3,0,5⟩,[r74,r55,r274,r275,64]),(⟨3,1,0⟩,[r245,r11,r253,r254,r255,r256,r257,r258,r259]),(⟨3,1,1⟩,[r129,r315,r316,r317,r318,r319,r320,768]),(⟨3,1,2⟩,[r283,r324,r325,r104,r260,r326,-224]),(⟨3,1,3⟩,[r102,r103,r104,r105,r106,-128]),(⟨3,1,4⟩,[r74,r55,r274,r275,64]),(⟨3,2,0⟩,[r283,r284,r285,r90,r286,r287,r288,r289]),(⟨3,2,1⟩,[r283,r324,r325,r104,r260,r326,-224]),(⟨3,3,0⟩,[r117,r293,r294,r295,r296,r297,r298]),(⟨3,3,1⟩,[r102,r103,r104,r105,r106,-128]),(⟨3,4,0⟩,[r74,r299,r300,r301,r302,r303]),(⟨3,4,1⟩,[r74,r55,r274,r275,64]),(⟨3,5,0⟩,[r74,r55,r274,r275,64]),(⟨4,0,0⟩,[0,r0,r213,r214,r215,r216,r217,r218,r219]),(⟨4,0,1⟩,[r186,r260,r261,r262,r263,r264,r265,r266]),(⟨4,0,2⟩,[0,r11,r131,r290,r291,r221,r292]),(⟨4,0,3⟩,[r74,r299,r300,r301,r302,r303]),(⟨4,1,0⟩,[r186,r260,r261,r262,r263,r264,r265,r266]),(⟨4,1,1⟩,[r117,r118,r321,r322,r75,r323,-448]),(⟨4,1,3⟩,[r74,r55,r274,r275,64]),(⟨4,2,0⟩,[0,r11,r131,r290,r291,r221,r292]),(⟨4,3,0⟩,[r74,r299,r300,r301,r302,r303]),(⟨4,3,1⟩,[r74,r55,r274,r275,64]),(⟨5,0,0⟩,[0,r220,r221,r222,r223,r224,r225,r226]),(⟨5,0,1⟩,[r186,r267,r268,r269,r270,r271,-672]),(⟨5,0,3⟩,[r74,r55,r274,r275,64]),(⟨5,1,0⟩,[r186,r267,r268,r269,r270,r271,-672]),(⟨5,3,0⟩,[r74,r55,r274,r275,64]),(⟨6,0,0⟩,[0,r21,r227,r228,r229,r230,64]),(⟨6,0,1⟩,[r74,r272,r63,r31,r273,-64]),(⟨6,1,0⟩,[r74,r272,r63,r31,r273,-64]),(⟨7,0,0⟩,[0,r11,r231,r232,r233,r234]),(⟨7,0,1⟩,[r74,r55,r274,r275,64]),(⟨7,1,0⟩,[r74,r55,r274,r275,64])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,3,-12,9,6]),(⟨0,0,1⟩,[-1,5,-9,5]),(⟨0,0,2⟩,[-1,4,-7]),(⟨0,0,3⟩,[2,-2]),(⟨0,0,4⟩,[2]),(⟨0,1,0⟩,[-1,5,-9,5]),(⟨0,2,0⟩,[-1,4,-7]),(⟨0,3,0⟩,[2,-2]),(⟨0,4,0⟩,[2]),(⟨1,0,0⟩,[-1,5,-9,5]),(⟨2,0,0⟩,[-1,4,-7]),(⟨3,0,0⟩,[2,-2]),(⟨4,0,0⟩,[2])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[0,-384,8064,-64256,246656,-476544,385152,5632,-79744]),(⟨0,0,1⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨0,0,2⟩,[0,384,-6400,33024,-52224,4480,12544]),(⟨0,0,3⟩,[0,384,-6656,34048,-49664,-2688]),(⟨0,1,0⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨0,1,1⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨0,1,3⟩,[-128,1536,-3840,-4608,15232]),(⟨0,2,0⟩,[0,384,-6400,33024,-52224,4480,12544]),(⟨0,3,0⟩,[0,384,-6656,34048,-49664,-2688]),(⟨0,3,1⟩,[-128,1536,-3840,-4608,15232]),(⟨1,0,0⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨1,0,1⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨1,0,3⟩,[-128,1536,-3840,-4608,15232]),(⟨1,1,0⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨1,3,0⟩,[-128,1536,-3840,-4608,15232]),(⟨2,0,0⟩,[0,384,-6400,33024,-52224,4480,12544]),(⟨3,0,0⟩,[0,384,-6656,34048,-49664,-2688]),(⟨3,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨3,1,0⟩,[-128,1536,-3840,-4608,15232])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 0 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r327) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 4 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r328) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨4,0,0⟩,[2])]

noncomputable def partial12 : Poly := [(⟨4,0,0⟩,[0,-768,16128,-128512,493312,-953088,770304,11264,-159488]),(⟨4,0,1⟩,[0,-768,14336,-96768,310272,-482048,254976,114688]),(⟨4,0,2⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨4,0,3⟩,[0,768,-13312,68096,-99328,-5376]),(⟨4,1,0⟩,[0,-768,14336,-96768,310272,-482048,254976,114688]),(⟨4,1,1⟩,[256,-3584,15616,-27648,4864,125440,-213248]),(⟨4,1,3⟩,[-256,3072,-7680,-9216,30464]),(⟨4,2,0⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨4,3,0⟩,[0,768,-13312,68096,-99328,-5376]),(⟨4,3,1⟩,[-256,3072,-7680,-9216,30464]),(⟨5,0,0⟩,[0,-768,14336,-96768,310272,-482048,254976,114688]),(⟨5,0,1⟩,[256,-3584,15616,-27648,4864,125440,-213248]),(⟨5,0,3⟩,[-256,3072,-7680,-9216,30464]),(⟨5,1,0⟩,[256,-3584,15616,-27648,4864,125440,-213248]),(⟨5,3,0⟩,[-256,3072,-7680,-9216,30464]),(⟨6,0,0⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨7,0,0⟩,[0,768,-13312,68096,-99328,-5376]),(⟨7,0,1⟩,[-256,3072,-7680,-9216,30464]),(⟨7,1,0⟩,[-256,3072,-7680,-9216,30464])]


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

noncomputable def partial8 : Poly := [(⟨0,4,0⟩,[0,-768,16128,-128512,493312,-953088,770304,11264,-159488]),(⟨0,4,1⟩,[0,-768,14336,-96768,310272,-482048,254976,114688]),(⟨0,4,2⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨0,4,3⟩,[0,768,-13312,68096,-99328,-5376]),(⟨0,5,0⟩,[0,-768,14336,-96768,310272,-482048,254976,114688]),(⟨0,5,1⟩,[256,-3584,15616,-27648,4864,125440,-213248]),(⟨0,5,3⟩,[-256,3072,-7680,-9216,30464]),(⟨0,6,0⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨0,7,0⟩,[0,768,-13312,68096,-99328,-5376]),(⟨0,7,1⟩,[-256,3072,-7680,-9216,30464]),(⟨1,0,0⟩,[0,384,-9984,108032,-642432,2328448,-5309056,7442304,-5741184,1476352,745856,-398720]),(⟨1,0,1⟩,[0,384,-9088,87680,-463488,1488000,-2970752,3524992,-2065792,121344,286720]),(⟨1,0,2⟩,[0,-384,8320,-68480,276864,-594816,644992,-238720,-90496,62720]),(⟨1,0,3⟩,[0,-384,8576,-70784,281728,-585344,603776,-224128,-13440]),(⟨1,1,0⟩,[0,384,-9088,87680,-463488,1488000,-2970752,3524992,-2065792,121344,286720]),(⟨1,1,1⟩,[-128,2432,-17920,69632,-150784,112896,329216,-1085440,1273216,-533120]),(⟨1,1,3⟩,[128,-2176,12672,-29056,3968,98432,-160128,76160]),(⟨1,2,0⟩,[0,-384,8320,-68480,276864,-594816,644992,-238720,-90496,62720]),(⟨1,3,0⟩,[0,-384,8576,-70784,281728,-585344,603776,-224128,-13440]),(⟨1,3,1⟩,[128,-2176,12672,-29056,3968,98432,-160128,76160]),(⟨1,4,0⟩,[0,-768,14336,-96768,310272,-482048,254976,114688]),(⟨1,4,1⟩,[256,-3584,15616,-27648,4864,125440,-213248]),(⟨1,4,3⟩,[-256,3072,-7680,-9216,30464]),(⟨1,5,0⟩,[256,-3584,15616,-27648,4864,125440,-213248]),(⟨1,7,0⟩,[-256,3072,-7680,-9216,30464]),(⟨2,0,0⟩,[0,768,-18688,186880,-1023616,3400960,-6988672,8395776,-4659584,-237056,844928]),(⟨2,0,1⟩,[-128,2816,-26624,149376,-549632,1313152,-1848320,1054336,610176,-934528]),(⟨2,0,2⟩,[0,-384,7936,-61312,229120,-444544,370944,18816,-87808]),(⟨2,0,3⟩,[128,-2560,20864,-92416,236416,-335872,176768,94976]),(⟨2,1,0⟩,[-128,2816,-26624,149376,-549632,1313152,-1848320,1054336,610176,-934528]),(⟨2,1,1⟩,[-128,2304,-15872,57600,-112384,43776,340480,-865536,746368]),(⟨2,1,3⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨2,2,0⟩,[0,-384,7936,-61312,229120,-444544,370944,18816,-87808]),(⟨2,3,0⟩,[128,-2560,20864,-92416,236416,-335872,176768,94976]),(⟨2,3,1⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨2,4,0⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨3,0,0⟩,[0,-768,16512,-133376,499840,-840960,190848,1142016,-924288,-179200]),(⟨3,0,1⟩,[-128,1536,-768,-53504,294656,-748544,1077504,-1005824,631680]),(⟨3,0,2⟩,[0,768,-13568,78848,-170496,113408,16128,-25088]),(⟨3,0,3⟩,[128,-1280,-3200,59904,-174208,187136,-101248]),(⟨3,1,0⟩,[-128,1536,-768,-53504,294656,-748544,1077504,-1005824,631680]),(⟨3,1,1⟩,[256,-3840,19200,-43264,32512,120576,-338688,213248]),(⟨3,1,3⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨3,2,0⟩,[0,768,-13568,78848,-170496,113408,16128,-25088]),(⟨3,3,0⟩,[128,-1280,-3200,59904,-174208,187136,-101248]),(⟨3,3,1⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨3,4,0⟩,[0,768,-13312,68096,-99328,-5376]),(⟨3,4,1⟩,[-256,3072,-7680,-9216,30464]),(⟨3,5,0⟩,[-256,3072,-7680,-9216,30464]),(⟨4,0,0⟩,[0,-2304,47744,-371712,1411200,-2775296,2482048,-334336,-375424]),(⟨4,0,1⟩,[384,-6784,46208,-169088,346752,-263040,-243840,404096]),(⟨4,0,2⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨4,0,3⟩,[-256,4096,-24064,66560,-59648,-35840]),(⟨4,1,0⟩,[384,-6784,46208,-169088,346752,-263040,-243840,404096]),(⟨4,1,1⟩,[256,-3584,15616,-27648,4864,125440,-213248]),(⟨4,1,3⟩,[-256,3072,-7680,-9216,30464]),(⟨4,2,0⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨4,3,0⟩,[-256,4096,-24064,66560,-59648,-35840]),(⟨4,3,1⟩,[-256,3072,-7680,-9216,30464]),(⟨5,0,0⟩,[0,-384,8960,-81280,372224,-802944,608000,108416]),(⟨5,0,1⟩,[384,-5632,26496,-49152,-1920,218624,-319872]),(⟨5,0,3⟩,[-256,3072,-7680,-9216,30464]),(⟨5,1,0⟩,[384,-5632,26496,-49152,-1920,218624,-319872]),(⟨5,3,0⟩,[-256,3072,-7680,-9216,30464]),(⟨6,0,0⟩,[0,1536,-26880,147456,-271872,102912,30464]),(⟨6,0,1⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨6,1,0⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨7,0,0⟩,[0,768,-13312,68096,-99328,-5376]),(⟨7,0,1⟩,[-256,3072,-7680,-9216,30464]),(⟨7,1,0⟩,[-256,3072,-7680,-9216,30464])]


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

noncomputable def partial4 : Poly := [(⟨0,0,4⟩,[0,-768,16128,-128512,493312,-953088,770304,11264,-159488]),(⟨0,0,5⟩,[0,-768,14336,-96768,310272,-482048,254976,114688]),(⟨0,0,6⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨0,0,7⟩,[0,768,-13312,68096,-99328,-5376]),(⟨0,1,0⟩,[0,384,-9984,108032,-642432,2328448,-5309056,7442304,-5741184,1476352,745856,-398720]),(⟨0,1,1⟩,[0,384,-9088,87680,-463488,1488000,-2970752,3524992,-2065792,121344,286720]),(⟨0,1,2⟩,[0,-384,8320,-68480,276864,-594816,644992,-238720,-90496,62720]),(⟨0,1,3⟩,[0,-384,8576,-70784,281728,-585344,603776,-224128,-13440]),(⟨0,1,4⟩,[0,-768,14336,-96768,310272,-482048,254976,114688]),(⟨0,1,5⟩,[256,-3584,15616,-27648,4864,125440,-213248]),(⟨0,1,7⟩,[-256,3072,-7680,-9216,30464]),(⟨0,2,0⟩,[0,768,-18688,186880,-1023616,3400960,-6988672,8395776,-4659584,-237056,844928]),(⟨0,2,1⟩,[-128,2816,-26624,149376,-549632,1313152,-1848320,1054336,610176,-934528]),(⟨0,2,2⟩,[0,-384,7936,-61312,229120,-444544,370944,18816,-87808]),(⟨0,2,3⟩,[128,-2560,20864,-92416,236416,-335872,176768,94976]),(⟨0,2,4⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨0,3,0⟩,[0,-768,16512,-133376,499840,-840960,190848,1142016,-924288,-179200]),(⟨0,3,1⟩,[-128,1536,-768,-53504,294656,-748544,1077504,-1005824,631680]),(⟨0,3,2⟩,[0,768,-13568,78848,-170496,113408,16128,-25088]),(⟨0,3,3⟩,[128,-1280,-3200,59904,-174208,187136,-101248]),(⟨0,3,4⟩,[0,768,-13312,68096,-99328,-5376]),(⟨0,3,5⟩,[-256,3072,-7680,-9216,30464]),(⟨0,4,0⟩,[0,-2304,47744,-371712,1411200,-2775296,2482048,-334336,-375424]),(⟨0,4,1⟩,[384,-6784,46208,-169088,346752,-263040,-243840,404096]),(⟨0,4,2⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨0,4,3⟩,[-256,4096,-24064,66560,-59648,-35840]),(⟨0,5,0⟩,[0,-384,8960,-81280,372224,-802944,608000,108416]),(⟨0,5,1⟩,[384,-5632,26496,-49152,-1920,218624,-319872]),(⟨0,5,3⟩,[-256,3072,-7680,-9216,30464]),(⟨0,6,0⟩,[0,1536,-26880,147456,-271872,102912,30464]),(⟨0,6,1⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨0,7,0⟩,[0,768,-13312,68096,-99328,-5376]),(⟨0,7,1⟩,[-256,3072,-7680,-9216,30464]),(⟨1,0,0⟩,[0,384,-9984,108032,-642432,2328448,-5309056,7442304,-5741184,1476352,745856,-398720]),(⟨1,0,1⟩,[0,384,-9088,87680,-463488,1488000,-2970752,3524992,-2065792,121344,286720]),(⟨1,0,2⟩,[0,-384,8320,-68480,276864,-594816,644992,-238720,-90496,62720]),(⟨1,0,3⟩,[0,-384,8576,-70784,281728,-585344,603776,-224128,-13440]),(⟨1,0,4⟩,[0,-768,14336,-96768,310272,-482048,254976,114688]),(⟨1,0,5⟩,[256,-3584,15616,-27648,4864,125440,-213248]),(⟨1,0,7⟩,[-256,3072,-7680,-9216,30464]),(⟨1,1,0⟩,[0,768,-18176,175360,-926976,2976000,-5941504,7049984,-4131584,242688,573440]),(⟨1,1,1⟩,[-256,4864,-35840,139264,-301568,225792,658432,-2170880,2546432,-1066240]),(⟨1,1,3⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨1,1,4⟩,[256,-3584,15616,-27648,4864,125440,-213248]),(⟨1,2,0⟩,[-128,2432,-18304,80896,-272768,718336,-1203328,815616,519680,-871808]),(⟨1,2,1⟩,[-128,2304,-15872,57600,-112384,43776,340480,-865536,746368]),(⟨1,2,3⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨1,3,0⟩,[-128,1152,7808,-124288,576384,-1333888,1681280,-1229952,618240]),(⟨1,3,1⟩,[384,-6016,31872,-72320,36480,219008,-498816,289408]),(⟨1,3,3⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨1,3,4⟩,[-256,3072,-7680,-9216,30464]),(⟨1,4,0⟩,[384,-6784,46208,-169088,346752,-263040,-243840,404096]),(⟨1,4,1⟩,[256,-3584,15616,-27648,4864,125440,-213248]),(⟨1,4,3⟩,[-256,3072,-7680,-9216,30464]),(⟨1,5,0⟩,[384,-5632,26496,-49152,-1920,218624,-319872]),(⟨1,6,0⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨1,7,0⟩,[-256,3072,-7680,-9216,30464]),(⟨2,0,0⟩,[0,768,-18688,186880,-1023616,3400960,-6988672,8395776,-4659584,-237056,844928]),(⟨2,0,1⟩,[-128,2816,-26624,149376,-549632,1313152,-1848320,1054336,610176,-934528]),(⟨2,0,2⟩,[0,-384,7936,-61312,229120,-444544,370944,18816,-87808]),(⟨2,0,3⟩,[128,-2560,20864,-92416,236416,-335872,176768,94976]),(⟨2,0,4⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨2,1,0⟩,[-128,2432,-18304,80896,-272768,718336,-1203328,815616,519680,-871808]),(⟨2,1,1⟩,[-128,2304,-15872,57600,-112384,43776,340480,-865536,746368]),(⟨2,1,3⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨2,2,0⟩,[0,-768,15872,-122624,458240,-889088,741888,37632,-175616]),(⟨2,3,0⟩,[128,-1792,7296,-13568,65920,-222464,192896,69888]),(⟨2,3,1⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨2,4,0⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨3,0,0⟩,[0,-768,16512,-133376,499840,-840960,190848,1142016,-924288,-179200]),(⟨3,0,1⟩,[-128,1536,-768,-53504,294656,-748544,1077504,-1005824,631680]),(⟨3,0,2⟩,[0,768,-13568,78848,-170496,113408,16128,-25088]),(⟨3,0,3⟩,[128,-1280,-3200,59904,-174208,187136,-101248]),(⟨3,0,4⟩,[0,768,-13312,68096,-99328,-5376]),(⟨3,0,5⟩,[-256,3072,-7680,-9216,30464]),(⟨3,1,0⟩,[-128,1152,7808,-124288,576384,-1333888,1681280,-1229952,618240]),(⟨3,1,1⟩,[384,-6016,31872,-72320,36480,219008,-498816,289408]),(⟨3,1,3⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨3,1,4⟩,[-256,3072,-7680,-9216,30464]),(⟨3,2,0⟩,[128,-1792,7296,-13568,65920,-222464,192896,69888]),(⟨3,2,1⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨3,3,0⟩,[256,-2560,-6400,119808,-348416,374272,-202496]),(⟨3,3,1⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨3,4,0⟩,[-256,4096,-24064,66560,-59648,-35840]),(⟨3,4,1⟩,[-256,3072,-7680,-9216,30464]),(⟨3,5,0⟩,[-256,3072,-7680,-9216,30464]),(⟨4,0,0⟩,[0,-2304,47744,-371712,1411200,-2775296,2482048,-334336,-375424]),(⟨4,0,1⟩,[384,-6784,46208,-169088,346752,-263040,-243840,404096]),(⟨4,0,2⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨4,0,3⟩,[-256,4096,-24064,66560,-59648,-35840]),(⟨4,1,0⟩,[384,-6784,46208,-169088,346752,-263040,-243840,404096]),(⟨4,1,1⟩,[256,-3584,15616,-27648,4864,125440,-213248]),(⟨4,1,3⟩,[-256,3072,-7680,-9216,30464]),(⟨4,2,0⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨4,3,0⟩,[-256,4096,-24064,66560,-59648,-35840]),(⟨4,3,1⟩,[-256,3072,-7680,-9216,30464]),(⟨5,0,0⟩,[0,-384,8960,-81280,372224,-802944,608000,108416]),(⟨5,0,1⟩,[384,-5632,26496,-49152,-1920,218624,-319872]),(⟨5,0,3⟩,[-256,3072,-7680,-9216,30464]),(⟨5,1,0⟩,[384,-5632,26496,-49152,-1920,218624,-319872]),(⟨5,3,0⟩,[-256,3072,-7680,-9216,30464]),(⟨6,0,0⟩,[0,1536,-26880,147456,-271872,102912,30464]),(⟨6,0,1⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨6,1,0⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨7,0,0⟩,[0,768,-13312,68096,-99328,-5376]),(⟨7,0,1⟩,[-256,3072,-7680,-9216,30464]),(⟨7,1,0⟩,[-256,3072,-7680,-9216,30464])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,0,-1152,28800,-292992,1581312,-4919424,8708352,-7413888,300288,3318528,-683904,-478464]),(⟨0,0,1⟩,[0,384,-11136,134144,-877056,3436672,-8286208,11822976,-8337408,489472,2026880,-54656]),(⟨0,0,2⟩,[0,768,-17536,163072,-844288,2792704,-6089728,8107776,-5083136,-97280,920192]),(⟨0,0,3⟩,[0,-768,17664,-157952,685312,-1456128,1045248,931584,-1246464,-195328]),(⟨0,0,4⟩,[0,-2304,47744,-371712,1411200,-2775296,2482048,-334336,-375424]),(⟨0,0,5⟩,[0,-384,8960,-81280,372224,-802944,608000,108416]),(⟨0,0,6⟩,[0,1536,-26880,147456,-271872,102912,30464]),(⟨0,0,7⟩,[0,768,-13312,68096,-99328,-5376]),(⟨0,1,0⟩,[0,384,-11136,134144,-877056,3436672,-8286208,11822976,-8337408,489472,2026880,-54656]),(⟨0,1,1⟩,[0,1152,-25088,221440,-1077504,3208704,-5860096,5916416,-2273024,-340608,-66304]),(⟨0,1,2⟩,[-128,2432,-18304,80896,-272768,718336,-1203328,815616,519680,-871808]),(⟨0,1,3⟩,[-128,768,13952,-155392,621696,-1258240,1433984,-1120512,709632]),(⟨0,1,4⟩,[384,-6784,46208,-169088,346752,-263040,-243840,404096]),(⟨0,1,5⟩,[384,-5632,26496,-49152,-1920,218624,-319872]),(⟨0,1,6⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨0,1,7⟩,[-256,3072,-7680,-9216,30464]),(⟨0,2,0⟩,[0,768,-17536,163072,-844288,2792704,-6089728,8107776,-5083136,-97280,920192]),(⟨0,2,1⟩,[-128,2432,-18304,80896,-272768,718336,-1203328,815616,519680,-871808]),(⟨0,2,2⟩,[0,-768,15872,-122624,458240,-889088,741888,37632,-175616]),(⟨0,2,3⟩,[128,-1792,7296,-13568,65920,-222464,192896,69888]),(⟨0,2,4⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨0,3,0⟩,[0,-768,17664,-157952,685312,-1456128,1045248,931584,-1246464,-195328]),(⟨0,3,1⟩,[-128,768,13952,-155392,621696,-1258240,1433984,-1120512,709632]),(⟨0,3,2⟩,[128,-1792,7296,-13568,65920,-222464,192896,69888]),(⟨0,3,3⟩,[256,-2560,-6400,119808,-348416,374272,-202496]),(⟨0,3,4⟩,[-256,4096,-24064,66560,-59648,-35840]),(⟨0,3,5⟩,[-256,3072,-7680,-9216,30464]),(⟨0,4,0⟩,[0,-2304,47744,-371712,1411200,-2775296,2482048,-334336,-375424]),(⟨0,4,1⟩,[384,-6784,46208,-169088,346752,-263040,-243840,404096]),(⟨0,4,2⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨0,4,3⟩,[-256,4096,-24064,66560,-59648,-35840]),(⟨0,5,0⟩,[0,-384,8960,-81280,372224,-802944,608000,108416]),(⟨0,5,1⟩,[384,-5632,26496,-49152,-1920,218624,-319872]),(⟨0,5,3⟩,[-256,3072,-7680,-9216,30464]),(⟨0,6,0⟩,[0,1536,-26880,147456,-271872,102912,30464]),(⟨0,6,1⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨0,7,0⟩,[0,768,-13312,68096,-99328,-5376]),(⟨0,7,1⟩,[-256,3072,-7680,-9216,30464]),(⟨1,0,0⟩,[0,384,-11136,134144,-877056,3436672,-8286208,11822976,-8337408,489472,2026880,-54656]),(⟨1,0,1⟩,[0,1152,-25088,221440,-1077504,3208704,-5860096,5916416,-2273024,-340608,-66304]),(⟨1,0,2⟩,[-128,2432,-18304,80896,-272768,718336,-1203328,815616,519680,-871808]),(⟨1,0,3⟩,[-128,768,13952,-155392,621696,-1258240,1433984,-1120512,709632]),(⟨1,0,4⟩,[384,-6784,46208,-169088,346752,-263040,-243840,404096]),(⟨1,0,5⟩,[384,-5632,26496,-49152,-1920,218624,-319872]),(⟨1,0,6⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨1,0,7⟩,[-256,3072,-7680,-9216,30464]),(⟨1,1,0⟩,[0,1152,-25088,221440,-1077504,3208704,-5860096,5916416,-2273024,-340608,-66304]),(⟨1,1,1⟩,[-384,7296,-53760,208896,-452352,338688,987648,-3256320,3819648,-1599360]),(⟨1,1,2⟩,[-128,2304,-15872,57600,-112384,43776,340480,-865536,746368]),(⟨1,1,3⟩,[512,-8192,44544,-101376,40448,317440,-658944,365568]),(⟨1,1,4⟩,[256,-3584,15616,-27648,4864,125440,-213248]),(⟨1,2,0⟩,[-128,2432,-18304,80896,-272768,718336,-1203328,815616,519680,-871808]),(⟨1,2,1⟩,[-128,2304,-15872,57600,-112384,43776,340480,-865536,746368]),(⟨1,2,3⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨1,3,0⟩,[-128,768,13952,-155392,621696,-1258240,1433984,-1120512,709632]),(⟨1,3,1⟩,[512,-8192,44544,-101376,40448,317440,-658944,365568]),(⟨1,3,2⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨1,3,3⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨1,3,4⟩,[-256,3072,-7680,-9216,30464]),(⟨1,4,0⟩,[384,-6784,46208,-169088,346752,-263040,-243840,404096]),(⟨1,4,1⟩,[256,-3584,15616,-27648,4864,125440,-213248]),(⟨1,4,3⟩,[-256,3072,-7680,-9216,30464]),(⟨1,5,0⟩,[384,-5632,26496,-49152,-1920,218624,-319872]),(⟨1,6,0⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨1,7,0⟩,[-256,3072,-7680,-9216,30464]),(⟨2,0,0⟩,[0,768,-17536,163072,-844288,2792704,-6089728,8107776,-5083136,-97280,920192]),(⟨2,0,1⟩,[-128,2432,-18304,80896,-272768,718336,-1203328,815616,519680,-871808]),(⟨2,0,2⟩,[0,-768,15872,-122624,458240,-889088,741888,37632,-175616]),(⟨2,0,3⟩,[128,-1792,7296,-13568,65920,-222464,192896,69888]),(⟨2,0,4⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨2,1,0⟩,[-128,2432,-18304,80896,-272768,718336,-1203328,815616,519680,-871808]),(⟨2,1,1⟩,[-128,2304,-15872,57600,-112384,43776,340480,-865536,746368]),(⟨2,1,3⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨2,2,0⟩,[0,-768,15872,-122624,458240,-889088,741888,37632,-175616]),(⟨2,3,0⟩,[128,-1792,7296,-13568,65920,-222464,192896,69888]),(⟨2,3,1⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨2,4,0⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨3,0,0⟩,[0,-768,17664,-157952,685312,-1456128,1045248,931584,-1246464,-195328]),(⟨3,0,1⟩,[-128,768,13952,-155392,621696,-1258240,1433984,-1120512,709632]),(⟨3,0,2⟩,[128,-1792,7296,-13568,65920,-222464,192896,69888]),(⟨3,0,3⟩,[256,-2560,-6400,119808,-348416,374272,-202496]),(⟨3,0,4⟩,[-256,4096,-24064,66560,-59648,-35840]),(⟨3,0,5⟩,[-256,3072,-7680,-9216,30464]),(⟨3,1,0⟩,[-128,768,13952,-155392,621696,-1258240,1433984,-1120512,709632]),(⟨3,1,1⟩,[512,-8192,44544,-101376,40448,317440,-658944,365568]),(⟨3,1,2⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨3,1,3⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨3,1,4⟩,[-256,3072,-7680,-9216,30464]),(⟨3,2,0⟩,[128,-1792,7296,-13568,65920,-222464,192896,69888]),(⟨3,2,1⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨3,3,0⟩,[256,-2560,-6400,119808,-348416,374272,-202496]),(⟨3,3,1⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨3,4,0⟩,[-256,4096,-24064,66560,-59648,-35840]),(⟨3,4,1⟩,[-256,3072,-7680,-9216,30464]),(⟨3,5,0⟩,[-256,3072,-7680,-9216,30464]),(⟨4,0,0⟩,[0,-2304,47744,-371712,1411200,-2775296,2482048,-334336,-375424]),(⟨4,0,1⟩,[384,-6784,46208,-169088,346752,-263040,-243840,404096]),(⟨4,0,2⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨4,0,3⟩,[-256,4096,-24064,66560,-59648,-35840]),(⟨4,1,0⟩,[384,-6784,46208,-169088,346752,-263040,-243840,404096]),(⟨4,1,1⟩,[256,-3584,15616,-27648,4864,125440,-213248]),(⟨4,1,3⟩,[-256,3072,-7680,-9216,30464]),(⟨4,2,0⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨4,3,0⟩,[-256,4096,-24064,66560,-59648,-35840]),(⟨4,3,1⟩,[-256,3072,-7680,-9216,30464]),(⟨5,0,0⟩,[0,-384,8960,-81280,372224,-802944,608000,108416]),(⟨5,0,1⟩,[384,-5632,26496,-49152,-1920,218624,-319872]),(⟨5,0,3⟩,[-256,3072,-7680,-9216,30464]),(⟨5,1,0⟩,[384,-5632,26496,-49152,-1920,218624,-319872]),(⟨5,3,0⟩,[-256,3072,-7680,-9216,30464]),(⟨6,0,0⟩,[0,1536,-26880,147456,-271872,102912,30464]),(⟨6,0,1⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨6,1,0⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨7,0,0⟩,[0,768,-13312,68096,-99328,-5376]),(⟨7,0,1⟩,[-256,3072,-7680,-9216,30464]),(⟨7,1,0⟩,[-256,3072,-7680,-9216,30464])]


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
    (Poly.add (Poly.scale (K.ofRat r329) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 0 4).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r327*r328 : ℚ)=r329 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 0 4 r327 r328 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 0=4 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 0 4).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C049

#print axioms Coulomb8.Columns.C049.sound
