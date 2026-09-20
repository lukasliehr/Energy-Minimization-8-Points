import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C065

def r0 : ℚ := { num := -192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 4512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -43392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 219936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -83136, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 294912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 507072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -837120, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 4046976, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -32386848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 18120768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -69408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -4159872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := 136320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -1600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 17344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -106688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 393024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := -737600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -397696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 6854208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -21599936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 38648832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -42200384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 25292672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -694336, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := -210560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := 32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 6304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -4992, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 140512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -358208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 263808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 228544, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -6775648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 13822208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := -16697376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := 11238464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -487008, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 768, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -44928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 27264, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -21888, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -293120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 3870336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -11361664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 18281600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -2356992, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 6733568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -15616, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 192, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 19776, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -295552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -66112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 2288256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -6995648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 11398400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := -10480768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := 648576, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -5568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 33280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -75968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := -35328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := 683456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := -1973504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 2885056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -2043968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := 35072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -3648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 26560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -74560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 9344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := 31552, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := -1716928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := 148032, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := -239840, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := 256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := -896, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -3200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 47232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -116736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 9344, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -3456, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 1280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -6336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := 2560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 43072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -131840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := 25920, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := 20032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := -120576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 419392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -104192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -360320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 5778176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -17010752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 28483584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -29303488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 2544640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := -771008, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := 64, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -5760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 4160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 10752, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 864000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -932032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -276160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 322432, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -426112, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 217728, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -30336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 136256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -283648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := -88384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := 2281088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := -403776, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := 11002240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := -1422720, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := 614656, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := -6400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := 38912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -17152, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 26880, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := 44288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := -799744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := 202496, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := -1472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := 1664, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := -39616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 35200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := 25408, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := -723584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := 171072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := -123200, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := 512, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := -15616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := 27648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := -4864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := -17920, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := 3840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := -2304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := 6144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 100864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -46848, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 551168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := -366080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 6912, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := 192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -3008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 13824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -8384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := -14464, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 372160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -715776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 843712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -489280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := -3840, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := 2240, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := -1280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := -34624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := 88064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := -14272, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := 41856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := -6912, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := 178688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -5632, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := -2816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 12480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -15360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := -24000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := 81664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := 1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := -3840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -4608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := -128, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := 2432, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := -5504, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -4096, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := 92544, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -1810560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 2438272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -218048, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 1664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := -768, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 19840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := 128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := -12800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := 19072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := -7168, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := 16128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 7296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := -54144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 216576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -72960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := 558336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := 567552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := -3110400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := 745344, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := -690816, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := -19200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := 43264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := -32512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := 48384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := 3328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := -1536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := 39680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := -5632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := 24960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := -30720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := -48000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := 163328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 2256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -21696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 109968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -41568, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 147456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := 253536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := -418560, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := 2023488, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := -16193424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := 9060384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := -34704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -2079936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 68160, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := 8672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := -53344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := 196512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -368800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := -198848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := 3427104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := -10799968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := 19324416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := -21100192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := 12646336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := -347168, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := -105280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := 16, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := 3152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := -2496, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 70256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -179104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := 131904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := 114272, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := -3387824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := 6911104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := -8348688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := 5619232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := -243504, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := 384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := -22464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := 13632, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -10944, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := -146560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := 1935168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := -5680832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := 9140800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := -1178496, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := 3366784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := -7808, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := 96, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := 9888, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := -147776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := -33056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := 1144128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := -3497824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := 5699200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := -5240384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := 324288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -2784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := 16640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := -37984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := -17664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := 341728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -986752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := 1442528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -1021984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 17536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := 80, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := -1824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := 13280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := -37280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := 4672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := 15776, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := -858464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := 74016, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := -119920, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := 128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -448, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := 23616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := -58368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := 4672, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := -1728, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -3168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 21536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -65920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 12960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := -128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 10016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -60288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := 209696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := -52096, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := -180160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := 2889088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := -8505376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := 14241792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := -14651744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := 1272320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -385504, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 32, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -2880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 2080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := 5376, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := 432000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -466016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := -138080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := 161216, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := -213056, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := 108864, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := -15168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := 68128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := -141824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := -44192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := 1140544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := -201888, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := 5501120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := -711360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := 307328, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := 19456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := -8576, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := 13440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := 22144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := -399872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := 101248, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := -736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := 832, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := -19808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := 17600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := 12704, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := -361792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := 85536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -61600, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := -7808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := -2432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := -8960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := 1920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := -1152, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := 3072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := 50432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := -23424, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := 275584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := -183040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := 3456, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := 96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := -1504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := 6912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := -4192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := -7232, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := 186080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := -357888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := 421856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := -244640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := -1920, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := 1120, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := -640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := -17312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := 44032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := -7136, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := 20928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := -3456, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := 89344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := -2816, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := -1408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := 6240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := -7680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := -12000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := 40832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := -1920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := -2304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := -64, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := 1216, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := -2752, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := -2048, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := 46272, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := -905280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := 1219136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := -109024, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := 832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := -384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := 9920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := 9536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := -3584, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := 8064, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := 3648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := -27072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := 108288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := -36480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := 279168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := 283776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := -1555200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := 372672, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := -345408, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := -9600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := 21632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := -16256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := 24192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := 1, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := 1, den := 476, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13],[r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27],[r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40],[r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52],[r53,r54,-256,r55,r56,r57,r58,r59,r60,r61,r62],[r63,r64,r65,r66,r67,r68,r69,r70,r71,r72],[r73,r74,r75,r76,r77,r78,r79,r80,r81],[r53,r82,r83,r84,r85,r86,r87,r88],[r89,r90,r91,r92,r93,r94,r95],[],[],[],[],[r14,r96,r97,r98,r99,r100,r101,r102,r103,r104,r105,r106,r107],[r89,r108,r109,r110,r111,-3136,r112,r113,r114,r115,r116,r117],[r53,r54,r118,r119,r120,r121,r122,r123,r124,r125,r126],[0,r127,r128,r129,r130,r131,r132,r133,r134,-8064],[r14,r135,r136,r137,r138,r139,r140,r141,r142],[0,r41,r143,r144,r145,r146,r147,1792],[],[],[],[],[],[0,0,r41,r148,r149,r150,r151,r152,r153,r154,r155],[r156,r157,r158,r159,r160,r161,r162,r163,r164,r165],[r89,r108,r128,r166,r167,r168,r169,r170,448],[r53,r82,r128,r171,r172,r173,r174,r175],[r156,r176,r177,r178,r179,r180,-576],[],[r53,r181,r182,r183,128],[],[],[r14,r184,r185,r186,r187,r188,r189,r190,r191],[0,0,r53,r192,r193,r194,r195,-128],[r196,r171,r150,r197,r198,r199,r200],[],[r53,r181,r182,r183,128],[],[],[],[],[],[],[],[],[],[],[],[0,r201,r202,r203,r204,r205,r206,r207,r208,r209,r210,18816],[0,0,0,r41,r148,r211,r212,r213,r98,r214,-1792],[0,r127,r128,r129,r130,r131,r132,r133,r134,-8064],[],[0,r41,r143,r144,r145,r146,r147,1792],[],[],[],[],[],[],[r89,r108,r128,r166,r167,r168,r169,r170,448],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,0,r41,r215,r216,r171,r217,-256],[],[],[],[],[],[r127,r218,r219,r220,r221,r222,-1152],[],[r53,r181,r182,r183,128],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,r223,r224,r225,r226,r227,r228,r229,r230,r231,r232,r233,r234,r235,r236]),(⟨0,0,1⟩,[r28,r237,r238,r239,r240,r241,r242,r243,r244,r245,r246,r247,r248,r249]),(⟨0,0,2⟩,[r250,r251,r252,r253,r254,r255,r256,r257,r258,r259,r260,r261,r262]),(⟨0,0,3⟩,[r53,r263,r264,r265,r266,r267,r268,r269,r270,r271,r272,r273]),(⟨0,0,4⟩,[r89,r274,-128,r275,r276,r277,r278,r279,r280,r281,r282]),(⟨0,0,5⟩,[r73,r283,r284,r285,r286,r287,r288,r289,r290,r291]),(⟨0,0,6⟩,[r292,r293,r294,r295,r296,r297,r298,r299,r300]),(⟨0,0,7⟩,[r89,r301,r302,r15,r303,r304,r305,r306]),(⟨0,0,8⟩,[r307,r308,r309,r90,r310,r311,r312]),(⟨0,1,0⟩,[r28,r237,r238,r239,r240,r241,r242,r243,r244,r245,r246,r247,r248,r249]),(⟨0,1,1⟩,[r28,r313,r314,r315,r316,r317,r318,r319,r320,r321,r322,r323,r324]),(⟨0,1,2⟩,[r307,r325,r326,r327,r328,-1568,r329,r330,r331,r332,r333,r334]),(⟨0,1,3⟩,[r89,r274,r335,r336,r337,r338,r339,r340,r341,r342,r343]),(⟨0,1,4⟩,[0,r156,r84,r344,r345,r346,r347,r348,r349,-4032]),(⟨0,1,5⟩,[r28,r350,r351,r352,r353,r354,r355,r356,r357]),(⟨0,1,6⟩,[0,r53,r82,r358,r158,r359,r360,896]),(⟨0,2,0⟩,[r250,r251,r252,r253,r254,r255,r256,r257,r258,r259,r260,r261,r262]),(⟨0,2,1⟩,[r307,r325,r326,r327,r328,-1568,r329,r330,r331,r332,r333,r334]),(⟨0,2,2⟩,[0,0,r53,r361,r362,r363,r364,r365,r366,r367,r368]),(⟨0,2,3⟩,[r369,r370,r371,r372,r373,r374,r375,r376,r377,r378]),(⟨0,2,4⟩,[r307,r325,r84,r379,r380,r381,r382,r383,224]),(⟨0,2,5⟩,[r89,r301,r84,r194,r384,r385,r386,r387]),(⟨0,2,6⟩,[r369,r388,r389,r390,r391,r392,-288]),(⟨0,2,8⟩,[r89,r393,r394,r395,64]),(⟨0,3,0⟩,[r53,r263,r264,r265,r266,r267,r268,r269,r270,r271,r272,r273]),(⟨0,3,1⟩,[r89,r274,r335,r336,r337,r338,r339,r340,r341,r342,r343]),(⟨0,3,2⟩,[r369,r370,r371,r372,r373,r374,r375,r376,r377,r378]),(⟨0,3,3⟩,[r28,r396,r397,r398,r399,r400,r401,r402,r403]),(⟨0,3,4⟩,[0,0,r89,r404,r405,r201,r406,-64]),(⟨0,3,5⟩,[r14,r194,r363,r128,r407,r408,r409]),(⟨0,3,7⟩,[r89,r393,r394,r395,64]),(⟨0,4,0⟩,[r89,r274,-128,r275,r276,r277,r278,r279,r280,r281,r282]),(⟨0,4,1⟩,[0,r156,r84,r344,r345,r346,r347,r348,r349,-4032]),(⟨0,4,2⟩,[r307,r325,r84,r379,r380,r381,r382,r383,224]),(⟨0,4,3⟩,[0,0,r89,r404,r405,r201,r406,-64]),(⟨0,5,0⟩,[r73,r283,r284,r285,r286,r287,r288,r289,r290,r291]),(⟨0,5,1⟩,[r28,r350,r351,r352,r353,r354,r355,r356,r357]),(⟨0,5,2⟩,[r89,r301,r84,r194,r384,r385,r386,r387]),(⟨0,5,3⟩,[r14,r194,r363,r128,r407,r408,r409]),(⟨0,6,0⟩,[r292,r293,r294,r295,r296,r297,r298,r299,r300]),(⟨0,6,1⟩,[0,r53,r82,r358,r158,r359,r360,896]),(⟨0,6,2⟩,[r369,r388,r389,r390,r391,r392,-288]),(⟨0,7,0⟩,[r89,r301,r302,r15,r303,r304,r305,r306]),(⟨0,7,3⟩,[r89,r393,r394,r395,64]),(⟨0,8,0⟩,[r307,r308,r309,r90,r310,r311,r312]),(⟨0,8,2⟩,[r89,r393,r394,r395,64]),(⟨1,0,0⟩,[r28,r237,r238,r239,r240,r241,r242,r243,r244,r245,r246,r247,r248,r249]),(⟨1,0,1⟩,[r28,r313,r314,r315,r316,r317,r318,r319,r320,r321,r322,r323,r324]),(⟨1,0,2⟩,[r307,r325,r326,r327,r328,-1568,r329,r330,r331,r332,r333,r334]),(⟨1,0,3⟩,[r89,r274,r335,r336,r337,r338,r339,r340,r341,r342,r343]),(⟨1,0,4⟩,[0,r156,r84,r344,r345,r346,r347,r348,r349,-4032]),(⟨1,0,5⟩,[r28,r350,r351,r352,r353,r354,r355,r356,r357]),(⟨1,0,6⟩,[0,r53,r82,r358,r158,r359,r360,896]),(⟨1,1,0⟩,[r28,r313,r314,r315,r316,r317,r318,r319,r320,r321,r322,r323,r324]),(⟨1,1,1⟩,[0,r0,r410,r411,r412,r413,r414,r415,r416,r417,r418,9408]),(⟨1,1,2⟩,[0,0,0,r53,r361,r419,r420,r421,r315,r422,-896]),(⟨1,1,3⟩,[0,r156,r84,r344,r345,r346,r347,r348,r349,-4032]),(⟨1,1,5⟩,[0,r53,r82,r358,r158,r359,r360,896]),(⟨1,2,0⟩,[r307,r325,r326,r327,r328,-1568,r329,r330,r331,r332,r333,r334]),(⟨1,2,1⟩,[0,0,0,r53,r361,r419,r420,r421,r315,r422,-896]),(⟨1,2,3⟩,[r307,r325,r84,r379,r380,r381,r382,r383,224]),(⟨1,3,0⟩,[r89,r274,r335,r336,r337,r338,r339,r340,r341,r342,r343]),(⟨1,3,1⟩,[0,r156,r84,r344,r345,r346,r347,r348,r349,-4032]),(⟨1,3,2⟩,[r307,r325,r84,r379,r380,r381,r382,r383,224]),(⟨1,4,0⟩,[0,r156,r84,r344,r345,r346,r347,r348,r349,-4032]),(⟨1,5,0⟩,[r28,r350,r351,r352,r353,r354,r355,r356,r357]),(⟨1,5,1⟩,[0,r53,r82,r358,r158,r359,r360,896]),(⟨1,6,0⟩,[0,r53,r82,r358,r158,r359,r360,896]),(⟨2,0,0⟩,[r250,r251,r252,r253,r254,r255,r256,r257,r258,r259,r260,r261,r262]),(⟨2,0,1⟩,[r307,r325,r326,r327,r328,-1568,r329,r330,r331,r332,r333,r334]),(⟨2,0,2⟩,[0,0,r53,r361,r362,r363,r364,r365,r366,r367,r368]),(⟨2,0,3⟩,[r369,r370,r371,r372,r373,r374,r375,r376,r377,r378]),(⟨2,0,4⟩,[r307,r325,r84,r379,r380,r381,r382,r383,224]),(⟨2,0,5⟩,[r89,r301,r84,r194,r384,r385,r386,r387]),(⟨2,0,6⟩,[r369,r388,r389,r390,r391,r392,-288]),(⟨2,0,8⟩,[r89,r393,r394,r395,64]),(⟨2,1,0⟩,[r307,r325,r326,r327,r328,-1568,r329,r330,r331,r332,r333,r334]),(⟨2,1,1⟩,[0,0,0,r53,r361,r419,r420,r421,r315,r422,-896]),(⟨2,1,3⟩,[r307,r325,r84,r379,r380,r381,r382,r383,224]),(⟨2,2,0⟩,[0,0,r53,r361,r362,r363,r364,r365,r366,r367,r368]),(⟨2,2,3⟩,[0,0,r53,r192,r193,r194,r195,-128]),(⟨2,3,0⟩,[r369,r370,r371,r372,r373,r374,r375,r376,r377,r378]),(⟨2,3,1⟩,[r307,r325,r84,r379,r380,r381,r382,r383,224]),(⟨2,3,2⟩,[0,0,r53,r192,r193,r194,r195,-128]),(⟨2,3,3⟩,[r156,r176,r177,r178,r179,r180,-576]),(⟨2,3,5⟩,[r89,r393,r394,r395,64]),(⟨2,4,0⟩,[r307,r325,r84,r379,r380,r381,r382,r383,224]),(⟨2,5,0⟩,[r89,r301,r84,r194,r384,r385,r386,r387]),(⟨2,5,3⟩,[r89,r393,r394,r395,64]),(⟨2,6,0⟩,[r369,r388,r389,r390,r391,r392,-288]),(⟨2,8,0⟩,[r89,r393,r394,r395,64]),(⟨3,0,0⟩,[r53,r263,r264,r265,r266,r267,r268,r269,r270,r271,r272,r273]),(⟨3,0,1⟩,[r89,r274,r335,r336,r337,r338,r339,r340,r341,r342,r343]),(⟨3,0,2⟩,[r369,r370,r371,r372,r373,r374,r375,r376,r377,r378]),(⟨3,0,3⟩,[r28,r396,r397,r398,r399,r400,r401,r402,r403]),(⟨3,0,4⟩,[0,0,r89,r404,r405,r201,r406,-64]),(⟨3,0,5⟩,[r14,r194,r363,r128,r407,r408,r409]),(⟨3,0,7⟩,[r89,r393,r394,r395,64]),(⟨3,1,0⟩,[r89,r274,r335,r336,r337,r338,r339,r340,r341,r342,r343]),(⟨3,1,1⟩,[0,r156,r84,r344,r345,r346,r347,r348,r349,-4032]),(⟨3,1,2⟩,[r307,r325,r84,r379,r380,r381,r382,r383,224]),(⟨3,2,0⟩,[r369,r370,r371,r372,r373,r374,r375,r376,r377,r378]),(⟨3,2,1⟩,[r307,r325,r84,r379,r380,r381,r382,r383,224]),(⟨3,2,2⟩,[0,0,r53,r192,r193,r194,r195,-128]),(⟨3,2,3⟩,[r156,r176,r177,r178,r179,r180,-576]),(⟨3,2,5⟩,[r89,r393,r394,r395,64]),(⟨3,3,0⟩,[r28,r396,r397,r398,r399,r400,r401,r402,r403]),(⟨3,3,2⟩,[r156,r176,r177,r178,r179,r180,-576]),(⟨3,4,0⟩,[0,0,r89,r404,r405,r201,r406,-64]),(⟨3,5,0⟩,[r14,r194,r363,r128,r407,r408,r409]),(⟨3,5,2⟩,[r89,r393,r394,r395,64]),(⟨3,7,0⟩,[r89,r393,r394,r395,64]),(⟨4,0,0⟩,[r89,r274,-128,r275,r276,r277,r278,r279,r280,r281,r282]),(⟨4,0,1⟩,[0,r156,r84,r344,r345,r346,r347,r348,r349,-4032]),(⟨4,0,2⟩,[r307,r325,r84,r379,r380,r381,r382,r383,224]),(⟨4,0,3⟩,[0,0,r89,r404,r405,r201,r406,-64]),(⟨4,1,0⟩,[0,r156,r84,r344,r345,r346,r347,r348,r349,-4032]),(⟨4,2,0⟩,[r307,r325,r84,r379,r380,r381,r382,r383,224]),(⟨4,3,0⟩,[0,0,r89,r404,r405,r201,r406,-64]),(⟨5,0,0⟩,[r73,r283,r284,r285,r286,r287,r288,r289,r290,r291]),(⟨5,0,1⟩,[r28,r350,r351,r352,r353,r354,r355,r356,r357]),(⟨5,0,2⟩,[r89,r301,r84,r194,r384,r385,r386,r387]),(⟨5,0,3⟩,[r14,r194,r363,r128,r407,r408,r409]),(⟨5,1,0⟩,[r28,r350,r351,r352,r353,r354,r355,r356,r357]),(⟨5,1,1⟩,[0,r53,r82,r358,r158,r359,r360,896]),(⟨5,2,0⟩,[r89,r301,r84,r194,r384,r385,r386,r387]),(⟨5,2,3⟩,[r89,r393,r394,r395,64]),(⟨5,3,0⟩,[r14,r194,r363,r128,r407,r408,r409]),(⟨5,3,2⟩,[r89,r393,r394,r395,64]),(⟨6,0,0⟩,[r292,r293,r294,r295,r296,r297,r298,r299,r300]),(⟨6,0,1⟩,[0,r53,r82,r358,r158,r359,r360,896]),(⟨6,0,2⟩,[r369,r388,r389,r390,r391,r392,-288]),(⟨6,1,0⟩,[0,r53,r82,r358,r158,r359,r360,896]),(⟨6,2,0⟩,[r369,r388,r389,r390,r391,r392,-288]),(⟨7,0,0⟩,[r89,r301,r302,r15,r303,r304,r305,r306]),(⟨7,0,3⟩,[r89,r393,r394,r395,64]),(⟨7,3,0⟩,[r89,r393,r394,r395,64]),(⟨8,0,0⟩,[r307,r308,r309,r90,r310,r311,r312]),(⟨8,0,2⟩,[r89,r393,r394,r395,64]),(⟨8,2,0⟩,[r89,r393,r394,r395,64])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,-3,15,-21,3,6]),(⟨0,0,1⟩,[1,-5,10,-11,7]),(⟨0,0,2⟩,[0,0,2,-2]),(⟨0,0,3⟩,[-3,8,-9]),(⟨0,0,5⟩,[2]),(⟨0,1,0⟩,[1,-5,10,-11,7]),(⟨0,2,0⟩,[0,0,2,-2]),(⟨0,3,0⟩,[-3,8,-9]),(⟨0,5,0⟩,[2]),(⟨1,0,0⟩,[1,-5,10,-11,7]),(⟨2,0,0⟩,[0,0,2,-2]),(⟨3,0,0⟩,[-3,8,-9]),(⟨5,0,0⟩,[2])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[128,-2368,16192,-48960,27712,296128,-1096256,1862976,-1545664,318080]),(⟨0,0,1⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨0,0,2⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨0,0,3⟩,[-64,1280,-6336,2560,43072,-131840,181440]),(⟨0,1,0⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨0,1,1⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248]),(⟨0,2,0⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨0,2,3⟩,[-128,1536,-3840,-4608,15232]),(⟨0,3,0⟩,[-64,1280,-6336,2560,43072,-131840,181440]),(⟨0,3,2⟩,[-128,1536,-3840,-4608,15232]),(⟨1,0,0⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨1,0,1⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248]),(⟨1,1,0⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248]),(⟨2,0,0⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨2,0,3⟩,[-128,1536,-3840,-4608,15232]),(⟨2,3,0⟩,[-128,1536,-3840,-4608,15232]),(⟨3,0,0⟩,[-64,1280,-6336,2560,43072,-131840,181440]),(⟨3,0,2⟩,[-128,1536,-3840,-4608,15232]),(⟨3,2,0⟩,[-128,1536,-3840,-4608,15232])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 1 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r423) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 7 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r424) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨5,0,0⟩,[2])]

noncomputable def partial12 : Poly := [(⟨5,0,0⟩,[256,-4736,32384,-97920,55424,592256,-2192512,3725952,-3091328,636160]),(⟨5,0,1⟩,[128,-2944,23296,-79232,70400,355712,-1447168,2395008,-1724800]),(⟨5,0,2⟩,[-256,3584,-12544,-6400,94464,-233472,317696,-48384]),(⟨5,0,3⟩,[-128,2560,-12672,5120,86144,-263680,362880]),(⟨5,1,0⟩,[128,-2944,23296,-79232,70400,355712,-1447168,2395008,-1724800]),(⟨5,1,1⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨5,2,0⟩,[-256,3584,-12544,-6400,94464,-233472,317696,-48384]),(⟨5,2,3⟩,[-256,3072,-7680,-9216,30464]),(⟨5,3,0⟩,[-128,2560,-12672,5120,86144,-263680,362880]),(⟨5,3,2⟩,[-256,3072,-7680,-9216,30464]),(⟨6,0,0⟩,[128,-2944,23296,-79232,70400,355712,-1447168,2395008,-1724800]),(⟨6,0,1⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨6,1,0⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨7,0,0⟩,[-256,3584,-12544,-6400,94464,-233472,317696,-48384]),(⟨7,0,3⟩,[-256,3072,-7680,-9216,30464]),(⟨7,3,0⟩,[-256,3072,-7680,-9216,30464]),(⟨8,0,0⟩,[-128,2560,-12672,5120,86144,-263680,362880]),(⟨8,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨8,2,0⟩,[-256,3072,-7680,-9216,30464])]


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

noncomputable def partial8 : Poly := [(⟨0,5,0⟩,[256,-4736,32384,-97920,55424,592256,-2192512,3725952,-3091328,636160]),(⟨0,5,1⟩,[128,-2944,23296,-79232,70400,355712,-1447168,2395008,-1724800]),(⟨0,5,2⟩,[-256,3584,-12544,-6400,94464,-233472,317696,-48384]),(⟨0,5,3⟩,[-128,2560,-12672,5120,86144,-263680,362880]),(⟨0,6,0⟩,[128,-2944,23296,-79232,70400,355712,-1447168,2395008,-1724800]),(⟨0,6,1⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨0,7,0⟩,[-256,3584,-12544,-6400,94464,-233472,317696,-48384]),(⟨0,7,3⟩,[-256,3072,-7680,-9216,30464]),(⟨0,8,0⟩,[-128,2560,-12672,5120,86144,-263680,362880]),(⟨0,8,2⟩,[-256,3072,-7680,-9216,30464]),(⟨1,0,0⟩,[128,-3008,29312,-155008,461376,-526720,-1647872,9657984,-24886528,40807872,-45213568,33223936,-14318528,2226560]),(⟨1,0,1⟩,[64,-1792,19648,-113280,366400,-532736,-743552,5929472,-15795776,25491456,-26861632,17868928,-6036800]),(⟨1,0,2⟩,[-128,2432,-16512,47488,-20096,-303360,1206144,-2527744,3324160,-2806400,1378048,-169344]),(⟨1,0,3⟩,[-64,1600,-13376,47744,-47616,-242944,1198848,-2681472,3566144,-2918720,1270080]),(⟨1,1,0⟩,[64,-1792,19648,-113280,366400,-532736,-743552,5929472,-15795776,25491456,-26861632,17868928,-6036800]),(⟨1,1,1⟩,[0,-256,4864,-36096,144384,-340480,372224,378368,-2073600,3478272,-3223808,1492736]),(⟨1,2,0⟩,[-128,2432,-16512,47488,-20096,-303360,1206144,-2527744,3324160,-2806400,1378048,-169344]),(⟨1,2,3⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨1,3,0⟩,[-64,1600,-13376,47744,-47616,-242944,1198848,-2681472,3566144,-2918720,1270080]),(⟨1,3,2⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨1,5,0⟩,[128,-2944,23296,-79232,70400,355712,-1447168,2395008,-1724800]),(⟨1,5,1⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨1,6,0⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨2,0,0⟩,[64,-1792,19904,-118272,403520,-663040,-590208,6466304,-18580544,31409920,-33678912,21596416,-6672960]),(⟨2,0,1⟩,[0,-256,4992,-39168,170624,-443008,521856,663680,-3876480,7320448,-7343616,3217536]),(⟨2,0,2⟩,[0,0,-256,3840,-16128,6144,100864,-327936,551168,-366080,48384]),(⟨2,0,3⟩,[0,0,-128,2688,-15232,17792,81024,-349824,626560,-362880]),(⟨2,1,0⟩,[0,-256,4992,-39168,170624,-443008,521856,663680,-3876480,7320448,-7343616,3217536]),(⟨2,1,1⟩,[0,0,0,-512,7680,-38400,86528,-65024,-241152,677376,-426496]),(⟨2,2,0⟩,[0,0,-256,3840,-16128,6144,100864,-327936,551168,-366080,48384]),(⟨2,2,3⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨2,3,0⟩,[0,0,-128,2688,-15232,17792,81024,-349824,626560,-362880]),(⟨2,3,2⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨2,5,0⟩,[-256,3584,-12544,-6400,94464,-233472,317696,-48384]),(⟨2,5,3⟩,[-256,3072,-7680,-9216,30464]),(⟨2,8,0⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[-512,10560,-85056,342144,-614400,-631936,6764160,-19266560,30928384,-29050560,13713856,-1307264]),(⟨3,0,1⟩,[-192,4928,-47296,224768,-519680,66176,3363328,-11046912,18438336,-16999360,7335104]),(⟨3,0,2⟩,[384,-6400,34304,-56704,-110848,756864,-1835520,2393984,-1623168,217728]),(⟨3,0,3⟩,[64,-2176,17024,-38528,-69632,647808,-1810560,2438272,-1526336]),(⟨3,1,0⟩,[-192,4928,-47296,224768,-519680,66176,3363328,-11046912,18438336,-16999360,7335104]),(⟨3,1,1⟩,[0,768,-12800,77824,-240128,376320,88576,-1599488,2834944,-1919232]),(⟨3,2,0⟩,[384,-6400,34304,-56704,-110848,756864,-1835520,2393984,-1623168,217728]),(⟨3,2,3⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨3,3,0⟩,[64,-2176,17024,-38528,-69632,647808,-1810560,2438272,-1526336]),(⟨3,3,2⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨3,5,0⟩,[-128,2560,-12672,5120,86144,-263680,362880]),(⟨3,5,2⟩,[-256,3072,-7680,-9216,30464]),(⟨3,7,0⟩,[-256,3072,-7680,-9216,30464]),(⟨4,0,0⟩,[-256,6528,-60928,276864,-591104,-132224,4576512,-13991296,22796800,-20961536,9080064]),(⟨4,0,1⟩,[0,768,-12800,77824,-240128,376320,88576,-1599488,2834944,-1919232]),(⟨4,0,2⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨4,0,3⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨4,1,0⟩,[0,768,-12800,77824,-240128,376320,88576,-1599488,2834944,-1919232]),(⟨4,2,0⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨4,3,0⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨5,0,0⟩,[640,-11136,66560,-151936,-70656,1366912,-3947008,5770112,-4087936,491008]),(⟨5,0,1⟩,[128,-2944,23296,-79232,70400,355712,-1447168,2395008,-1724800]),(⟨5,0,2⟩,[-256,3584,-12800,-3072,83712,-235008,357376,-78848]),(⟨5,0,3⟩,[256,-3072,12288,-25600,38144,-100352,225792]),(⟨5,1,0⟩,[128,-2944,23296,-79232,70400,355712,-1447168,2395008,-1724800]),(⟨5,1,1⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨5,2,0⟩,[-256,3584,-12800,-3072,83712,-235008,357376,-78848]),(⟨5,2,3⟩,[-256,3072,-7680,-9216,30464]),(⟨5,3,0⟩,[256,-3072,12288,-25600,38144,-100352,225792]),(⟨5,3,2⟩,[-256,3072,-7680,-9216,30464]),(⟨6,0,0⟩,[320,-7296,53120,-149120,18688,1072768,-3433856,5033088,-3357760]),(⟨6,0,1⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨6,0,2⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨6,1,0⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨6,2,0⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨7,0,0⟩,[-256,3584,-12544,-6400,94464,-233472,317696,-48384]),(⟨7,0,3⟩,[-256,3072,-7680,-9216,30464]),(⟨7,3,0⟩,[-256,3072,-7680,-9216,30464]),(⟨8,0,0⟩,[-128,2560,-12672,5120,86144,-263680,362880]),(⟨8,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨8,2,0⟩,[-256,3072,-7680,-9216,30464])]


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

noncomputable def partial4 : Poly := [(⟨0,0,5⟩,[256,-4736,32384,-97920,55424,592256,-2192512,3725952,-3091328,636160]),(⟨0,0,6⟩,[128,-2944,23296,-79232,70400,355712,-1447168,2395008,-1724800]),(⟨0,0,7⟩,[-256,3584,-12544,-6400,94464,-233472,317696,-48384]),(⟨0,0,8⟩,[-128,2560,-12672,5120,86144,-263680,362880]),(⟨0,1,0⟩,[128,-3008,29312,-155008,461376,-526720,-1647872,9657984,-24886528,40807872,-45213568,33223936,-14318528,2226560]),(⟨0,1,1⟩,[64,-1792,19648,-113280,366400,-532736,-743552,5929472,-15795776,25491456,-26861632,17868928,-6036800]),(⟨0,1,2⟩,[-128,2432,-16512,47488,-20096,-303360,1206144,-2527744,3324160,-2806400,1378048,-169344]),(⟨0,1,3⟩,[-64,1600,-13376,47744,-47616,-242944,1198848,-2681472,3566144,-2918720,1270080]),(⟨0,1,5⟩,[128,-2944,23296,-79232,70400,355712,-1447168,2395008,-1724800]),(⟨0,1,6⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨0,2,0⟩,[64,-1792,19904,-118272,403520,-663040,-590208,6466304,-18580544,31409920,-33678912,21596416,-6672960]),(⟨0,2,1⟩,[0,-256,4992,-39168,170624,-443008,521856,663680,-3876480,7320448,-7343616,3217536]),(⟨0,2,2⟩,[0,0,-256,3840,-16128,6144,100864,-327936,551168,-366080,48384]),(⟨0,2,3⟩,[0,0,-128,2688,-15232,17792,81024,-349824,626560,-362880]),(⟨0,2,5⟩,[-256,3584,-12544,-6400,94464,-233472,317696,-48384]),(⟨0,2,8⟩,[-256,3072,-7680,-9216,30464]),(⟨0,3,0⟩,[-512,10560,-85056,342144,-614400,-631936,6764160,-19266560,30928384,-29050560,13713856,-1307264]),(⟨0,3,1⟩,[-192,4928,-47296,224768,-519680,66176,3363328,-11046912,18438336,-16999360,7335104]),(⟨0,3,2⟩,[384,-6400,34304,-56704,-110848,756864,-1835520,2393984,-1623168,217728]),(⟨0,3,3⟩,[64,-2176,17024,-38528,-69632,647808,-1810560,2438272,-1526336]),(⟨0,3,5⟩,[-128,2560,-12672,5120,86144,-263680,362880]),(⟨0,3,7⟩,[-256,3072,-7680,-9216,30464]),(⟨0,4,0⟩,[-256,6528,-60928,276864,-591104,-132224,4576512,-13991296,22796800,-20961536,9080064]),(⟨0,4,1⟩,[0,768,-12800,77824,-240128,376320,88576,-1599488,2834944,-1919232]),(⟨0,4,2⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨0,4,3⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨0,5,0⟩,[640,-11136,66560,-151936,-70656,1366912,-3947008,5770112,-4087936,491008]),(⟨0,5,1⟩,[128,-2944,23296,-79232,70400,355712,-1447168,2395008,-1724800]),(⟨0,5,2⟩,[-256,3584,-12800,-3072,83712,-235008,357376,-78848]),(⟨0,5,3⟩,[256,-3072,12288,-25600,38144,-100352,225792]),(⟨0,6,0⟩,[320,-7296,53120,-149120,18688,1072768,-3433856,5033088,-3357760]),(⟨0,6,1⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨0,6,2⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨0,7,0⟩,[-256,3584,-12544,-6400,94464,-233472,317696,-48384]),(⟨0,7,3⟩,[-256,3072,-7680,-9216,30464]),(⟨0,8,0⟩,[-128,2560,-12672,5120,86144,-263680,362880]),(⟨0,8,2⟩,[-256,3072,-7680,-9216,30464]),(⟨1,0,0⟩,[128,-3008,29312,-155008,461376,-526720,-1647872,9657984,-24886528,40807872,-45213568,33223936,-14318528,2226560]),(⟨1,0,1⟩,[64,-1792,19648,-113280,366400,-532736,-743552,5929472,-15795776,25491456,-26861632,17868928,-6036800]),(⟨1,0,2⟩,[-128,2432,-16512,47488,-20096,-303360,1206144,-2527744,3324160,-2806400,1378048,-169344]),(⟨1,0,3⟩,[-64,1600,-13376,47744,-47616,-242944,1198848,-2681472,3566144,-2918720,1270080]),(⟨1,0,5⟩,[128,-2944,23296,-79232,70400,355712,-1447168,2395008,-1724800]),(⟨1,0,6⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨1,1,0⟩,[128,-3584,39296,-226560,732800,-1065472,-1487104,11858944,-31591552,50982912,-53723264,35737856,-12073600]),(⟨1,1,1⟩,[0,-512,9728,-72192,288768,-680960,744448,756736,-4147200,6956544,-6447616,2985472]),(⟨1,1,5⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨1,2,0⟩,[-128,2176,-11520,8320,150528,-746368,1728000,-1864064,-552320,4514048,-5965568,3048192]),(⟨1,2,1⟩,[0,0,0,-512,7680,-38400,86528,-65024,-241152,677376,-426496]),(⟨1,2,3⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨1,3,0⟩,[-256,6528,-60672,272512,-567296,-176768,4562176,-13728384,22004480,-19918080,8605184]),(⟨1,3,1⟩,[0,768,-12800,77824,-240128,376320,88576,-1599488,2834944,-1919232]),(⟨1,3,2⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨1,4,0⟩,[0,768,-12800,77824,-240128,376320,88576,-1599488,2834944,-1919232]),(⟨1,5,0⟩,[128,-2944,23296,-79232,70400,355712,-1447168,2395008,-1724800]),(⟨1,5,1⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨1,6,0⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨2,0,0⟩,[64,-1792,19904,-118272,403520,-663040,-590208,6466304,-18580544,31409920,-33678912,21596416,-6672960]),(⟨2,0,1⟩,[0,-256,4992,-39168,170624,-443008,521856,663680,-3876480,7320448,-7343616,3217536]),(⟨2,0,2⟩,[0,0,-256,3840,-16128,6144,100864,-327936,551168,-366080,48384]),(⟨2,0,3⟩,[0,0,-128,2688,-15232,17792,81024,-349824,626560,-362880]),(⟨2,0,5⟩,[-256,3584,-12544,-6400,94464,-233472,317696,-48384]),(⟨2,0,8⟩,[-256,3072,-7680,-9216,30464]),(⟨2,1,0⟩,[-128,2176,-11520,8320,150528,-746368,1728000,-1864064,-552320,4514048,-5965568,3048192]),(⟨2,1,1⟩,[0,0,0,-512,7680,-38400,86528,-65024,-241152,677376,-426496]),(⟨2,1,3⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨2,2,0⟩,[0,0,-512,7680,-32256,12288,201728,-655872,1102336,-732160,96768]),(⟨2,2,3⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨2,3,0⟩,[384,-6400,34176,-54016,-126080,774656,-1754496,2044160,-996608,-145152]),(⟨2,3,2⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨2,3,3⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨2,3,5⟩,[-256,3072,-7680,-9216,30464]),(⟨2,4,0⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨2,5,0⟩,[-256,3584,-12800,-3072,83712,-235008,357376,-78848]),(⟨2,5,3⟩,[-256,3072,-7680,-9216,30464]),(⟨2,6,0⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨2,8,0⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[-512,10560,-85056,342144,-614400,-631936,6764160,-19266560,30928384,-29050560,13713856,-1307264]),(⟨3,0,1⟩,[-192,4928,-47296,224768,-519680,66176,3363328,-11046912,18438336,-16999360,7335104]),(⟨3,0,2⟩,[384,-6400,34304,-56704,-110848,756864,-1835520,2393984,-1623168,217728]),(⟨3,0,3⟩,[64,-2176,17024,-38528,-69632,647808,-1810560,2438272,-1526336]),(⟨3,0,5⟩,[-128,2560,-12672,5120,86144,-263680,362880]),(⟨3,0,7⟩,[-256,3072,-7680,-9216,30464]),(⟨3,1,0⟩,[-256,6528,-60672,272512,-567296,-176768,4562176,-13728384,22004480,-19918080,8605184]),(⟨3,1,1⟩,[0,768,-12800,77824,-240128,376320,88576,-1599488,2834944,-1919232]),(⟨3,1,2⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨3,2,0⟩,[384,-6400,34176,-54016,-126080,774656,-1754496,2044160,-996608,-145152]),(⟨3,2,2⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨3,2,3⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨3,2,5⟩,[-256,3072,-7680,-9216,30464]),(⟨3,3,0⟩,[128,-4352,34048,-77056,-139264,1295616,-3621120,4876544,-3052672]),(⟨3,3,2⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨3,4,0⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨3,5,0⟩,[256,-3072,12288,-25600,38144,-100352,225792]),(⟨3,5,2⟩,[-256,3072,-7680,-9216,30464]),(⟨3,7,0⟩,[-256,3072,-7680,-9216,30464]),(⟨4,0,0⟩,[-256,6528,-60928,276864,-591104,-132224,4576512,-13991296,22796800,-20961536,9080064]),(⟨4,0,1⟩,[0,768,-12800,77824,-240128,376320,88576,-1599488,2834944,-1919232]),(⟨4,0,2⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨4,0,3⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨4,1,0⟩,[0,768,-12800,77824,-240128,376320,88576,-1599488,2834944,-1919232]),(⟨4,2,0⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨4,3,0⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨5,0,0⟩,[640,-11136,66560,-151936,-70656,1366912,-3947008,5770112,-4087936,491008]),(⟨5,0,1⟩,[128,-2944,23296,-79232,70400,355712,-1447168,2395008,-1724800]),(⟨5,0,2⟩,[-256,3584,-12800,-3072,83712,-235008,357376,-78848]),(⟨5,0,3⟩,[256,-3072,12288,-25600,38144,-100352,225792]),(⟨5,1,0⟩,[128,-2944,23296,-79232,70400,355712,-1447168,2395008,-1724800]),(⟨5,1,1⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨5,2,0⟩,[-256,3584,-12800,-3072,83712,-235008,357376,-78848]),(⟨5,2,3⟩,[-256,3072,-7680,-9216,30464]),(⟨5,3,0⟩,[256,-3072,12288,-25600,38144,-100352,225792]),(⟨5,3,2⟩,[-256,3072,-7680,-9216,30464]),(⟨6,0,0⟩,[320,-7296,53120,-149120,18688,1072768,-3433856,5033088,-3357760]),(⟨6,0,1⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨6,0,2⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨6,1,0⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨6,2,0⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨7,0,0⟩,[-256,3584,-12544,-6400,94464,-233472,317696,-48384]),(⟨7,0,3⟩,[-256,3072,-7680,-9216,30464]),(⟨7,3,0⟩,[-256,3072,-7680,-9216,30464]),(⟨8,0,0⟩,[-128,2560,-12672,5120,86144,-263680,362880]),(⟨8,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨8,2,0⟩,[-256,3072,-7680,-9216,30464])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,-384,9024,-86784,439872,-1163904,589824,7099008,-28462080,56657664,-64773696,36241536,-138816,-8319744,1908480]),(⟨0,0,1⟩,[128,-3200,34688,-213376,786048,-1475200,-795392,13708416,-43199872,77297664,-84400768,50585344,-9720704,-2947840]),(⟨0,0,2⟩,[64,-1408,12608,-69888,281024,-716416,527616,3199616,-13551296,27644416,-33394752,22476928,-6818112]),(⟨0,0,3⟩,[-512,10752,-89856,381696,-744192,-586240,7740672,-22723328,36563200,-32997888,13467136,-218624]),(⟨0,0,4⟩,[-256,6528,-60928,276864,-591104,-132224,4576512,-13991296,22796800,-20961536,9080064]),(⟨0,0,5⟩,[640,-11136,66560,-151936,-70656,1366912,-3947008,5770112,-4087936,491008]),(⟨0,0,6⟩,[320,-7296,53120,-149120,18688,1072768,-3433856,5033088,-3357760]),(⟨0,0,7⟩,[-256,3584,-12544,-6400,94464,-233472,317696,-48384]),(⟨0,0,8⟩,[-128,2560,-12672,5120,86144,-263680,362880]),(⟨0,1,0⟩,[128,-3200,34688,-213376,786048,-1475200,-795392,13708416,-43199872,77297664,-84400768,50585344,-9720704,-2947840]),(⟨0,1,1⟩,[128,-3584,40064,-241152,838784,-1458688,-720640,11556352,-34021504,56967168,-58606976,35624960,-10794112]),(⟨0,1,2⟩,[-128,2176,-11520,8320,150528,-746368,1728000,-1864064,-552320,4514048,-5965568,3048192]),(⟨0,1,3⟩,[-256,6528,-60672,272512,-567296,-176768,4562176,-13728384,22004480,-19918080,8605184]),(⟨0,1,4⟩,[0,768,-12800,77824,-240128,376320,88576,-1599488,2834944,-1919232]),(⟨0,1,5⟩,[128,-2944,23296,-79232,70400,355712,-1447168,2395008,-1724800]),(⟨0,1,6⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨0,2,0⟩,[64,-1408,12608,-69888,281024,-716416,527616,3199616,-13551296,27644416,-33394752,22476928,-6818112]),(⟨0,2,1⟩,[-128,2176,-11520,8320,150528,-746368,1728000,-1864064,-552320,4514048,-5965568,3048192]),(⟨0,2,2⟩,[0,0,-512,7680,-32256,12288,201728,-655872,1102336,-732160,96768]),(⟨0,2,3⟩,[384,-6016,27648,-16768,-202496,744320,-1431552,1687424,-978560,-53760]),(⟨0,2,4⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨0,2,5⟩,[-256,3584,-12800,-3072,83712,-235008,357376,-78848]),(⟨0,2,6⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨0,2,8⟩,[-256,3072,-7680,-9216,30464]),(⟨0,3,0⟩,[-512,10752,-89856,381696,-744192,-586240,7740672,-22723328,36563200,-32997888,13467136,-218624]),(⟨0,3,1⟩,[-256,6528,-60672,272512,-567296,-176768,4562176,-13728384,22004480,-19918080,8605184]),(⟨0,3,2⟩,[384,-6016,27648,-16768,-202496,744320,-1431552,1687424,-978560,-53760]),(⟨0,3,3⟩,[128,-4352,34048,-77056,-139264,1295616,-3621120,4876544,-3052672]),(⟨0,3,4⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨0,3,5⟩,[256,-3072,12288,-25600,38144,-100352,225792]),(⟨0,3,7⟩,[-256,3072,-7680,-9216,30464]),(⟨0,4,0⟩,[-256,6528,-60928,276864,-591104,-132224,4576512,-13991296,22796800,-20961536,9080064]),(⟨0,4,1⟩,[0,768,-12800,77824,-240128,376320,88576,-1599488,2834944,-1919232]),(⟨0,4,2⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨0,4,3⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨0,5,0⟩,[640,-11136,66560,-151936,-70656,1366912,-3947008,5770112,-4087936,491008]),(⟨0,5,1⟩,[128,-2944,23296,-79232,70400,355712,-1447168,2395008,-1724800]),(⟨0,5,2⟩,[-256,3584,-12800,-3072,83712,-235008,357376,-78848]),(⟨0,5,3⟩,[256,-3072,12288,-25600,38144,-100352,225792]),(⟨0,6,0⟩,[320,-7296,53120,-149120,18688,1072768,-3433856,5033088,-3357760]),(⟨0,6,1⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨0,6,2⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨0,7,0⟩,[-256,3584,-12544,-6400,94464,-233472,317696,-48384]),(⟨0,7,3⟩,[-256,3072,-7680,-9216,30464]),(⟨0,8,0⟩,[-128,2560,-12672,5120,86144,-263680,362880]),(⟨0,8,2⟩,[-256,3072,-7680,-9216,30464]),(⟨1,0,0⟩,[128,-3200,34688,-213376,786048,-1475200,-795392,13708416,-43199872,77297664,-84400768,50585344,-9720704,-2947840]),(⟨1,0,1⟩,[128,-3584,40064,-241152,838784,-1458688,-720640,11556352,-34021504,56967168,-58606976,35624960,-10794112]),(⟨1,0,2⟩,[-128,2176,-11520,8320,150528,-746368,1728000,-1864064,-552320,4514048,-5965568,3048192]),(⟨1,0,3⟩,[-256,6528,-60672,272512,-567296,-176768,4562176,-13728384,22004480,-19918080,8605184]),(⟨1,0,4⟩,[0,768,-12800,77824,-240128,376320,88576,-1599488,2834944,-1919232]),(⟨1,0,5⟩,[128,-2944,23296,-79232,70400,355712,-1447168,2395008,-1724800]),(⟨1,0,6⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨1,1,0⟩,[128,-3584,40064,-241152,838784,-1458688,-720640,11556352,-34021504,56967168,-58606976,35624960,-10794112]),(⟨1,1,1⟩,[0,-768,14592,-108288,433152,-1021440,1116672,1135104,-6220800,10434816,-9671424,4478208]),(⟨1,1,2⟩,[0,0,0,-512,7680,-38400,86528,-65024,-241152,677376,-426496]),(⟨1,1,3⟩,[0,768,-12800,77824,-240128,376320,88576,-1599488,2834944,-1919232]),(⟨1,1,5⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨1,2,0⟩,[-128,2176,-11520,8320,150528,-746368,1728000,-1864064,-552320,4514048,-5965568,3048192]),(⟨1,2,1⟩,[0,0,0,-512,7680,-38400,86528,-65024,-241152,677376,-426496]),(⟨1,2,3⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨1,3,0⟩,[-256,6528,-60672,272512,-567296,-176768,4562176,-13728384,22004480,-19918080,8605184]),(⟨1,3,1⟩,[0,768,-12800,77824,-240128,376320,88576,-1599488,2834944,-1919232]),(⟨1,3,2⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨1,4,0⟩,[0,768,-12800,77824,-240128,376320,88576,-1599488,2834944,-1919232]),(⟨1,5,0⟩,[128,-2944,23296,-79232,70400,355712,-1447168,2395008,-1724800]),(⟨1,5,1⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨1,6,0⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨2,0,0⟩,[64,-1408,12608,-69888,281024,-716416,527616,3199616,-13551296,27644416,-33394752,22476928,-6818112]),(⟨2,0,1⟩,[-128,2176,-11520,8320,150528,-746368,1728000,-1864064,-552320,4514048,-5965568,3048192]),(⟨2,0,2⟩,[0,0,-512,7680,-32256,12288,201728,-655872,1102336,-732160,96768]),(⟨2,0,3⟩,[384,-6016,27648,-16768,-202496,744320,-1431552,1687424,-978560,-53760]),(⟨2,0,4⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨2,0,5⟩,[-256,3584,-12800,-3072,83712,-235008,357376,-78848]),(⟨2,0,6⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨2,0,8⟩,[-256,3072,-7680,-9216,30464]),(⟨2,1,0⟩,[-128,2176,-11520,8320,150528,-746368,1728000,-1864064,-552320,4514048,-5965568,3048192]),(⟨2,1,1⟩,[0,0,0,-512,7680,-38400,86528,-65024,-241152,677376,-426496]),(⟨2,1,3⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨2,2,0⟩,[0,0,-512,7680,-32256,12288,201728,-655872,1102336,-732160,96768]),(⟨2,2,3⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨2,3,0⟩,[384,-6016,27648,-16768,-202496,744320,-1431552,1687424,-978560,-53760]),(⟨2,3,1⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨2,3,2⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨2,3,3⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨2,3,5⟩,[-256,3072,-7680,-9216,30464]),(⟨2,4,0⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨2,5,0⟩,[-256,3584,-12800,-3072,83712,-235008,357376,-78848]),(⟨2,5,3⟩,[-256,3072,-7680,-9216,30464]),(⟨2,6,0⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨2,8,0⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[-512,10752,-89856,381696,-744192,-586240,7740672,-22723328,36563200,-32997888,13467136,-218624]),(⟨3,0,1⟩,[-256,6528,-60672,272512,-567296,-176768,4562176,-13728384,22004480,-19918080,8605184]),(⟨3,0,2⟩,[384,-6016,27648,-16768,-202496,744320,-1431552,1687424,-978560,-53760]),(⟨3,0,3⟩,[128,-4352,34048,-77056,-139264,1295616,-3621120,4876544,-3052672]),(⟨3,0,4⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨3,0,5⟩,[256,-3072,12288,-25600,38144,-100352,225792]),(⟨3,0,7⟩,[-256,3072,-7680,-9216,30464]),(⟨3,1,0⟩,[-256,6528,-60672,272512,-567296,-176768,4562176,-13728384,22004480,-19918080,8605184]),(⟨3,1,1⟩,[0,768,-12800,77824,-240128,376320,88576,-1599488,2834944,-1919232]),(⟨3,1,2⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨3,2,0⟩,[384,-6016,27648,-16768,-202496,744320,-1431552,1687424,-978560,-53760]),(⟨3,2,1⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨3,2,2⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨3,2,3⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨3,2,5⟩,[-256,3072,-7680,-9216,30464]),(⟨3,3,0⟩,[128,-4352,34048,-77056,-139264,1295616,-3621120,4876544,-3052672]),(⟨3,3,2⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨3,4,0⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨3,5,0⟩,[256,-3072,12288,-25600,38144,-100352,225792]),(⟨3,5,2⟩,[-256,3072,-7680,-9216,30464]),(⟨3,7,0⟩,[-256,3072,-7680,-9216,30464]),(⟨4,0,0⟩,[-256,6528,-60928,276864,-591104,-132224,4576512,-13991296,22796800,-20961536,9080064]),(⟨4,0,1⟩,[0,768,-12800,77824,-240128,376320,88576,-1599488,2834944,-1919232]),(⟨4,0,2⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨4,0,3⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨4,1,0⟩,[0,768,-12800,77824,-240128,376320,88576,-1599488,2834944,-1919232]),(⟨4,2,0⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨4,3,0⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨5,0,0⟩,[640,-11136,66560,-151936,-70656,1366912,-3947008,5770112,-4087936,491008]),(⟨5,0,1⟩,[128,-2944,23296,-79232,70400,355712,-1447168,2395008,-1724800]),(⟨5,0,2⟩,[-256,3584,-12800,-3072,83712,-235008,357376,-78848]),(⟨5,0,3⟩,[256,-3072,12288,-25600,38144,-100352,225792]),(⟨5,1,0⟩,[128,-2944,23296,-79232,70400,355712,-1447168,2395008,-1724800]),(⟨5,1,1⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨5,2,0⟩,[-256,3584,-12800,-3072,83712,-235008,357376,-78848]),(⟨5,2,3⟩,[-256,3072,-7680,-9216,30464]),(⟨5,3,0⟩,[256,-3072,12288,-25600,38144,-100352,225792]),(⟨5,3,2⟩,[-256,3072,-7680,-9216,30464]),(⟨6,0,0⟩,[320,-7296,53120,-149120,18688,1072768,-3433856,5033088,-3357760]),(⟨6,0,1⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨6,0,2⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨6,1,0⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨6,2,0⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨7,0,0⟩,[-256,3584,-12544,-6400,94464,-233472,317696,-48384]),(⟨7,0,3⟩,[-256,3072,-7680,-9216,30464]),(⟨7,3,0⟩,[-256,3072,-7680,-9216,30464]),(⟨8,0,0⟩,[-128,2560,-12672,5120,86144,-263680,362880]),(⟨8,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨8,2,0⟩,[-256,3072,-7680,-9216,30464])]


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
    (Poly.add (Poly.scale (K.ofRat r425) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 1 7).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r423*r424 : ℚ)=r425 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 1 7 r423 r424 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 1=7 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 1 7).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C065

#print axioms Coulomb8.Columns.C065.sound
