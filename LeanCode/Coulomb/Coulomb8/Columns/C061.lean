import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C061

def r0 : ℚ := { num := -192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 3648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -22464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 11328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 522048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -2920128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 7652544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -10712640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 6995328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -353664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -1526016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 350208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -1408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 11712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -36096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := -89792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 1201024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -283072, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 10629888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -13693056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 9306368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -2004224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := -83712, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -1152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 7104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -18944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 6464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := 208640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -1224768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 3485184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -5241216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 4003200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -1314688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 256, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -1280, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -20736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 36480, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -2676992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 5578240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -5932288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 2628992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -7680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 4672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -3648, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 960, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 20800, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -1614400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 197312, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -3640256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 253248, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -4224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 8768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 83968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -482368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -815936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 96512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -4864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 14528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := -24384, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := 848128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := -676544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 1280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -2048, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 69504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -1792, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -37376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := 76672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 20480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -65152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := -22784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := 967808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 455808, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -9176448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 6295552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -305408, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := -64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := 128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := -1984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -22656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 22208, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -405120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 438208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 129152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -111872, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := 78080, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := -320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := 5760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -4544, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 30080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := 351296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := -1634432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 3334976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -3578752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 250368, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -11392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 51584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -66816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := -13824, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 346496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := 1216, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -4608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := -172864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 454912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -57152, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := 6144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := -15360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -18432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := -3840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := 128, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := -768, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := 34176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := -2560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := -8320, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := 384768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -363904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 18816, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := 192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := -2432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 3520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := 54912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -255936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 415104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := -229056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := -35456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -2816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 12480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -24000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 81664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -5632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 12672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := 14336, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := -75904, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := 135680, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := -690048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 768, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := -76800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := 26880, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := -15360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -415488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 1056768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -171264, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := -12800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 30848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := -11264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -90752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := 173056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := -120448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := 49920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := -61440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := -96000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := 326656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 3328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -1536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := -1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := 39680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := -96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 1824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := -11232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 5664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := 261024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -1460064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 3826272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -5356320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := 3497664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := -176832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := -763008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := 175104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := 32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := -704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := 5856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := -18048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -44896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 600512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := -141536, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := 5314944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -6846528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := 4653184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -1002112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := -41856, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 3552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := -9472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := 3232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 104320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -612384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 1742592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -2620608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := 2001600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := -657344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -640, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := -10368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := 18240, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := -1338496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := 2789120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -2966144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := 1314496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := 2336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -1824, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := 480, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := 10400, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := -807200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 98656, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -1820128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := 126624, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := -2112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 4384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := 41984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := -241184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := -407968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := 48256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := 7264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := -12192, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := 424064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := -338272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := 640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := -1024, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := 34752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := -896, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := -18688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := 38336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := -192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := 10240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -32576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 483904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := 227904, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -4588224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 3147776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := -152704, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := 64, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := -11328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := 11104, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := -202560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := 219104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := 64576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := -55936, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := 39040, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := 2880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := -2272, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 15040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := 175648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := -817216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := 1667488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := -1789376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := 125184, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := -5696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := 25792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := -33408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := -6912, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := 173248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := 608, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -2304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := -86432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := 227456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := -28576, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := 3072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := -9216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -1920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 64, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := -384, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := 17088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := -1280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := -4160, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := 192384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := -181952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := 9408, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := 96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := -1216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := 1760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := 27456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := -127968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := 207552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := -114528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -17728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := 6240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -12000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 40832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := 6336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 7168, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -37952, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := 67840, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := -345024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := 384, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := -38400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := 13440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := -7680, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -207744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := 528384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := -85632, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -6400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 15424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -45376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 86528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -60224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 24960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -30720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := -48000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := 163328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 1664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -768, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := 19840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := 1, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := 1, den := 476, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11],[r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23],[r12,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33],[r34,r35,r36,r37,r38,r39,r40,r41,r42,r43],[r34,r44,r45,r46,r47,r48,r49,r50,r51],[r52,r53,r54,r55,r56,8320,r57,r58],[r52,r59,r60,512,r61,r62,r63],[r64,r65,r65,r66,r67,r68],[r64,r69,r70,r71,r72],[],[],[],[],[r73,r74,r75,r76,r77,r78,-32000,r79,r80,r81,r82],[r83,r84,r85,r86,r87,r88,r89,r90,r91,r92],[r93,r94,r95,r96,r97,r98,r99,r100,r101],[0,r102,r103,r104,r105,r106,r107,-2432],[r52,r59,r108,r109,r110,r111,r112],[0,r113,r114,r115,r116,512],[r64,r69,r117,r109,128],[],[],[],[],[r64,r118,r119,r120,r121,r122,r123,r124,r125],[r126,r127,r128,r129,r130,r131,r132,r133],[r126,r134,r135,r115,r136,r137,-576],[r64,r65,r65,r66,r67,r68],[r64,r69,r117,r109,128],[],[],[],[],[r138,r139,r140,r141,r142,r143,r144],[],[r64,r69,r70,r71,r72],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,r145,r146,r147,r148,r149,r150,r151,r152,5376],[r64,r118,r153,r154,r155,r156,r157,r158,384],[0,r102,r155,r159,r160,r161,r162,-2304],[],[0,r113,r114,r115,r116,512],[],[],[],[],[],[0,0,r34,r163,r164,r165,r166,-256],[r126,r134,r135,r115,r136,r137,-576],[],[r64,r69,r117,r109,128],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,r167,r168,r169,r170,r171,r172,r173,r174,r175,r176,r177,r178]),(⟨0,0,1⟩,[r179,r180,r181,r182,r183,r184,r185,r186,r187,r188,r189,r190]),(⟨0,0,2⟩,[r179,r191,r192,r193,r194,r195,r196,r197,r198,r199,r200]),(⟨0,0,3⟩,[r64,r118,r201,r202,r203,r204,r205,r206,r207,r117]),(⟨0,0,4⟩,[r64,r208,r209,r210,r211,r212,r213,r214,r215]),(⟨0,0,5⟩,[r216,r217,r218,r219,r220,4160,r221,r222]),(⟨0,0,6⟩,[r216,r127,r223,256,r224,r225,r226]),(⟨0,0,7⟩,[r83,r227,r227,r228,r229,r230]),(⟨0,0,8⟩,[r83,r102,r73,r231,r232]),(⟨0,1,0⟩,[r179,r180,r181,r182,r183,r184,r185,r186,r187,r188,r189,r190]),(⟨0,1,1⟩,[r12,r233,r234,r235,r103,r236,-16000,r237,r238,r239,r240]),(⟨0,1,2⟩,[r241,r242,r243,r244,r245,r246,r247,r248,r249,r250]),(⟨0,1,3⟩,[r251,r252,r253,r254,r255,r256,r257,r258,r259]),(⟨0,1,4⟩,[0,r138,r260,r261,r262,r263,r264,-1216]),(⟨0,1,5⟩,[r216,r127,r265,r266,r267,r268,r269]),(⟨0,1,6⟩,[0,r34,r270,r43,r271,256]),(⟨0,1,7⟩,[r83,r102,r272,r266,64]),(⟨0,2,0⟩,[r179,r191,r192,r193,r194,r195,r196,r197,r198,r199,r200]),(⟨0,2,1⟩,[r241,r242,r243,r244,r245,r246,r247,r248,r249,r250]),(⟨0,2,2⟩,[r83,r273,r274,r275,r276,r277,r278,r279,r280]),(⟨0,2,3⟩,[r281,r282,r283,r284,r285,r286,r287,r288]),(⟨0,2,4⟩,[r281,r13,r289,r43,r290,r291,-288]),(⟨0,2,5⟩,[r83,r227,r227,r228,r229,r230]),(⟨0,2,6⟩,[r83,r102,r272,r266,64]),(⟨0,3,0⟩,[r64,r118,r201,r202,r203,r204,r205,r206,r207,r117]),(⟨0,3,1⟩,[r251,r252,r253,r254,r255,r256,r257,r258,r259]),(⟨0,3,2⟩,[r281,r282,r283,r284,r285,r286,r287,r288]),(⟨0,3,3⟩,[r126,r134,r292,r293,r294,r295,r296]),(⟨0,3,5⟩,[r83,r102,r73,r231,r232]),(⟨0,4,0⟩,[r64,r208,r209,r210,r211,r212,r213,r214,r215]),(⟨0,4,1⟩,[0,r138,r260,r261,r262,r263,r264,-1216]),(⟨0,4,2⟩,[r281,r13,r289,r43,r290,r291,-288]),(⟨0,5,0⟩,[r216,r217,r218,r219,r220,4160,r221,r222]),(⟨0,5,1⟩,[r216,r127,r265,r266,r267,r268,r269]),(⟨0,5,2⟩,[r83,r227,r227,r228,r229,r230]),(⟨0,5,3⟩,[r83,r102,r73,r231,r232]),(⟨0,6,0⟩,[r216,r127,r223,256,r224,r225,r226]),(⟨0,6,1⟩,[0,r34,r270,r43,r271,256]),(⟨0,6,2⟩,[r83,r102,r272,r266,64]),(⟨0,7,0⟩,[r83,r227,r227,r228,r229,r230]),(⟨0,7,1⟩,[r83,r102,r272,r266,64]),(⟨0,8,0⟩,[r83,r102,r73,r231,r232]),(⟨1,0,0⟩,[r179,r180,r181,r182,r183,r184,r185,r186,r187,r188,r189,r190]),(⟨1,0,1⟩,[r12,r233,r234,r235,r103,r236,-16000,r237,r238,r239,r240]),(⟨1,0,2⟩,[r241,r242,r243,r244,r245,r246,r247,r248,r249,r250]),(⟨1,0,3⟩,[r251,r252,r253,r254,r255,r256,r257,r258,r259]),(⟨1,0,4⟩,[0,r138,r260,r261,r262,r263,r264,-1216]),(⟨1,0,5⟩,[r216,r127,r265,r266,r267,r268,r269]),(⟨1,0,6⟩,[0,r34,r270,r43,r271,256]),(⟨1,0,7⟩,[r83,r102,r272,r266,64]),(⟨1,1,0⟩,[r12,r233,r234,r235,r103,r236,-16000,r237,r238,r239,r240]),(⟨1,1,1⟩,[0,r297,r298,r299,r300,r301,r302,r303,r304,2688]),(⟨1,1,2⟩,[r83,r273,r305,r306,r139,r307,r308,r309,192]),(⟨1,1,3⟩,[0,r138,r139,r310,r311,r312,r313,-1152]),(⟨1,1,5⟩,[0,r34,r270,r43,r271,256]),(⟨1,2,0⟩,[r241,r242,r243,r244,r245,r246,r247,r248,r249,r250]),(⟨1,2,1⟩,[r83,r273,r305,r306,r139,r307,r308,r309,192]),(⟨1,2,2⟩,[0,0,r64,r314,r315,r145,r316,-128]),(⟨1,2,3⟩,[r281,r13,r289,r43,r290,r291,-288]),(⟨1,2,5⟩,[r83,r102,r272,r266,64]),(⟨1,3,0⟩,[r251,r252,r253,r254,r255,r256,r257,r258,r259]),(⟨1,3,1⟩,[0,r138,r139,r310,r311,r312,r313,-1152]),(⟨1,3,2⟩,[r281,r13,r289,r43,r290,r291,-288]),(⟨1,4,0⟩,[0,r138,r260,r261,r262,r263,r264,-1216]),(⟨1,5,0⟩,[r216,r127,r265,r266,r267,r268,r269]),(⟨1,5,1⟩,[0,r34,r270,r43,r271,256]),(⟨1,5,2⟩,[r83,r102,r272,r266,64]),(⟨1,6,0⟩,[0,r34,r270,r43,r271,256]),(⟨1,7,0⟩,[r83,r102,r272,r266,64]),(⟨2,0,0⟩,[r179,r191,r192,r193,r194,r195,r196,r197,r198,r199,r200]),(⟨2,0,1⟩,[r241,r242,r243,r244,r245,r246,r247,r248,r249,r250]),(⟨2,0,2⟩,[r83,r273,r274,r275,r276,r277,r278,r279,r280]),(⟨2,0,3⟩,[r281,r282,r283,r284,r285,r286,r287,r288]),(⟨2,0,4⟩,[r281,r13,r289,r43,r290,r291,-288]),(⟨2,0,5⟩,[r83,r227,r227,r228,r229,r230]),(⟨2,0,6⟩,[r83,r102,r272,r266,64]),(⟨2,1,0⟩,[r241,r242,r243,r244,r245,r246,r247,r248,r249,r250]),(⟨2,1,1⟩,[r83,r273,r305,r306,r139,r307,r308,r309,192]),(⟨2,1,2⟩,[0,0,r64,r314,r315,r145,r316,-128]),(⟨2,1,3⟩,[r281,r13,r289,r43,r290,r291,-288]),(⟨2,1,5⟩,[r83,r102,r272,r266,64]),(⟨2,2,0⟩,[r83,r273,r274,r275,r276,r277,r278,r279,r280]),(⟨2,2,1⟩,[0,0,r64,r314,r315,r145,r316,-128]),(⟨2,3,0⟩,[r281,r282,r283,r284,r285,r286,r287,r288]),(⟨2,3,1⟩,[r281,r13,r289,r43,r290,r291,-288]),(⟨2,4,0⟩,[r281,r13,r289,r43,r290,r291,-288]),(⟨2,5,0⟩,[r83,r227,r227,r228,r229,r230]),(⟨2,5,1⟩,[r83,r102,r272,r266,64]),(⟨2,6,0⟩,[r83,r102,r272,r266,64]),(⟨3,0,0⟩,[r64,r118,r201,r202,r203,r204,r205,r206,r207,r117]),(⟨3,0,1⟩,[r251,r252,r253,r254,r255,r256,r257,r258,r259]),(⟨3,0,2⟩,[r281,r282,r283,r284,r285,r286,r287,r288]),(⟨3,0,3⟩,[r126,r134,r292,r293,r294,r295,r296]),(⟨3,0,5⟩,[r83,r102,r73,r231,r232]),(⟨3,1,0⟩,[r251,r252,r253,r254,r255,r256,r257,r258,r259]),(⟨3,1,1⟩,[0,r138,r139,r310,r311,r312,r313,-1152]),(⟨3,1,2⟩,[r281,r13,r289,r43,r290,r291,-288]),(⟨3,2,0⟩,[r281,r282,r283,r284,r285,r286,r287,r288]),(⟨3,2,1⟩,[r281,r13,r289,r43,r290,r291,-288]),(⟨3,3,0⟩,[r126,r134,r292,r293,r294,r295,r296]),(⟨3,5,0⟩,[r83,r102,r73,r231,r232]),(⟨4,0,0⟩,[r64,r208,r209,r210,r211,r212,r213,r214,r215]),(⟨4,0,1⟩,[0,r138,r260,r261,r262,r263,r264,-1216]),(⟨4,0,2⟩,[r281,r13,r289,r43,r290,r291,-288]),(⟨4,1,0⟩,[0,r138,r260,r261,r262,r263,r264,-1216]),(⟨4,2,0⟩,[r281,r13,r289,r43,r290,r291,-288]),(⟨5,0,0⟩,[r216,r217,r218,r219,r220,4160,r221,r222]),(⟨5,0,1⟩,[r216,r127,r265,r266,r267,r268,r269]),(⟨5,0,2⟩,[r83,r227,r227,r228,r229,r230]),(⟨5,0,3⟩,[r83,r102,r73,r231,r232]),(⟨5,1,0⟩,[r216,r127,r265,r266,r267,r268,r269]),(⟨5,1,1⟩,[0,r34,r270,r43,r271,256]),(⟨5,1,2⟩,[r83,r102,r272,r266,64]),(⟨5,2,0⟩,[r83,r227,r227,r228,r229,r230]),(⟨5,2,1⟩,[r83,r102,r272,r266,64]),(⟨5,3,0⟩,[r83,r102,r73,r231,r232]),(⟨6,0,0⟩,[r216,r127,r223,256,r224,r225,r226]),(⟨6,0,1⟩,[0,r34,r270,r43,r271,256]),(⟨6,0,2⟩,[r83,r102,r272,r266,64]),(⟨6,1,0⟩,[0,r34,r270,r43,r271,256]),(⟨6,2,0⟩,[r83,r102,r272,r266,64]),(⟨7,0,0⟩,[r83,r227,r227,r228,r229,r230]),(⟨7,0,1⟩,[r83,r102,r272,r266,64]),(⟨7,1,0⟩,[r83,r102,r272,r266,64]),(⟨8,0,0⟩,[r83,r102,r73,r231,r232])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,-3,15,-21,3,6]),(⟨0,0,1⟩,[1,-5,10,-11,7]),(⟨0,0,2⟩,[0,0,2,-2]),(⟨0,0,3⟩,[-3,8,-9]),(⟨0,0,5⟩,[2]),(⟨0,1,0⟩,[1,-5,10,-11,7]),(⟨0,2,0⟩,[0,0,2,-2]),(⟨0,3,0⟩,[-3,8,-9]),(⟨0,5,0⟩,[2]),(⟨1,0,0⟩,[1,-5,10,-11,7]),(⟨2,0,0⟩,[0,0,2,-2]),(⟨3,0,0⟩,[-3,8,-9]),(⟨5,0,0⟩,[2])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[128,-1792,5120,30720,-231808,574208,-567040,116736]),(⟨0,0,1⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨0,0,2⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨0,0,3⟩,[-128,1536,256,-37376,76672]),(⟨0,1,0⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨0,1,1⟩,[0,-512,6144,-15360,-18432,60928]),(⟨0,1,2⟩,[-128,1536,-3840,-4608,15232]),(⟨0,2,0⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨0,2,1⟩,[-128,1536,-3840,-4608,15232]),(⟨0,3,0⟩,[-128,1536,256,-37376,76672]),(⟨1,0,0⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨1,0,1⟩,[0,-512,6144,-15360,-18432,60928]),(⟨1,0,2⟩,[-128,1536,-3840,-4608,15232]),(⟨1,1,0⟩,[0,-512,6144,-15360,-18432,60928]),(⟨1,2,0⟩,[-128,1536,-3840,-4608,15232]),(⟨2,0,0⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨2,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨2,1,0⟩,[-128,1536,-3840,-4608,15232]),(⟨3,0,0⟩,[-128,1536,256,-37376,76672])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 1 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r317) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 3 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r318) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨5,0,0⟩,[2])]

noncomputable def partial12 : Poly := [(⟨5,0,0⟩,[256,-3584,10240,61440,-463616,1148416,-1134080,233472]),(⟨5,0,1⟩,[256,-4096,16384,21504,-297728,746496,-663040]),(⟨5,0,2⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨5,0,3⟩,[-256,3072,512,-74752,153344]),(⟨5,1,0⟩,[256,-4096,16384,21504,-297728,746496,-663040]),(⟨5,1,1⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨5,1,2⟩,[-256,3072,-7680,-9216,30464]),(⟨5,2,0⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨5,2,1⟩,[-256,3072,-7680,-9216,30464]),(⟨5,3,0⟩,[-256,3072,512,-74752,153344]),(⟨6,0,0⟩,[256,-4096,16384,21504,-297728,746496,-663040]),(⟨6,0,1⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨6,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨6,1,0⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨6,2,0⟩,[-256,3072,-7680,-9216,30464]),(⟨7,0,0⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨7,0,1⟩,[-256,3072,-7680,-9216,30464]),(⟨7,1,0⟩,[-256,3072,-7680,-9216,30464]),(⟨8,0,0⟩,[-256,3072,512,-74752,153344])]


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

noncomputable def partial8 : Poly := [(⟨0,5,0⟩,[256,-3584,10240,61440,-463616,1148416,-1134080,233472]),(⟨0,5,1⟩,[256,-4096,16384,21504,-297728,746496,-663040]),(⟨0,5,2⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨0,5,3⟩,[-256,3072,512,-74752,153344]),(⟨0,6,0⟩,[256,-4096,16384,21504,-297728,746496,-663040]),(⟨0,6,1⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨0,6,2⟩,[-256,3072,-7680,-9216,30464]),(⟨0,7,0⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨0,7,1⟩,[-256,3072,-7680,-9216,30464]),(⟨0,8,0⟩,[-256,3072,512,-74752,153344]),(⟨1,0,0⟩,[128,-2432,15360,-14208,-313600,1971584,-6058240,11458944,-14193024,11424256,-5253376,817152]),(⟨1,0,1⟩,[128,-2688,19712,-52096,-97280,1120640,-3747328,7102848,-8462976,6259456,-2320640]),(⟨1,0,2⟩,[-128,1920,-6400,-27008,241408,-713344,1149696,-1133696,624512,-87808]),(⟨1,0,3⟩,[-128,2176,-8704,-21888,248320,-749184,1179648,-1105024,536704]),(⟨1,1,0⟩,[128,-2688,19712,-52096,-97280,1120640,-3747328,7102848,-8462976,6259456,-2320640]),(⟨1,1,1⟩,[0,-512,8704,-51200,125440,-71680,-276992,704512,-799232,426496]),(⟨1,1,2⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨1,2,0⟩,[-128,1920,-6400,-27008,241408,-713344,1149696,-1133696,624512,-87808]),(⟨1,2,1⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨1,3,0⟩,[-128,2176,-8704,-21888,248320,-749184,1179648,-1105024,536704]),(⟨1,5,0⟩,[256,-4096,16384,21504,-297728,746496,-663040]),(⟨1,5,1⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨1,5,2⟩,[-256,3072,-7680,-9216,30464]),(⟨1,6,0⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨1,7,0⟩,[-256,3072,-7680,-9216,30464]),(⟨2,0,0⟩,[128,-2688,19968,-55936,-83456,1171840,-4272384,8714880,-10745472,7627008,-2554112]),(⟨2,0,1⟩,[0,-512,8960,-55552,145920,-66560,-596224,1748736,-2208768,1089536]),(⟨2,0,2⟩,[-128,2176,-13056,34176,-17920,-141440,384768,-363904,131712]),(⟨2,0,3⟩,[0,0,-256,3328,-2560,-75264,228096,-153344]),(⟨2,1,0⟩,[0,-512,8960,-55552,145920,-66560,-596224,1748736,-2208768,1089536]),(⟨2,1,1⟩,[0,0,0,-1024,13312,-43008,-6144,158720,-121856]),(⟨2,1,2⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨2,2,0⟩,[-128,2176,-13056,34176,-17920,-141440,384768,-363904,131712]),(⟨2,2,1⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨2,3,0⟩,[0,0,-256,3328,-2560,-75264,228096,-153344]),(⟨2,5,0⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨2,5,1⟩,[-256,3072,-7680,-9216,30464]),(⟨2,6,0⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[-512,8320,-36992,-66432,1156992,-4561792,9211520,-10143872,5252224,-475392]),(⟨3,0,1⟩,[-512,9344,-54912,82048,454272,-2519680,5490304,-6052480,2968448]),(⟨3,0,2⟩,[384,-4864,7296,106496,-509312,905472,-686208,82432]),(⟨3,0,3⟩,[384,-5632,12672,100352,-531328,949760,-690048]),(⟨3,1,0⟩,[-512,9344,-54912,82048,454272,-2519680,5490304,-6052480,2968448]),(⟨3,1,1⟩,[0,1536,-22528,99840,-122880,-192000,653312,-548352]),(⟨3,1,2⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨3,2,0⟩,[384,-4864,7296,106496,-509312,905472,-686208,82432]),(⟨3,2,1⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨3,3,0⟩,[384,-5632,12672,100352,-531328,949760,-690048]),(⟨3,5,0⟩,[-256,3072,512,-74752,153344]),(⟨4,0,0⟩,[-512,9344,-51072,32640,707200,-3228800,6708608,-7280512,3545472]),(⟨4,0,1⟩,[0,1536,-22784,103168,-133632,-193536,692992,-578816]),(⟨4,0,2⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨4,1,0⟩,[0,1536,-22784,103168,-133632,-193536,692992,-578816]),(⟨4,2,0⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨5,0,0⟩,[640,-8448,17536,167936,-964736,1980160,-1631872,193024]),(⟨5,0,1⟩,[640,-9728,41344,-9216,-345728,909824,-800128]),(⟨5,0,2⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨5,0,3⟩,[-256,3072,512,-74752,153344]),(⟨5,1,0⟩,[640,-9728,41344,-9216,-345728,909824,-800128]),(⟨5,1,1⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨5,1,2⟩,[-256,3072,-7680,-9216,30464]),(⟨5,2,0⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨5,2,1⟩,[-256,3072,-7680,-9216,30464]),(⟨5,3,0⟩,[-256,3072,512,-74752,153344]),(⟨6,0,0⟩,[640,-9728,29056,121856,-829056,1696256,-1353088]),(⟨6,0,1⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨6,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨6,1,0⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨6,2,0⟩,[-256,3072,-7680,-9216,30464]),(⟨7,0,0⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨7,0,1⟩,[-256,3072,-7680,-9216,30464]),(⟨7,1,0⟩,[-256,3072,-7680,-9216,30464]),(⟨8,0,0⟩,[-256,3072,512,-74752,153344])]


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

noncomputable def partial4 : Poly := [(⟨0,0,5⟩,[256,-3584,10240,61440,-463616,1148416,-1134080,233472]),(⟨0,0,6⟩,[256,-4096,16384,21504,-297728,746496,-663040]),(⟨0,0,7⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨0,0,8⟩,[-256,3072,512,-74752,153344]),(⟨0,1,0⟩,[128,-2432,15360,-14208,-313600,1971584,-6058240,11458944,-14193024,11424256,-5253376,817152]),(⟨0,1,1⟩,[128,-2688,19712,-52096,-97280,1120640,-3747328,7102848,-8462976,6259456,-2320640]),(⟨0,1,2⟩,[-128,1920,-6400,-27008,241408,-713344,1149696,-1133696,624512,-87808]),(⟨0,1,3⟩,[-128,2176,-8704,-21888,248320,-749184,1179648,-1105024,536704]),(⟨0,1,5⟩,[256,-4096,16384,21504,-297728,746496,-663040]),(⟨0,1,6⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨0,1,7⟩,[-256,3072,-7680,-9216,30464]),(⟨0,2,0⟩,[128,-2688,19968,-55936,-83456,1171840,-4272384,8714880,-10745472,7627008,-2554112]),(⟨0,2,1⟩,[0,-512,8960,-55552,145920,-66560,-596224,1748736,-2208768,1089536]),(⟨0,2,2⟩,[-128,2176,-13056,34176,-17920,-141440,384768,-363904,131712]),(⟨0,2,3⟩,[0,0,-256,3328,-2560,-75264,228096,-153344]),(⟨0,2,5⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨0,2,6⟩,[-256,3072,-7680,-9216,30464]),(⟨0,3,0⟩,[-512,8320,-36992,-66432,1156992,-4561792,9211520,-10143872,5252224,-475392]),(⟨0,3,1⟩,[-512,9344,-54912,82048,454272,-2519680,5490304,-6052480,2968448]),(⟨0,3,2⟩,[384,-4864,7296,106496,-509312,905472,-686208,82432]),(⟨0,3,3⟩,[384,-5632,12672,100352,-531328,949760,-690048]),(⟨0,3,5⟩,[-256,3072,512,-74752,153344]),(⟨0,4,0⟩,[-512,9344,-51072,32640,707200,-3228800,6708608,-7280512,3545472]),(⟨0,4,1⟩,[0,1536,-22784,103168,-133632,-193536,692992,-578816]),(⟨0,4,2⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨0,5,0⟩,[640,-8448,17536,167936,-964736,1980160,-1631872,193024]),(⟨0,5,1⟩,[640,-9728,41344,-9216,-345728,909824,-800128]),(⟨0,5,2⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨0,5,3⟩,[-256,3072,512,-74752,153344]),(⟨0,6,0⟩,[640,-9728,29056,121856,-829056,1696256,-1353088]),(⟨0,6,1⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨0,6,2⟩,[-256,3072,-7680,-9216,30464]),(⟨0,7,0⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨0,7,1⟩,[-256,3072,-7680,-9216,30464]),(⟨0,8,0⟩,[-256,3072,512,-74752,153344]),(⟨1,0,0⟩,[128,-2432,15360,-14208,-313600,1971584,-6058240,11458944,-14193024,11424256,-5253376,817152]),(⟨1,0,1⟩,[128,-2688,19712,-52096,-97280,1120640,-3747328,7102848,-8462976,6259456,-2320640]),(⟨1,0,2⟩,[-128,1920,-6400,-27008,241408,-713344,1149696,-1133696,624512,-87808]),(⟨1,0,3⟩,[-128,2176,-8704,-21888,248320,-749184,1179648,-1105024,536704]),(⟨1,0,5⟩,[256,-4096,16384,21504,-297728,746496,-663040]),(⟨1,0,6⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨1,0,7⟩,[-256,3072,-7680,-9216,30464]),(⟨1,1,0⟩,[256,-5376,39424,-104192,-194560,2241280,-7494656,14205696,-16925952,12518912,-4641280]),(⟨1,1,1⟩,[0,-1024,17408,-102400,250880,-143360,-553984,1409024,-1598464,852992]),(⟨1,1,2⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨1,1,5⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨1,2,0⟩,[-128,1408,2560,-82560,387328,-779904,553472,615040,-1584256,1001728]),(⟨1,2,1⟩,[-128,2176,-12800,30336,-4608,-112256,169984,-41088,-15232]),(⟨1,2,2⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨1,2,5⟩,[-256,3072,-7680,-9216,30464]),(⟨1,3,0⟩,[-640,11520,-63616,60160,702592,-3268864,6669952,-7157504,3505152]),(⟨1,3,1⟩,[0,1536,-22528,99840,-122880,-192000,653312,-548352]),(⟨1,3,2⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨1,4,0⟩,[0,1536,-22784,103168,-133632,-193536,692992,-578816]),(⟨1,5,0⟩,[640,-9728,41344,-9216,-345728,909824,-800128]),(⟨1,5,1⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨1,5,2⟩,[-256,3072,-7680,-9216,30464]),(⟨1,6,0⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨1,7,0⟩,[-256,3072,-7680,-9216,30464]),(⟨2,0,0⟩,[128,-2688,19968,-55936,-83456,1171840,-4272384,8714880,-10745472,7627008,-2554112]),(⟨2,0,1⟩,[0,-512,8960,-55552,145920,-66560,-596224,1748736,-2208768,1089536]),(⟨2,0,2⟩,[-128,2176,-13056,34176,-17920,-141440,384768,-363904,131712]),(⟨2,0,3⟩,[0,0,-256,3328,-2560,-75264,228096,-153344]),(⟨2,0,5⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨2,0,6⟩,[-256,3072,-7680,-9216,30464]),(⟨2,1,0⟩,[-128,1408,2560,-82560,387328,-779904,553472,615040,-1584256,1001728]),(⟨2,1,1⟩,[-128,2176,-12800,30336,-4608,-112256,169984,-41088,-15232]),(⟨2,1,2⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨2,1,5⟩,[-256,3072,-7680,-9216,30464]),(⟨2,2,0⟩,[-256,4352,-26112,68352,-35840,-282880,769536,-727808,263424]),(⟨2,2,1⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨2,3,0⟩,[384,-4864,7040,109824,-511872,830208,-458112,-70912]),(⟨2,3,1⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨2,4,0⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨2,5,0⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨2,5,1⟩,[-256,3072,-7680,-9216,30464]),(⟨2,6,0⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[-512,8320,-36992,-66432,1156992,-4561792,9211520,-10143872,5252224,-475392]),(⟨3,0,1⟩,[-512,9344,-54912,82048,454272,-2519680,5490304,-6052480,2968448]),(⟨3,0,2⟩,[384,-4864,7296,106496,-509312,905472,-686208,82432]),(⟨3,0,3⟩,[384,-5632,12672,100352,-531328,949760,-690048]),(⟨3,0,5⟩,[-256,3072,512,-74752,153344]),(⟨3,1,0⟩,[-640,11520,-63616,60160,702592,-3268864,6669952,-7157504,3505152]),(⟨3,1,1⟩,[0,1536,-22528,99840,-122880,-192000,653312,-548352]),(⟨3,1,2⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨3,2,0⟩,[384,-4864,7040,109824,-511872,830208,-458112,-70912]),(⟨3,2,1⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨3,3,0⟩,[768,-11264,25344,200704,-1062656,1899520,-1380096]),(⟨3,5,0⟩,[-256,3072,512,-74752,153344]),(⟨4,0,0⟩,[-512,9344,-51072,32640,707200,-3228800,6708608,-7280512,3545472]),(⟨4,0,1⟩,[0,1536,-22784,103168,-133632,-193536,692992,-578816]),(⟨4,0,2⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨4,1,0⟩,[0,1536,-22784,103168,-133632,-193536,692992,-578816]),(⟨4,2,0⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨5,0,0⟩,[640,-8448,17536,167936,-964736,1980160,-1631872,193024]),(⟨5,0,1⟩,[640,-9728,41344,-9216,-345728,909824,-800128]),(⟨5,0,2⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨5,0,3⟩,[-256,3072,512,-74752,153344]),(⟨5,1,0⟩,[640,-9728,41344,-9216,-345728,909824,-800128]),(⟨5,1,1⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨5,1,2⟩,[-256,3072,-7680,-9216,30464]),(⟨5,2,0⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨5,2,1⟩,[-256,3072,-7680,-9216,30464]),(⟨5,3,0⟩,[-256,3072,512,-74752,153344]),(⟨6,0,0⟩,[640,-9728,29056,121856,-829056,1696256,-1353088]),(⟨6,0,1⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨6,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨6,1,0⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨6,2,0⟩,[-256,3072,-7680,-9216,30464]),(⟨7,0,0⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨7,0,1⟩,[-256,3072,-7680,-9216,30464]),(⟨7,1,0⟩,[-256,3072,-7680,-9216,30464]),(⟨8,0,0⟩,[-256,3072,512,-74752,153344])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,-384,7296,-44928,22656,1044096,-5840256,15305088,-21425280,13990656,-707328,-3052032,700416]),(⟨0,0,1⟩,[128,-2816,23424,-72192,-179584,2402048,-9624448,21259776,-27386112,18612736,-4008448,-1171968]),(⟨0,0,2⟩,[128,-2304,14208,-37888,12928,417280,-2449536,6970368,-10482432,8006400,-2629376]),(⟨0,0,3⟩,[-512,8704,-43520,-41472,1240320,-5353984,11156480,-11864576,5257984,-15360]),(⟨0,0,4⟩,[-512,9344,-51072,32640,707200,-3228800,6708608,-7280512,3545472]),(⟨0,0,5⟩,[640,-8448,17536,167936,-964736,1980160,-1631872,193024]),(⟨0,0,6⟩,[640,-9728,29056,121856,-829056,1696256,-1353088]),(⟨0,0,7⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨0,0,8⟩,[-256,3072,512,-74752,153344]),(⟨0,1,0⟩,[128,-2816,23424,-72192,-179584,2402048,-9624448,21259776,-27386112,18612736,-4008448,-1171968]),(⟨0,1,1⟩,[256,-5376,40960,-130304,-45568,1935616,-7616000,15497472,-18352896,12591104,-4275712]),(⟨0,1,2⟩,[-128,1792,-3968,-45312,310912,-810240,876416,258304,-1566208,1093120]),(⟨0,1,3⟩,[-640,11520,-63616,60160,702592,-3268864,6669952,-7157504,3505152]),(⟨0,1,4⟩,[0,1536,-22784,103168,-133632,-193536,692992,-578816]),(⟨0,1,5⟩,[640,-9728,41344,-9216,-345728,909824,-800128]),(⟨0,1,6⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨0,1,7⟩,[-256,3072,-7680,-9216,30464]),(⟨0,2,0⟩,[128,-2304,14208,-37888,12928,417280,-2449536,6970368,-10482432,8006400,-2629376]),(⟨0,2,1⟩,[-128,1792,-3968,-45312,310912,-810240,876416,258304,-1566208,1093120]),(⟨0,2,2⟩,[-256,4352,-26112,68352,-35840,-282880,769536,-727808,263424]),(⟨0,2,3⟩,[384,-4864,7040,109824,-511872,830208,-458112,-70912]),(⟨0,2,4⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨0,2,5⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨0,2,6⟩,[-256,3072,-7680,-9216,30464]),(⟨0,3,0⟩,[-512,8704,-43520,-41472,1240320,-5353984,11156480,-11864576,5257984,-15360]),(⟨0,3,1⟩,[-640,11520,-63616,60160,702592,-3268864,6669952,-7157504,3505152]),(⟨0,3,2⟩,[384,-4864,7040,109824,-511872,830208,-458112,-70912]),(⟨0,3,3⟩,[768,-11264,25344,200704,-1062656,1899520,-1380096]),(⟨0,3,5⟩,[-256,3072,512,-74752,153344]),(⟨0,4,0⟩,[-512,9344,-51072,32640,707200,-3228800,6708608,-7280512,3545472]),(⟨0,4,1⟩,[0,1536,-22784,103168,-133632,-193536,692992,-578816]),(⟨0,4,2⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨0,5,0⟩,[640,-8448,17536,167936,-964736,1980160,-1631872,193024]),(⟨0,5,1⟩,[640,-9728,41344,-9216,-345728,909824,-800128]),(⟨0,5,2⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨0,5,3⟩,[-256,3072,512,-74752,153344]),(⟨0,6,0⟩,[640,-9728,29056,121856,-829056,1696256,-1353088]),(⟨0,6,1⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨0,6,2⟩,[-256,3072,-7680,-9216,30464]),(⟨0,7,0⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨0,7,1⟩,[-256,3072,-7680,-9216,30464]),(⟨0,8,0⟩,[-256,3072,512,-74752,153344]),(⟨1,0,0⟩,[128,-2816,23424,-72192,-179584,2402048,-9624448,21259776,-27386112,18612736,-4008448,-1171968]),(⟨1,0,1⟩,[256,-5376,40960,-130304,-45568,1935616,-7616000,15497472,-18352896,12591104,-4275712]),(⟨1,0,2⟩,[-128,1792,-3968,-45312,310912,-810240,876416,258304,-1566208,1093120]),(⟨1,0,3⟩,[-640,11520,-63616,60160,702592,-3268864,6669952,-7157504,3505152]),(⟨1,0,4⟩,[0,1536,-22784,103168,-133632,-193536,692992,-578816]),(⟨1,0,5⟩,[640,-9728,41344,-9216,-345728,909824,-800128]),(⟨1,0,6⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨1,0,7⟩,[-256,3072,-7680,-9216,30464]),(⟨1,1,0⟩,[256,-5376,40960,-130304,-45568,1935616,-7616000,15497472,-18352896,12591104,-4275712]),(⟨1,1,1⟩,[0,-1536,26112,-153600,376320,-215040,-830976,2113536,-2397696,1279488]),(⟨1,1,2⟩,[-256,4352,-25600,61696,-22528,-181504,346112,-240896,91392]),(⟨1,1,3⟩,[0,1536,-22528,99840,-122880,-192000,653312,-548352]),(⟨1,1,5⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨1,2,0⟩,[-128,1792,-3968,-45312,310912,-810240,876416,258304,-1566208,1093120]),(⟨1,2,1⟩,[-256,4352,-25600,61696,-22528,-181504,346112,-240896,91392]),(⟨1,2,2⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨1,2,3⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨1,2,5⟩,[-256,3072,-7680,-9216,30464]),(⟨1,3,0⟩,[-640,11520,-63616,60160,702592,-3268864,6669952,-7157504,3505152]),(⟨1,3,1⟩,[0,1536,-22528,99840,-122880,-192000,653312,-548352]),(⟨1,3,2⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨1,4,0⟩,[0,1536,-22784,103168,-133632,-193536,692992,-578816]),(⟨1,5,0⟩,[640,-9728,41344,-9216,-345728,909824,-800128]),(⟨1,5,1⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨1,5,2⟩,[-256,3072,-7680,-9216,30464]),(⟨1,6,0⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨1,7,0⟩,[-256,3072,-7680,-9216,30464]),(⟨2,0,0⟩,[128,-2304,14208,-37888,12928,417280,-2449536,6970368,-10482432,8006400,-2629376]),(⟨2,0,1⟩,[-128,1792,-3968,-45312,310912,-810240,876416,258304,-1566208,1093120]),(⟨2,0,2⟩,[-256,4352,-26112,68352,-35840,-282880,769536,-727808,263424]),(⟨2,0,3⟩,[384,-4864,7040,109824,-511872,830208,-458112,-70912]),(⟨2,0,4⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨2,0,5⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨2,0,6⟩,[-256,3072,-7680,-9216,30464]),(⟨2,1,0⟩,[-128,1792,-3968,-45312,310912,-810240,876416,258304,-1566208,1093120]),(⟨2,1,1⟩,[-256,4352,-25600,61696,-22528,-181504,346112,-240896,91392]),(⟨2,1,2⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨2,1,3⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨2,1,5⟩,[-256,3072,-7680,-9216,30464]),(⟨2,2,0⟩,[-256,4352,-26112,68352,-35840,-282880,769536,-727808,263424]),(⟨2,2,1⟩,[0,0,-512,6656,-21504,-3072,79360,-60928]),(⟨2,3,0⟩,[384,-4864,7040,109824,-511872,830208,-458112,-70912]),(⟨2,3,1⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨2,4,0⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨2,5,0⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨2,5,1⟩,[-256,3072,-7680,-9216,30464]),(⟨2,6,0⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[-512,8704,-43520,-41472,1240320,-5353984,11156480,-11864576,5257984,-15360]),(⟨3,0,1⟩,[-640,11520,-63616,60160,702592,-3268864,6669952,-7157504,3505152]),(⟨3,0,2⟩,[384,-4864,7040,109824,-511872,830208,-458112,-70912]),(⟨3,0,3⟩,[768,-11264,25344,200704,-1062656,1899520,-1380096]),(⟨3,0,5⟩,[-256,3072,512,-74752,153344]),(⟨3,1,0⟩,[-640,11520,-63616,60160,702592,-3268864,6669952,-7157504,3505152]),(⟨3,1,1⟩,[0,1536,-22528,99840,-122880,-192000,653312,-548352]),(⟨3,1,2⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨3,2,0⟩,[384,-4864,7040,109824,-511872,830208,-458112,-70912]),(⟨3,2,1⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨3,3,0⟩,[768,-11264,25344,200704,-1062656,1899520,-1380096]),(⟨3,5,0⟩,[-256,3072,512,-74752,153344]),(⟨4,0,0⟩,[-512,9344,-51072,32640,707200,-3228800,6708608,-7280512,3545472]),(⟨4,0,1⟩,[0,1536,-22784,103168,-133632,-193536,692992,-578816]),(⟨4,0,2⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨4,1,0⟩,[0,1536,-22784,103168,-133632,-193536,692992,-578816]),(⟨4,2,0⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨5,0,0⟩,[640,-8448,17536,167936,-964736,1980160,-1631872,193024]),(⟨5,0,1⟩,[640,-9728,41344,-9216,-345728,909824,-800128]),(⟨5,0,2⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨5,0,3⟩,[-256,3072,512,-74752,153344]),(⟨5,1,0⟩,[640,-9728,41344,-9216,-345728,909824,-800128]),(⟨5,1,1⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨5,1,2⟩,[-256,3072,-7680,-9216,30464]),(⟨5,2,0⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨5,2,1⟩,[-256,3072,-7680,-9216,30464]),(⟨5,3,0⟩,[-256,3072,512,-74752,153344]),(⟨6,0,0⟩,[640,-9728,29056,121856,-829056,1696256,-1353088]),(⟨6,0,1⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨6,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨6,1,0⟩,[0,-1024,12288,-30720,-36864,121856]),(⟨6,2,0⟩,[-256,3072,-7680,-9216,30464]),(⟨7,0,0⟩,[-256,2560,2560,-69632,139008,-25088]),(⟨7,0,1⟩,[-256,3072,-7680,-9216,30464]),(⟨7,1,0⟩,[-256,3072,-7680,-9216,30464]),(⟨8,0,0⟩,[-256,3072,512,-74752,153344])]


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
    (Poly.add (Poly.scale (K.ofRat r319) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 1 3).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r317*r318 : ℚ)=r319 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 1 3 r317 r318 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 1=3 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 1 3).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C061

#print axioms Coulomb8.Columns.C061.sound
