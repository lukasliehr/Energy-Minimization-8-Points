import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C052

def r0 : ℚ := { num := 192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -4320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 39072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -180864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 401088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 15168, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -491904, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 10787712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -17541120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 14845728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -3275040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -3205632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 136320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 1600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -17184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 102528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -50112, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 520512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 953600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -1006912, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 18147456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -26348416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 20800544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -5583808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := -256000, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 2144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -19616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 14304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -300672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 352384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 1100672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -6138880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 14088416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -18614752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 13288224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -477408, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -2944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 20064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -56832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -12416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 588288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -1853568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 2608128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -669728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -3125376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 454880, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -5856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 43136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -140480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 111040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 107008, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -3083648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := 5676992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -5356000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 245536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 9536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -54976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 156992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -953152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 1838784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -210464, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := -192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := 448, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := -1984, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 5696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 87744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -41664, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 472128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := 1280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := -6336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := 2560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 43072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -131840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 25920, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := 256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := -19968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := 118336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := -55936, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := 563456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 865280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -6321536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 15385024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -20566016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 2047488, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := -524608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -32, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := -3232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := 43712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -206144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 26240, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -110400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := -1945024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 5377056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -6683296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 498720, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -2208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 2496, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -58432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 33792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 401280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -1552960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 2735168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := -2340448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 81376, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -1728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := 15488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := -58816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := 78464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 145344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -844160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 219456, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -153664, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := -256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := 512, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := -15616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := 27648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := -4864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -17920, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := -2304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := 2048, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -34432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := -2304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := 328064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := -956416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := 1476736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := -172672, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := 24192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := -4416, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := 11264, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 16960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -353216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := 696000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -80736, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -17728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 49216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := -67520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := 78784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 1984, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -1024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 320, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -1536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := -3392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 6656, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := -128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := 1664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -768, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := -768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := 19840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := -3840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -4608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -2560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := -11264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := 84992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := -251392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 466432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := -40960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -8192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 39680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -85248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := 18304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := -7296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := 7680, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := -12288, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := 452352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -48384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := -987648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := 3256320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := -545664, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := 15872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := -57600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := 112384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := -43776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -48640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 123648, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := 3840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := -19200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := 43264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -32512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := -120576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := 48384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := -64, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := 6336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := -14528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := 1984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -80064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := -2048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := 640, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := -3072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -6784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := 13312, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := 3328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := -1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -2160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := 19536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := -90432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := 200544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 7584, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -245952, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := 5393856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := -8770560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := 7422864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := -1637520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -1602816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := 68160, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := -8592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := 51264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := -25056, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := 260256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 476800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -503456, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 9073728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := -13174208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := 10400272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := -2791904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := -128000, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := -48, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := 1072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -9808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 7152, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -150336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := 176192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 550336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := -3069440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := 7044208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := -9307376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := 6644112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := -238704, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := 80, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := -1472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := 10032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := -28416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := -6208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := 294144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -926784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := 1304064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := -334864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := -1562688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := 227440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := 144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -2928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := 21568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -70240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 55520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := 53504, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := -1541824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := 2838496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := -2678000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := 122768, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -16, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := -160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := 4768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := -27488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := 78496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := -476576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := 919392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := -105232, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := 224, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := -992, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := 2848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := 43872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := -20832, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := 236064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := 640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := -3168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := 21536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -65920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := 12960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := 128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := -9984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := 59168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -27968, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := 281728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := 432640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := -3160768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := 7692512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := -10283008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := 1023744, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := -262304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := 16, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -16, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := -1616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := 21856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := -103072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := 13120, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -55200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := -972512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := 2688528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -3341648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 249360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := 48, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := -1104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := 1248, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := -29216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := 16896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 200640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := -776480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 1367584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -1170224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := 40688, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := -864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := 7744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := -29408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := 39232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := 72672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := -422080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := 109728, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -76832, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := -7808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := 13824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := -2432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := -8960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := -1152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := 1024, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := -17216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -1152, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 164032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -478208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 738368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -86336, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 12096, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := 480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := -2208, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := 5632, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := 8480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := -176608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := 348000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := -40368, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := 352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := -8864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := 24608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := -33760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := 39392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := 992, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := -512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := 160, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := -1696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := 3328, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := 832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := -384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := 9920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := 768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := -1920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := -1280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := -5632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := 42496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := -125696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := 233216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := -20480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := -64, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := -4096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := -42624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := 9152, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := -3648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := 3840, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := -6144, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := 226176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := -24192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := -493824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := 1628160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := -272832, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := 7936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := -28800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := 56192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := -21888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := -24320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := 61824, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := 1920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := -9600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := 21632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := -16256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := -60288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := -32, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := 3168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := -7264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := -40032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := 1, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := 1, den := 476, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12],[r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25],[r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37],[r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48],[r49,r50,r51,r52,r53,r54,r55,r56,r57,r58],[r59,r60,r61,r62,768,r63,r64,r65,r66],[r67,r68,r69,r70,r71,r72,r73,-1728],[r13,r74,r75,r76,r77,r78,r79],[],[],[],[],[],[r13,r80,r81,r82,r83,r84,r85,r86,r87,r88,r89,r90],[r91,r92,r93,r94,r95,r96,r97,r98,r99,r100,r101],[r102,r103,r104,r105,r106,r107,r108,r109,r110,r111],[r112,r113,r114,r115,r116,r117,r118,r119,r120],[0,r121,r122,r123,r124,r125,r126,1792],[],[],[],[],[],[],[r127,r128,r129,r130,r131,r132,r133,r134,r135,r136],[r26,r137,r137,r138,r139,r140,r141,r142,r143],[r13,r144,r112,r145,r146,r147,r148,r149],[r112,r150,r151,r152,r153,r154,-448],[r155,r156,r157,r158,r159,-128],[r155,r160,r161,r162,128],[],[],[],[0,r163,r164,r165,r166,r167,r168,r169],[0,r170,r171,r172,r173,r174,r175],[r155,r156,r157,r158,r159,-128],[r155,r160,r161,r162,128],[],[],[],[],[],[],[],[],[],[],[],[],[0,r176,r177,r178,r179,r180,r181,r182,r183,r184,13440],[0,r127,r128,r185,r186,r187,r188,r189,r190,-6272],[0,r121,r191,r192,r193,r194,r195,r196,-1792],[0,r121,r122,r123,r124,r125,r126,1792],[],[],[],[],[],[],[],[r112,r197,r198,r199,r200,r146,r201,320],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[r127,r202,r203,r204,r205,r206,-896],[],[],[],[],[],[r121,r207,r152,r208,r173,-256],[r155,r160,r161,r162,128],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,r102,r209,r210,r211,r212,r213,r214,r215,r216,r217,r218,r219,r220]),(⟨0,0,1⟩,[r59,r221,r222,r223,r224,r225,r226,r227,r228,r229,r230,r231,r232]),(⟨0,0,2⟩,[r233,r234,r235,r236,r237,r238,r239,r240,r241,r242,r243,r244]),(⟨0,0,3⟩,[r245,r246,r247,r248,r249,r250,r251,r252,r253,r254,r255]),(⟨0,0,4⟩,[r256,r257,r258,r259,r260,r261,r262,r263,r264,r265]),(⟨0,0,5⟩,[r266,r267,r268,r269,384,r270,r271,r272,r273]),(⟨0,0,6⟩,[r26,r274,r275,r276,r277,r278,r279,-864]),(⟨0,0,7⟩,[r59,r280,r281,r74,r282,r283,r284]),(⟨0,1,0⟩,[r59,r221,r222,r223,r224,r225,r226,r227,r228,r229,r230,r231,r232]),(⟨0,1,1⟩,[r59,r285,r286,r287,r288,r289,r290,r291,r292,r293,r294,r295]),(⟨0,1,2⟩,[r296,r297,r298,r299,r300,r301,r302,r303,r304,r305,r306]),(⟨0,1,3⟩,[r307,r308,r309,r310,r311,r312,r313,r314,r315,r316]),(⟨0,1,4⟩,[r91,r317,r318,r319,r320,r321,r322,r323,r324]),(⟨0,1,5⟩,[0,r155,r80,r325,r326,r327,r328,896]),(⟨0,2,0⟩,[r233,r234,r235,r236,r237,r238,r239,r240,r241,r242,r243,r244]),(⟨0,2,1⟩,[r296,r297,r298,r299,r300,r301,r302,r303,r304,r305,r306]),(⟨0,2,2⟩,[r112,r329,r330,r331,r332,r333,r334,r335,r336,r337]),(⟨0,2,3⟩,[r233,r338,r338,r339,r340,r341,r342,r343,r344]),(⟨0,2,4⟩,[r59,r345,r91,r346,r347,r348,r349,r350]),(⟨0,2,5⟩,[r91,r351,r352,r157,r353,r354,-224]),(⟨0,2,6⟩,[r13,r355,r356,r357,r358,-64]),(⟨0,2,7⟩,[r13,r359,r360,r128,64]),(⟨0,3,0⟩,[r245,r246,r247,r248,r249,r250,r251,r252,r253,r254,r255]),(⟨0,3,1⟩,[r307,r308,r309,r310,r311,r312,r313,r314,r315,r316]),(⟨0,3,2⟩,[r233,r338,r338,r339,r340,r341,r342,r343,r344]),(⟨0,3,3⟩,[0,r170,r361,r362,r363,r364,r365,r366]),(⟨0,3,4⟩,[0,r127,r367,r368,r159,r369,r370]),(⟨0,3,5⟩,[r13,r355,r356,r357,r358,-64]),(⟨0,3,6⟩,[r13,r359,r360,r128,64]),(⟨0,4,0⟩,[r256,r257,r258,r259,r260,r261,r262,r263,r264,r265]),(⟨0,4,1⟩,[r91,r317,r318,r319,r320,r321,r322,r323,r324]),(⟨0,4,2⟩,[r59,r345,r91,r346,r347,r348,r349,r350]),(⟨0,4,3⟩,[0,r127,r367,r368,r159,r369,r370]),(⟨0,5,0⟩,[r266,r267,r268,r269,384,r270,r271,r272,r273]),(⟨0,5,1⟩,[0,r155,r80,r325,r326,r327,r328,896]),(⟨0,5,2⟩,[r91,r351,r352,r157,r353,r354,-224]),(⟨0,5,3⟩,[r13,r355,r356,r357,r358,-64]),(⟨0,6,0⟩,[r26,r274,r275,r276,r277,r278,r279,-864]),(⟨0,6,2⟩,[r13,r355,r356,r357,r358,-64]),(⟨0,6,3⟩,[r13,r359,r360,r128,64]),(⟨0,7,0⟩,[r59,r280,r281,r74,r282,r283,r284]),(⟨0,7,2⟩,[r13,r359,r360,r128,64]),(⟨1,0,0⟩,[r59,r221,r222,r223,r224,r225,r226,r227,r228,r229,r230,r231,r232]),(⟨1,0,1⟩,[r59,r285,r286,r287,r288,r289,r290,r291,r292,r293,r294,r295]),(⟨1,0,2⟩,[r296,r297,r298,r299,r300,r301,r302,r303,r304,r305,r306]),(⟨1,0,3⟩,[r307,r308,r309,r310,r311,r312,r313,r314,r315,r316]),(⟨1,0,4⟩,[r91,r317,r318,r319,r320,r321,r322,r323,r324]),(⟨1,0,5⟩,[0,r155,r80,r325,r326,r327,r328,896]),(⟨1,1,0⟩,[r59,r285,r286,r287,r288,r289,r290,r291,r292,r293,r294,r295]),(⟨1,1,1⟩,[0,r0,r371,r372,r373,r374,r375,r376,r377,r378,6720]),(⟨1,1,2⟩,[0,r112,r329,r379,r380,r381,r382,r383,r384,-3136]),(⟨1,1,3⟩,[0,r155,r385,r386,r387,r388,r389,r136,-896]),(⟨1,1,4⟩,[0,r155,r80,r325,r326,r327,r328,896]),(⟨1,2,0⟩,[r296,r297,r298,r299,r300,r301,r302,r303,r304,r305,r306]),(⟨1,2,1⟩,[0,r112,r329,r379,r380,r381,r382,r383,r384,-3136]),(⟨1,2,3⟩,[r91,r390,r391,r392,r393,r347,r394,160]),(⟨1,3,0⟩,[r307,r308,r309,r310,r311,r312,r313,r314,r315,r316]),(⟨1,3,1⟩,[0,r155,r385,r386,r387,r388,r389,r136,-896]),(⟨1,3,2⟩,[r91,r390,r391,r392,r393,r347,r394,160]),(⟨1,4,0⟩,[r91,r317,r318,r319,r320,r321,r322,r323,r324]),(⟨1,4,1⟩,[0,r155,r80,r325,r326,r327,r328,896]),(⟨1,5,0⟩,[0,r155,r80,r325,r326,r327,r328,896]),(⟨2,0,0⟩,[r233,r234,r235,r236,r237,r238,r239,r240,r241,r242,r243,r244]),(⟨2,0,1⟩,[r296,r297,r298,r299,r300,r301,r302,r303,r304,r305,r306]),(⟨2,0,2⟩,[r112,r329,r330,r331,r332,r333,r334,r335,r336,r337]),(⟨2,0,3⟩,[r233,r338,r338,r339,r340,r341,r342,r343,r344]),(⟨2,0,4⟩,[r59,r345,r91,r346,r347,r348,r349,r350]),(⟨2,0,5⟩,[r91,r351,r352,r157,r353,r354,-224]),(⟨2,0,6⟩,[r13,r355,r356,r357,r358,-64]),(⟨2,0,7⟩,[r13,r359,r360,r128,64]),(⟨2,1,0⟩,[r296,r297,r298,r299,r300,r301,r302,r303,r304,r305,r306]),(⟨2,1,1⟩,[0,r112,r329,r379,r380,r381,r382,r383,r384,-3136]),(⟨2,1,3⟩,[r91,r390,r391,r392,r393,r347,r394,160]),(⟨2,2,0⟩,[r112,r329,r330,r331,r332,r333,r334,r335,r336,r337]),(⟨2,2,3⟩,[r112,r150,r151,r152,r153,r154,-448]),(⟨2,3,0⟩,[r233,r338,r338,r339,r340,r341,r342,r343,r344]),(⟨2,3,1⟩,[r91,r390,r391,r392,r393,r347,r394,160]),(⟨2,3,2⟩,[r112,r150,r151,r152,r153,r154,-448]),(⟨2,3,3⟩,[r155,r156,r157,r158,r159,-128]),(⟨2,3,4⟩,[r13,r359,r360,r128,64]),(⟨2,4,0⟩,[r59,r345,r91,r346,r347,r348,r349,r350]),(⟨2,4,3⟩,[r13,r359,r360,r128,64]),(⟨2,5,0⟩,[r91,r351,r352,r157,r353,r354,-224]),(⟨2,6,0⟩,[r13,r355,r356,r357,r358,-64]),(⟨2,7,0⟩,[r13,r359,r360,r128,64]),(⟨3,0,0⟩,[r245,r246,r247,r248,r249,r250,r251,r252,r253,r254,r255]),(⟨3,0,1⟩,[r307,r308,r309,r310,r311,r312,r313,r314,r315,r316]),(⟨3,0,2⟩,[r233,r338,r338,r339,r340,r341,r342,r343,r344]),(⟨3,0,3⟩,[0,r170,r361,r362,r363,r364,r365,r366]),(⟨3,0,4⟩,[0,r127,r367,r368,r159,r369,r370]),(⟨3,0,5⟩,[r13,r355,r356,r357,r358,-64]),(⟨3,0,6⟩,[r13,r359,r360,r128,64]),(⟨3,1,0⟩,[r307,r308,r309,r310,r311,r312,r313,r314,r315,r316]),(⟨3,1,1⟩,[0,r155,r385,r386,r387,r388,r389,r136,-896]),(⟨3,1,2⟩,[r91,r390,r391,r392,r393,r347,r394,160]),(⟨3,2,0⟩,[r233,r338,r338,r339,r340,r341,r342,r343,r344]),(⟨3,2,1⟩,[r91,r390,r391,r392,r393,r347,r394,160]),(⟨3,2,2⟩,[r112,r150,r151,r152,r153,r154,-448]),(⟨3,2,3⟩,[r155,r156,r157,r158,r159,-128]),(⟨3,2,4⟩,[r13,r359,r360,r128,64]),(⟨3,3,0⟩,[0,r170,r361,r362,r363,r364,r365,r366]),(⟨3,3,2⟩,[r155,r156,r157,r158,r159,-128]),(⟨3,4,0⟩,[0,r127,r367,r368,r159,r369,r370]),(⟨3,4,2⟩,[r13,r359,r360,r128,64]),(⟨3,5,0⟩,[r13,r355,r356,r357,r358,-64]),(⟨3,6,0⟩,[r13,r359,r360,r128,64]),(⟨4,0,0⟩,[r256,r257,r258,r259,r260,r261,r262,r263,r264,r265]),(⟨4,0,1⟩,[r91,r317,r318,r319,r320,r321,r322,r323,r324]),(⟨4,0,2⟩,[r59,r345,r91,r346,r347,r348,r349,r350]),(⟨4,0,3⟩,[0,r127,r367,r368,r159,r369,r370]),(⟨4,1,0⟩,[r91,r317,r318,r319,r320,r321,r322,r323,r324]),(⟨4,1,1⟩,[0,r155,r80,r325,r326,r327,r328,896]),(⟨4,2,0⟩,[r59,r345,r91,r346,r347,r348,r349,r350]),(⟨4,2,3⟩,[r13,r359,r360,r128,64]),(⟨4,3,0⟩,[0,r127,r367,r368,r159,r369,r370]),(⟨4,3,2⟩,[r13,r359,r360,r128,64]),(⟨5,0,0⟩,[r266,r267,r268,r269,384,r270,r271,r272,r273]),(⟨5,0,1⟩,[0,r155,r80,r325,r326,r327,r328,896]),(⟨5,0,2⟩,[r91,r351,r352,r157,r353,r354,-224]),(⟨5,0,3⟩,[r13,r355,r356,r357,r358,-64]),(⟨5,1,0⟩,[0,r155,r80,r325,r326,r327,r328,896]),(⟨5,2,0⟩,[r91,r351,r352,r157,r353,r354,-224]),(⟨5,3,0⟩,[r13,r355,r356,r357,r358,-64]),(⟨6,0,0⟩,[r26,r274,r275,r276,r277,r278,r279,-864]),(⟨6,0,2⟩,[r13,r355,r356,r357,r358,-64]),(⟨6,0,3⟩,[r13,r359,r360,r128,64]),(⟨6,2,0⟩,[r13,r355,r356,r357,r358,-64]),(⟨6,3,0⟩,[r13,r359,r360,r128,64]),(⟨7,0,0⟩,[r59,r280,r281,r74,r282,r283,r284]),(⟨7,0,2⟩,[r13,r359,r360,r128,64]),(⟨7,2,0⟩,[r13,r359,r360,r128,64])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,3,-12,9,6]),(⟨0,0,1⟩,[-1,5,-9,5]),(⟨0,0,2⟩,[-1,4,-7]),(⟨0,0,3⟩,[2,-2]),(⟨0,0,4⟩,[2]),(⟨0,1,0⟩,[-1,5,-9,5]),(⟨0,2,0⟩,[-1,4,-7]),(⟨0,3,0⟩,[2,-2]),(⟨0,4,0⟩,[2]),(⟨1,0,0⟩,[-1,5,-9,5]),(⟨2,0,0⟩,[-1,4,-7]),(⟨3,0,0⟩,[2,-2]),(⟨4,0,0⟩,[2])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[128,-2368,16192,-48960,27712,296128,-1096256,1862976,-1545664,318080]),(⟨0,0,1⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨0,0,2⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨0,0,3⟩,[-64,1280,-6336,2560,43072,-131840,181440]),(⟨0,1,0⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨0,1,1⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248]),(⟨0,2,0⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨0,2,3⟩,[-128,1536,-3840,-4608,15232]),(⟨0,3,0⟩,[-64,1280,-6336,2560,43072,-131840,181440]),(⟨0,3,2⟩,[-128,1536,-3840,-4608,15232]),(⟨1,0,0⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨1,0,1⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248]),(⟨1,1,0⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248]),(⟨2,0,0⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨2,0,3⟩,[-128,1536,-3840,-4608,15232]),(⟨2,3,0⟩,[-128,1536,-3840,-4608,15232]),(⟨3,0,0⟩,[-64,1280,-6336,2560,43072,-131840,181440]),(⟨3,0,2⟩,[-128,1536,-3840,-4608,15232]),(⟨3,2,0⟩,[-128,1536,-3840,-4608,15232])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 0 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r395) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 7 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r396) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨4,0,0⟩,[2])]

noncomputable def partial12 : Poly := [(⟨4,0,0⟩,[256,-4736,32384,-97920,55424,592256,-2192512,3725952,-3091328,636160]),(⟨4,0,1⟩,[128,-2944,23296,-79232,70400,355712,-1447168,2395008,-1724800]),(⟨4,0,2⟩,[-256,3584,-12544,-6400,94464,-233472,317696,-48384]),(⟨4,0,3⟩,[-128,2560,-12672,5120,86144,-263680,362880]),(⟨4,1,0⟩,[128,-2944,23296,-79232,70400,355712,-1447168,2395008,-1724800]),(⟨4,1,1⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨4,2,0⟩,[-256,3584,-12544,-6400,94464,-233472,317696,-48384]),(⟨4,2,3⟩,[-256,3072,-7680,-9216,30464]),(⟨4,3,0⟩,[-128,2560,-12672,5120,86144,-263680,362880]),(⟨4,3,2⟩,[-256,3072,-7680,-9216,30464]),(⟨5,0,0⟩,[128,-2944,23296,-79232,70400,355712,-1447168,2395008,-1724800]),(⟨5,0,1⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨5,1,0⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨6,0,0⟩,[-256,3584,-12544,-6400,94464,-233472,317696,-48384]),(⟨6,0,3⟩,[-256,3072,-7680,-9216,30464]),(⟨6,3,0⟩,[-256,3072,-7680,-9216,30464]),(⟨7,0,0⟩,[-128,2560,-12672,5120,86144,-263680,362880]),(⟨7,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨7,2,0⟩,[-256,3072,-7680,-9216,30464])]


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

noncomputable def partial8 : Poly := [(⟨0,4,0⟩,[256,-4736,32384,-97920,55424,592256,-2192512,3725952,-3091328,636160]),(⟨0,4,1⟩,[128,-2944,23296,-79232,70400,355712,-1447168,2395008,-1724800]),(⟨0,4,2⟩,[-256,3584,-12544,-6400,94464,-233472,317696,-48384]),(⟨0,4,3⟩,[-128,2560,-12672,5120,86144,-263680,362880]),(⟨0,5,0⟩,[128,-2944,23296,-79232,70400,355712,-1447168,2395008,-1724800]),(⟨0,5,1⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨0,6,0⟩,[-256,3584,-12544,-6400,94464,-233472,317696,-48384]),(⟨0,6,3⟩,[-256,3072,-7680,-9216,30464]),(⟨0,7,0⟩,[-128,2560,-12672,5120,86144,-263680,362880]),(⟨0,7,2⟩,[-256,3072,-7680,-9216,30464]),(⟨1,0,0⟩,[-128,3008,-29184,151872,-430080,364032,2082688,-9870848,22207488,-30294464,24816256,-10591040,1590400]),(⟨1,0,1⟩,[-64,1792,-19584,111424,-345472,412928,1097984,-6240128,14251456,-18707456,13749120,-4312000]),(⟨1,0,2⟩,[128,-2432,16384,-44928,2176,350336,-1183616,2105216,-2134272,1011968,-120960]),(⟨1,0,3⟩,[64,-1600,13312,-46080,33152,292480,-1215488,2309120,-2292160,907200]),(⟨1,1,0⟩,[-64,1792,-19584,111424,-345472,412928,1097984,-6240128,14251456,-18707456,13749120,-4312000]),(⟨1,1,1⟩,[0,256,-4864,35840,-139264,301568,-225792,-658432,2170880,-2546432,1066240]),(⟨1,2,0⟩,[128,-2432,16384,-44928,2176,350336,-1183616,2105216,-2134272,1011968,-120960]),(⟨1,2,3⟩,[128,-2176,12672,-29056,3968,98432,-160128,76160]),(⟨1,3,0⟩,[64,-1600,13312,-46080,33152,292480,-1215488,2309120,-2292160,907200]),(⟨1,3,2⟩,[128,-2176,12672,-29056,3968,98432,-160128,76160]),(⟨1,4,0⟩,[128,-2944,23296,-79232,70400,355712,-1447168,2395008,-1724800]),(⟨1,4,1⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨1,5,0⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨2,0,0⟩,[-192,4672,-46144,241728,-682368,570368,3184768,-14561024,30922816,-38249024,25841088,-6538560]),(⟨2,0,1⟩,[-64,1984,-22848,132352,-414464,541824,962816,-5995264,12888384,-14378560,7103040]),(⟨2,0,2⟩,[128,-2304,14336,-34432,-16128,328064,-956416,1476736,-1208704,169344]),(⟨2,0,3⟩,[64,-1536,11904,-36864,11520,286208,-1010304,1648640,-1270080]),(⟨2,1,0⟩,[-64,1984,-22848,132352,-414464,541824,962816,-5995264,12888384,-14378560,7103040]),(⟨2,1,1⟩,[0,256,-4608,31744,-115200,224768,-87552,-680960,1731072,-1492736]),(⟨2,2,0⟩,[128,-2304,14336,-34432,-16128,328064,-956416,1476736,-1208704,169344]),(⟨2,2,3⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨2,3,0⟩,[64,-1536,11904,-36864,11520,286208,-1010304,1648640,-1270080]),(⟨2,3,2⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨2,4,0⟩,[-256,3584,-12544,-6400,94464,-233472,317696,-48384]),(⟨2,4,3⟩,[-256,3072,-7680,-9216,30464]),(⟨2,7,0⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[320,-5696,35520,-78720,-119680,1127424,-2779776,2686848,1765952,-7092672,5279680]),(⟨3,0,1⟩,[128,-2816,21632,-70784,34432,510080,-1890432,3161216,-2388736,232064]),(⟨3,0,2⟩,[-256,3840,-16128,6144,100864,-327936,551168,-366080,48384]),(⟨3,0,3⟩,[0,512,-2560,-11264,84992,-251392,466432,-286720]),(⟨3,1,0⟩,[128,-2816,21632,-70784,34432,510080,-1890432,3161216,-2388736,232064]),(⟨3,1,1⟩,[0,-512,7680,-38400,86528,-65024,-241152,677376,-426496]),(⟨3,2,0⟩,[-256,3840,-16128,6144,100864,-327936,551168,-366080,48384]),(⟨3,2,3⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨3,3,0⟩,[0,512,-2560,-11264,84992,-251392,466432,-286720]),(⟨3,3,2⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨3,4,0⟩,[-128,2560,-12672,5120,86144,-263680,362880]),(⟨3,4,2⟩,[-256,3072,-7680,-9216,30464]),(⟨3,6,0⟩,[-256,3072,-7680,-9216,30464]),(⟨4,0,0⟩,[576,-11712,86272,-280960,222080,1498112,-6167296,11353984,-10712000,3437504]),(⟨4,0,1⟩,[128,-3456,30976,-117632,156928,290688,-1688320,3072384,-2151296]),(⟨4,0,2⟩,[-128,1408,128,-35456,98432,-135040,157568,27776]),(⟨4,0,3⟩,[0,512,-1792,-16384,79360,-170496,256256]),(⟨4,1,0⟩,[128,-3456,30976,-117632,156928,290688,-1688320,3072384,-2151296]),(⟨4,1,1⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨4,2,0⟩,[-128,1408,128,-35456,98432,-135040,157568,27776]),(⟨4,2,3⟩,[-256,3072,-7680,-9216,30464]),(⟨4,3,0⟩,[0,512,-1792,-16384,79360,-170496,256256]),(⟨4,3,2⟩,[-256,3072,-7680,-9216,30464]),(⟨5,0,0⟩,[-64,-640,19072,-109952,182784,313984,-1906304,3677568,-2946496]),(⟨5,0,1⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨5,0,2⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨5,0,3⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨5,1,0⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨5,2,0⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨5,3,0⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨6,0,0⟩,[-384,6272,-27776,11392,175488,-583296,944256,-411264]),(⟨6,0,2⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨6,0,3⟩,[-256,3072,-7680,-9216,30464]),(⟨6,2,0⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨6,3,0⟩,[-256,3072,-7680,-9216,30464]),(⟨7,0,0⟩,[-128,2560,-12672,5120,86144,-263680,362880]),(⟨7,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨7,2,0⟩,[-256,3072,-7680,-9216,30464])]


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

noncomputable def partial4 : Poly := [(⟨0,0,4⟩,[256,-4736,32384,-97920,55424,592256,-2192512,3725952,-3091328,636160]),(⟨0,0,5⟩,[128,-2944,23296,-79232,70400,355712,-1447168,2395008,-1724800]),(⟨0,0,6⟩,[-256,3584,-12544,-6400,94464,-233472,317696,-48384]),(⟨0,0,7⟩,[-128,2560,-12672,5120,86144,-263680,362880]),(⟨0,1,0⟩,[-128,3008,-29184,151872,-430080,364032,2082688,-9870848,22207488,-30294464,24816256,-10591040,1590400]),(⟨0,1,1⟩,[-64,1792,-19584,111424,-345472,412928,1097984,-6240128,14251456,-18707456,13749120,-4312000]),(⟨0,1,2⟩,[128,-2432,16384,-44928,2176,350336,-1183616,2105216,-2134272,1011968,-120960]),(⟨0,1,3⟩,[64,-1600,13312,-46080,33152,292480,-1215488,2309120,-2292160,907200]),(⟨0,1,4⟩,[128,-2944,23296,-79232,70400,355712,-1447168,2395008,-1724800]),(⟨0,1,5⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨0,2,0⟩,[-192,4672,-46144,241728,-682368,570368,3184768,-14561024,30922816,-38249024,25841088,-6538560]),(⟨0,2,1⟩,[-64,1984,-22848,132352,-414464,541824,962816,-5995264,12888384,-14378560,7103040]),(⟨0,2,2⟩,[128,-2304,14336,-34432,-16128,328064,-956416,1476736,-1208704,169344]),(⟨0,2,3⟩,[64,-1536,11904,-36864,11520,286208,-1010304,1648640,-1270080]),(⟨0,2,4⟩,[-256,3584,-12544,-6400,94464,-233472,317696,-48384]),(⟨0,2,7⟩,[-256,3072,-7680,-9216,30464]),(⟨0,3,0⟩,[320,-5696,35520,-78720,-119680,1127424,-2779776,2686848,1765952,-7092672,5279680]),(⟨0,3,1⟩,[128,-2816,21632,-70784,34432,510080,-1890432,3161216,-2388736,232064]),(⟨0,3,2⟩,[-256,3840,-16128,6144,100864,-327936,551168,-366080,48384]),(⟨0,3,3⟩,[0,512,-2560,-11264,84992,-251392,466432,-286720]),(⟨0,3,4⟩,[-128,2560,-12672,5120,86144,-263680,362880]),(⟨0,3,6⟩,[-256,3072,-7680,-9216,30464]),(⟨0,4,0⟩,[576,-11712,86272,-280960,222080,1498112,-6167296,11353984,-10712000,3437504]),(⟨0,4,1⟩,[128,-3456,30976,-117632,156928,290688,-1688320,3072384,-2151296]),(⟨0,4,2⟩,[-128,1408,128,-35456,98432,-135040,157568,27776]),(⟨0,4,3⟩,[0,512,-1792,-16384,79360,-170496,256256]),(⟨0,5,0⟩,[-64,-640,19072,-109952,182784,313984,-1906304,3677568,-2946496]),(⟨0,5,1⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨0,5,2⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨0,5,3⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨0,6,0⟩,[-384,6272,-27776,11392,175488,-583296,944256,-411264]),(⟨0,6,2⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨0,6,3⟩,[-256,3072,-7680,-9216,30464]),(⟨0,7,0⟩,[-128,2560,-12672,5120,86144,-263680,362880]),(⟨0,7,2⟩,[-256,3072,-7680,-9216,30464]),(⟨1,0,0⟩,[-128,3008,-29184,151872,-430080,364032,2082688,-9870848,22207488,-30294464,24816256,-10591040,1590400]),(⟨1,0,1⟩,[-64,1792,-19584,111424,-345472,412928,1097984,-6240128,14251456,-18707456,13749120,-4312000]),(⟨1,0,2⟩,[128,-2432,16384,-44928,2176,350336,-1183616,2105216,-2134272,1011968,-120960]),(⟨1,0,3⟩,[64,-1600,13312,-46080,33152,292480,-1215488,2309120,-2292160,907200]),(⟨1,0,4⟩,[128,-2944,23296,-79232,70400,355712,-1447168,2395008,-1724800]),(⟨1,0,5⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨1,1,0⟩,[-128,3584,-39168,222848,-690944,825856,2195968,-12480256,28502912,-37414912,27498240,-8624000]),(⟨1,1,1⟩,[0,512,-9728,71680,-278528,603136,-451584,-1316864,4341760,-5092864,2132480]),(⟨1,1,4⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨1,2,0⟩,[64,-448,-6464,87424,-412288,892160,-220800,-3890048,10754112,-13366592,6982080]),(⟨1,2,1⟩,[0,256,-4608,31744,-115200,224768,-87552,-680960,1731072,-1492736]),(⟨1,2,3⟩,[128,-2176,12672,-29056,3968,98432,-160128,76160]),(⟨1,3,0⟩,[192,-4416,34944,-116864,67584,802560,-3105920,5470336,-4680896,1139264]),(⟨1,3,1⟩,[0,-512,7680,-38400,86528,-65024,-241152,677376,-426496]),(⟨1,3,2⟩,[128,-2176,12672,-29056,3968,98432,-160128,76160]),(⟨1,4,0⟩,[128,-3456,30976,-117632,156928,290688,-1688320,3072384,-2151296]),(⟨1,4,1⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨1,5,0⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨2,0,0⟩,[-192,4672,-46144,241728,-682368,570368,3184768,-14561024,30922816,-38249024,25841088,-6538560]),(⟨2,0,1⟩,[-64,1984,-22848,132352,-414464,541824,962816,-5995264,12888384,-14378560,7103040]),(⟨2,0,2⟩,[128,-2304,14336,-34432,-16128,328064,-956416,1476736,-1208704,169344]),(⟨2,0,3⟩,[64,-1536,11904,-36864,11520,286208,-1010304,1648640,-1270080]),(⟨2,0,4⟩,[-256,3584,-12544,-6400,94464,-233472,317696,-48384]),(⟨2,0,7⟩,[-256,3072,-7680,-9216,30464]),(⟨2,1,0⟩,[64,-448,-6464,87424,-412288,892160,-220800,-3890048,10754112,-13366592,6982080]),(⟨2,1,1⟩,[0,256,-4608,31744,-115200,224768,-87552,-680960,1731072,-1492736]),(⟨2,1,3⟩,[128,-2176,12672,-29056,3968,98432,-160128,76160]),(⟨2,2,0⟩,[256,-4608,28672,-68864,-32256,656128,-1912832,2953472,-2417408,338688]),(⟨2,2,3⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨2,3,0⟩,[-192,2304,-4224,-30720,112384,-41728,-459136,1282560,-1221696]),(⟨2,3,2⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨2,3,3⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨2,3,4⟩,[-256,3072,-7680,-9216,30464]),(⟨2,4,0⟩,[-128,1408,128,-35456,98432,-135040,157568,27776]),(⟨2,4,3⟩,[-256,3072,-7680,-9216,30464]),(⟨2,5,0⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨2,6,0⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨2,7,0⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[320,-5696,35520,-78720,-119680,1127424,-2779776,2686848,1765952,-7092672,5279680]),(⟨3,0,1⟩,[128,-2816,21632,-70784,34432,510080,-1890432,3161216,-2388736,232064]),(⟨3,0,2⟩,[-256,3840,-16128,6144,100864,-327936,551168,-366080,48384]),(⟨3,0,3⟩,[0,512,-2560,-11264,84992,-251392,466432,-286720]),(⟨3,0,4⟩,[-128,2560,-12672,5120,86144,-263680,362880]),(⟨3,0,6⟩,[-256,3072,-7680,-9216,30464]),(⟨3,1,0⟩,[192,-4416,34944,-116864,67584,802560,-3105920,5470336,-4680896,1139264]),(⟨3,1,1⟩,[0,-512,7680,-38400,86528,-65024,-241152,677376,-426496]),(⟨3,1,2⟩,[128,-2176,12672,-29056,3968,98432,-160128,76160]),(⟨3,2,0⟩,[-192,2304,-4224,-30720,112384,-41728,-459136,1282560,-1221696]),(⟨3,2,2⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨3,2,3⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨3,2,4⟩,[-256,3072,-7680,-9216,30464]),(⟨3,3,0⟩,[0,1024,-5120,-22528,169984,-502784,932864,-573440]),(⟨3,3,2⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨3,4,0⟩,[0,512,-1792,-16384,79360,-170496,256256]),(⟨3,4,2⟩,[-256,3072,-7680,-9216,30464]),(⟨3,5,0⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨3,6,0⟩,[-256,3072,-7680,-9216,30464]),(⟨4,0,0⟩,[576,-11712,86272,-280960,222080,1498112,-6167296,11353984,-10712000,3437504]),(⟨4,0,1⟩,[128,-3456,30976,-117632,156928,290688,-1688320,3072384,-2151296]),(⟨4,0,2⟩,[-128,1408,128,-35456,98432,-135040,157568,27776]),(⟨4,0,3⟩,[0,512,-1792,-16384,79360,-170496,256256]),(⟨4,1,0⟩,[128,-3456,30976,-117632,156928,290688,-1688320,3072384,-2151296]),(⟨4,1,1⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨4,2,0⟩,[-128,1408,128,-35456,98432,-135040,157568,27776]),(⟨4,2,3⟩,[-256,3072,-7680,-9216,30464]),(⟨4,3,0⟩,[0,512,-1792,-16384,79360,-170496,256256]),(⟨4,3,2⟩,[-256,3072,-7680,-9216,30464]),(⟨5,0,0⟩,[-64,-640,19072,-109952,182784,313984,-1906304,3677568,-2946496]),(⟨5,0,1⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨5,0,2⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨5,0,3⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨5,1,0⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨5,2,0⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨5,3,0⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨6,0,0⟩,[-384,6272,-27776,11392,175488,-583296,944256,-411264]),(⟨6,0,2⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨6,0,3⟩,[-256,3072,-7680,-9216,30464]),(⟨6,2,0⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨6,3,0⟩,[-256,3072,-7680,-9216,30464]),(⟨7,0,0⟩,[-128,2560,-12672,5120,86144,-263680,362880]),(⟨7,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨7,2,0⟩,[-256,3072,-7680,-9216,30464])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,384,-8640,78144,-361728,802176,212352,-6886656,21575424,-35082240,29691456,-6550080,-6411264,1908480]),(⟨0,0,1⟩,[-128,3200,-34368,205056,-701568,1041024,1907200,-14096768,36294912,-52696832,41601088,-11167616,-3584000]),(⟨0,0,2⟩,[-192,4288,-39232,200256,-601344,704768,2201344,-12277760,28176832,-37229504,26576448,-6683712]),(⟨0,0,3⟩,[320,-5888,40128,-113664,-24832,1176576,-3707136,5216256,-1339456,-6250752,6368320]),(⟨0,0,4⟩,[576,-11712,86272,-280960,222080,1498112,-6167296,11353984,-10712000,3437504]),(⟨0,0,5⟩,[-64,-640,19072,-109952,182784,313984,-1906304,3677568,-2946496]),(⟨0,0,6⟩,[-384,6272,-27776,11392,175488,-583296,944256,-411264]),(⟨0,0,7⟩,[-128,2560,-12672,5120,86144,-263680,362880]),(⟨0,1,0⟩,[-128,3200,-34368,205056,-701568,1041024,1907200,-14096768,36294912,-52696832,41601088,-11167616,-3584000]),(⟨0,1,1⟩,[-128,3584,-39936,236672,-783104,1126912,1730560,-12643072,30770048,-41132032,28664832,-7344512]),(⟨0,1,2⟩,[64,-448,-6464,87424,-412288,892160,-220800,-3890048,10754112,-13366592,6982080]),(⟨0,1,3⟩,[192,-4416,34944,-116864,67584,802560,-3105920,5470336,-4680896,1139264]),(⟨0,1,4⟩,[128,-3456,30976,-117632,156928,290688,-1688320,3072384,-2151296]),(⟨0,1,5⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨0,2,0⟩,[-192,4288,-39232,200256,-601344,704768,2201344,-12277760,28176832,-37229504,26576448,-6683712]),(⟨0,2,1⟩,[64,-448,-6464,87424,-412288,892160,-220800,-3890048,10754112,-13366592,6982080]),(⟨0,2,2⟩,[256,-4608,28672,-68864,-32256,656128,-1912832,2953472,-2417408,338688]),(⟨0,2,3⟩,[-192,1920,1920,-61824,157696,33920,-706432,1392000,-1130304]),(⟨0,2,4⟩,[-128,1408,128,-35456,98432,-135040,157568,27776]),(⟨0,2,5⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨0,2,6⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨0,2,7⟩,[-256,3072,-7680,-9216,30464]),(⟨0,3,0⟩,[320,-5888,40128,-113664,-24832,1176576,-3707136,5216256,-1339456,-6250752,6368320]),(⟨0,3,1⟩,[192,-4416,34944,-116864,67584,802560,-3105920,5470336,-4680896,1139264]),(⟨0,3,2⟩,[-192,1920,1920,-61824,157696,33920,-706432,1392000,-1130304]),(⟨0,3,3⟩,[0,1024,-5120,-22528,169984,-502784,932864,-573440]),(⟨0,3,4⟩,[0,512,-1792,-16384,79360,-170496,256256]),(⟨0,3,5⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨0,3,6⟩,[-256,3072,-7680,-9216,30464]),(⟨0,4,0⟩,[576,-11712,86272,-280960,222080,1498112,-6167296,11353984,-10712000,3437504]),(⟨0,4,1⟩,[128,-3456,30976,-117632,156928,290688,-1688320,3072384,-2151296]),(⟨0,4,2⟩,[-128,1408,128,-35456,98432,-135040,157568,27776]),(⟨0,4,3⟩,[0,512,-1792,-16384,79360,-170496,256256]),(⟨0,5,0⟩,[-64,-640,19072,-109952,182784,313984,-1906304,3677568,-2946496]),(⟨0,5,1⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨0,5,2⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨0,5,3⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨0,6,0⟩,[-384,6272,-27776,11392,175488,-583296,944256,-411264]),(⟨0,6,2⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨0,6,3⟩,[-256,3072,-7680,-9216,30464]),(⟨0,7,0⟩,[-128,2560,-12672,5120,86144,-263680,362880]),(⟨0,7,2⟩,[-256,3072,-7680,-9216,30464]),(⟨1,0,0⟩,[-128,3200,-34368,205056,-701568,1041024,1907200,-14096768,36294912,-52696832,41601088,-11167616,-3584000]),(⟨1,0,1⟩,[-128,3584,-39936,236672,-783104,1126912,1730560,-12643072,30770048,-41132032,28664832,-7344512]),(⟨1,0,2⟩,[64,-448,-6464,87424,-412288,892160,-220800,-3890048,10754112,-13366592,6982080]),(⟨1,0,3⟩,[192,-4416,34944,-116864,67584,802560,-3105920,5470336,-4680896,1139264]),(⟨1,0,4⟩,[128,-3456,30976,-117632,156928,290688,-1688320,3072384,-2151296]),(⟨1,0,5⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨1,1,0⟩,[-128,3584,-39936,236672,-783104,1126912,1730560,-12643072,30770048,-41132032,28664832,-7344512]),(⟨1,1,1⟩,[0,768,-14592,107520,-417792,904704,-677376,-1975296,6512640,-7639296,3198720]),(⟨1,1,2⟩,[0,256,-4608,31744,-115200,224768,-87552,-680960,1731072,-1492736]),(⟨1,1,3⟩,[0,-512,7680,-38400,86528,-65024,-241152,677376,-426496]),(⟨1,1,4⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨1,2,0⟩,[64,-448,-6464,87424,-412288,892160,-220800,-3890048,10754112,-13366592,6982080]),(⟨1,2,1⟩,[0,256,-4608,31744,-115200,224768,-87552,-680960,1731072,-1492736]),(⟨1,2,3⟩,[128,-2176,12672,-29056,3968,98432,-160128,76160]),(⟨1,3,0⟩,[192,-4416,34944,-116864,67584,802560,-3105920,5470336,-4680896,1139264]),(⟨1,3,1⟩,[0,-512,7680,-38400,86528,-65024,-241152,677376,-426496]),(⟨1,3,2⟩,[128,-2176,12672,-29056,3968,98432,-160128,76160]),(⟨1,4,0⟩,[128,-3456,30976,-117632,156928,290688,-1688320,3072384,-2151296]),(⟨1,4,1⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨1,5,0⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨2,0,0⟩,[-192,4288,-39232,200256,-601344,704768,2201344,-12277760,28176832,-37229504,26576448,-6683712]),(⟨2,0,1⟩,[64,-448,-6464,87424,-412288,892160,-220800,-3890048,10754112,-13366592,6982080]),(⟨2,0,2⟩,[256,-4608,28672,-68864,-32256,656128,-1912832,2953472,-2417408,338688]),(⟨2,0,3⟩,[-192,1920,1920,-61824,157696,33920,-706432,1392000,-1130304]),(⟨2,0,4⟩,[-128,1408,128,-35456,98432,-135040,157568,27776]),(⟨2,0,5⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨2,0,6⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨2,0,7⟩,[-256,3072,-7680,-9216,30464]),(⟨2,1,0⟩,[64,-448,-6464,87424,-412288,892160,-220800,-3890048,10754112,-13366592,6982080]),(⟨2,1,1⟩,[0,256,-4608,31744,-115200,224768,-87552,-680960,1731072,-1492736]),(⟨2,1,3⟩,[128,-2176,12672,-29056,3968,98432,-160128,76160]),(⟨2,2,0⟩,[256,-4608,28672,-68864,-32256,656128,-1912832,2953472,-2417408,338688]),(⟨2,2,3⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨2,3,0⟩,[-192,1920,1920,-61824,157696,33920,-706432,1392000,-1130304]),(⟨2,3,1⟩,[128,-2176,12672,-29056,3968,98432,-160128,76160]),(⟨2,3,2⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨2,3,3⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨2,3,4⟩,[-256,3072,-7680,-9216,30464]),(⟨2,4,0⟩,[-128,1408,128,-35456,98432,-135040,157568,27776]),(⟨2,4,3⟩,[-256,3072,-7680,-9216,30464]),(⟨2,5,0⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨2,6,0⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨2,7,0⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[320,-5888,40128,-113664,-24832,1176576,-3707136,5216256,-1339456,-6250752,6368320]),(⟨3,0,1⟩,[192,-4416,34944,-116864,67584,802560,-3105920,5470336,-4680896,1139264]),(⟨3,0,2⟩,[-192,1920,1920,-61824,157696,33920,-706432,1392000,-1130304]),(⟨3,0,3⟩,[0,1024,-5120,-22528,169984,-502784,932864,-573440]),(⟨3,0,4⟩,[0,512,-1792,-16384,79360,-170496,256256]),(⟨3,0,5⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨3,0,6⟩,[-256,3072,-7680,-9216,30464]),(⟨3,1,0⟩,[192,-4416,34944,-116864,67584,802560,-3105920,5470336,-4680896,1139264]),(⟨3,1,1⟩,[0,-512,7680,-38400,86528,-65024,-241152,677376,-426496]),(⟨3,1,2⟩,[128,-2176,12672,-29056,3968,98432,-160128,76160]),(⟨3,2,0⟩,[-192,1920,1920,-61824,157696,33920,-706432,1392000,-1130304]),(⟨3,2,1⟩,[128,-2176,12672,-29056,3968,98432,-160128,76160]),(⟨3,2,2⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨3,2,3⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨3,2,4⟩,[-256,3072,-7680,-9216,30464]),(⟨3,3,0⟩,[0,1024,-5120,-22528,169984,-502784,932864,-573440]),(⟨3,3,2⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨3,4,0⟩,[0,512,-1792,-16384,79360,-170496,256256]),(⟨3,4,2⟩,[-256,3072,-7680,-9216,30464]),(⟨3,5,0⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨3,6,0⟩,[-256,3072,-7680,-9216,30464]),(⟨4,0,0⟩,[576,-11712,86272,-280960,222080,1498112,-6167296,11353984,-10712000,3437504]),(⟨4,0,1⟩,[128,-3456,30976,-117632,156928,290688,-1688320,3072384,-2151296]),(⟨4,0,2⟩,[-128,1408,128,-35456,98432,-135040,157568,27776]),(⟨4,0,3⟩,[0,512,-1792,-16384,79360,-170496,256256]),(⟨4,1,0⟩,[128,-3456,30976,-117632,156928,290688,-1688320,3072384,-2151296]),(⟨4,1,1⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨4,2,0⟩,[-128,1408,128,-35456,98432,-135040,157568,27776]),(⟨4,2,3⟩,[-256,3072,-7680,-9216,30464]),(⟨4,3,0⟩,[0,512,-1792,-16384,79360,-170496,256256]),(⟨4,3,2⟩,[-256,3072,-7680,-9216,30464]),(⟨5,0,0⟩,[-64,-640,19072,-109952,182784,313984,-1906304,3677568,-2946496]),(⟨5,0,1⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨5,0,2⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨5,0,3⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨5,1,0⟩,[0,-512,7168,-31232,55296,-9728,-250880,426496]),(⟨5,2,0⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨5,3,0⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨6,0,0⟩,[-384,6272,-27776,11392,175488,-583296,944256,-411264]),(⟨6,0,2⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨6,0,3⟩,[-256,3072,-7680,-9216,30464]),(⟨6,2,0⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨6,3,0⟩,[-256,3072,-7680,-9216,30464]),(⟨7,0,0⟩,[-128,2560,-12672,5120,86144,-263680,362880]),(⟨7,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨7,2,0⟩,[-256,3072,-7680,-9216,30464])]


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
    (Poly.add (Poly.scale (K.ofRat r397) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 0 7).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r395*r396 : ℚ)=r397 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 0 7 r395 r396 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 0=7 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 0 7).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C052

#print axioms Coulomb8.Columns.C052.sound
