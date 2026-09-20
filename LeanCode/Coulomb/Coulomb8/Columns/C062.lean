import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C062

def r0 : ℚ := { num := 576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -14976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 160896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -937152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 3250368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -6813888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 8061120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -3857088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -1509120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 285888, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -102720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -34176, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := 5568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := -67840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := 456768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := -1893312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 5041536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -8603200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 8844544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -4363392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := -215616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := 926784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := -15296, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := 3968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := -31936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := 20480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := -469568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := 1290496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -2647488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 3292160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 77696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 45440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -2624, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 177280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -903552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 2669824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := -4595200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := 600960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -1311360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -620800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 48192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -2368, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 138944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -87232, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 224320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -2390848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 1944128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := -495296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -40000, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := -960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 19200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -140736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 478848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -800064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := 535552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 82624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -19072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 18688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -127808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 395776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -588864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 340224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := 9920, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -6400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 33024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -3072, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 1792, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -6656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := 4864, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := -49664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := -576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := 12736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := -114560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := 571264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := -1773696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := 3542016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := -632576, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := 3229312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := -185024, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := 41408, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 11648, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := 64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := -1024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := 4864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -2048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := -50112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 185856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -361152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 73728, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -645760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := 682496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -55232, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := 960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := -2816, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 155264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -632448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 1494016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := -2127872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := 1769344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := -39040, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -16448, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := -256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 4288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -25856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 10816, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := -14720, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -56768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 487936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -115520, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 7040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -46720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 149760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -241792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 147328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := 6016, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := -4608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := 20288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -29184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := -21568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := 144384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := -128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := -3840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -13568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 11264, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := -170496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := 113408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := 2304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := -3584, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 4736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -60800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 223232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -358144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := 238464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -22912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := -64, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -1152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 22784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := -155520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := 470528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := -697216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := 465152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := -896, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := 192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := -2816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 12480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := -15360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -24000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := 81664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := -3648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := 27072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := -108288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 36480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -279168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := -283776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := 1555200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := -372672, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := 345408, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := 128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := -1920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := 9600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := -21632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := 16256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := 60288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := -24192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := 768, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := -4608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := -16000, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := 576000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := -129792, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := -256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := 7808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := -13824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := 2432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 8960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := 1664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := -768, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := 19840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -5632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 24960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -30720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := -48000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := 163328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := 288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := -7488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := 80448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := -468576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := 1625184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := -3406944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := 4030560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -1928544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := -754560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := 142944, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := -51360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -17088, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := 2784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := -33920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := 228384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := -946656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := 2520768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := -4301600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 4422272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -2181696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -107808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 463392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := -7648, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 1984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -15968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := 10240, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := -234784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := 645248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -1323744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 1646080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := 38848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 22720, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -1312, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 88640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := -451776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := 1334912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := -2297600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := 300480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := -655680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := -310400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := 24096, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := -1184, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := 69472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -43616, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 112160, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := -1195424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := 972064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := -247648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -20000, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := -480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := -70368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := 239424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := -400032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := 267776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := 41312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := -9536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := 9344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := -63904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := 197888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := -294432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := 170112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := 4960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -3200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := 16512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -1536, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := 896, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := -3328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := 2432, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := -24832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := 6368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := -57280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := 285632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := -886848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := 1771008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -316288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 1614656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := -92512, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := 20704, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := 5824, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := 32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := -512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := -25056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := 92928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := -180576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := 36864, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -322880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := 341248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := -27616, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := 480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := -1408, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := 77632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := -316224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := 747008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := -1063936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := 884672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := -19520, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -8224, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := 2144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := -12928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := 5408, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := -7360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := -28384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := 243968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := -57760, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := 3520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := -23360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := 74880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -120896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 73664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := 3008, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -2304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 10144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -14592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := -10784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := 72192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := -6784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := 5632, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := -85248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := 56704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := 1152, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := -1792, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := -32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := 256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := 2368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := -30400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := 111616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := -179072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := 119232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := -11456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := -32, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := 11392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -77760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 235264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -348608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 232576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -448, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -1408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 6240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := -7680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := -12000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := 40832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := -1824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := 13536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := -54144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := 18240, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := -139584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := -141888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := 777600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := -186336, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := 172704, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := 4800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := -10816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := 8128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := 30144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := -12096, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := -160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := 384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -2304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := -8000, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := 288000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := -64896, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := -128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := 3904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := -6912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := 1216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := 4480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := 832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := 9920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := 1, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := 1, den := 476, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11],[0,r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23],[0,r12,r24,r25,r26,r27,r28,r29,r30,-16128,r31,r32],[0,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42],[0,r33,r43,r44,r45,r46,r47,r48,r49,r50],[0,r51,r52,r53,r54,r55,r56,r57,r58],[0,r51,r59,r60,r61,r62,r63,r64],[0,r65,r66,r67,r68,r69,r70],[0,r65,r71,r72,r73,r74],[],[],[],[],[0,r75,r76,r77,r78,r79,r80,r81,r82,r83,r84,r85],[r86,r87,r88,r89,r90,r91,r92,r93,r94,r95,r96],[0,r97,r98,r99,r100,r101,r102,r103,r104,r105],[r106,r107,r108,r109,r110,r111,r112,r113,4480],[0,r114,r115,r116,r117,r118,r119,r120],[r121,r122,r123,r124,r125,r126,-1472],[],[r127,r128,r129,r122,128],[],[],[],[0,0,0,r33,r130,r131,r132,r133,r134,r135],[r136,r137,r138,r139,r140,r141,r142,r143,r144],[],[0,r65,r66,r67,r68,r69,r70],[],[],[],[],[],[0,r145,r146,r147,r148,r149,r150,r151],[r152,r153,r154,r155,r156,r157,-576],[0,r65,r71,r72,r73,r74],[r127,r128,r129,r122,128],[],[],[],[],[],[],[],[],[],[],[],[],[r152,r158,r159,r160,r161,r162,r163,r164,r165,r166,-9408],[0,0,r167,r168,r169,r170,r171,r172,r173,896],[r174,r175,r176,768,r177,-768,r178,r179,4928],[],[r167,r180,r181,r182,r183,r184,-896],[],[],[],[],[],[],[0,0,r127,r185,r186,r187,r188,-128],[],[],[],[],[],[],[r65,r189,r190,r191,r192,r193,-1152],[],[r127,r128,r129,r122,128],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,0,r194,r195,r196,r197,r198,r199,r200,r201,r202,r203,r204,r205]),(⟨0,0,1⟩,[0,r206,r207,r208,r209,r210,r211,r212,r213,r214,r215,r216,r217]),(⟨0,0,2⟩,[0,r206,r218,r219,r220,r221,r222,r223,r224,-8064,r225,r226]),(⟨0,0,3⟩,[0,r65,r227,r228,r229,r230,r231,r232,r233,r234,r235]),(⟨0,0,4⟩,[0,r65,r236,r237,r238,r239,r240,r241,r242,r243]),(⟨0,0,5⟩,[0,r244,r169,r245,r246,r247,r248,r249,r250]),(⟨0,0,6⟩,[0,r244,r251,r252,r253,r254,r255,r256]),(⟨0,0,7⟩,[0,r152,r257,r258,r259,r260,r261]),(⟨0,0,8⟩,[0,r152,r262,r263,r264,r265]),(⟨0,1,0⟩,[0,r206,r207,r208,r209,r210,r211,r212,r213,r214,r215,r216,r217]),(⟨0,1,1⟩,[0,r266,r267,r268,r269,r270,r271,r272,r273,r274,r275,r276]),(⟨0,1,2⟩,[r277,r278,r183,r87,r279,r280,r281,r282,r283,r284,r285]),(⟨0,1,3⟩,[0,r286,r287,r288,r289,r290,r291,r292,r293,r294]),(⟨0,1,4⟩,[r127,r295,r296,r297,r298,r299,r300,r301,2240]),(⟨0,1,5⟩,[0,r12,r302,r303,r304,r305,r306,r307]),(⟨0,1,6⟩,[r308,r309,r310,r311,r312,r313,-736]),(⟨0,1,8⟩,[r136,r33,r168,r309,64]),(⟨0,2,0⟩,[0,r206,r218,r219,r220,r221,r222,r223,r224,-8064,r225,r226]),(⟨0,2,1⟩,[r277,r278,r183,r87,r279,r280,r281,r282,r283,r284,r285]),(⟨0,2,2⟩,[0,0,0,r65,r314,r315,r316,r317,r318,r319]),(⟨0,2,3⟩,[r320,r321,r322,r323,r324,r325,r326,r327,r328]),(⟨0,2,5⟩,[0,r152,r257,r258,r259,r260,r261]),(⟨0,3,0⟩,[0,r65,r227,r228,r229,r230,r231,r232,r233,r234,r235]),(⟨0,3,1⟩,[0,r286,r287,r288,r289,r290,r291,r292,r293,r294]),(⟨0,3,2⟩,[r320,r321,r322,r323,r324,r325,r326,r327,r328]),(⟨0,3,3⟩,[0,r75,r329,r330,r331,r332,r333,r334]),(⟨0,3,4⟩,[r335,r336,r337,r338,r339,r340,-288]),(⟨0,3,5⟩,[0,r152,r262,r263,r264,r265]),(⟨0,3,6⟩,[r136,r33,r168,r309,64]),(⟨0,4,0⟩,[0,r65,r236,r237,r238,r239,r240,r241,r242,r243]),(⟨0,4,1⟩,[r127,r295,r296,r297,r298,r299,r300,r301,2240]),(⟨0,4,3⟩,[r335,r336,r337,r338,r339,r340,-288]),(⟨0,5,0⟩,[0,r244,r169,r245,r246,r247,r248,r249,r250]),(⟨0,5,1⟩,[0,r12,r302,r303,r304,r305,r306,r307]),(⟨0,5,2⟩,[0,r152,r257,r258,r259,r260,r261]),(⟨0,5,3⟩,[0,r152,r262,r263,r264,r265]),(⟨0,6,0⟩,[0,r244,r251,r252,r253,r254,r255,r256]),(⟨0,6,1⟩,[r308,r309,r310,r311,r312,r313,-736]),(⟨0,6,3⟩,[r136,r33,r168,r309,64]),(⟨0,7,0⟩,[0,r152,r257,r258,r259,r260,r261]),(⟨0,8,0⟩,[0,r152,r262,r263,r264,r265]),(⟨0,8,1⟩,[r136,r33,r168,r309,64]),(⟨1,0,0⟩,[0,r206,r207,r208,r209,r210,r211,r212,r213,r214,r215,r216,r217]),(⟨1,0,1⟩,[0,r266,r267,r268,r269,r270,r271,r272,r273,r274,r275,r276]),(⟨1,0,2⟩,[r277,r278,r183,r87,r279,r280,r281,r282,r283,r284,r285]),(⟨1,0,3⟩,[0,r286,r287,r288,r289,r290,r291,r292,r293,r294]),(⟨1,0,4⟩,[r127,r295,r296,r297,r298,r299,r300,r301,2240]),(⟨1,0,5⟩,[0,r12,r302,r303,r304,r305,r306,r307]),(⟨1,0,6⟩,[r308,r309,r310,r311,r312,r313,-736]),(⟨1,0,8⟩,[r136,r33,r168,r309,64]),(⟨1,1,0⟩,[0,r266,r267,r268,r269,r270,r271,r272,r273,r274,r275,r276]),(⟨1,1,1⟩,[r335,r341,r342,r343,r344,r345,r346,r347,r348,r349,-4704]),(⟨1,1,2⟩,[0,0,r86,r51,r350,r351,r352,r353,r354,448]),(⟨1,1,3⟩,[r355,r356,r357,384,r358,-384,r359,r360,2464]),(⟨1,1,5⟩,[r86,r361,r362,r363,r364,r365,-448]),(⟨1,2,0⟩,[r277,r278,r183,r87,r279,r280,r281,r282,r283,r284,r285]),(⟨1,2,1⟩,[0,0,r86,r51,r350,r351,r352,r353,r354,448]),(⟨1,2,3⟩,[0,0,r136,r366,r74,r114,r367,-64]),(⟨1,3,0⟩,[0,r286,r287,r288,r289,r290,r291,r292,r293,r294]),(⟨1,3,1⟩,[r355,r356,r357,384,r358,-384,r359,r360,2464]),(⟨1,3,2⟩,[0,0,r136,r366,r74,r114,r367,-64]),(⟨1,3,3⟩,[r152,r153,r154,r155,r156,r157,-576]),(⟨1,3,5⟩,[r136,r33,r168,r309,64]),(⟨1,4,0⟩,[r127,r295,r296,r297,r298,r299,r300,r301,2240]),(⟨1,5,0⟩,[0,r12,r302,r303,r304,r305,r306,r307]),(⟨1,5,1⟩,[r86,r361,r362,r363,r364,r365,-448]),(⟨1,5,3⟩,[r136,r33,r168,r309,64]),(⟨1,6,0⟩,[r308,r309,r310,r311,r312,r313,-736]),(⟨1,8,0⟩,[r136,r33,r168,r309,64]),(⟨2,0,0⟩,[0,r206,r218,r219,r220,r221,r222,r223,r224,-8064,r225,r226]),(⟨2,0,1⟩,[r277,r278,r183,r87,r279,r280,r281,r282,r283,r284,r285]),(⟨2,0,2⟩,[0,0,0,r65,r314,r315,r316,r317,r318,r319]),(⟨2,0,3⟩,[r320,r321,r322,r323,r324,r325,r326,r327,r328]),(⟨2,0,5⟩,[0,r152,r257,r258,r259,r260,r261]),(⟨2,1,0⟩,[r277,r278,r183,r87,r279,r280,r281,r282,r283,r284,r285]),(⟨2,1,1⟩,[0,0,r86,r51,r350,r351,r352,r353,r354,448]),(⟨2,1,3⟩,[0,0,r136,r366,r74,r114,r367,-64]),(⟨2,2,0⟩,[0,0,0,r65,r314,r315,r316,r317,r318,r319]),(⟨2,3,0⟩,[r320,r321,r322,r323,r324,r325,r326,r327,r328]),(⟨2,3,1⟩,[0,0,r136,r366,r74,r114,r367,-64]),(⟨2,5,0⟩,[0,r152,r257,r258,r259,r260,r261]),(⟨3,0,0⟩,[0,r65,r227,r228,r229,r230,r231,r232,r233,r234,r235]),(⟨3,0,1⟩,[0,r286,r287,r288,r289,r290,r291,r292,r293,r294]),(⟨3,0,2⟩,[r320,r321,r322,r323,r324,r325,r326,r327,r328]),(⟨3,0,3⟩,[0,r75,r329,r330,r331,r332,r333,r334]),(⟨3,0,4⟩,[r335,r336,r337,r338,r339,r340,-288]),(⟨3,0,5⟩,[0,r152,r262,r263,r264,r265]),(⟨3,0,6⟩,[r136,r33,r168,r309,64]),(⟨3,1,0⟩,[0,r286,r287,r288,r289,r290,r291,r292,r293,r294]),(⟨3,1,1⟩,[r355,r356,r357,384,r358,-384,r359,r360,2464]),(⟨3,1,2⟩,[0,0,r136,r366,r74,r114,r367,-64]),(⟨3,1,3⟩,[r152,r153,r154,r155,r156,r157,-576]),(⟨3,1,5⟩,[r136,r33,r168,r309,64]),(⟨3,2,0⟩,[r320,r321,r322,r323,r324,r325,r326,r327,r328]),(⟨3,2,1⟩,[0,0,r136,r366,r74,r114,r367,-64]),(⟨3,3,0⟩,[0,r75,r329,r330,r331,r332,r333,r334]),(⟨3,3,1⟩,[r152,r153,r154,r155,r156,r157,-576]),(⟨3,4,0⟩,[r335,r336,r337,r338,r339,r340,-288]),(⟨3,5,0⟩,[0,r152,r262,r263,r264,r265]),(⟨3,5,1⟩,[r136,r33,r168,r309,64]),(⟨3,6,0⟩,[r136,r33,r168,r309,64]),(⟨4,0,0⟩,[0,r65,r236,r237,r238,r239,r240,r241,r242,r243]),(⟨4,0,1⟩,[r127,r295,r296,r297,r298,r299,r300,r301,2240]),(⟨4,0,3⟩,[r335,r336,r337,r338,r339,r340,-288]),(⟨4,1,0⟩,[r127,r295,r296,r297,r298,r299,r300,r301,2240]),(⟨4,3,0⟩,[r335,r336,r337,r338,r339,r340,-288]),(⟨5,0,0⟩,[0,r244,r169,r245,r246,r247,r248,r249,r250]),(⟨5,0,1⟩,[0,r12,r302,r303,r304,r305,r306,r307]),(⟨5,0,2⟩,[0,r152,r257,r258,r259,r260,r261]),(⟨5,0,3⟩,[0,r152,r262,r263,r264,r265]),(⟨5,1,0⟩,[0,r12,r302,r303,r304,r305,r306,r307]),(⟨5,1,1⟩,[r86,r361,r362,r363,r364,r365,-448]),(⟨5,1,3⟩,[r136,r33,r168,r309,64]),(⟨5,2,0⟩,[0,r152,r257,r258,r259,r260,r261]),(⟨5,3,0⟩,[0,r152,r262,r263,r264,r265]),(⟨5,3,1⟩,[r136,r33,r168,r309,64]),(⟨6,0,0⟩,[0,r244,r251,r252,r253,r254,r255,r256]),(⟨6,0,1⟩,[r308,r309,r310,r311,r312,r313,-736]),(⟨6,0,3⟩,[r136,r33,r168,r309,64]),(⟨6,1,0⟩,[r308,r309,r310,r311,r312,r313,-736]),(⟨6,3,0⟩,[r136,r33,r168,r309,64]),(⟨7,0,0⟩,[0,r152,r257,r258,r259,r260,r261]),(⟨8,0,0⟩,[0,r152,r262,r263,r264,r265]),(⟨8,0,1⟩,[r136,r33,r168,r309,64]),(⟨8,1,0⟩,[r136,r33,r168,r309,64])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,-3,15,-21,3,6]),(⟨0,0,1⟩,[1,-5,10,-11,7]),(⟨0,0,2⟩,[0,0,2,-2]),(⟨0,0,3⟩,[-3,8,-9]),(⟨0,0,5⟩,[2]),(⟨0,1,0⟩,[1,-5,10,-11,7]),(⟨0,2,0⟩,[0,0,2,-2]),(⟨0,3,0⟩,[-3,8,-9]),(⟨0,5,0⟩,[2]),(⟨1,0,0⟩,[1,-5,10,-11,7]),(⟨2,0,0⟩,[0,0,2,-2]),(⟨3,0,0⟩,[-3,8,-9]),(⟨5,0,0⟩,[2])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[0,-384,8064,-64256,246656,-476544,385152,5632,-79744]),(⟨0,0,1⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨0,0,2⟩,[0,384,-6400,33024,-52224,4480,12544]),(⟨0,0,3⟩,[0,384,-6656,34048,-49664,-2688]),(⟨0,1,0⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨0,1,1⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨0,1,3⟩,[-128,1536,-3840,-4608,15232]),(⟨0,2,0⟩,[0,384,-6400,33024,-52224,4480,12544]),(⟨0,3,0⟩,[0,384,-6656,34048,-49664,-2688]),(⟨0,3,1⟩,[-128,1536,-3840,-4608,15232]),(⟨1,0,0⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨1,0,1⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨1,0,3⟩,[-128,1536,-3840,-4608,15232]),(⟨1,1,0⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨1,3,0⟩,[-128,1536,-3840,-4608,15232]),(⟨2,0,0⟩,[0,384,-6400,33024,-52224,4480,12544]),(⟨3,0,0⟩,[0,384,-6656,34048,-49664,-2688]),(⟨3,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨3,1,0⟩,[-128,1536,-3840,-4608,15232])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 1 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r368) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 4 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r369) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨5,0,0⟩,[2])]

noncomputable def partial12 : Poly := [(⟨5,0,0⟩,[0,-768,16128,-128512,493312,-953088,770304,11264,-159488]),(⟨5,0,1⟩,[0,-768,14336,-96768,310272,-482048,254976,114688]),(⟨5,0,2⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨5,0,3⟩,[0,768,-13312,68096,-99328,-5376]),(⟨5,1,0⟩,[0,-768,14336,-96768,310272,-482048,254976,114688]),(⟨5,1,1⟩,[256,-3584,15616,-27648,4864,125440,-213248]),(⟨5,1,3⟩,[-256,3072,-7680,-9216,30464]),(⟨5,2,0⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨5,3,0⟩,[0,768,-13312,68096,-99328,-5376]),(⟨5,3,1⟩,[-256,3072,-7680,-9216,30464]),(⟨6,0,0⟩,[0,-768,14336,-96768,310272,-482048,254976,114688]),(⟨6,0,1⟩,[256,-3584,15616,-27648,4864,125440,-213248]),(⟨6,0,3⟩,[-256,3072,-7680,-9216,30464]),(⟨6,1,0⟩,[256,-3584,15616,-27648,4864,125440,-213248]),(⟨6,3,0⟩,[-256,3072,-7680,-9216,30464]),(⟨7,0,0⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨8,0,0⟩,[0,768,-13312,68096,-99328,-5376]),(⟨8,0,1⟩,[-256,3072,-7680,-9216,30464]),(⟨8,1,0⟩,[-256,3072,-7680,-9216,30464])]


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

noncomputable def partial8 : Poly := [(⟨0,5,0⟩,[0,-768,16128,-128512,493312,-953088,770304,11264,-159488]),(⟨0,5,1⟩,[0,-768,14336,-96768,310272,-482048,254976,114688]),(⟨0,5,2⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨0,5,3⟩,[0,768,-13312,68096,-99328,-5376]),(⟨0,6,0⟩,[0,-768,14336,-96768,310272,-482048,254976,114688]),(⟨0,6,1⟩,[256,-3584,15616,-27648,4864,125440,-213248]),(⟨0,6,3⟩,[-256,3072,-7680,-9216,30464]),(⟨0,7,0⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨0,8,0⟩,[0,768,-13312,68096,-99328,-5376]),(⟨0,8,1⟩,[-256,3072,-7680,-9216,30464]),(⟨1,0,0⟩,[0,-384,9984,-108416,652800,-2443776,5997696,-9848576,10712192,-7117440,1836672,916608,-558208]),(⟨1,0,1⟩,[0,-384,9088,-88064,472960,-1582080,3466368,-5035520,4725376,-2516096,261632,401408]),(⟨1,0,2⟩,[0,384,-8320,68864,-285568,668928,-940160,787712,-289408,-106624,87808]),(⟨1,0,3⟩,[0,384,-8576,71168,-290688,662016,-904320,757760,-318080,-18816]),(⟨1,1,0⟩,[0,-384,9088,-88064,472960,-1582080,3466368,-5035520,4725376,-2516096,261632,401408]),(⟨1,1,1⟩,[128,-2432,18048,-72192,170240,-186112,-189184,1036800,-1739136,1611904,-746368]),(⟨1,1,3⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨1,2,0⟩,[0,384,-8320,68864,-285568,668928,-940160,787712,-289408,-106624,87808]),(⟨1,3,0⟩,[0,384,-8576,71168,-290688,662016,-904320,757760,-318080,-18816]),(⟨1,3,1⟩,[-128,2176,-12800,31360,-17920,-69248,176128,-199808,106624]),(⟨1,5,0⟩,[0,-768,14336,-96768,310272,-482048,254976,114688]),(⟨1,5,1⟩,[256,-3584,15616,-27648,4864,125440,-213248]),(⟨1,5,3⟩,[-256,3072,-7680,-9216,30464]),(⟨1,6,0⟩,[256,-3584,15616,-27648,4864,125440,-213248]),(⟨1,8,0⟩,[-256,3072,-7680,-9216,30464]),(⟨2,0,0⟩,[0,-384,9088,-88832,489856,-1726720,4088192,-6481920,6448768,-3275136,90880,560896]),(⟨2,0,1⟩,[128,-2432,18048,-72960,185344,-297216,217856,244480,-1002112,1471616,-861056]),(⟨2,0,2⟩,[0,0,0,768,-13568,78848,-170496,113408,16128,-25088]),(⟨2,0,3⟩,[-128,2176,-12800,32128,-32000,12160,8704,-105856,112000]),(⟨2,1,0⟩,[128,-2432,18048,-72960,185344,-297216,217856,244480,-1002112,1471616,-861056]),(⟨2,1,1⟩,[0,0,256,-3840,19200,-43264,32512,120576,-338688,213248]),(⟨2,1,3⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨2,2,0⟩,[0,0,0,768,-13568,78848,-170496,113408,16128,-25088]),(⟨2,3,0⟩,[-128,2176,-12800,32128,-32000,12160,8704,-105856,112000]),(⟨2,3,1⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨2,5,0⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨3,0,0⟩,[0,1536,-35584,328832,-1597056,4539008,-7720832,7348608,-2734464,-935552,690816]),(⟨3,0,1⟩,[0,1152,-24320,202112,-897792,2356352,-3674368,3137664,-1027328,-302848]),(⟨3,0,2⟩,[0,-1152,22272,-153728,478464,-728448,468224,60032,-112896]),(⟨3,0,3⟩,[0,-1152,22784,-155520,470528,-697216,465152,-6272]),(⟨3,1,0⟩,[0,1152,-24320,202112,-897792,2356352,-3674368,3137664,-1027328,-302848]),(⟨3,1,1⟩,[-384,6400,-38912,120064,-188160,-44288,799744,-1417472,959616]),(⟨3,1,3⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨3,2,0⟩,[0,-1152,22272,-153728,478464,-728448,468224,60032,-112896]),(⟨3,3,0⟩,[0,-1152,22784,-155520,470528,-697216,465152,-6272]),(⟨3,3,1⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨3,5,0⟩,[0,768,-13312,68096,-99328,-5376]),(⟨3,5,1⟩,[-256,3072,-7680,-9216,30464]),(⟨3,6,0⟩,[-256,3072,-7680,-9216,30464]),(⟨4,0,0⟩,[0,1536,-33152,277888,-1221248,3140480,-4781696,3888256,-990592,-560000]),(⟨4,0,1⟩,[-512,8576,-51712,151424,-206080,-113536,975872,-1617280,1066240]),(⟨4,0,3⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨4,1,0⟩,[-512,8576,-51712,151424,-206080,-113536,975872,-1617280,1066240]),(⟨4,3,0⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨5,0,0⟩,[0,-1920,38400,-281472,957696,-1600128,1071104,165248,-267008]),(⟨5,0,1⟩,[0,-768,14080,-93440,299520,-483584,294656,84224]),(⟨5,0,2⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨5,0,3⟩,[0,768,-13312,68096,-99328,-5376]),(⟨5,1,0⟩,[0,-768,14080,-93440,299520,-483584,294656,84224]),(⟨5,1,1⟩,[256,-3584,15616,-27648,4864,125440,-213248]),(⟨5,1,3⟩,[-256,3072,-7680,-9216,30464]),(⟨5,2,0⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨5,3,0⟩,[0,768,-13312,68096,-99328,-5376]),(⟨5,3,1⟩,[-256,3072,-7680,-9216,30464]),(⟨6,0,0⟩,[0,-1920,37376,-255616,791552,-1177728,680448,138880]),(⟨6,0,1⟩,[640,-9216,40576,-58368,-43136,288768,-350336]),(⟨6,0,3⟩,[-256,3072,-7680,-9216,30464]),(⟨6,1,0⟩,[640,-9216,40576,-58368,-43136,288768,-350336]),(⟨6,3,0⟩,[-256,3072,-7680,-9216,30464]),(⟨7,0,0⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨8,0,0⟩,[0,768,-13312,68096,-99328,-5376]),(⟨8,0,1⟩,[-256,3072,-7680,-9216,30464]),(⟨8,1,0⟩,[-256,3072,-7680,-9216,30464])]


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

noncomputable def partial4 : Poly := [(⟨0,0,5⟩,[0,-768,16128,-128512,493312,-953088,770304,11264,-159488]),(⟨0,0,6⟩,[0,-768,14336,-96768,310272,-482048,254976,114688]),(⟨0,0,7⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨0,0,8⟩,[0,768,-13312,68096,-99328,-5376]),(⟨0,1,0⟩,[0,-384,9984,-108416,652800,-2443776,5997696,-9848576,10712192,-7117440,1836672,916608,-558208]),(⟨0,1,1⟩,[0,-384,9088,-88064,472960,-1582080,3466368,-5035520,4725376,-2516096,261632,401408]),(⟨0,1,2⟩,[0,384,-8320,68864,-285568,668928,-940160,787712,-289408,-106624,87808]),(⟨0,1,3⟩,[0,384,-8576,71168,-290688,662016,-904320,757760,-318080,-18816]),(⟨0,1,5⟩,[0,-768,14336,-96768,310272,-482048,254976,114688]),(⟨0,1,6⟩,[256,-3584,15616,-27648,4864,125440,-213248]),(⟨0,1,8⟩,[-256,3072,-7680,-9216,30464]),(⟨0,2,0⟩,[0,-384,9088,-88832,489856,-1726720,4088192,-6481920,6448768,-3275136,90880,560896]),(⟨0,2,1⟩,[128,-2432,18048,-72960,185344,-297216,217856,244480,-1002112,1471616,-861056]),(⟨0,2,2⟩,[0,0,0,768,-13568,78848,-170496,113408,16128,-25088]),(⟨0,2,3⟩,[-128,2176,-12800,32128,-32000,12160,8704,-105856,112000]),(⟨0,2,5⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨0,3,0⟩,[0,1536,-35584,328832,-1597056,4539008,-7720832,7348608,-2734464,-935552,690816]),(⟨0,3,1⟩,[0,1152,-24320,202112,-897792,2356352,-3674368,3137664,-1027328,-302848]),(⟨0,3,2⟩,[0,-1152,22272,-153728,478464,-728448,468224,60032,-112896]),(⟨0,3,3⟩,[0,-1152,22784,-155520,470528,-697216,465152,-6272]),(⟨0,3,5⟩,[0,768,-13312,68096,-99328,-5376]),(⟨0,3,6⟩,[-256,3072,-7680,-9216,30464]),(⟨0,4,0⟩,[0,1536,-33152,277888,-1221248,3140480,-4781696,3888256,-990592,-560000]),(⟨0,4,1⟩,[-512,8576,-51712,151424,-206080,-113536,975872,-1617280,1066240]),(⟨0,4,3⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨0,5,0⟩,[0,-1920,38400,-281472,957696,-1600128,1071104,165248,-267008]),(⟨0,5,1⟩,[0,-768,14080,-93440,299520,-483584,294656,84224]),(⟨0,5,2⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨0,5,3⟩,[0,768,-13312,68096,-99328,-5376]),(⟨0,6,0⟩,[0,-1920,37376,-255616,791552,-1177728,680448,138880]),(⟨0,6,1⟩,[640,-9216,40576,-58368,-43136,288768,-350336]),(⟨0,6,3⟩,[-256,3072,-7680,-9216,30464]),(⟨0,7,0⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨0,8,0⟩,[0,768,-13312,68096,-99328,-5376]),(⟨0,8,1⟩,[-256,3072,-7680,-9216,30464]),(⟨1,0,0⟩,[0,-384,9984,-108416,652800,-2443776,5997696,-9848576,10712192,-7117440,1836672,916608,-558208]),(⟨1,0,1⟩,[0,-384,9088,-88064,472960,-1582080,3466368,-5035520,4725376,-2516096,261632,401408]),(⟨1,0,2⟩,[0,384,-8320,68864,-285568,668928,-940160,787712,-289408,-106624,87808]),(⟨1,0,3⟩,[0,384,-8576,71168,-290688,662016,-904320,757760,-318080,-18816]),(⟨1,0,5⟩,[0,-768,14336,-96768,310272,-482048,254976,114688]),(⟨1,0,6⟩,[256,-3584,15616,-27648,4864,125440,-213248]),(⟨1,0,8⟩,[-256,3072,-7680,-9216,30464]),(⟨1,1,0⟩,[0,-768,18176,-176128,945920,-3164160,6932736,-10071040,9450752,-5032192,523264,802816]),(⟨1,1,1⟩,[256,-4864,36096,-144384,340480,-372224,-378368,2073600,-3478272,3223808,-1492736]),(⟨1,1,3⟩,[-256,4352,-25600,62720,-35840,-138496,352256,-399616,213248]),(⟨1,1,5⟩,[256,-3584,15616,-27648,4864,125440,-213248]),(⟨1,2,0⟩,[128,-2048,9728,-4096,-100224,371712,-722304,1032192,-1291520,1364992,-773248]),(⟨1,2,1⟩,[0,0,256,-3840,19200,-43264,32512,120576,-338688,213248]),(⟨1,2,3⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨1,3,0⟩,[0,1536,-32896,273280,-1188480,3018368,-4578688,3895424,-1345408,-321664]),(⟨1,3,1⟩,[-512,8576,-51712,151424,-206080,-113536,975872,-1617280,1066240]),(⟨1,3,3⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨1,3,5⟩,[-256,3072,-7680,-9216,30464]),(⟨1,4,0⟩,[-512,8576,-51712,151424,-206080,-113536,975872,-1617280,1066240]),(⟨1,5,0⟩,[0,-768,14080,-93440,299520,-483584,294656,84224]),(⟨1,5,1⟩,[256,-3584,15616,-27648,4864,125440,-213248]),(⟨1,5,3⟩,[-256,3072,-7680,-9216,30464]),(⟨1,6,0⟩,[640,-9216,40576,-58368,-43136,288768,-350336]),(⟨1,8,0⟩,[-256,3072,-7680,-9216,30464]),(⟨2,0,0⟩,[0,-384,9088,-88832,489856,-1726720,4088192,-6481920,6448768,-3275136,90880,560896]),(⟨2,0,1⟩,[128,-2432,18048,-72960,185344,-297216,217856,244480,-1002112,1471616,-861056]),(⟨2,0,2⟩,[0,0,0,768,-13568,78848,-170496,113408,16128,-25088]),(⟨2,0,3⟩,[-128,2176,-12800,32128,-32000,12160,8704,-105856,112000]),(⟨2,0,5⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨2,1,0⟩,[128,-2048,9728,-4096,-100224,371712,-722304,1032192,-1291520,1364992,-773248]),(⟨2,1,1⟩,[0,0,256,-3840,19200,-43264,32512,120576,-338688,213248]),(⟨2,1,3⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨2,2,0⟩,[0,0,0,1536,-27136,157696,-340992,226816,32256,-50176]),(⟨2,3,0⟩,[-128,1024,9472,-121600,446464,-716288,476928,-45824,-896]),(⟨2,3,1⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨2,5,0⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨3,0,0⟩,[0,1536,-35584,328832,-1597056,4539008,-7720832,7348608,-2734464,-935552,690816]),(⟨3,0,1⟩,[0,1152,-24320,202112,-897792,2356352,-3674368,3137664,-1027328,-302848]),(⟨3,0,2⟩,[0,-1152,22272,-153728,478464,-728448,468224,60032,-112896]),(⟨3,0,3⟩,[0,-1152,22784,-155520,470528,-697216,465152,-6272]),(⟨3,0,5⟩,[0,768,-13312,68096,-99328,-5376]),(⟨3,0,6⟩,[-256,3072,-7680,-9216,30464]),(⟨3,1,0⟩,[0,1536,-32896,273280,-1188480,3018368,-4578688,3895424,-1345408,-321664]),(⟨3,1,1⟩,[-512,8576,-51712,151424,-206080,-113536,975872,-1617280,1066240]),(⟨3,1,3⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨3,1,5⟩,[-256,3072,-7680,-9216,30464]),(⟨3,2,0⟩,[-128,1024,9472,-121600,446464,-716288,476928,-45824,-896]),(⟨3,2,1⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨3,3,0⟩,[0,-2304,45568,-311040,941056,-1394432,930304,-12544]),(⟨3,3,1⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨3,4,0⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨3,5,0⟩,[0,768,-13312,68096,-99328,-5376]),(⟨3,5,1⟩,[-256,3072,-7680,-9216,30464]),(⟨3,6,0⟩,[-256,3072,-7680,-9216,30464]),(⟨4,0,0⟩,[0,1536,-33152,277888,-1221248,3140480,-4781696,3888256,-990592,-560000]),(⟨4,0,1⟩,[-512,8576,-51712,151424,-206080,-113536,975872,-1617280,1066240]),(⟨4,0,3⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨4,1,0⟩,[-512,8576,-51712,151424,-206080,-113536,975872,-1617280,1066240]),(⟨4,3,0⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨5,0,0⟩,[0,-1920,38400,-281472,957696,-1600128,1071104,165248,-267008]),(⟨5,0,1⟩,[0,-768,14080,-93440,299520,-483584,294656,84224]),(⟨5,0,2⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨5,0,3⟩,[0,768,-13312,68096,-99328,-5376]),(⟨5,1,0⟩,[0,-768,14080,-93440,299520,-483584,294656,84224]),(⟨5,1,1⟩,[256,-3584,15616,-27648,4864,125440,-213248]),(⟨5,1,3⟩,[-256,3072,-7680,-9216,30464]),(⟨5,2,0⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨5,3,0⟩,[0,768,-13312,68096,-99328,-5376]),(⟨5,3,1⟩,[-256,3072,-7680,-9216,30464]),(⟨6,0,0⟩,[0,-1920,37376,-255616,791552,-1177728,680448,138880]),(⟨6,0,1⟩,[640,-9216,40576,-58368,-43136,288768,-350336]),(⟨6,0,3⟩,[-256,3072,-7680,-9216,30464]),(⟨6,1,0⟩,[640,-9216,40576,-58368,-43136,288768,-350336]),(⟨6,3,0⟩,[-256,3072,-7680,-9216,30464]),(⟨7,0,0⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨8,0,0⟩,[0,768,-13312,68096,-99328,-5376]),(⟨8,0,1⟩,[-256,3072,-7680,-9216,30464]),(⟨8,1,0⟩,[-256,3072,-7680,-9216,30464])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,0,1152,-29952,321792,-1874304,6500736,-13627776,16122240,-7714176,-3018240,4002432,-205440,-478464]),(⟨0,0,1⟩,[0,-384,11136,-135680,913536,-3786624,10083072,-17206400,17689088,-8726784,-431232,1853568,-214144]),(⟨0,0,2⟩,[0,-384,7936,-63872,286720,-939136,2580992,-5294976,6584320,-3838464,155392,636160]),(⟨0,0,3⟩,[0,1536,-36736,354560,-1807104,5339648,-9190400,8413440,-2622720,-1241600,674688]),(⟨0,0,4⟩,[0,1536,-33152,277888,-1221248,3140480,-4781696,3888256,-990592,-560000]),(⟨0,0,5⟩,[0,-1920,38400,-281472,957696,-1600128,1071104,165248,-267008]),(⟨0,0,6⟩,[0,-1920,37376,-255616,791552,-1177728,680448,138880]),(⟨0,0,7⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨0,0,8⟩,[0,768,-13312,68096,-99328,-5376]),(⟨0,1,0⟩,[0,-384,11136,-135680,913536,-3786624,10083072,-17206400,17689088,-8726784,-431232,1853568,-214144]),(⟨0,1,1⟩,[0,-1152,25472,-229120,1142528,-3547392,7084032,-8856064,6458624,-2590336,579712,163072]),(⟨0,1,2⟩,[128,-2048,9728,-4096,-100224,371712,-722304,1032192,-1291520,1364992,-773248]),(⟨0,1,3⟩,[0,1920,-39424,310528,-1264896,2988032,-4255744,3538688,-1327360,-230272]),(⟨0,1,4⟩,[-512,8576,-51712,151424,-206080,-113536,975872,-1617280,1066240]),(⟨0,1,5⟩,[0,-768,14080,-93440,299520,-483584,294656,84224]),(⟨0,1,6⟩,[640,-9216,40576,-58368,-43136,288768,-350336]),(⟨0,1,8⟩,[-256,3072,-7680,-9216,30464]),(⟨0,2,0⟩,[0,-384,7936,-63872,286720,-939136,2580992,-5294976,6584320,-3838464,155392,636160]),(⟨0,2,1⟩,[128,-2048,9728,-4096,-100224,371712,-722304,1032192,-1291520,1364992,-773248]),(⟨0,2,2⟩,[0,0,0,1536,-27136,157696,-340992,226816,32256,-50176]),(⟨0,2,3⟩,[-128,1024,9472,-121600,446464,-716288,476928,-45824,-896]),(⟨0,2,5⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨0,3,0⟩,[0,1536,-36736,354560,-1807104,5339648,-9190400,8413440,-2622720,-1241600,674688]),(⟨0,3,1⟩,[0,1920,-39424,310528,-1264896,2988032,-4255744,3538688,-1327360,-230272]),(⟨0,3,2⟩,[-128,1024,9472,-121600,446464,-716288,476928,-45824,-896]),(⟨0,3,3⟩,[0,-2304,45568,-311040,941056,-1394432,930304,-12544]),(⟨0,3,4⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨0,3,5⟩,[0,768,-13312,68096,-99328,-5376]),(⟨0,3,6⟩,[-256,3072,-7680,-9216,30464]),(⟨0,4,0⟩,[0,1536,-33152,277888,-1221248,3140480,-4781696,3888256,-990592,-560000]),(⟨0,4,1⟩,[-512,8576,-51712,151424,-206080,-113536,975872,-1617280,1066240]),(⟨0,4,3⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨0,5,0⟩,[0,-1920,38400,-281472,957696,-1600128,1071104,165248,-267008]),(⟨0,5,1⟩,[0,-768,14080,-93440,299520,-483584,294656,84224]),(⟨0,5,2⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨0,5,3⟩,[0,768,-13312,68096,-99328,-5376]),(⟨0,6,0⟩,[0,-1920,37376,-255616,791552,-1177728,680448,138880]),(⟨0,6,1⟩,[640,-9216,40576,-58368,-43136,288768,-350336]),(⟨0,6,3⟩,[-256,3072,-7680,-9216,30464]),(⟨0,7,0⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨0,8,0⟩,[0,768,-13312,68096,-99328,-5376]),(⟨0,8,1⟩,[-256,3072,-7680,-9216,30464]),(⟨1,0,0⟩,[0,-384,11136,-135680,913536,-3786624,10083072,-17206400,17689088,-8726784,-431232,1853568,-214144]),(⟨1,0,1⟩,[0,-1152,25472,-229120,1142528,-3547392,7084032,-8856064,6458624,-2590336,579712,163072]),(⟨1,0,2⟩,[128,-2048,9728,-4096,-100224,371712,-722304,1032192,-1291520,1364992,-773248]),(⟨1,0,3⟩,[0,1920,-39424,310528,-1264896,2988032,-4255744,3538688,-1327360,-230272]),(⟨1,0,4⟩,[-512,8576,-51712,151424,-206080,-113536,975872,-1617280,1066240]),(⟨1,0,5⟩,[0,-768,14080,-93440,299520,-483584,294656,84224]),(⟨1,0,6⟩,[640,-9216,40576,-58368,-43136,288768,-350336]),(⟨1,0,8⟩,[-256,3072,-7680,-9216,30464]),(⟨1,1,0⟩,[0,-1152,25472,-229120,1142528,-3547392,7084032,-8856064,6458624,-2590336,579712,163072]),(⟨1,1,1⟩,[384,-7296,54144,-216576,510720,-558336,-567552,3110400,-5217408,4835712,-2239104]),(⟨1,1,2⟩,[0,0,256,-3840,19200,-43264,32512,120576,-338688,213248]),(⟨1,1,3⟩,[-640,10752,-64512,182784,-224000,-182784,1152000,-1817088,1172864]),(⟨1,1,5⟩,[256,-3584,15616,-27648,4864,125440,-213248]),(⟨1,2,0⟩,[128,-2048,9728,-4096,-100224,371712,-722304,1032192,-1291520,1364992,-773248]),(⟨1,2,1⟩,[0,0,256,-3840,19200,-43264,32512,120576,-338688,213248]),(⟨1,2,3⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨1,3,0⟩,[0,1920,-39424,310528,-1264896,2988032,-4255744,3538688,-1327360,-230272]),(⟨1,3,1⟩,[-640,10752,-64512,182784,-224000,-182784,1152000,-1817088,1172864]),(⟨1,3,2⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨1,3,3⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨1,3,5⟩,[-256,3072,-7680,-9216,30464]),(⟨1,4,0⟩,[-512,8576,-51712,151424,-206080,-113536,975872,-1617280,1066240]),(⟨1,5,0⟩,[0,-768,14080,-93440,299520,-483584,294656,84224]),(⟨1,5,1⟩,[256,-3584,15616,-27648,4864,125440,-213248]),(⟨1,5,3⟩,[-256,3072,-7680,-9216,30464]),(⟨1,6,0⟩,[640,-9216,40576,-58368,-43136,288768,-350336]),(⟨1,8,0⟩,[-256,3072,-7680,-9216,30464]),(⟨2,0,0⟩,[0,-384,7936,-63872,286720,-939136,2580992,-5294976,6584320,-3838464,155392,636160]),(⟨2,0,1⟩,[128,-2048,9728,-4096,-100224,371712,-722304,1032192,-1291520,1364992,-773248]),(⟨2,0,2⟩,[0,0,0,1536,-27136,157696,-340992,226816,32256,-50176]),(⟨2,0,3⟩,[-128,1024,9472,-121600,446464,-716288,476928,-45824,-896]),(⟨2,0,5⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨2,1,0⟩,[128,-2048,9728,-4096,-100224,371712,-722304,1032192,-1291520,1364992,-773248]),(⟨2,1,1⟩,[0,0,256,-3840,19200,-43264,32512,120576,-338688,213248]),(⟨2,1,3⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨2,2,0⟩,[0,0,0,1536,-27136,157696,-340992,226816,32256,-50176]),(⟨2,3,0⟩,[-128,1024,9472,-121600,446464,-716288,476928,-45824,-896]),(⟨2,3,1⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨2,5,0⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨3,0,0⟩,[0,1536,-36736,354560,-1807104,5339648,-9190400,8413440,-2622720,-1241600,674688]),(⟨3,0,1⟩,[0,1920,-39424,310528,-1264896,2988032,-4255744,3538688,-1327360,-230272]),(⟨3,0,2⟩,[-128,1024,9472,-121600,446464,-716288,476928,-45824,-896]),(⟨3,0,3⟩,[0,-2304,45568,-311040,941056,-1394432,930304,-12544]),(⟨3,0,4⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨3,0,5⟩,[0,768,-13312,68096,-99328,-5376]),(⟨3,0,6⟩,[-256,3072,-7680,-9216,30464]),(⟨3,1,0⟩,[0,1920,-39424,310528,-1264896,2988032,-4255744,3538688,-1327360,-230272]),(⟨3,1,1⟩,[-640,10752,-64512,182784,-224000,-182784,1152000,-1817088,1172864]),(⟨3,1,2⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨3,1,3⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨3,1,5⟩,[-256,3072,-7680,-9216,30464]),(⟨3,2,0⟩,[-128,1024,9472,-121600,446464,-716288,476928,-45824,-896]),(⟨3,2,1⟩,[0,0,-256,3328,-10752,-1536,39680,-30464]),(⟨3,3,0⟩,[0,-2304,45568,-311040,941056,-1394432,930304,-12544]),(⟨3,3,1⟩,[768,-11264,49920,-61440,-96000,326656,-274176]),(⟨3,4,0⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨3,5,0⟩,[0,768,-13312,68096,-99328,-5376]),(⟨3,5,1⟩,[-256,3072,-7680,-9216,30464]),(⟨3,6,0⟩,[-256,3072,-7680,-9216,30464]),(⟨4,0,0⟩,[0,1536,-33152,277888,-1221248,3140480,-4781696,3888256,-990592,-560000]),(⟨4,0,1⟩,[-512,8576,-51712,151424,-206080,-113536,975872,-1617280,1066240]),(⟨4,0,3⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨4,1,0⟩,[-512,8576,-51712,151424,-206080,-113536,975872,-1617280,1066240]),(⟨4,3,0⟩,[384,-5632,24960,-30720,-48000,163328,-137088]),(⟨5,0,0⟩,[0,-1920,38400,-281472,957696,-1600128,1071104,165248,-267008]),(⟨5,0,1⟩,[0,-768,14080,-93440,299520,-483584,294656,84224]),(⟨5,0,2⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨5,0,3⟩,[0,768,-13312,68096,-99328,-5376]),(⟨5,1,0⟩,[0,-768,14080,-93440,299520,-483584,294656,84224]),(⟨5,1,1⟩,[256,-3584,15616,-27648,4864,125440,-213248]),(⟨5,1,3⟩,[-256,3072,-7680,-9216,30464]),(⟨5,2,0⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨5,3,0⟩,[0,768,-13312,68096,-99328,-5376]),(⟨5,3,1⟩,[-256,3072,-7680,-9216,30464]),(⟨6,0,0⟩,[0,-1920,37376,-255616,791552,-1177728,680448,138880]),(⟨6,0,1⟩,[640,-9216,40576,-58368,-43136,288768,-350336]),(⟨6,0,3⟩,[-256,3072,-7680,-9216,30464]),(⟨6,1,0⟩,[640,-9216,40576,-58368,-43136,288768,-350336]),(⟨6,3,0⟩,[-256,3072,-7680,-9216,30464]),(⟨7,0,0⟩,[0,768,-12800,66048,-104448,8960,25088]),(⟨8,0,0⟩,[0,768,-13312,68096,-99328,-5376]),(⟨8,0,1⟩,[-256,3072,-7680,-9216,30464]),(⟨8,1,0⟩,[-256,3072,-7680,-9216,30464])]


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
    (Poly.add (Poly.scale (K.ofRat r370) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 1 4).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r368*r369 : ℚ)=r370 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 1 4 r368 r369 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 1=4 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 1 4).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C062

#print axioms Coulomb8.Columns.C062.sound
