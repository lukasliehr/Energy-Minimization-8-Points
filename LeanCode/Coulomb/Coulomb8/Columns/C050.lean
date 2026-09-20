import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C050

def r0 : ℚ := { num := 96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 2112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 114624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -1143168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 5508864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -944064, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 4243968, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -33917280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 20092416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -117888, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -4918464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 140928, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -3200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := -25472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 62400, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -403712, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 1554368, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -27401600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 45844000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -49090176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 29498176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -5409792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := -342208, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 64, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -4096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -34240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 455936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -366144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 1285120, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -21126464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 33177152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -33311872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 2682624, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -560896, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -4224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 106752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -724544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 2521600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -4830528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 4298752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 59904, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -5955648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 591936, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -160, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 1408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 162880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -1225344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 4437120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -551552, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := 11860160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -8278336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 310752, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -227328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 69248, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -2787136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 496384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -281568, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := -128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := 1216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 7424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -113088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 446336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -852672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 857088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := 3648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := -54528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := 197696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := -331136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := 37952, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -9600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 12032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := 268288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := -2197248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := 8820608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := -21791104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := 4969920, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := -35206720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := 1195520, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -687744, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -9344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := 9600, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := -203904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := 27968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := 1779840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -6189440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := 10607232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := -9884704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 590336, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -1312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 87936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -631488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 132416, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -4729728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 5982080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := -4186272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := 156704, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -1728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 1984, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -24896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -173120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 143168, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -2236736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 2490688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -172800, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := -1600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := 13504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := -43712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := 4672, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 100928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := -257216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := -1024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := 320, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := -1536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -3392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 6656, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 1664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := -768, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 19840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := 1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := -3840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -4608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := -1920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := 9856, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := -444672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 212096, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -2914432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 477056, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -278208, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := 31360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := 128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 512, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -27008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 28352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 33408, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -902912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 199808, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -128352, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := -576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := 1536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := -9920, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 196096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := -39232, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := 180224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := 6016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := -116352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := 72064, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := -1057664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 1193600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -75904, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 9088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -3840, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 194304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -284544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := 30336, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := -256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := 3328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 39680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := 768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -14592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 6144, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := 35328, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := 19968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := -2070528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 592896, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -3796224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := 256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := 30720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -98816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 137728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := 84480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := -36864, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := 140800, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := -512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := 7680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := -36352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := 59904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 20992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -228864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 359936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := -384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -8320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 34688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := 8832, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := -19840, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := 3072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := -7680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := -9216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := 48, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 1056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := 57312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := -571584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := 2754432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -472032, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := 2121984, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := -16958640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := 10046208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := -58944, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := -2459232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := 70464, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := -16, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := 320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -12736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 31200, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := -201856, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 777184, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -13700800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := 22922000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := -24545088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := 14749088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -2704896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := -171104, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := 32, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := -2048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -17120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 227968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := -183072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := 642560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := -10563232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := 16588576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := -16655936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := 1341312, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -280448, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := -352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -2112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := 53376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := -362272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := 1260800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -2415264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := 2149376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := 29952, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := -2977824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := 295968, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := -80, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := 704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := 81440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := -612672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := 2218560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -275776, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := 5930080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := -4139168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 155376, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := 16, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := -64, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := 480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := -113664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := 34624, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := -1393568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := 248192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := -140784, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := 608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := 3712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -56544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := 223168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := -426336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := 428544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := 1824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := -27264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := 98848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -165568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 18976, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := 96, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := -4800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := 134144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := -1098624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := 4410304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := -10895552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := 2484960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := -17603360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := 597760, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -343872, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := 240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := -4672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := 4800, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := -101952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := 13984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := 889920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -3094720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 5303616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -4942352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 295168, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := -192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := 43968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -315744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := 66208, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := -2364864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := 2991040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := -2093136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := 78352, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := -864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := 992, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -12448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := -86560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := 71584, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := -1118368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := 1245344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := -86400, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 6752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := -21856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 2336, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := 50464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := -128608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := 160, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := -1696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := 3328, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := 832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := 9920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := -2304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := -960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := 4928, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := -222336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := 106048, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := -1457216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := 238528, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := -139104, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := 15680, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -13504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 14176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := 16704, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := -451456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := 99904, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := -64176, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := -288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := 768, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := -4960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := 98048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := -19616, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := 90112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := 3008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := -58176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := 36032, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := -528832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := 596800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := -37952, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := 4544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := -1920, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := 97152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := -142272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := 15168, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := 384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := -7296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := 3072, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := 17664, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := 9984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := -1035264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := 296448, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := -1898112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := 15360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := -49408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := 68864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := 42240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := -18432, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := 70400, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := 3840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := -18176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := 29952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := 10496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := -114432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := 179968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := -192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := -4160, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := 17344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := 4416, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := -9920, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := 1, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := 1, den := 476, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12],[r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25],[r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37],[r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48],[r49,r50,r51,r52,r53,r54,r55,r56,r57,r58],[r59,r60,r61,0,r62,r63,r64,r65,r66],[r67,r68,r69,r70,r71,r72,r73,-2496],[r26,r14,r74,r75,r76,r77,r78],[],[],[],[],[],[r26,r79,r80,r81,r82,r83,r84,r85,r86,r87,r88,r89],[0,r90,r91,r92,r93,r94,r95,r96,r97,r98,r99],[r0,r100,r101,r102,r103,r104,r105,r106,r107,r108],[r38,r109,r110,r111,r112,r113,r114,r115,r116],[r38,r117,r118,r119,r120,r121,r122,1856],[r38,r123,r124,r125,r126,r127,-448],[r67,r128,r129,r130,r131,-128],[r67,r132,r133,r134,128],[],[],[],[r38,r130,r135,r136,r137,r138,r139,r140,r141,r142],[r13,r143,r144,r145,r146,r147,r148,r149,r150],[0,r151,r152,r153,r154,r155,r156,r61],[],[],[],[],[],[],[r67,r51,r157,r158,r159,r160,r161,r162],[0,r101,r163,r164,r165,r166,r167],[],[],[],[],[],[r168,r169,r125,r1,r170,-256],[r67,r132,r133,r134,128],[],[],[],[],[],[],[],[0,r171,r172,r173,-3072,r174,r175,r176,r177,r178,11520],[0,r179,r134,r180,r181,r182,r183,r184,r185,-5376],[0,r186,r187,r188,r189,r190,r191,r192,-1536],[r143,r193,r131,r194,r195,r196,r197,2176],[],[],[],[],[],[],[],[],[r38,r123,r124,r125,r126,r127,-448],[],[],[],[],[],[],[r67,r128,r129,r130,r131,-128],[],[],[],[],[r168,r198,r199,r200,256],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,r201,r130,r202,r203,r204,r205,r206,r207,r208,r209,r210,r211,r212]),(⟨0,0,1⟩,[r213,r214,r117,r215,r216,r217,r218,r219,r220,r221,r222,r223,r224]),(⟨0,0,2⟩,[r13,r225,r226,r227,r228,r229,r230,r231,r232,r233,r234,r235]),(⟨0,0,3⟩,[r59,r236,r237,r238,r239,r240,r241,r242,r243,r244,r245]),(⟨0,0,4⟩,[r0,r246,r247,r248,r249,r250,r251,r252,r253,r254]),(⟨0,0,5⟩,[r255,r256,r257,0,r258,r259,r260,r261,r262]),(⟨0,0,6⟩,[r26,r263,r264,r265,r266,r267,r268,-1248]),(⟨0,0,7⟩,[r13,r214,r269,r270,r271,r272,r273]),(⟨0,1,0⟩,[r213,r214,r117,r215,r216,r217,r218,r219,r220,r221,r222,r223,r224]),(⟨0,1,1⟩,[r13,r274,r275,r157,r276,r277,r278,r279,r280,r281,r282,r283]),(⟨0,1,2⟩,[0,r284,r285,r286,r287,r288,r289,r290,r291,r292,r293]),(⟨0,1,3⟩,[r201,r294,r295,r296,r297,r298,r299,r300,r301,r302]),(⟨0,1,4⟩,[r59,r303,r304,r305,r306,r307,r308,r309,r310]),(⟨0,1,5⟩,[r59,r311,r312,r313,r314,r315,r316,928]),(⟨0,1,6⟩,[r59,r186,r317,r129,r318,r319,-224]),(⟨0,1,7⟩,[r26,r320,r193,r101,r321,-64]),(⟨0,1,8⟩,[r26,r171,r135,r322,64]),(⟨0,2,0⟩,[r13,r225,r226,r227,r228,r229,r230,r231,r232,r233,r234,r235]),(⟨0,2,1⟩,[0,r284,r285,r286,r287,r288,r289,r290,r291,r292,r293]),(⟨0,2,2⟩,[r59,r101,r323,r324,r325,r326,r327,r328,r329,r330]),(⟨0,2,3⟩,[r213,r38,r331,r332,r333,r334,r335,r336,r337]),(⟨0,2,4⟩,[0,r338,r339,r340,r341,r342,r343,r257]),(⟨0,3,0⟩,[r59,r236,r237,r238,r239,r240,r241,r242,r243,r244,r245]),(⟨0,3,1⟩,[r201,r294,r295,r296,r297,r298,r299,r300,r301,r302]),(⟨0,3,2⟩,[r213,r38,r331,r332,r333,r334,r335,r336,r337]),(⟨0,3,3⟩,[r26,r247,r344,r345,r346,r347,r348,r349]),(⟨0,3,4⟩,[0,r295,r350,r351,r352,r353,r354]),(⟨0,4,0⟩,[r0,r246,r247,r248,r249,r250,r251,r252,r253,r254]),(⟨0,4,1⟩,[r59,r303,r304,r305,r306,r307,r308,r309,r310]),(⟨0,4,2⟩,[0,r338,r339,r340,r341,r342,r343,r257]),(⟨0,4,3⟩,[0,r295,r350,r351,r352,r353,r354]),(⟨0,4,4⟩,[r67,r128,r129,r130,r131,-128]),(⟨0,4,5⟩,[r26,r171,r135,r322,64]),(⟨0,5,0⟩,[r255,r256,r257,0,r258,r259,r260,r261,r262]),(⟨0,5,1⟩,[r59,r311,r312,r313,r314,r315,r316,928]),(⟨0,5,4⟩,[r26,r171,r135,r322,64]),(⟨0,6,0⟩,[r26,r263,r264,r265,r266,r267,r268,-1248]),(⟨0,6,1⟩,[r59,r186,r317,r129,r318,r319,-224]),(⟨0,7,0⟩,[r13,r214,r269,r270,r271,r272,r273]),(⟨0,7,1⟩,[r26,r320,r193,r101,r321,-64]),(⟨0,8,1⟩,[r26,r171,r135,r322,64]),(⟨1,0,0⟩,[r213,r214,r117,r215,r216,r217,r218,r219,r220,r221,r222,r223,r224]),(⟨1,0,1⟩,[r13,r274,r275,r157,r276,r277,r278,r279,r280,r281,r282,r283]),(⟨1,0,2⟩,[0,r284,r285,r286,r287,r288,r289,r290,r291,r292,r293]),(⟨1,0,3⟩,[r201,r294,r295,r296,r297,r298,r299,r300,r301,r302]),(⟨1,0,4⟩,[r59,r303,r304,r305,r306,r307,r308,r309,r310]),(⟨1,0,5⟩,[r59,r311,r312,r313,r314,r315,r316,928]),(⟨1,0,6⟩,[r59,r186,r317,r129,r318,r319,-224]),(⟨1,0,7⟩,[r26,r320,r193,r101,r321,-64]),(⟨1,0,8⟩,[r26,r171,r135,r322,64]),(⟨1,1,0⟩,[r13,r274,r275,r157,r276,r277,r278,r279,r280,r281,r282,r283]),(⟨1,1,1⟩,[0,r355,r356,r357,-1536,r358,r359,r360,r361,r362,5760]),(⟨1,1,2⟩,[0,r143,r322,r363,r364,r365,r366,r367,r368,-2688]),(⟨1,1,3⟩,[0,r168,r369,r370,r371,r372,r373,r374,-768]),(⟨1,1,4⟩,[r38,r375,r321,r376,r377,r378,r379,1088]),(⟨1,2,0⟩,[0,r284,r285,r286,r287,r288,r289,r290,r291,r292,r293]),(⟨1,2,1⟩,[0,r143,r322,r363,r364,r365,r366,r367,r368,-2688]),(⟨1,2,4⟩,[r59,r186,r317,r129,r318,r319,-224]),(⟨1,3,0⟩,[r201,r294,r295,r296,r297,r298,r299,r300,r301,r302]),(⟨1,3,1⟩,[0,r168,r369,r370,r371,r372,r373,r374,-768]),(⟨1,3,4⟩,[r26,r320,r193,r101,r321,-64]),(⟨1,4,0⟩,[r59,r303,r304,r305,r306,r307,r308,r309,r310]),(⟨1,4,1⟩,[r38,r375,r321,r376,r377,r378,r379,1088]),(⟨1,4,2⟩,[r59,r186,r317,r129,r318,r319,-224]),(⟨1,4,3⟩,[r26,r320,r193,r101,r321,-64]),(⟨1,4,4⟩,[r67,r132,r133,r134,128]),(⟨1,5,0⟩,[r59,r311,r312,r313,r314,r315,r316,928]),(⟨1,6,0⟩,[r59,r186,r317,r129,r318,r319,-224]),(⟨1,7,0⟩,[r26,r320,r193,r101,r321,-64]),(⟨1,8,0⟩,[r26,r171,r135,r322,64]),(⟨2,0,0⟩,[r13,r225,r226,r227,r228,r229,r230,r231,r232,r233,r234,r235]),(⟨2,0,1⟩,[0,r284,r285,r286,r287,r288,r289,r290,r291,r292,r293]),(⟨2,0,2⟩,[r59,r101,r323,r324,r325,r326,r327,r328,r329,r330]),(⟨2,0,3⟩,[r213,r38,r331,r332,r333,r334,r335,r336,r337]),(⟨2,0,4⟩,[0,r338,r339,r340,r341,r342,r343,r257]),(⟨2,1,0⟩,[0,r284,r285,r286,r287,r288,r289,r290,r291,r292,r293]),(⟨2,1,1⟩,[0,r143,r322,r363,r364,r365,r366,r367,r368,-2688]),(⟨2,1,4⟩,[r59,r186,r317,r129,r318,r319,-224]),(⟨2,2,0⟩,[r59,r101,r323,r324,r325,r326,r327,r328,r329,r330]),(⟨2,3,0⟩,[r213,r38,r331,r332,r333,r334,r335,r336,r337]),(⟨2,4,0⟩,[0,r338,r339,r340,r341,r342,r343,r257]),(⟨2,4,1⟩,[r59,r186,r317,r129,r318,r319,-224]),(⟨3,0,0⟩,[r59,r236,r237,r238,r239,r240,r241,r242,r243,r244,r245]),(⟨3,0,1⟩,[r201,r294,r295,r296,r297,r298,r299,r300,r301,r302]),(⟨3,0,2⟩,[r213,r38,r331,r332,r333,r334,r335,r336,r337]),(⟨3,0,3⟩,[r26,r247,r344,r345,r346,r347,r348,r349]),(⟨3,0,4⟩,[0,r295,r350,r351,r352,r353,r354]),(⟨3,1,0⟩,[r201,r294,r295,r296,r297,r298,r299,r300,r301,r302]),(⟨3,1,1⟩,[0,r168,r369,r370,r371,r372,r373,r374,-768]),(⟨3,1,4⟩,[r26,r320,r193,r101,r321,-64]),(⟨3,2,0⟩,[r213,r38,r331,r332,r333,r334,r335,r336,r337]),(⟨3,3,0⟩,[r26,r247,r344,r345,r346,r347,r348,r349]),(⟨3,4,0⟩,[0,r295,r350,r351,r352,r353,r354]),(⟨3,4,1⟩,[r26,r320,r193,r101,r321,-64]),(⟨4,0,0⟩,[r0,r246,r247,r248,r249,r250,r251,r252,r253,r254]),(⟨4,0,1⟩,[r59,r303,r304,r305,r306,r307,r308,r309,r310]),(⟨4,0,2⟩,[0,r338,r339,r340,r341,r342,r343,r257]),(⟨4,0,3⟩,[0,r295,r350,r351,r352,r353,r354]),(⟨4,0,4⟩,[r67,r128,r129,r130,r131,-128]),(⟨4,0,5⟩,[r26,r171,r135,r322,64]),(⟨4,1,0⟩,[r59,r303,r304,r305,r306,r307,r308,r309,r310]),(⟨4,1,1⟩,[r38,r375,r321,r376,r377,r378,r379,1088]),(⟨4,1,2⟩,[r59,r186,r317,r129,r318,r319,-224]),(⟨4,1,3⟩,[r26,r320,r193,r101,r321,-64]),(⟨4,1,4⟩,[r67,r132,r133,r134,128]),(⟨4,2,0⟩,[0,r338,r339,r340,r341,r342,r343,r257]),(⟨4,2,1⟩,[r59,r186,r317,r129,r318,r319,-224]),(⟨4,3,0⟩,[0,r295,r350,r351,r352,r353,r354]),(⟨4,3,1⟩,[r26,r320,r193,r101,r321,-64]),(⟨4,4,0⟩,[r67,r128,r129,r130,r131,-128]),(⟨4,4,1⟩,[r67,r132,r133,r134,128]),(⟨4,5,0⟩,[r26,r171,r135,r322,64]),(⟨5,0,0⟩,[r255,r256,r257,0,r258,r259,r260,r261,r262]),(⟨5,0,1⟩,[r59,r311,r312,r313,r314,r315,r316,928]),(⟨5,0,4⟩,[r26,r171,r135,r322,64]),(⟨5,1,0⟩,[r59,r311,r312,r313,r314,r315,r316,928]),(⟨5,4,0⟩,[r26,r171,r135,r322,64]),(⟨6,0,0⟩,[r26,r263,r264,r265,r266,r267,r268,-1248]),(⟨6,0,1⟩,[r59,r186,r317,r129,r318,r319,-224]),(⟨6,1,0⟩,[r59,r186,r317,r129,r318,r319,-224]),(⟨7,0,0⟩,[r13,r214,r269,r270,r271,r272,r273]),(⟨7,0,1⟩,[r26,r320,r193,r101,r321,-64]),(⟨7,1,0⟩,[r26,r320,r193,r101,r321,-64]),(⟨8,0,1⟩,[r26,r171,r135,r322,64]),(⟨8,1,0⟩,[r26,r171,r135,r322,64])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,3,-12,9,6]),(⟨0,0,1⟩,[-1,5,-9,5]),(⟨0,0,2⟩,[-1,4,-7]),(⟨0,0,3⟩,[2,-2]),(⟨0,0,4⟩,[2]),(⟨0,1,0⟩,[-1,5,-9,5]),(⟨0,2,0⟩,[-1,4,-7]),(⟨0,3,0⟩,[2,-2]),(⟨0,4,0⟩,[2]),(⟨1,0,0⟩,[-1,5,-9,5]),(⟨2,0,0⟩,[-1,4,-7]),(⟨3,0,0⟩,[2,-2]),(⟨4,0,0⟩,[2])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[64,-768,-1856,71168,-470336,1581440,-3104960,3581696,-2132736,328832]),(⟨0,0,1⟩,[64,-1024,3136,27008,-255680,943360,-1884224,2076032,-1072512]),(⟨0,0,2⟩,[-64,512,4416,-54912,194112,-323840,260288,-31360]),(⟨0,0,3⟩,[-64,640,3648,-54528,197696,-331136,265664]),(⟨0,1,0⟩,[64,-1024,3136,27008,-255680,943360,-1884224,2076032,-1072512]),(⟨0,1,1⟩,[0,-512,7168,-29184,30720,51712,-177152,182784]),(⟨0,1,4⟩,[-128,1536,-3840,-4608,15232]),(⟨0,2,0⟩,[-64,512,4416,-54912,194112,-323840,260288,-31360]),(⟨0,3,0⟩,[-64,640,3648,-54528,197696,-331136,265664]),(⟨0,4,1⟩,[-128,1536,-3840,-4608,15232]),(⟨1,0,0⟩,[64,-1024,3136,27008,-255680,943360,-1884224,2076032,-1072512]),(⟨1,0,1⟩,[0,-512,7168,-29184,30720,51712,-177152,182784]),(⟨1,0,4⟩,[-128,1536,-3840,-4608,15232]),(⟨1,1,0⟩,[0,-512,7168,-29184,30720,51712,-177152,182784]),(⟨1,4,0⟩,[-128,1536,-3840,-4608,15232]),(⟨2,0,0⟩,[-64,512,4416,-54912,194112,-323840,260288,-31360]),(⟨3,0,0⟩,[-64,640,3648,-54528,197696,-331136,265664]),(⟨4,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨4,1,0⟩,[-128,1536,-3840,-4608,15232])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 0 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r380) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 5 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r381) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨4,0,0⟩,[2])]

noncomputable def partial12 : Poly := [(⟨4,0,0⟩,[128,-1536,-3712,142336,-940672,3162880,-6209920,7163392,-4265472,657664]),(⟨4,0,1⟩,[128,-2048,6272,54016,-511360,1886720,-3768448,4152064,-2145024]),(⟨4,0,2⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨4,0,3⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨4,1,0⟩,[128,-2048,6272,54016,-511360,1886720,-3768448,4152064,-2145024]),(⟨4,1,1⟩,[0,-1024,14336,-58368,61440,103424,-354304,365568]),(⟨4,1,4⟩,[-256,3072,-7680,-9216,30464]),(⟨4,2,0⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨4,3,0⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨4,4,1⟩,[-256,3072,-7680,-9216,30464]),(⟨5,0,0⟩,[128,-2048,6272,54016,-511360,1886720,-3768448,4152064,-2145024]),(⟨5,0,1⟩,[0,-1024,14336,-58368,61440,103424,-354304,365568]),(⟨5,0,4⟩,[-256,3072,-7680,-9216,30464]),(⟨5,1,0⟩,[0,-1024,14336,-58368,61440,103424,-354304,365568]),(⟨5,4,0⟩,[-256,3072,-7680,-9216,30464]),(⟨6,0,0⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨7,0,0⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨8,0,1⟩,[-256,3072,-7680,-9216,30464]),(⟨8,1,0⟩,[-256,3072,-7680,-9216,30464])]


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

noncomputable def partial8 : Poly := [(⟨0,4,0⟩,[128,-1536,-3712,142336,-940672,3162880,-6209920,7163392,-4265472,657664]),(⟨0,4,1⟩,[128,-2048,6272,54016,-511360,1886720,-3768448,4152064,-2145024]),(⟨0,4,2⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨0,4,3⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨0,5,0⟩,[128,-2048,6272,54016,-511360,1886720,-3768448,4152064,-2145024]),(⟨0,5,1⟩,[0,-1024,14336,-58368,61440,103424,-354304,365568]),(⟨0,5,4⟩,[-256,3072,-7680,-9216,30464]),(⟨0,6,0⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨0,7,0⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨0,8,1⟩,[-256,3072,-7680,-9216,30464]),(⟨1,0,0⟩,[-64,1088,-2560,-73216,839040,-4582912,15601024,-35691136,55893056,-58752576,38747264,-13623168,1644160]),(⟨1,0,1⟩,[-64,1344,-8832,-1792,357376,-2449152,9037184,-21265792,33127488,-33467968,20032768,-5362560]),(⟨1,0,2⟩,[64,-832,-1280,72064,-505856,1810688,-3901056,5217920,-4118592,1583680,-156800]),(⟨1,0,3⟩,[64,-960,128,66688,-499968,1828608,-3973248,5297024,-4046656,1328320]),(⟨1,1,0⟩,[-64,1344,-8832,-1792,357376,-2449152,9037184,-21265792,33127488,-33467968,20032768,-5362560]),(⟨1,1,1⟩,[0,512,-9728,69632,-243712,400384,13312,-1380352,2766848,-2530816,913920]),(⟨1,1,4⟩,[128,-2176,12672,-29056,3968,98432,-160128,76160]),(⟨1,2,0⟩,[64,-832,-1280,72064,-505856,1810688,-3901056,5217920,-4118592,1583680,-156800]),(⟨1,3,0⟩,[64,-960,128,66688,-499968,1828608,-3973248,5297024,-4046656,1328320]),(⟨1,4,0⟩,[128,-2048,6272,54016,-511360,1886720,-3768448,4152064,-2145024]),(⟨1,4,1⟩,[128,-3200,27008,-87424,65408,201856,-514432,441728]),(⟨1,4,4⟩,[-256,3072,-7680,-9216,30464]),(⟨1,5,0⟩,[0,-1024,14336,-58368,61440,103424,-354304,365568]),(⟨1,8,0⟩,[-256,3072,-7680,-9216,30464]),(⟨2,0,0⟩,[-128,2368,-10496,-75008,1125376,-6410112,21760256,-48337408,71321728,-67399616,36277248,-7664384]),(⟨2,0,1⟩,[-64,1792,-17408,62336,98048,-1754752,7460736,-17596800,25333056,-21353088,8421504]),(⟨2,0,2⟩,[64,-768,-1920,68992,-444672,1484672,-2914432,3339392,-1947456,219520]),(⟨2,0,3⟩,[64,-896,-640,64640,-441344,1503616,-2974080,3380608,-1859648]),(⟨2,0,4⟩,[128,-2176,12672,-29056,3968,98432,-160128,76160]),(⟨2,1,0⟩,[-64,1792,-17408,62336,98048,-1754752,7460736,-17596800,25333056,-21353088,8421504]),(⟨2,1,1⟩,[0,512,-9216,61440,-197632,275456,168960,-1253376,1971200,-1279488]),(⟨2,1,4⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨2,2,0⟩,[64,-768,-1920,68992,-444672,1484672,-2914432,3339392,-1947456,219520]),(⟨2,3,0⟩,[64,-896,-640,64640,-441344,1503616,-2974080,3380608,-1859648]),(⟨2,4,0⟩,[0,-1152,21504,-138880,392192,-549248,360448,13440]),(⟨2,4,1⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨3,0,0⟩,[128,-1216,-11136,210816,-1247104,3759104,-5826432,2374784,7018752,-12315456,6693120]),(⟨3,0,1⟩,[128,-1664,-896,109184,-763008,2673536,-5486208,6667136,-4325888,865536]),(⟨3,0,2⟩,[-128,1152,7808,-118656,498048,-1035904,1168256,-583296,62720]),(⟨3,0,3⟩,[-128,1408,6016,-116352,504448,-1057664,1193600,-531328]),(⟨3,0,4⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨3,1,0⟩,[128,-1664,-896,109184,-763008,2673536,-5486208,6667136,-4325888,865536]),(⟨3,1,1⟩,[0,-1024,15360,-72704,119808,41984,-457728,719872,-365568]),(⟨3,1,4⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨3,2,0⟩,[-128,1152,7808,-118656,498048,-1035904,1168256,-583296,62720]),(⟨3,3,0⟩,[-128,1408,6016,-116352,504448,-1057664,1193600,-531328]),(⟨3,4,0⟩,[0,-768,18176,-130560,388608,-569088,424704]),(⟨3,4,1⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨4,0,0⟩,[384,-5440,2816,325760,-2450688,8874240,-18752768,23720320,-16556672,4350528]),(⟨4,0,1⟩,[128,-3072,21632,-18688,-391552,1928704,-4226176,4871936,-2510592]),(⟨4,0,2⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨4,0,3⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨4,0,4⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨4,1,0⟩,[128,-3072,21632,-18688,-391552,1928704,-4226176,4871936,-2510592]),(⟨4,1,1⟩,[0,-1024,14336,-58368,61440,103424,-354304,365568]),(⟨4,1,4⟩,[-256,3072,-7680,-9216,30464]),(⟨4,2,0⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨4,3,0⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨4,4,0⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨4,4,1⟩,[-512,6144,-15360,-18432,60928]),(⟨4,5,0⟩,[-256,3072,-7680,-9216,30464]),(⟨5,0,0⟩,[64,-1792,13440,0,-454656,2354432,-5574272,6949376,-3941952]),(⟨5,0,1⟩,[128,-3200,27008,-87424,65408,201856,-514432,441728]),(⟨5,0,4⟩,[-256,3072,-7680,-9216,30464]),(⟨5,1,0⟩,[128,-3200,27008,-87424,65408,201856,-514432,441728]),(⟨5,4,0⟩,[-256,3072,-7680,-9216,30464]),(⟨6,0,0⟩,[-256,2432,14848,-226176,892672,-1705344,1714176,-594048]),(⟨6,0,1⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨6,1,0⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨7,0,0⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨7,0,1⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨7,1,0⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨8,0,1⟩,[-256,3072,-7680,-9216,30464]),(⟨8,1,0⟩,[-256,3072,-7680,-9216,30464])]


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

noncomputable def partial4 : Poly := [(⟨0,0,4⟩,[128,-1536,-3712,142336,-940672,3162880,-6209920,7163392,-4265472,657664]),(⟨0,0,5⟩,[128,-2048,6272,54016,-511360,1886720,-3768448,4152064,-2145024]),(⟨0,0,6⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨0,0,7⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨0,1,0⟩,[-64,1088,-2560,-73216,839040,-4582912,15601024,-35691136,55893056,-58752576,38747264,-13623168,1644160]),(⟨0,1,1⟩,[-64,1344,-8832,-1792,357376,-2449152,9037184,-21265792,33127488,-33467968,20032768,-5362560]),(⟨0,1,2⟩,[64,-832,-1280,72064,-505856,1810688,-3901056,5217920,-4118592,1583680,-156800]),(⟨0,1,3⟩,[64,-960,128,66688,-499968,1828608,-3973248,5297024,-4046656,1328320]),(⟨0,1,4⟩,[128,-2048,6272,54016,-511360,1886720,-3768448,4152064,-2145024]),(⟨0,1,5⟩,[0,-1024,14336,-58368,61440,103424,-354304,365568]),(⟨0,1,8⟩,[-256,3072,-7680,-9216,30464]),(⟨0,2,0⟩,[-128,2368,-10496,-75008,1125376,-6410112,21760256,-48337408,71321728,-67399616,36277248,-7664384]),(⟨0,2,1⟩,[-64,1792,-17408,62336,98048,-1754752,7460736,-17596800,25333056,-21353088,8421504]),(⟨0,2,2⟩,[64,-768,-1920,68992,-444672,1484672,-2914432,3339392,-1947456,219520]),(⟨0,2,3⟩,[64,-896,-640,64640,-441344,1503616,-2974080,3380608,-1859648]),(⟨0,2,4⟩,[0,-1152,21504,-138880,392192,-549248,360448,13440]),(⟨0,3,0⟩,[128,-1216,-11136,210816,-1247104,3759104,-5826432,2374784,7018752,-12315456,6693120]),(⟨0,3,1⟩,[128,-1664,-896,109184,-763008,2673536,-5486208,6667136,-4325888,865536]),(⟨0,3,2⟩,[-128,1152,7808,-118656,498048,-1035904,1168256,-583296,62720]),(⟨0,3,3⟩,[-128,1408,6016,-116352,504448,-1057664,1193600,-531328]),(⟨0,3,4⟩,[0,-768,18176,-130560,388608,-569088,424704]),(⟨0,4,0⟩,[384,-5440,2816,325760,-2450688,8874240,-18752768,23720320,-16556672,4350528]),(⟨0,4,1⟩,[128,-3072,21632,-18688,-391552,1928704,-4226176,4871936,-2510592]),(⟨0,4,2⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨0,4,3⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨0,4,4⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨0,4,5⟩,[-256,3072,-7680,-9216,30464]),(⟨0,5,0⟩,[64,-1792,13440,0,-454656,2354432,-5574272,6949376,-3941952]),(⟨0,5,1⟩,[128,-3200,27008,-87424,65408,201856,-514432,441728]),(⟨0,5,4⟩,[-256,3072,-7680,-9216,30464]),(⟨0,6,0⟩,[-256,2432,14848,-226176,892672,-1705344,1714176,-594048]),(⟨0,6,1⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨0,7,0⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨0,7,1⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨0,8,1⟩,[-256,3072,-7680,-9216,30464]),(⟨1,0,0⟩,[-64,1088,-2560,-73216,839040,-4582912,15601024,-35691136,55893056,-58752576,38747264,-13623168,1644160]),(⟨1,0,1⟩,[-64,1344,-8832,-1792,357376,-2449152,9037184,-21265792,33127488,-33467968,20032768,-5362560]),(⟨1,0,2⟩,[64,-832,-1280,72064,-505856,1810688,-3901056,5217920,-4118592,1583680,-156800]),(⟨1,0,3⟩,[64,-960,128,66688,-499968,1828608,-3973248,5297024,-4046656,1328320]),(⟨1,0,4⟩,[128,-2048,6272,54016,-511360,1886720,-3768448,4152064,-2145024]),(⟨1,0,5⟩,[0,-1024,14336,-58368,61440,103424,-354304,365568]),(⟨1,0,8⟩,[-256,3072,-7680,-9216,30464]),(⟨1,1,0⟩,[-128,2688,-17664,-3584,714752,-4898304,18074368,-42531584,66254976,-66935936,40065536,-10725120]),(⟨1,1,1⟩,[0,1024,-19456,139264,-487424,800768,26624,-2760704,5533696,-5061632,1827840]),(⟨1,1,4⟩,[256,-5376,39680,-116480,69376,300288,-674560,517888]),(⟨1,2,0⟩,[0,960,-18688,134400,-407808,55936,3559680,-12378880,21214464,-19769408,8264704]),(⟨1,2,1⟩,[0,512,-9216,61440,-197632,275456,168960,-1253376,1971200,-1279488]),(⟨1,2,4⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨1,3,0⟩,[192,-2624,-768,175872,-1262976,4502144,-9459456,11964160,-8372544,2193856]),(⟨1,3,1⟩,[0,-1024,15360,-72704,119808,41984,-457728,719872,-365568]),(⟨1,3,4⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨1,4,0⟩,[128,-3072,21632,-18688,-391552,1928704,-4226176,4871936,-2510592]),(⟨1,4,1⟩,[128,-3200,27008,-87424,65408,201856,-514432,441728]),(⟨1,4,4⟩,[-512,6144,-15360,-18432,60928]),(⟨1,5,0⟩,[128,-3200,27008,-87424,65408,201856,-514432,441728]),(⟨1,6,0⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨1,7,0⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨1,8,0⟩,[-256,3072,-7680,-9216,30464]),(⟨2,0,0⟩,[-128,2368,-10496,-75008,1125376,-6410112,21760256,-48337408,71321728,-67399616,36277248,-7664384]),(⟨2,0,1⟩,[-64,1792,-17408,62336,98048,-1754752,7460736,-17596800,25333056,-21353088,8421504]),(⟨2,0,2⟩,[64,-768,-1920,68992,-444672,1484672,-2914432,3339392,-1947456,219520]),(⟨2,0,3⟩,[64,-896,-640,64640,-441344,1503616,-2974080,3380608,-1859648]),(⟨2,0,4⟩,[0,-1152,21504,-138880,392192,-549248,360448,13440]),(⟨2,1,0⟩,[0,960,-18688,134400,-407808,55936,3559680,-12378880,21214464,-19769408,8264704]),(⟨2,1,1⟩,[0,512,-9216,61440,-197632,275456,168960,-1253376,1971200,-1279488]),(⟨2,1,4⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨2,2,0⟩,[128,-1536,-3840,137984,-889344,2969344,-5828864,6678784,-3894912,439040]),(⟨2,3,0⟩,[-64,256,7168,-54016,56704,467712,-1805824,2797312,-1796928]),(⟨2,4,0⟩,[0,-1152,21504,-138880,392192,-549248,360448,13440]),(⟨2,4,1⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨3,0,0⟩,[128,-1216,-11136,210816,-1247104,3759104,-5826432,2374784,7018752,-12315456,6693120]),(⟨3,0,1⟩,[128,-1664,-896,109184,-763008,2673536,-5486208,6667136,-4325888,865536]),(⟨3,0,2⟩,[-128,1152,7808,-118656,498048,-1035904,1168256,-583296,62720]),(⟨3,0,3⟩,[-128,1408,6016,-116352,504448,-1057664,1193600,-531328]),(⟨3,0,4⟩,[0,-768,18176,-130560,388608,-569088,424704]),(⟨3,1,0⟩,[192,-2624,-768,175872,-1262976,4502144,-9459456,11964160,-8372544,2193856]),(⟨3,1,1⟩,[0,-1024,15360,-72704,119808,41984,-457728,719872,-365568]),(⟨3,1,4⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨3,2,0⟩,[-64,256,7168,-54016,56704,467712,-1805824,2797312,-1796928]),(⟨3,3,0⟩,[-256,2816,12032,-232704,1008896,-2115328,2387200,-1062656]),(⟨3,4,0⟩,[0,-768,18176,-130560,388608,-569088,424704]),(⟨3,4,1⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨4,0,0⟩,[384,-5440,2816,325760,-2450688,8874240,-18752768,23720320,-16556672,4350528]),(⟨4,0,1⟩,[128,-3072,21632,-18688,-391552,1928704,-4226176,4871936,-2510592]),(⟨4,0,2⟩,[-128,1024,8832,-109824,388224,-647680,520576,-62720]),(⟨4,0,3⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨4,0,4⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨4,0,5⟩,[-256,3072,-7680,-9216,30464]),(⟨4,1,0⟩,[128,-3072,21632,-18688,-391552,1928704,-4226176,4871936,-2510592]),(⟨4,1,1⟩,[128,-3200,27008,-87424,65408,201856,-514432,441728]),(⟨4,1,4⟩,[-512,6144,-15360,-18432,60928]),(⟨4,2,0⟩,[0,-1152,21504,-138880,392192,-549248,360448,13440]),(⟨4,2,1⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨4,3,0⟩,[0,-768,18176,-130560,388608,-569088,424704]),(⟨4,3,1⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨4,4,0⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨4,4,1⟩,[-512,6144,-15360,-18432,60928]),(⟨4,5,0⟩,[-256,3072,-7680,-9216,30464]),(⟨5,0,0⟩,[64,-1792,13440,0,-454656,2354432,-5574272,6949376,-3941952]),(⟨5,0,1⟩,[128,-3200,27008,-87424,65408,201856,-514432,441728]),(⟨5,0,4⟩,[-256,3072,-7680,-9216,30464]),(⟨5,1,0⟩,[128,-3200,27008,-87424,65408,201856,-514432,441728]),(⟨5,4,0⟩,[-256,3072,-7680,-9216,30464]),(⟨6,0,0⟩,[-256,2432,14848,-226176,892672,-1705344,1714176,-594048]),(⟨6,0,1⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨6,1,0⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨7,0,0⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨7,0,1⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨7,1,0⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨8,0,1⟩,[-256,3072,-7680,-9216,30464]),(⟨8,1,0⟩,[-256,3072,-7680,-9216,30464])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,192,-3072,4224,229248,-2286336,11017728,-32098176,59415552,-67834560,40184832,-1650432,-9836928,1972992]),(⟨0,0,1⟩,[-64,1280,-6400,-50944,873600,-5651968,21761152,-54803200,91688000,-98180352,58996352,-10819584,-4790912]),(⟨0,0,2⟩,[-128,2176,-8192,-68480,911872,-5126016,17991680,-42252928,66354304,-66623744,37556736,-7852544]),(⟨0,0,3⟩,[128,-1408,-8448,213504,-1449088,5043200,-9661056,8597504,2036736,-11911296,8287104]),(⟨0,0,4⟩,[384,-5440,2816,325760,-2450688,8874240,-18752768,23720320,-16556672,4350528]),(⟨0,0,5⟩,[64,-1792,13440,0,-454656,2354432,-5574272,6949376,-3941952]),(⟨0,0,6⟩,[-256,2432,14848,-226176,892672,-1705344,1714176,-594048]),(⟨0,0,7⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨0,1,0⟩,[-64,1280,-6400,-50944,873600,-5651968,21761152,-54803200,91688000,-98180352,58996352,-10819584,-4790912]),(⟨0,1,1⟩,[-128,2688,-19200,24064,536576,-4394496,17641216,-43582208,69578880,-70413440,40647680,-9628416]),(⟨0,1,2⟩,[0,960,-18688,134400,-407808,55936,3559680,-12378880,21214464,-19769408,8264704]),(⟨0,1,3⟩,[192,-2624,-768,175872,-1262976,4502144,-9459456,11964160,-8372544,2193856]),(⟨0,1,4⟩,[128,-3456,27776,-49792,-346240,2004352,-4473472,4981376,-2419200]),(⟨0,1,5⟩,[128,-3200,27008,-87424,65408,201856,-514432,441728]),(⟨0,1,6⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨0,1,7⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨0,1,8⟩,[-256,3072,-7680,-9216,30464]),(⟨0,2,0⟩,[-128,2176,-8192,-68480,911872,-5126016,17991680,-42252928,66354304,-66623744,37556736,-7852544]),(⟨0,2,1⟩,[0,960,-18688,134400,-407808,55936,3559680,-12378880,21214464,-19769408,8264704]),(⟨0,2,2⟩,[128,-1536,-3840,137984,-889344,2969344,-5828864,6678784,-3894912,439040]),(⟨0,2,3⟩,[-64,256,7168,-54016,56704,467712,-1805824,2797312,-1796928]),(⟨0,2,4⟩,[0,-1152,21504,-138880,392192,-549248,360448,13440]),(⟨0,3,0⟩,[128,-1408,-8448,213504,-1449088,5043200,-9661056,8597504,2036736,-11911296,8287104]),(⟨0,3,1⟩,[192,-2624,-768,175872,-1262976,4502144,-9459456,11964160,-8372544,2193856]),(⟨0,3,2⟩,[-64,256,7168,-54016,56704,467712,-1805824,2797312,-1796928]),(⟨0,3,3⟩,[-256,2816,12032,-232704,1008896,-2115328,2387200,-1062656]),(⟨0,3,4⟩,[0,-768,18176,-130560,388608,-569088,424704]),(⟨0,4,0⟩,[384,-5440,2816,325760,-2450688,8874240,-18752768,23720320,-16556672,4350528]),(⟨0,4,1⟩,[128,-3456,27776,-49792,-346240,2004352,-4473472,4981376,-2419200]),(⟨0,4,2⟩,[0,-1152,21504,-138880,392192,-549248,360448,13440]),(⟨0,4,3⟩,[0,-768,18176,-130560,388608,-569088,424704]),(⟨0,4,4⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨0,4,5⟩,[-256,3072,-7680,-9216,30464]),(⟨0,5,0⟩,[64,-1792,13440,0,-454656,2354432,-5574272,6949376,-3941952]),(⟨0,5,1⟩,[128,-3200,27008,-87424,65408,201856,-514432,441728]),(⟨0,5,4⟩,[-256,3072,-7680,-9216,30464]),(⟨0,6,0⟩,[-256,2432,14848,-226176,892672,-1705344,1714176,-594048]),(⟨0,6,1⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨0,7,0⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨0,7,1⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨0,8,1⟩,[-256,3072,-7680,-9216,30464]),(⟨1,0,0⟩,[-64,1280,-6400,-50944,873600,-5651968,21761152,-54803200,91688000,-98180352,58996352,-10819584,-4790912]),(⟨1,0,1⟩,[-128,2688,-19200,24064,536576,-4394496,17641216,-43582208,69578880,-70413440,40647680,-9628416]),(⟨1,0,2⟩,[0,960,-18688,134400,-407808,55936,3559680,-12378880,21214464,-19769408,8264704]),(⟨1,0,3⟩,[192,-2624,-768,175872,-1262976,4502144,-9459456,11964160,-8372544,2193856]),(⟨1,0,4⟩,[128,-3456,27776,-49792,-346240,2004352,-4473472,4981376,-2419200]),(⟨1,0,5⟩,[128,-3200,27008,-87424,65408,201856,-514432,441728]),(⟨1,0,6⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨1,0,7⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨1,0,8⟩,[-256,3072,-7680,-9216,30464]),(⟨1,1,0⟩,[-128,2688,-19200,24064,536576,-4394496,17641216,-43582208,69578880,-70413440,40647680,-9628416]),(⟨1,1,1⟩,[0,1536,-29184,208896,-731136,1201152,39936,-4141056,8300544,-7592448,2741760]),(⟨1,1,2⟩,[0,512,-9216,61440,-197632,275456,168960,-1253376,1971200,-1279488]),(⟨1,1,3⟩,[0,-1024,15360,-72704,119808,41984,-457728,719872,-365568]),(⟨1,1,4⟩,[256,-5376,39680,-116480,69376,300288,-674560,517888]),(⟨1,2,0⟩,[0,960,-18688,134400,-407808,55936,3559680,-12378880,21214464,-19769408,8264704]),(⟨1,2,1⟩,[0,512,-9216,61440,-197632,275456,168960,-1253376,1971200,-1279488]),(⟨1,2,4⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨1,3,0⟩,[192,-2624,-768,175872,-1262976,4502144,-9459456,11964160,-8372544,2193856]),(⟨1,3,1⟩,[0,-1024,15360,-72704,119808,41984,-457728,719872,-365568]),(⟨1,3,4⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨1,4,0⟩,[128,-3456,27776,-49792,-346240,2004352,-4473472,4981376,-2419200]),(⟨1,4,1⟩,[256,-5376,39680,-116480,69376,300288,-674560,517888]),(⟨1,4,2⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨1,4,3⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨1,4,4⟩,[-512,6144,-15360,-18432,60928]),(⟨1,5,0⟩,[128,-3200,27008,-87424,65408,201856,-514432,441728]),(⟨1,6,0⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨1,7,0⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨1,8,0⟩,[-256,3072,-7680,-9216,30464]),(⟨2,0,0⟩,[-128,2176,-8192,-68480,911872,-5126016,17991680,-42252928,66354304,-66623744,37556736,-7852544]),(⟨2,0,1⟩,[0,960,-18688,134400,-407808,55936,3559680,-12378880,21214464,-19769408,8264704]),(⟨2,0,2⟩,[128,-1536,-3840,137984,-889344,2969344,-5828864,6678784,-3894912,439040]),(⟨2,0,3⟩,[-64,256,7168,-54016,56704,467712,-1805824,2797312,-1796928]),(⟨2,0,4⟩,[0,-1152,21504,-138880,392192,-549248,360448,13440]),(⟨2,1,0⟩,[0,960,-18688,134400,-407808,55936,3559680,-12378880,21214464,-19769408,8264704]),(⟨2,1,1⟩,[0,512,-9216,61440,-197632,275456,168960,-1253376,1971200,-1279488]),(⟨2,1,4⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨2,2,0⟩,[128,-1536,-3840,137984,-889344,2969344,-5828864,6678784,-3894912,439040]),(⟨2,3,0⟩,[-64,256,7168,-54016,56704,467712,-1805824,2797312,-1796928]),(⟨2,4,0⟩,[0,-1152,21504,-138880,392192,-549248,360448,13440]),(⟨2,4,1⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨3,0,0⟩,[128,-1408,-8448,213504,-1449088,5043200,-9661056,8597504,2036736,-11911296,8287104]),(⟨3,0,1⟩,[192,-2624,-768,175872,-1262976,4502144,-9459456,11964160,-8372544,2193856]),(⟨3,0,2⟩,[-64,256,7168,-54016,56704,467712,-1805824,2797312,-1796928]),(⟨3,0,3⟩,[-256,2816,12032,-232704,1008896,-2115328,2387200,-1062656]),(⟨3,0,4⟩,[0,-768,18176,-130560,388608,-569088,424704]),(⟨3,1,0⟩,[192,-2624,-768,175872,-1262976,4502144,-9459456,11964160,-8372544,2193856]),(⟨3,1,1⟩,[0,-1024,15360,-72704,119808,41984,-457728,719872,-365568]),(⟨3,1,4⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨3,2,0⟩,[-64,256,7168,-54016,56704,467712,-1805824,2797312,-1796928]),(⟨3,3,0⟩,[-256,2816,12032,-232704,1008896,-2115328,2387200,-1062656]),(⟨3,4,0⟩,[0,-768,18176,-130560,388608,-569088,424704]),(⟨3,4,1⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨4,0,0⟩,[384,-5440,2816,325760,-2450688,8874240,-18752768,23720320,-16556672,4350528]),(⟨4,0,1⟩,[128,-3456,27776,-49792,-346240,2004352,-4473472,4981376,-2419200]),(⟨4,0,2⟩,[0,-1152,21504,-138880,392192,-549248,360448,13440]),(⟨4,0,3⟩,[0,-768,18176,-130560,388608,-569088,424704]),(⟨4,0,4⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨4,0,5⟩,[-256,3072,-7680,-9216,30464]),(⟨4,1,0⟩,[128,-3456,27776,-49792,-346240,2004352,-4473472,4981376,-2419200]),(⟨4,1,1⟩,[256,-5376,39680,-116480,69376,300288,-674560,517888]),(⟨4,1,2⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨4,1,3⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨4,1,4⟩,[-512,6144,-15360,-18432,60928]),(⟨4,2,0⟩,[0,-1152,21504,-138880,392192,-549248,360448,13440]),(⟨4,2,1⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨4,3,0⟩,[0,-768,18176,-130560,388608,-569088,424704]),(⟨4,3,1⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨4,4,0⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨4,4,1⟩,[-512,6144,-15360,-18432,60928]),(⟨4,5,0⟩,[-256,3072,-7680,-9216,30464]),(⟨5,0,0⟩,[64,-1792,13440,0,-454656,2354432,-5574272,6949376,-3941952]),(⟨5,0,1⟩,[128,-3200,27008,-87424,65408,201856,-514432,441728]),(⟨5,0,4⟩,[-256,3072,-7680,-9216,30464]),(⟨5,1,0⟩,[128,-3200,27008,-87424,65408,201856,-514432,441728]),(⟨5,4,0⟩,[-256,3072,-7680,-9216,30464]),(⟨6,0,0⟩,[-256,2432,14848,-226176,892672,-1705344,1714176,-594048]),(⟨6,0,1⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨6,1,0⟩,[128,-2048,10880,-21504,-6784,93184,-106624]),(⟨7,0,0⟩,[-128,1280,7296,-109056,395392,-662272,531328]),(⟨7,0,1⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨7,1,0⟩,[-256,3328,-10752,-1536,39680,-30464]),(⟨8,0,1⟩,[-256,3072,-7680,-9216,30464]),(⟨8,1,0⟩,[-256,3072,-7680,-9216,30464])]


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
    (Poly.add (Poly.scale (K.ofRat r382) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 0 5).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r380*r381 : ℚ)=r382 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 0 5 r380 r381 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 0=5 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 0 5).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C050

#print axioms Coulomb8.Columns.C050.sound
