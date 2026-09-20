import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C073

def r0 : ℚ := { num := 288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -5952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 43200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -80064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -716736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 5700672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -2829696, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 40011840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -47768160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 28950528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -1654080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -6691968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 1575936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 2304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -21888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 91136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 13312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -293376, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 11125696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -32551040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 59378656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -67207680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 2461376, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -8115328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := -435072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -21312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 77568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -27584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -1195072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 968512, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -20186560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 36620096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -40279104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 24258944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -808640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 23488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 3200, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -108160, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 3616384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -8526208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 10259584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -3625088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -684800, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 4300480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -6240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 5568, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -52608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -496064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 423488, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -1109440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := 11339392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -9012096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 416608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 1920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := -1216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -54784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 214016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -169088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := -541504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := 1298176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := -124320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 1216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -4160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -11456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := 82752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := -203968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := 52416, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := -304960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := 128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := -2048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := 8192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 1536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -148864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 373248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -47360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 1280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -2048, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 69504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -1792, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -37376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 76672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := -192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 4416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -2304, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 166528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -208512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -1429376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 1287168, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -25959424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 6438592, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := -48242112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := 29123840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -1042816, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := -2560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := 65216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := -20416, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 105792, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := 151744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -4445888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 10422912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -11124224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 694208, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -7296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 44992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -70080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := -432576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := 2624448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := -6632384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := 9330112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := -7158720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := 314688, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := 32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -1472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 18176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -88512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 171456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 13504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := -619264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := 1003200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 3008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := -15424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := 29504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := 192, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := -106432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := 170048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := -512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 6144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -15360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := -18432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -3840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := -4608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -704, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 34560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -99200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := -4864, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 1089280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -3280640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 661120, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -451584, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 97216, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := 704, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := -4800, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 38208, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := -9920, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -735040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := 1621184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := -150976, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 6016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := -18560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -84352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 629120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -222336, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 1867904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -843392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := 1152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 9216, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := -549888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 922368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -54528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -3050496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 924672, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -873600, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := 192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := -3520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 3328, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -67072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := 46464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := 204672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -506624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 38976, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 12032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := -61696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := 118016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := 768, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := -425728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := 680192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := -1408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := 12288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := -53632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := 106880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := 128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := -55296, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := 92288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -2976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := 21600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := -40032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -358368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 2850336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := -1414848, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 20005920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -23884080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := 14475264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := -827040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := -3345984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := 787968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := -48, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := -10944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := 45568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 6656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -146688, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := 5562848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := -16275520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := 29689328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := -33603840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := 1230688, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := -4057664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := -217536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := 192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -10656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 38784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -13792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := -597536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := 484256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := -10093280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := 18310048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := -20139552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := 12129472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := -404320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := -320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := 11744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := 1600, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := -54080, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := 1808192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -4263104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 5129792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := -1812544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -342400, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := 2150240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := 160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := -3120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := 2784, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := -26304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := -248032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := 211744, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := -554720, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := 5669696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -4506048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := 208304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := -80, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := -27392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := 107008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := -84544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -270752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 649088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -62160, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := -32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := 608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := -2080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -5728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := 41376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := -101984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := 26208, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := -152480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := -1024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := 4096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := 768, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := -74432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := 186624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := -23680, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := 640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := -1024, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := 34752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := -896, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := 768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := -18688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := 38336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := 2208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := -1152, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := 83264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := -104256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := -714688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := 643584, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := -12979712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := 3219296, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := -24121056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := 14561920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := -521408, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := -1280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := 32608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -10208, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := 52896, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := 75872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := -2222944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := 5211456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -5562112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := 347104, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := -3648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := 22496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := -35040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -216288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 1312224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -3316192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 4665056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -3579360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 157344, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := 16, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := -736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := 9088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := -44256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := 85728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := 6752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := -309632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := 501600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := 1504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := -7712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := 14752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := 96, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := -53216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := 85024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := -256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := 3072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := -7680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -9216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := -1920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -2304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := -352, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := 17280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := -49600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -2432, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 544640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := -1640320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := 330560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := -225792, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := 48608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := 352, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := -2400, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := 19104, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := -4960, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := -367520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := 810592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := -75488, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := -9280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := -42176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := 314560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := -111168, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := 933952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := -421696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := 576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := 4608, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -274944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := 461184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := -27264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := -1525248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := 462336, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := -436800, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := 96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := -1760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := 1664, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := -33536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := 23232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := 102336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := -253312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := 19488, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := -30848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := 59008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := 384, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := -212864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := 340096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := -26816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := 53440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := 64, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := -27648, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := 46144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := 1, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := 1, den := 952, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12],[r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25],[r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37],[r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48],[r49,r50,r51,r52,r53,r54,r55,r56,r57,r58],[r59,r60,r61,r62,r63,r64,r65,r66,r67],[r68,r69,r70,r71,r72,r73,r74,r75],[r76,r77,r78,r79,r80,r81,r82],[r26,r83,r83,r84,r85,r86],[r26,r87,r38,r88,r89],[],[],[],[r90,r91,r92,r93,r94,r95,r96,r97,r98,r99,r100,r101],[r102,r103,r104,r105,r106,r107,r108,r109,r110,r111,r112],[r113,r114,r115,r116,r117,r118,r119,r120,r121,r122],[r123,r124,r125,r126,r127,r128,r129,r130,-4384],[r90,r131,r132,r133,r134,r135,r136,-704],[r76,r77,r78,r79,r80,r81,r82],[0,r137,r138,r139,r140,512],[r26,r87,r141,r142,128],[],[],[],[r38,r143,r144,r145,r146,r147,r148,r149,r150,r151],[r26,r69,r152,r153,r154,r155,r156,r157,r158],[r90,r131,r132,r133,r134,r135,r136,-704],[],[r26,r83,r83,r84,r85,r86],[r26,r87,r141,r142,128],[],[],[],[r159,r160,r161,r162,r163,r164,r165,r166],[],[],[r26,r87,r38,r88,r89],[],[],[],[],[],[],[],[],[],[],[],[],[0,r167,r15,r168,r169,r170,r171,r172,r173,r174,18816],[r175,r176,r177,r178,r179,r180,r181,2560,r182,-3136],[0,r183,r184,r185,r186,r187,r188,r189,-2816],[],[],[0,r137,r138,r139,r140,512],[],[],[],[],[r102,r190,r191,r192,r193,r194,r195,r196,-3136],[r90,r131,r132,r133,r134,r135,r136,-704],[],[],[r26,r87,r141,r142,128],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,r197,r198,r199,r200,r201,r202,r203,r204,r205,r206,r207,r208,r209]),(⟨0,0,1⟩,[r210,r167,r211,r212,r213,r214,r215,r216,r217,r218,r219,r220,r221]),(⟨0,0,2⟩,[r68,r222,r223,r224,r225,r226,r227,r228,r229,r230,r231,r232]),(⟨0,0,3⟩,[r76,r233,r234,r235,r236,r237,r238,r239,r240,r241,r242]),(⟨0,0,4⟩,[r243,r244,r245,r246,r247,r248,r249,r250,r251,r252]),(⟨0,0,5⟩,[r253,r254,r255,r256,r257,r258,r259,r260,r261]),(⟨0,0,6⟩,[r262,r263,r264,r265,r266,r267,r268,r269]),(⟨0,0,7⟩,[r102,r270,r271,r272,r273,r274,r275]),(⟨0,0,8⟩,[r68,r276,r276,r277,r278,r279]),(⟨0,0,9⟩,[r68,r280,r76,r281,r282]),(⟨0,1,0⟩,[r210,r167,r211,r212,r213,r214,r215,r216,r217,r218,r219,r220,r221]),(⟨0,1,1⟩,[r13,r283,r284,r285,r286,r287,r288,r289,r290,r291,r292,r293]),(⟨0,1,2⟩,[r123,r294,r295,r296,r297,r298,r299,r300,r301,r302,r303]),(⟨0,1,3⟩,[r175,r304,r305,r306,r307,r308,r309,r310,r311,r312]),(⟨0,1,4⟩,[r313,r314,r315,r316,r317,r318,r319,r320,-2192]),(⟨0,1,5⟩,[r13,r321,r322,r323,r324,r325,r326,-352]),(⟨0,1,6⟩,[r102,r270,r271,r272,r273,r274,r275]),(⟨0,1,7⟩,[0,r327,r328,r329,r330,256]),(⟨0,1,8⟩,[r68,r280,r331,r332,64]),(⟨0,2,0⟩,[r68,r222,r223,r224,r225,r226,r227,r228,r229,r230,r231,r232]),(⟨0,2,1⟩,[r123,r294,r295,r296,r297,r298,r299,r300,r301,r302,r303]),(⟨0,2,2⟩,[r76,r333,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨0,2,3⟩,[r68,r263,r342,r343,r344,r345,r346,r347,r348]),(⟨0,2,4⟩,[r13,r321,r322,r323,r324,r325,r326,-352]),(⟨0,2,6⟩,[r68,r276,r276,r277,r278,r279]),(⟨0,2,7⟩,[r68,r280,r331,r332,64]),(⟨0,3,0⟩,[r76,r233,r234,r235,r236,r237,r238,r239,r240,r241,r242]),(⟨0,3,1⟩,[r175,r304,r305,r306,r307,r308,r309,r310,r311,r312]),(⟨0,3,2⟩,[r68,r263,r342,r343,r344,r345,r346,r347,r348]),(⟨0,3,3⟩,[r90,r131,r349,r350,r351,r352,r353,r354]),(⟨0,3,6⟩,[r68,r280,r76,r281,r282]),(⟨0,4,0⟩,[r243,r244,r245,r246,r247,r248,r249,r250,r251,r252]),(⟨0,4,1⟩,[r313,r314,r315,r316,r317,r318,r319,r320,-2192]),(⟨0,4,2⟩,[r13,r321,r322,r323,r324,r325,r326,-352]),(⟨0,5,0⟩,[r253,r254,r255,r256,r257,r258,r259,r260,r261]),(⟨0,5,1⟩,[r13,r321,r322,r323,r324,r325,r326,-352]),(⟨0,6,0⟩,[r262,r263,r264,r265,r266,r267,r268,r269]),(⟨0,6,1⟩,[r102,r270,r271,r272,r273,r274,r275]),(⟨0,6,2⟩,[r68,r276,r276,r277,r278,r279]),(⟨0,6,3⟩,[r68,r280,r76,r281,r282]),(⟨0,7,0⟩,[r102,r270,r271,r272,r273,r274,r275]),(⟨0,7,1⟩,[0,r327,r328,r329,r330,256]),(⟨0,7,2⟩,[r68,r280,r331,r332,64]),(⟨0,8,0⟩,[r68,r276,r276,r277,r278,r279]),(⟨0,8,1⟩,[r68,r280,r331,r332,64]),(⟨0,9,0⟩,[r68,r280,r76,r281,r282]),(⟨1,0,0⟩,[r210,r167,r211,r212,r213,r214,r215,r216,r217,r218,r219,r220,r221]),(⟨1,0,1⟩,[r13,r283,r284,r285,r286,r287,r288,r289,r290,r291,r292,r293]),(⟨1,0,2⟩,[r123,r294,r295,r296,r297,r298,r299,r300,r301,r302,r303]),(⟨1,0,3⟩,[r175,r304,r305,r306,r307,r308,r309,r310,r311,r312]),(⟨1,0,4⟩,[r313,r314,r315,r316,r317,r318,r319,r320,-2192]),(⟨1,0,5⟩,[r13,r321,r322,r323,r324,r325,r326,-352]),(⟨1,0,6⟩,[r102,r270,r271,r272,r273,r274,r275]),(⟨1,0,7⟩,[0,r327,r328,r329,r330,256]),(⟨1,0,8⟩,[r68,r280,r331,r332,64]),(⟨1,1,0⟩,[r13,r283,r284,r285,r286,r287,r288,r289,r290,r291,r292,r293]),(⟨1,1,1⟩,[0,r355,r211,r356,r357,r358,r359,r360,r361,r362,9408]),(⟨1,1,2⟩,[r363,r364,r365,r366,r367,r368,r369,1280,r370,-1568]),(⟨1,1,3⟩,[0,r159,r160,r371,r372,r373,r374,r375,-1408]),(⟨1,1,6⟩,[0,r327,r328,r329,r330,256]),(⟨1,2,0⟩,[r123,r294,r295,r296,r297,r298,r299,r300,r301,r302,r303]),(⟨1,2,1⟩,[r363,r364,r365,r366,r367,r368,r369,1280,r370,-1568]),(⟨1,2,2⟩,[r123,r103,r138,r376,r377,r378,r379,r380,-1568]),(⟨1,2,3⟩,[r13,r321,r322,r323,r324,r325,r326,-352]),(⟨1,2,6⟩,[r68,r280,r331,r332,64]),(⟨1,3,0⟩,[r175,r304,r305,r306,r307,r308,r309,r310,r311,r312]),(⟨1,3,1⟩,[0,r159,r160,r371,r372,r373,r374,r375,-1408]),(⟨1,3,2⟩,[r13,r321,r322,r323,r324,r325,r326,-352]),(⟨1,4,0⟩,[r313,r314,r315,r316,r317,r318,r319,r320,-2192]),(⟨1,5,0⟩,[r13,r321,r322,r323,r324,r325,r326,-352]),(⟨1,6,0⟩,[r102,r270,r271,r272,r273,r274,r275]),(⟨1,6,1⟩,[0,r327,r328,r329,r330,256]),(⟨1,6,2⟩,[r68,r280,r331,r332,64]),(⟨1,7,0⟩,[0,r327,r328,r329,r330,256]),(⟨1,8,0⟩,[r68,r280,r331,r332,64]),(⟨2,0,0⟩,[r68,r222,r223,r224,r225,r226,r227,r228,r229,r230,r231,r232]),(⟨2,0,1⟩,[r123,r294,r295,r296,r297,r298,r299,r300,r301,r302,r303]),(⟨2,0,2⟩,[r76,r333,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨2,0,3⟩,[r68,r263,r342,r343,r344,r345,r346,r347,r348]),(⟨2,0,4⟩,[r13,r321,r322,r323,r324,r325,r326,-352]),(⟨2,0,6⟩,[r68,r276,r276,r277,r278,r279]),(⟨2,0,7⟩,[r68,r280,r331,r332,64]),(⟨2,1,0⟩,[r123,r294,r295,r296,r297,r298,r299,r300,r301,r302,r303]),(⟨2,1,1⟩,[r363,r364,r365,r366,r367,r368,r369,1280,r370,-1568]),(⟨2,1,2⟩,[r123,r103,r138,r376,r377,r378,r379,r380,-1568]),(⟨2,1,3⟩,[r13,r321,r322,r323,r324,r325,r326,-352]),(⟨2,1,6⟩,[r68,r280,r331,r332,64]),(⟨2,2,0⟩,[r76,r333,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨2,2,1⟩,[r123,r103,r138,r376,r377,r378,r379,r380,-1568]),(⟨2,3,0⟩,[r68,r263,r342,r343,r344,r345,r346,r347,r348]),(⟨2,3,1⟩,[r13,r321,r322,r323,r324,r325,r326,-352]),(⟨2,4,0⟩,[r13,r321,r322,r323,r324,r325,r326,-352]),(⟨2,6,0⟩,[r68,r276,r276,r277,r278,r279]),(⟨2,6,1⟩,[r68,r280,r331,r332,64]),(⟨2,7,0⟩,[r68,r280,r331,r332,64]),(⟨3,0,0⟩,[r76,r233,r234,r235,r236,r237,r238,r239,r240,r241,r242]),(⟨3,0,1⟩,[r175,r304,r305,r306,r307,r308,r309,r310,r311,r312]),(⟨3,0,2⟩,[r68,r263,r342,r343,r344,r345,r346,r347,r348]),(⟨3,0,3⟩,[r90,r131,r349,r350,r351,r352,r353,r354]),(⟨3,0,6⟩,[r68,r280,r76,r281,r282]),(⟨3,1,0⟩,[r175,r304,r305,r306,r307,r308,r309,r310,r311,r312]),(⟨3,1,1⟩,[0,r159,r160,r371,r372,r373,r374,r375,-1408]),(⟨3,1,2⟩,[r13,r321,r322,r323,r324,r325,r326,-352]),(⟨3,2,0⟩,[r68,r263,r342,r343,r344,r345,r346,r347,r348]),(⟨3,2,1⟩,[r13,r321,r322,r323,r324,r325,r326,-352]),(⟨3,3,0⟩,[r90,r131,r349,r350,r351,r352,r353,r354]),(⟨3,6,0⟩,[r68,r280,r76,r281,r282]),(⟨4,0,0⟩,[r243,r244,r245,r246,r247,r248,r249,r250,r251,r252]),(⟨4,0,1⟩,[r313,r314,r315,r316,r317,r318,r319,r320,-2192]),(⟨4,0,2⟩,[r13,r321,r322,r323,r324,r325,r326,-352]),(⟨4,1,0⟩,[r313,r314,r315,r316,r317,r318,r319,r320,-2192]),(⟨4,2,0⟩,[r13,r321,r322,r323,r324,r325,r326,-352]),(⟨5,0,0⟩,[r253,r254,r255,r256,r257,r258,r259,r260,r261]),(⟨5,0,1⟩,[r13,r321,r322,r323,r324,r325,r326,-352]),(⟨5,1,0⟩,[r13,r321,r322,r323,r324,r325,r326,-352]),(⟨6,0,0⟩,[r262,r263,r264,r265,r266,r267,r268,r269]),(⟨6,0,1⟩,[r102,r270,r271,r272,r273,r274,r275]),(⟨6,0,2⟩,[r68,r276,r276,r277,r278,r279]),(⟨6,0,3⟩,[r68,r280,r76,r281,r282]),(⟨6,1,0⟩,[r102,r270,r271,r272,r273,r274,r275]),(⟨6,1,1⟩,[0,r327,r328,r329,r330,256]),(⟨6,1,2⟩,[r68,r280,r331,r332,64]),(⟨6,2,0⟩,[r68,r276,r276,r277,r278,r279]),(⟨6,2,1⟩,[r68,r280,r331,r332,64]),(⟨6,3,0⟩,[r68,r280,r76,r281,r282]),(⟨7,0,0⟩,[r102,r270,r271,r272,r273,r274,r275]),(⟨7,0,1⟩,[0,r327,r328,r329,r330,256]),(⟨7,0,2⟩,[r68,r280,r331,r332,64]),(⟨7,1,0⟩,[0,r327,r328,r329,r330,256]),(⟨7,2,0⟩,[r68,r280,r331,r332,64]),(⟨8,0,0⟩,[r68,r276,r276,r277,r278,r279]),(⟨8,0,1⟩,[r68,r280,r331,r332,64]),(⟨8,1,0⟩,[r68,r280,r331,r332,64]),(⟨9,0,0⟩,[r68,r280,r76,r281,r282])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,9,-60,150,-162,33,54]),(⟨0,0,1⟩,[-3,21,-66,118,-119,49]),(⟨0,0,2⟩,[-1,10,-42,70,-49]),(⟨0,0,3⟩,[6,-22,38,-22]),(⟨0,0,6⟩,[4]),(⟨0,1,0⟩,[-3,21,-66,118,-119,49]),(⟨0,2,0⟩,[-1,10,-42,70,-49]),(⟨0,3,0⟩,[6,-22,38,-22]),(⟨0,6,0⟩,[4]),(⟨1,0,0⟩,[-3,21,-66,118,-119,49]),(⟨2,0,0⟩,[-1,10,-42,70,-49]),(⟨3,0,0⟩,[6,-22,38,-22]),(⟨6,0,0⟩,[4])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[128,-1792,5120,30720,-231808,574208,-567040,116736]),(⟨0,0,1⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨0,0,2⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨0,0,3⟩,[-128,1536,256,-37376,76672]),(⟨0,1,0⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨0,1,1⟩,[0,-512,6144,-15360,-18432,60928]),(⟨0,1,2⟩,[-128,1536,-3840,-4608,15232]),(⟨0,2,0⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨0,2,1⟩,[-128,1536,-3840,-4608,15232]),(⟨0,3,0⟩,[-128,1536,256,-37376,76672]),(⟨1,0,0⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨1,0,1⟩,[0,-512,6144,-15360,-18432,60928]),(⟨1,0,2⟩,[-128,1536,-3840,-4608,15232]),(⟨1,1,0⟩,[0,-512,6144,-15360,-18432,60928]),(⟨1,2,0⟩,[-128,1536,-3840,-4608,15232]),(⟨2,0,0⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨2,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨2,1,0⟩,[-128,1536,-3840,-4608,15232]),(⟨3,0,0⟩,[-128,1536,256,-37376,76672])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 2 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r381) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 3 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r382) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨6,0,0⟩,[4])]

noncomputable def partial12 : Poly := [(⟨6,0,0⟩,[512,-7168,20480,122880,-927232,2296832,-2268160,466944]),(⟨6,0,1⟩,[512,-8192,32768,43008,-595456,1492992,-1326080]),(⟨6,0,2⟩,[-512,5120,5120,-139264,278016,-50176]),(⟨6,0,3⟩,[-512,6144,1024,-149504,306688]),(⟨6,1,0⟩,[512,-8192,32768,43008,-595456,1492992,-1326080]),(⟨6,1,1⟩,[0,-2048,24576,-61440,-73728,243712]),(⟨6,1,2⟩,[-512,6144,-15360,-18432,60928]),(⟨6,2,0⟩,[-512,5120,5120,-139264,278016,-50176]),(⟨6,2,1⟩,[-512,6144,-15360,-18432,60928]),(⟨6,3,0⟩,[-512,6144,1024,-149504,306688]),(⟨7,0,0⟩,[512,-8192,32768,43008,-595456,1492992,-1326080]),(⟨7,0,1⟩,[0,-2048,24576,-61440,-73728,243712]),(⟨7,0,2⟩,[-512,6144,-15360,-18432,60928]),(⟨7,1,0⟩,[0,-2048,24576,-61440,-73728,243712]),(⟨7,2,0⟩,[-512,6144,-15360,-18432,60928]),(⟨8,0,0⟩,[-512,5120,5120,-139264,278016,-50176]),(⟨8,0,1⟩,[-512,6144,-15360,-18432,60928]),(⟨8,1,0⟩,[-512,6144,-15360,-18432,60928]),(⟨9,0,0⟩,[-512,6144,1024,-149504,306688])]


theorem partial_checked12 :
    (Poly.add (Poly.add (Poly.mul chunk12 sourceRight) partial13)
      (Poly.scale (K.ofRat (-1)) partial12)).isZero := by decide +kernel

theorem partial_sound12 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 12)
      sourceRight).eval u v t=partial12.eval u v t := by
  change (Poly.mul (chunk12++(sourceLeft.drop 13))
    sourceRight).eval u v t=partial12.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound13 partial_checked12 u v t


noncomputable def chunk8 : Poly := [(⟨0,6,0⟩,[4]),(⟨1,0,0⟩,[-3,21,-66,118,-119,49]),(⟨2,0,0⟩,[-1,10,-42,70,-49]),(⟨3,0,0⟩,[6,-22,38,-22])]

noncomputable def partial8 : Poly := [(⟨0,6,0⟩,[512,-7168,20480,122880,-927232,2296832,-2268160,466944]),(⟨0,6,1⟩,[512,-8192,32768,43008,-595456,1492992,-1326080]),(⟨0,6,2⟩,[-512,5120,5120,-139264,278016,-50176]),(⟨0,6,3⟩,[-512,6144,1024,-149504,306688]),(⟨0,7,0⟩,[512,-8192,32768,43008,-595456,1492992,-1326080]),(⟨0,7,1⟩,[0,-2048,24576,-61440,-73728,243712]),(⟨0,7,2⟩,[-512,6144,-15360,-18432,60928]),(⟨0,8,0⟩,[-512,5120,5120,-139264,278016,-50176]),(⟨0,8,1⟩,[-512,6144,-15360,-18432,60928]),(⟨0,9,0⟩,[-512,6144,1024,-149504,306688]),(⟨1,0,0⟩,[-384,8064,-61440,148736,775936,-7794432,31986688,-80913920,136723072,-154304640,109388800,-41676544,5720064]),(⟨1,0,1⟩,[-384,8832,-76032,290048,-125184,-3738880,18851328,-50040320,84165248,-90830208,57740032,-16244480]),(⟨1,0,2⟩,[384,-6528,31488,31744,-857856,3787520,-9048576,13235200,-11457152,4898432,-614656]),(⟨1,0,3⟩,[384,-7296,39936,1024,-835328,3918080,-9425920,13507584,-10955392,3756928]),(⟨1,1,0⟩,[-384,8832,-76032,290048,-125184,-3738880,18851328,-50040320,84165248,-90830208,57740032,-16244480]),(⟨1,1,1⟩,[0,1536,-29184,208896,-733184,1229824,-72704,-4067328,8630272,-8153600,2985472]),(⟨1,1,2⟩,[384,-7296,52224,-183296,307456,-18176,-1016832,2157568,-2038400,746368]),(⟨1,2,0⟩,[384,-6528,31488,31744,-857856,3787520,-9048576,13235200,-11457152,4898432,-614656]),(⟨1,2,1⟩,[384,-7296,52224,-183296,307456,-18176,-1016832,2157568,-2038400,746368]),(⟨1,3,0⟩,[384,-7296,39936,1024,-835328,3918080,-9425920,13507584,-10955392,3756928]),(⟨1,6,0⟩,[512,-8192,32768,43008,-595456,1492992,-1326080]),(⟨1,6,1⟩,[0,-2048,24576,-61440,-73728,243712]),(⟨1,6,2⟩,[-512,6144,-15360,-18432,60928]),(⟨1,7,0⟩,[0,-2048,24576,-61440,-73728,243712]),(⟨1,8,0⟩,[-512,6144,-15360,-18432,60928]),(⟨2,0,0⟩,[-512,11904,-104448,394752,67072,-7475200,36795904,-97676032,160701440,-163562112,93696512,-21964544]),(⟨2,0,1⟩,[-128,4864,-63232,375040,-970496,-409856,10594816,-34006272,55975808,-49649152,19229952]),(⟨2,0,2⟩,[512,-9856,69120,-198400,-68096,2178560,-6561280,9255680,-6322176,1361024]),(⟨2,0,3⟩,[128,-2816,20480,-33536,-347392,2279168,-5849088,7198464,-3756928]),(⟨2,1,0⟩,[-128,4864,-63232,375040,-970496,-409856,10594816,-34006272,55975808,-49649152,19229952]),(⟨2,1,1⟩,[0,512,-11264,98304,-429056,855040,7168,-3096576,5168128,-2985472]),(⟨2,1,2⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨2,2,0⟩,[512,-9856,69120,-198400,-68096,2178560,-6561280,9255680,-6322176,1361024]),(⟨2,2,1⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨2,3,0⟩,[128,-2816,20480,-33536,-347392,2279168,-5849088,7198464,-3756928]),(⟨2,6,0⟩,[-512,5120,5120,-139264,278016,-50176]),(⟨2,6,1⟩,[-512,6144,-15360,-18432,60928]),(⟨2,7,0⟩,[-512,6144,-15360,-18432,60928]),(⟨3,0,0⟩,[1024,-16768,72448,198656,-2927872,11747584,-23900416,23391232,-859904,-19686272,13061632]),(⟨3,0,1⟩,[1152,-21888,140032,-281344,-894976,6579712,-17103616,23812864,-17679488,5054336]),(⟨3,0,2⟩,[-640,7680,-768,-292864,1417216,-2953728,2908928,-713728,-470400]),(⟨3,0,3⟩,[-768,12032,-37120,-168704,1258240,-3112704,3735808,-1686784]),(⟨3,1,0⟩,[1152,-21888,140032,-281344,-894976,6579712,-17103616,23812864,-17679488,5054336]),(⟨3,1,1⟩,[0,-3072,48128,-246784,472064,52224,-1702912,2720768,-1340416]),(⟨3,1,2⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨3,2,0⟩,[-640,7680,-768,-292864,1417216,-2953728,2908928,-713728,-470400]),(⟨3,2,1⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨3,3,0⟩,[-768,12032,-37120,-168704,1258240,-3112704,3735808,-1686784]),(⟨3,6,0⟩,[-512,6144,1024,-149504,306688]),(⟨4,0,0⟩,[1280,-24960,155904,-210432,-1984256,11857664,-31064320,45357568,-36048384,11665024]),(⟨4,0,1⟩,[128,-5888,72704,-354048,685824,54016,-2477056,4012800,-2086784]),(⟨4,0,2⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨4,1,0⟩,[128,-5888,72704,-354048,685824,54016,-2477056,4012800,-2086784]),(⟨4,2,0⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨5,0,0⟩,[-640,7680,-4864,-219136,856064,-676352,-2166016,5192704,-3480960]),(⟨5,0,1⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨5,1,0⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨6,0,0⟩,[-256,4864,-16640,-45824,331008,-815872,1467648,-1219840]),(⟨6,0,1⟩,[512,-8192,32768,43008,-595456,1492992,-1326080]),(⟨6,0,2⟩,[-512,5120,5120,-139264,278016,-50176]),(⟨6,0,3⟩,[-512,6144,1024,-149504,306688]),(⟨6,1,0⟩,[512,-8192,32768,43008,-595456,1492992,-1326080]),(⟨6,1,1⟩,[0,-2048,24576,-61440,-73728,243712]),(⟨6,1,2⟩,[-512,6144,-15360,-18432,60928]),(⟨6,2,0⟩,[-512,5120,5120,-139264,278016,-50176]),(⟨6,2,1⟩,[-512,6144,-15360,-18432,60928]),(⟨6,3,0⟩,[-512,6144,1024,-149504,306688]),(⟨7,0,0⟩,[512,-8192,32768,43008,-595456,1492992,-1326080]),(⟨7,0,1⟩,[0,-2048,24576,-61440,-73728,243712]),(⟨7,0,2⟩,[-512,6144,-15360,-18432,60928]),(⟨7,1,0⟩,[0,-2048,24576,-61440,-73728,243712]),(⟨7,2,0⟩,[-512,6144,-15360,-18432,60928]),(⟨8,0,0⟩,[-512,5120,5120,-139264,278016,-50176]),(⟨8,0,1⟩,[-512,6144,-15360,-18432,60928]),(⟨8,1,0⟩,[-512,6144,-15360,-18432,60928]),(⟨9,0,0⟩,[-512,6144,1024,-149504,306688])]


theorem partial_checked8 :
    (Poly.add (Poly.add (Poly.mul chunk8 sourceRight) partial12)
      (Poly.scale (K.ofRat (-1)) partial8)).isZero := by decide +kernel

theorem partial_sound8 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 8)
      sourceRight).eval u v t=partial8.eval u v t := by
  change (Poly.mul (chunk8++(sourceLeft.drop 12))
    sourceRight).eval u v t=partial8.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound12 partial_checked8 u v t


noncomputable def chunk4 : Poly := [(⟨0,0,6⟩,[4]),(⟨0,1,0⟩,[-3,21,-66,118,-119,49]),(⟨0,2,0⟩,[-1,10,-42,70,-49]),(⟨0,3,0⟩,[6,-22,38,-22])]

noncomputable def partial4 : Poly := [(⟨0,0,6⟩,[512,-7168,20480,122880,-927232,2296832,-2268160,466944]),(⟨0,0,7⟩,[512,-8192,32768,43008,-595456,1492992,-1326080]),(⟨0,0,8⟩,[-512,5120,5120,-139264,278016,-50176]),(⟨0,0,9⟩,[-512,6144,1024,-149504,306688]),(⟨0,1,0⟩,[-384,8064,-61440,148736,775936,-7794432,31986688,-80913920,136723072,-154304640,109388800,-41676544,5720064]),(⟨0,1,1⟩,[-384,8832,-76032,290048,-125184,-3738880,18851328,-50040320,84165248,-90830208,57740032,-16244480]),(⟨0,1,2⟩,[384,-6528,31488,31744,-857856,3787520,-9048576,13235200,-11457152,4898432,-614656]),(⟨0,1,3⟩,[384,-7296,39936,1024,-835328,3918080,-9425920,13507584,-10955392,3756928]),(⟨0,1,6⟩,[512,-8192,32768,43008,-595456,1492992,-1326080]),(⟨0,1,7⟩,[0,-2048,24576,-61440,-73728,243712]),(⟨0,1,8⟩,[-512,6144,-15360,-18432,60928]),(⟨0,2,0⟩,[-512,11904,-104448,394752,67072,-7475200,36795904,-97676032,160701440,-163562112,93696512,-21964544]),(⟨0,2,1⟩,[-128,4864,-63232,375040,-970496,-409856,10594816,-34006272,55975808,-49649152,19229952]),(⟨0,2,2⟩,[512,-9856,69120,-198400,-68096,2178560,-6561280,9255680,-6322176,1361024]),(⟨0,2,3⟩,[128,-2816,20480,-33536,-347392,2279168,-5849088,7198464,-3756928]),(⟨0,2,6⟩,[-512,5120,5120,-139264,278016,-50176]),(⟨0,2,7⟩,[-512,6144,-15360,-18432,60928]),(⟨0,3,0⟩,[1024,-16768,72448,198656,-2927872,11747584,-23900416,23391232,-859904,-19686272,13061632]),(⟨0,3,1⟩,[1152,-21888,140032,-281344,-894976,6579712,-17103616,23812864,-17679488,5054336]),(⟨0,3,2⟩,[-640,7680,-768,-292864,1417216,-2953728,2908928,-713728,-470400]),(⟨0,3,3⟩,[-768,12032,-37120,-168704,1258240,-3112704,3735808,-1686784]),(⟨0,3,6⟩,[-512,6144,1024,-149504,306688]),(⟨0,4,0⟩,[1280,-24960,155904,-210432,-1984256,11857664,-31064320,45357568,-36048384,11665024]),(⟨0,4,1⟩,[128,-5888,72704,-354048,685824,54016,-2477056,4012800,-2086784]),(⟨0,4,2⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨0,5,0⟩,[-640,7680,-4864,-219136,856064,-676352,-2166016,5192704,-3480960]),(⟨0,5,1⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨0,6,0⟩,[-256,4864,-16640,-45824,331008,-815872,1467648,-1219840]),(⟨0,6,1⟩,[512,-8192,32768,43008,-595456,1492992,-1326080]),(⟨0,6,2⟩,[-512,5120,5120,-139264,278016,-50176]),(⟨0,6,3⟩,[-512,6144,1024,-149504,306688]),(⟨0,7,0⟩,[512,-8192,32768,43008,-595456,1492992,-1326080]),(⟨0,7,1⟩,[0,-2048,24576,-61440,-73728,243712]),(⟨0,7,2⟩,[-512,6144,-15360,-18432,60928]),(⟨0,8,0⟩,[-512,5120,5120,-139264,278016,-50176]),(⟨0,8,1⟩,[-512,6144,-15360,-18432,60928]),(⟨0,9,0⟩,[-512,6144,1024,-149504,306688]),(⟨1,0,0⟩,[-384,8064,-61440,148736,775936,-7794432,31986688,-80913920,136723072,-154304640,109388800,-41676544,5720064]),(⟨1,0,1⟩,[-384,8832,-76032,290048,-125184,-3738880,18851328,-50040320,84165248,-90830208,57740032,-16244480]),(⟨1,0,2⟩,[384,-6528,31488,31744,-857856,3787520,-9048576,13235200,-11457152,4898432,-614656]),(⟨1,0,3⟩,[384,-7296,39936,1024,-835328,3918080,-9425920,13507584,-10955392,3756928]),(⟨1,0,6⟩,[512,-8192,32768,43008,-595456,1492992,-1326080]),(⟨1,0,7⟩,[0,-2048,24576,-61440,-73728,243712]),(⟨1,0,8⟩,[-512,6144,-15360,-18432,60928]),(⟨1,1,0⟩,[-768,17664,-152064,580096,-250368,-7477760,37702656,-100080640,168330496,-181660416,115480064,-32488960]),(⟨1,1,1⟩,[0,3072,-58368,417792,-1466368,2459648,-145408,-8134656,17260544,-16307200,5970944]),(⟨1,1,2⟩,[768,-14592,104448,-366592,614912,-36352,-2033664,4315136,-4076800,1492736]),(⟨1,1,6⟩,[0,-2048,24576,-61440,-73728,243712]),(⟨1,2,0⟩,[256,-1664,-31744,406784,-1828352,3377664,1546240,-20771072,44518656,-44750720,18615296]),(⟨1,2,1⟩,[384,-6784,40960,-84992,-121600,836864,-1009664,-939008,3129728,-2239104]),(⟨1,2,2⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨1,2,6⟩,[-512,6144,-15360,-18432,60928]),(⟨1,3,0⟩,[1536,-29184,179968,-280320,-1730304,10497792,-26529536,37320448,-28634880,8811264]),(⟨1,3,1⟩,[0,-3072,48128,-246784,472064,52224,-1702912,2720768,-1340416]),(⟨1,3,2⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨1,4,0⟩,[128,-5888,72704,-354048,685824,54016,-2477056,4012800,-2086784]),(⟨1,5,0⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨1,6,0⟩,[512,-8192,32768,43008,-595456,1492992,-1326080]),(⟨1,6,1⟩,[0,-2048,24576,-61440,-73728,243712]),(⟨1,6,2⟩,[-512,6144,-15360,-18432,60928]),(⟨1,7,0⟩,[0,-2048,24576,-61440,-73728,243712]),(⟨1,8,0⟩,[-512,6144,-15360,-18432,60928]),(⟨2,0,0⟩,[-512,11904,-104448,394752,67072,-7475200,36795904,-97676032,160701440,-163562112,93696512,-21964544]),(⟨2,0,1⟩,[-128,4864,-63232,375040,-970496,-409856,10594816,-34006272,55975808,-49649152,19229952]),(⟨2,0,2⟩,[512,-9856,69120,-198400,-68096,2178560,-6561280,9255680,-6322176,1361024]),(⟨2,0,3⟩,[128,-2816,20480,-33536,-347392,2279168,-5849088,7198464,-3756928]),(⟨2,0,6⟩,[-512,5120,5120,-139264,278016,-50176]),(⟨2,0,7⟩,[-512,6144,-15360,-18432,60928]),(⟨2,1,0⟩,[256,-1664,-31744,406784,-1828352,3377664,1546240,-20771072,44518656,-44750720,18615296]),(⟨2,1,1⟩,[384,-6784,40960,-84992,-121600,836864,-1009664,-939008,3129728,-2239104]),(⟨2,1,2⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨2,1,6⟩,[-512,6144,-15360,-18432,60928]),(⟨2,2,0⟩,[1024,-19712,138240,-396800,-136192,4357120,-13122560,18511360,-12644352,2722048]),(⟨2,2,1⟩,[256,-5632,49152,-214528,427520,3584,-1548288,2584064,-1492736]),(⟨2,3,0⟩,[-512,4864,19712,-326400,1069824,-674560,-2940160,6484736,-4227328]),(⟨2,3,1⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨2,4,0⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨2,6,0⟩,[-512,5120,5120,-139264,278016,-50176]),(⟨2,6,1⟩,[-512,6144,-15360,-18432,60928]),(⟨2,7,0⟩,[-512,6144,-15360,-18432,60928]),(⟨3,0,0⟩,[1024,-16768,72448,198656,-2927872,11747584,-23900416,23391232,-859904,-19686272,13061632]),(⟨3,0,1⟩,[1152,-21888,140032,-281344,-894976,6579712,-17103616,23812864,-17679488,5054336]),(⟨3,0,2⟩,[-640,7680,-768,-292864,1417216,-2953728,2908928,-713728,-470400]),(⟨3,0,3⟩,[-768,12032,-37120,-168704,1258240,-3112704,3735808,-1686784]),(⟨3,0,6⟩,[-512,6144,1024,-149504,306688]),(⟨3,1,0⟩,[1536,-29184,179968,-280320,-1730304,10497792,-26529536,37320448,-28634880,8811264]),(⟨3,1,1⟩,[0,-3072,48128,-246784,472064,52224,-1702912,2720768,-1340416]),(⟨3,1,2⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨3,2,0⟩,[-512,4864,19712,-326400,1069824,-674560,-2940160,6484736,-4227328]),(⟨3,2,1⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨3,3,0⟩,[-1536,24064,-74240,-337408,2516480,-6225408,7471616,-3373568]),(⟨3,6,0⟩,[-512,6144,1024,-149504,306688]),(⟨4,0,0⟩,[1280,-24960,155904,-210432,-1984256,11857664,-31064320,45357568,-36048384,11665024]),(⟨4,0,1⟩,[128,-5888,72704,-354048,685824,54016,-2477056,4012800,-2086784]),(⟨4,0,2⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨4,1,0⟩,[128,-5888,72704,-354048,685824,54016,-2477056,4012800,-2086784]),(⟨4,2,0⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨5,0,0⟩,[-640,7680,-4864,-219136,856064,-676352,-2166016,5192704,-3480960]),(⟨5,0,1⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨5,1,0⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨6,0,0⟩,[-256,4864,-16640,-45824,331008,-815872,1467648,-1219840]),(⟨6,0,1⟩,[512,-8192,32768,43008,-595456,1492992,-1326080]),(⟨6,0,2⟩,[-512,5120,5120,-139264,278016,-50176]),(⟨6,0,3⟩,[-512,6144,1024,-149504,306688]),(⟨6,1,0⟩,[512,-8192,32768,43008,-595456,1492992,-1326080]),(⟨6,1,1⟩,[0,-2048,24576,-61440,-73728,243712]),(⟨6,1,2⟩,[-512,6144,-15360,-18432,60928]),(⟨6,2,0⟩,[-512,5120,5120,-139264,278016,-50176]),(⟨6,2,1⟩,[-512,6144,-15360,-18432,60928]),(⟨6,3,0⟩,[-512,6144,1024,-149504,306688]),(⟨7,0,0⟩,[512,-8192,32768,43008,-595456,1492992,-1326080]),(⟨7,0,1⟩,[0,-2048,24576,-61440,-73728,243712]),(⟨7,0,2⟩,[-512,6144,-15360,-18432,60928]),(⟨7,1,0⟩,[0,-2048,24576,-61440,-73728,243712]),(⟨7,2,0⟩,[-512,6144,-15360,-18432,60928]),(⟨8,0,0⟩,[-512,5120,5120,-139264,278016,-50176]),(⟨8,0,1⟩,[-512,6144,-15360,-18432,60928]),(⟨8,1,0⟩,[-512,6144,-15360,-18432,60928]),(⟨9,0,0⟩,[-512,6144,1024,-149504,306688])]


theorem partial_checked4 :
    (Poly.add (Poly.add (Poly.mul chunk4 sourceRight) partial8)
      (Poly.scale (K.ofRat (-1)) partial4)).isZero := by decide +kernel

theorem partial_sound4 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 4)
      sourceRight).eval u v t=partial4.eval u v t := by
  change (Poly.mul (chunk4++(sourceLeft.drop 8))
    sourceRight).eval u v t=partial4.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound8 partial_checked4 u v t


noncomputable def chunk0 : Poly := [(⟨0,0,0⟩,[0,9,-60,150,-162,33,54]),(⟨0,0,1⟩,[-3,21,-66,118,-119,49]),(⟨0,0,2⟩,[-1,10,-42,70,-49]),(⟨0,0,3⟩,[6,-22,38,-22])]

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,1152,-23808,172800,-320256,-2866944,22802688,-79231488,160047360,-191072640,115802112,-6616320,-26767872,6303744]),(⟨0,0,1⟩,[-384,9216,-87552,364544,53248,-8214528,44502784,-130204160,237514624,-268830720,167373568,-32461312,-12182016]),(⟨0,0,2⟩,[-512,10752,-85248,310272,-110336,-4780288,27118336,-80746240,146480384,-161116416,97035776,-22641920]),(⟨0,0,3⟩,[1024,-17920,93952,89600,-3028480,14465536,-34104832,41038336,-14500352,-19174400,17201920]),(⟨0,0,4⟩,[1280,-24960,155904,-210432,-1984256,11857664,-31064320,45357568,-36048384,11665024]),(⟨0,0,5⟩,[-640,7680,-4864,-219136,856064,-676352,-2166016,5192704,-3480960]),(⟨0,0,6⟩,[-256,4864,-16640,-45824,331008,-815872,1467648,-1219840]),(⟨0,0,7⟩,[512,-8192,32768,43008,-595456,1492992,-1326080]),(⟨0,0,8⟩,[-512,5120,5120,-139264,278016,-50176]),(⟨0,0,9⟩,[-512,6144,1024,-149504,306688]),(⟨0,1,0⟩,[-384,9216,-87552,364544,53248,-8214528,44502784,-130204160,237514624,-268830720,167373568,-32461312,-12182016]),(⟨0,1,1⟩,[-768,17664,-156672,666112,-834048,-5717504,36040704,-103837696,180280576,-192968448,116495360,-29198848]),(⟨0,1,2⟩,[256,-2816,-10240,260864,-1388288,2962176,606976,-17783552,41691648,-44496896,19437824]),(⟨0,1,3⟩,[1536,-29184,179968,-280320,-1730304,10497792,-26529536,37320448,-28634880,8811264]),(⟨0,1,4⟩,[128,-5888,72704,-354048,685824,54016,-2477056,4012800,-2086784]),(⟨0,1,5⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨0,1,6⟩,[512,-8192,32768,43008,-595456,1492992,-1326080]),(⟨0,1,7⟩,[0,-2048,24576,-61440,-73728,243712]),(⟨0,1,8⟩,[-512,6144,-15360,-18432,60928]),(⟨0,2,0⟩,[-512,10752,-85248,310272,-110336,-4780288,27118336,-80746240,146480384,-161116416,97035776,-22641920]),(⟨0,2,1⟩,[256,-2816,-10240,260864,-1388288,2962176,606976,-17783552,41691648,-44496896,19437824]),(⟨0,2,2⟩,[1024,-19712,138240,-396800,-136192,4357120,-13122560,18511360,-12644352,2722048]),(⟨0,2,3⟩,[-512,4864,19712,-326400,1069824,-674560,-2940160,6484736,-4227328]),(⟨0,2,4⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨0,2,6⟩,[-512,5120,5120,-139264,278016,-50176]),(⟨0,2,7⟩,[-512,6144,-15360,-18432,60928]),(⟨0,3,0⟩,[1024,-17920,93952,89600,-3028480,14465536,-34104832,41038336,-14500352,-19174400,17201920]),(⟨0,3,1⟩,[1536,-29184,179968,-280320,-1730304,10497792,-26529536,37320448,-28634880,8811264]),(⟨0,3,2⟩,[-512,4864,19712,-326400,1069824,-674560,-2940160,6484736,-4227328]),(⟨0,3,3⟩,[-1536,24064,-74240,-337408,2516480,-6225408,7471616,-3373568]),(⟨0,3,6⟩,[-512,6144,1024,-149504,306688]),(⟨0,4,0⟩,[1280,-24960,155904,-210432,-1984256,11857664,-31064320,45357568,-36048384,11665024]),(⟨0,4,1⟩,[128,-5888,72704,-354048,685824,54016,-2477056,4012800,-2086784]),(⟨0,4,2⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨0,5,0⟩,[-640,7680,-4864,-219136,856064,-676352,-2166016,5192704,-3480960]),(⟨0,5,1⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨0,6,0⟩,[-256,4864,-16640,-45824,331008,-815872,1467648,-1219840]),(⟨0,6,1⟩,[512,-8192,32768,43008,-595456,1492992,-1326080]),(⟨0,6,2⟩,[-512,5120,5120,-139264,278016,-50176]),(⟨0,6,3⟩,[-512,6144,1024,-149504,306688]),(⟨0,7,0⟩,[512,-8192,32768,43008,-595456,1492992,-1326080]),(⟨0,7,1⟩,[0,-2048,24576,-61440,-73728,243712]),(⟨0,7,2⟩,[-512,6144,-15360,-18432,60928]),(⟨0,8,0⟩,[-512,5120,5120,-139264,278016,-50176]),(⟨0,8,1⟩,[-512,6144,-15360,-18432,60928]),(⟨0,9,0⟩,[-512,6144,1024,-149504,306688]),(⟨1,0,0⟩,[-384,9216,-87552,364544,53248,-8214528,44502784,-130204160,237514624,-268830720,167373568,-32461312,-12182016]),(⟨1,0,1⟩,[-768,17664,-156672,666112,-834048,-5717504,36040704,-103837696,180280576,-192968448,116495360,-29198848]),(⟨1,0,2⟩,[256,-2816,-10240,260864,-1388288,2962176,606976,-17783552,41691648,-44496896,19437824]),(⟨1,0,3⟩,[1536,-29184,179968,-280320,-1730304,10497792,-26529536,37320448,-28634880,8811264]),(⟨1,0,4⟩,[128,-5888,72704,-354048,685824,54016,-2477056,4012800,-2086784]),(⟨1,0,5⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨1,0,6⟩,[512,-8192,32768,43008,-595456,1492992,-1326080]),(⟨1,0,7⟩,[0,-2048,24576,-61440,-73728,243712]),(⟨1,0,8⟩,[-512,6144,-15360,-18432,60928]),(⟨1,1,0⟩,[-768,17664,-156672,666112,-834048,-5717504,36040704,-103837696,180280576,-192968448,116495360,-29198848]),(⟨1,1,1⟩,[0,4608,-87552,626688,-2199552,3689472,-218112,-12201984,25890816,-24460800,8956416]),(⟨1,1,2⟩,[768,-14080,93184,-268288,185856,818688,-2026496,1218560,1091328,-1492736]),(⟨1,1,3⟩,[0,-3072,48128,-246784,472064,52224,-1702912,2720768,-1340416]),(⟨1,1,6⟩,[0,-2048,24576,-61440,-73728,243712]),(⟨1,2,0⟩,[256,-2816,-10240,260864,-1388288,2962176,606976,-17783552,41691648,-44496896,19437824]),(⟨1,2,1⟩,[768,-14080,93184,-268288,185856,818688,-2026496,1218560,1091328,-1492736]),(⟨1,2,2⟩,[256,-5632,49152,-214528,427520,3584,-1548288,2584064,-1492736]),(⟨1,2,3⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨1,2,6⟩,[-512,6144,-15360,-18432,60928]),(⟨1,3,0⟩,[1536,-29184,179968,-280320,-1730304,10497792,-26529536,37320448,-28634880,8811264]),(⟨1,3,1⟩,[0,-3072,48128,-246784,472064,52224,-1702912,2720768,-1340416]),(⟨1,3,2⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨1,4,0⟩,[128,-5888,72704,-354048,685824,54016,-2477056,4012800,-2086784]),(⟨1,5,0⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨1,6,0⟩,[512,-8192,32768,43008,-595456,1492992,-1326080]),(⟨1,6,1⟩,[0,-2048,24576,-61440,-73728,243712]),(⟨1,6,2⟩,[-512,6144,-15360,-18432,60928]),(⟨1,7,0⟩,[0,-2048,24576,-61440,-73728,243712]),(⟨1,8,0⟩,[-512,6144,-15360,-18432,60928]),(⟨2,0,0⟩,[-512,10752,-85248,310272,-110336,-4780288,27118336,-80746240,146480384,-161116416,97035776,-22641920]),(⟨2,0,1⟩,[256,-2816,-10240,260864,-1388288,2962176,606976,-17783552,41691648,-44496896,19437824]),(⟨2,0,2⟩,[1024,-19712,138240,-396800,-136192,4357120,-13122560,18511360,-12644352,2722048]),(⟨2,0,3⟩,[-512,4864,19712,-326400,1069824,-674560,-2940160,6484736,-4227328]),(⟨2,0,4⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨2,0,6⟩,[-512,5120,5120,-139264,278016,-50176]),(⟨2,0,7⟩,[-512,6144,-15360,-18432,60928]),(⟨2,1,0⟩,[256,-2816,-10240,260864,-1388288,2962176,606976,-17783552,41691648,-44496896,19437824]),(⟨2,1,1⟩,[768,-14080,93184,-268288,185856,818688,-2026496,1218560,1091328,-1492736]),(⟨2,1,2⟩,[256,-5632,49152,-214528,427520,3584,-1548288,2584064,-1492736]),(⟨2,1,3⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨2,1,6⟩,[-512,6144,-15360,-18432,60928]),(⟨2,2,0⟩,[1024,-19712,138240,-396800,-136192,4357120,-13122560,18511360,-12644352,2722048]),(⟨2,2,1⟩,[256,-5632,49152,-214528,427520,3584,-1548288,2584064,-1492736]),(⟨2,3,0⟩,[-512,4864,19712,-326400,1069824,-674560,-2940160,6484736,-4227328]),(⟨2,3,1⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨2,4,0⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨2,6,0⟩,[-512,5120,5120,-139264,278016,-50176]),(⟨2,6,1⟩,[-512,6144,-15360,-18432,60928]),(⟨2,7,0⟩,[-512,6144,-15360,-18432,60928]),(⟨3,0,0⟩,[1024,-17920,93952,89600,-3028480,14465536,-34104832,41038336,-14500352,-19174400,17201920]),(⟨3,0,1⟩,[1536,-29184,179968,-280320,-1730304,10497792,-26529536,37320448,-28634880,8811264]),(⟨3,0,2⟩,[-512,4864,19712,-326400,1069824,-674560,-2940160,6484736,-4227328]),(⟨3,0,3⟩,[-1536,24064,-74240,-337408,2516480,-6225408,7471616,-3373568]),(⟨3,0,6⟩,[-512,6144,1024,-149504,306688]),(⟨3,1,0⟩,[1536,-29184,179968,-280320,-1730304,10497792,-26529536,37320448,-28634880,8811264]),(⟨3,1,1⟩,[0,-3072,48128,-246784,472064,52224,-1702912,2720768,-1340416]),(⟨3,1,2⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨3,2,0⟩,[-512,4864,19712,-326400,1069824,-674560,-2940160,6484736,-4227328]),(⟨3,2,1⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨3,3,0⟩,[-1536,24064,-74240,-337408,2516480,-6225408,7471616,-3373568]),(⟨3,6,0⟩,[-512,6144,1024,-149504,306688]),(⟨4,0,0⟩,[1280,-24960,155904,-210432,-1984256,11857664,-31064320,45357568,-36048384,11665024]),(⟨4,0,1⟩,[128,-5888,72704,-354048,685824,54016,-2477056,4012800,-2086784]),(⟨4,0,2⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨4,1,0⟩,[128,-5888,72704,-354048,685824,54016,-2477056,4012800,-2086784]),(⟨4,2,0⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨5,0,0⟩,[-640,7680,-4864,-219136,856064,-676352,-2166016,5192704,-3480960]),(⟨5,0,1⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨5,1,0⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨6,0,0⟩,[-256,4864,-16640,-45824,331008,-815872,1467648,-1219840]),(⟨6,0,1⟩,[512,-8192,32768,43008,-595456,1492992,-1326080]),(⟨6,0,2⟩,[-512,5120,5120,-139264,278016,-50176]),(⟨6,0,3⟩,[-512,6144,1024,-149504,306688]),(⟨6,1,0⟩,[512,-8192,32768,43008,-595456,1492992,-1326080]),(⟨6,1,1⟩,[0,-2048,24576,-61440,-73728,243712]),(⟨6,1,2⟩,[-512,6144,-15360,-18432,60928]),(⟨6,2,0⟩,[-512,5120,5120,-139264,278016,-50176]),(⟨6,2,1⟩,[-512,6144,-15360,-18432,60928]),(⟨6,3,0⟩,[-512,6144,1024,-149504,306688]),(⟨7,0,0⟩,[512,-8192,32768,43008,-595456,1492992,-1326080]),(⟨7,0,1⟩,[0,-2048,24576,-61440,-73728,243712]),(⟨7,0,2⟩,[-512,6144,-15360,-18432,60928]),(⟨7,1,0⟩,[0,-2048,24576,-61440,-73728,243712]),(⟨7,2,0⟩,[-512,6144,-15360,-18432,60928]),(⟨8,0,0⟩,[-512,5120,5120,-139264,278016,-50176]),(⟨8,0,1⟩,[-512,6144,-15360,-18432,60928]),(⟨8,1,0⟩,[-512,6144,-15360,-18432,60928]),(⟨9,0,0⟩,[-512,6144,1024,-149504,306688])]


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
    (Poly.add (Poly.scale (K.ofRat r383) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 2 3).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r381*r382 : ℚ)=r383 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 2 3 r381 r382 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 2=3 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 2 3).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C073

#print axioms Coulomb8.Columns.C073.sound
