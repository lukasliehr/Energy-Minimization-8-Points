import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C058

def r0 : ℚ := { num := -384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 9216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -96384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 580224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -2195712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 5243904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -7346688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 5095680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -3705984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 13639680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -3234432, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 9312384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 5217024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -1539072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -3200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 37760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -273024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 1297920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := -4081920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := 8237056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := -1425920, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := 7536512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := -1505920, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := 25721984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := -31479680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := 11670016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 3432192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -3456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 38912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -254336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 1087872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -3143936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 6000384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -7083264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 5687936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -1329792, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 20804864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := -3013248, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := 803968, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 7552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -64128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 43904, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -871168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 1286912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -369408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -940288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -1253248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 3472256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 2746752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -6157184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 10496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -106240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 552192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -1606400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 356608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -1658368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 954112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -4775808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 7930880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -2879232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -2304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := -3328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := 103680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := -64256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := 795904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 70400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -1944576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 410624, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -6656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 51456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -170496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 229120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -5632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 19200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -644608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 19456, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -2048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 20992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -74240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 5120, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := 37888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 31232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -363008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := -1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := 29440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 1136384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -3234816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 330240, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := -813056, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 5009920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -12205568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 24937216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -22532096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := 913664, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := 128, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := -12928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 2944, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := 118528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -688896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 83712, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -1175296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 131712, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -675456, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 9870208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := -971392, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := 2560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -38912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 241664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -779264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 1350656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -173056, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := 1019904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := -2407424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := 3119616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := -773120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := 1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := -1280, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := 121088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := -323328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := 352000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := 38144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := 37120, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := -280320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := 294144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 4096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := -49152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := 122880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := 147456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := -256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := 5632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := -48640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := 221184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := -567808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := 754688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := -326656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 49152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -1150208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 231936, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := 32256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := -3840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := 18432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := -1024, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -122368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 55808, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := -262144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -23552, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := -617216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := 186112, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := -4608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := 28416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := -10752, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 67840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 2560, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := 25856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -250368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := -4608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -4096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 46080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := -190464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := 46080, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := -98304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -13312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := -112640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := 726016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := -6144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 6144, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := -608256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 1394688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -4724736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := 7686144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 32768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -10240, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := 49152, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 108544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := -212992, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -53248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := 24576, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := 24576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -634880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := -124416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := 181248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 302592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := -141312, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := 437760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := 512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := -512, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := 50688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := -116224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := 15872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 393728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := -640512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -8192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := -12288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -27136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 53248, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -1024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := 13312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := -6144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := 158720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 12288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := -30720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := -36864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := 4608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := -48192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := 290112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -1097856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := 2621952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := -3673344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := 2547840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := -1852992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := 6819840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -1617216, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 4656192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := 2608512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := -769536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := 64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := -1600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 18880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := -136512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := 648960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := -2040960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := 4118528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := -712960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := 3768256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := -752960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := 12860992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := -15739840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := 5835008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := 1716096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := -1728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := 19456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -127168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 543936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -1571968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := 3000192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := -3541632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := 2843968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -664896, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := 10402432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -1506624, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := 401984, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := 3776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := -32064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := 21952, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := -435584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := 643456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := -184704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -470144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := -626624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := 1736128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 1373376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -3078592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := 5248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -53120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := 276096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -803200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 178304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -829184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := 477056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := -2387904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := 3965440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -1439616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -1152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := -1664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := 51840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := -32128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := 397952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := 35200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -972288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 205312, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := 25728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := -85248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := 114560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := -2816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := 9600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := -322304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := 9728, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := -37120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := 18944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := 15616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := -181504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := -768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := 14720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := 568192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -1617408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := 165120, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -406528, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 2504960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -6102784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 12468608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -11266048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := 456832, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := -64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := 64, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := -6464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := 1472, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := 59264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := -344448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := 41856, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := -587648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := 65856, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -337728, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 4935104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -485696, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 1280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -19456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 120832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -389632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 675328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := -86528, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 509952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -1203712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := 1559808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := -386560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := 768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := -640, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := 60544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := -161664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := 176000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := 19072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := 18560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := -140160, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := 147072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 2048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := -24576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := 61440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := 73728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 2816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -24320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 110592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -283904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 377344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -163328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := -575104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := 115968, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := 16128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := -1920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := -61184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := 27904, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := -131072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := -11776, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := -308608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := 93056, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := 14208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := -5376, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := 33920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := 1280, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := 12928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := -125184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := -2304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := 23040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := -95232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := 23040, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -56320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := 363008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := -3072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := 3072, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := -304128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := 697344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := -2362368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := 3843072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := 16384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := -5120, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := 54272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := -106496, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := -26624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := 12288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := -317440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := -62208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := 90624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := 151296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := -70656, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := 218880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := -256, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := 25344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := -58112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := 7936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := 196864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := -320256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := -13568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := 26624, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := -512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := 6656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := -3072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := 79360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := 6144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := -15360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := -18432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := 1, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := 1, den := 476, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13],[r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27],[r14,r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39],[r0,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50],[r0,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60],[r61,r62,r63,r64,r65,r66,-3328,r67,r68,r69],[r61,r70,r71,r72,r73,r74,r75,r76,r77],[0,r78,r79,r80,r81,r82,r83,r84],[],[],[],[],[],[0,r85,r86,-2048,r87,r88,r89,r90,r91,r92,r93,r94,r95],[r96,r97,r98,r99,r100,r101,r102,r103,r104,r105,r106,r107],[0,r108,r109,r110,r111,r112,r113,r114,r115,r116,r117],[0,r118,r119,r120,r121,r122,r123,r124,r125,r126],[0,0,0,0,r127,r128,r129,r130,-4096],[],[],[],[],[],[],[r131,r132,r133,r134,r135,r136,r137,r138,r139,r140,r141],[r61,r142,r143,r144,r145,r146,r147,r148,r149,r150],[r61,r151,r152,r153,r154,r155,r156,r157,r158],[],[],[],[],[],[],[0,r159,r160,r161,r162,r163,r164,r165,r166],[0,r78,r79,r80,r81,r82,r83,r84],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,0,0,0,r167,r168,r169,r170,r161,r171,r172,-30720],[0,0,0,0,r78,r173,r174,r175,r176,r177,14336],[0,0,0,0,r127,r178,r179,r180,r181,4096],[0,0,0,0,r127,r128,r129,r130,-4096],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,r85,r180,r182,r183,r184,r185,r186,3072],[r187,r188,r189,r190,r191,r192,r193,2560],[r187,r194,r155,r195,r196,r197,-3584],[r198,r199,r200,r167,r201,-1024],[r198,r202,r203,r204,1024],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,r205,r206,r207,r208,r209,r210,r211,r212,r213,r214,r215,r216,r217,r218]),(⟨0,0,1⟩,[r219,r220,r221,r222,r223,r224,r225,r226,r227,r228,r229,r230,r231,r232]),(⟨0,0,2⟩,[r219,r233,r234,r235,r236,r237,r238,r239,r240,r241,r242,r243,r244]),(⟨0,0,3⟩,[r205,r245,r246,r247,r248,r249,r250,r251,r252,r253,r254,r255]),(⟨0,0,4⟩,[r205,r256,r257,r258,r259,r260,r261,r262,r263,r264,r265]),(⟨0,0,5⟩,[r14,r266,r267,r268,r269,r270,-1664,r271,r272,r273]),(⟨0,0,6⟩,[r14,r63,r274,r275,r276,r277,r278,r279,r280]),(⟨0,0,7⟩,[0,r198,r51,r281,r155,r282,r283,r284]),(⟨0,1,0⟩,[r219,r220,r221,r222,r223,r224,r225,r226,r227,r228,r229,r230,r231,r232]),(⟨0,1,1⟩,[0,r285,r286,-1024,r287,r288,r289,r290,r291,r292,r293,r294,r295]),(⟨0,1,2⟩,[r296,r297,r298,r299,r300,r301,r302,r303,r304,r305,r306,r307]),(⟨0,1,3⟩,[0,r308,r309,r310,r311,r312,r313,r314,r315,r316,r317]),(⟨0,1,4⟩,[0,r318,r319,r320,r321,r322,r323,r324,r325,r326]),(⟨0,1,5⟩,[0,0,0,0,r327,r328,r329,r330,-2048]),(⟨0,2,0⟩,[r219,r233,r234,r235,r236,r237,r238,r239,r240,r241,r242,r243,r244]),(⟨0,2,1⟩,[r296,r297,r298,r299,r300,r301,r302,r303,r304,r305,r306,r307]),(⟨0,2,2⟩,[r96,r331,r332,r333,r334,r335,r336,r180,r337,r338,r339]),(⟨0,2,3⟩,[r14,r340,r1,r188,r341,r342,r343,r344,r345,r346]),(⟨0,2,4⟩,[r14,r62,r347,r348,r349,r350,r351,r352,r353]),(⟨0,3,0⟩,[r205,r245,r246,r247,r248,r249,r250,r251,r252,r253,r254,r255]),(⟨0,3,1⟩,[0,r308,r309,r310,r311,r312,r313,r314,r315,r316,r317]),(⟨0,3,2⟩,[r14,r340,r1,r188,r341,r342,r343,r344,r345,r346]),(⟨0,3,3⟩,[0,r78,r354,r355,r356,r128,r70,r357,r358]),(⟨0,3,4⟩,[0,r198,r51,r281,r155,r282,r283,r284]),(⟨0,4,0⟩,[r205,r256,r257,r258,r259,r260,r261,r262,r263,r264,r265]),(⟨0,4,1⟩,[0,r318,r319,r320,r321,r322,r323,r324,r325,r326]),(⟨0,4,2⟩,[r14,r62,r347,r348,r349,r350,r351,r352,r353]),(⟨0,4,3⟩,[0,r198,r51,r281,r155,r282,r283,r284]),(⟨0,5,0⟩,[r14,r266,r267,r268,r269,r270,-1664,r271,r272,r273]),(⟨0,5,1⟩,[0,0,0,0,r327,r328,r329,r330,-2048]),(⟨0,6,0⟩,[r14,r63,r274,r275,r276,r277,r278,r279,r280]),(⟨0,7,0⟩,[0,r198,r51,r281,r155,r282,r283,r284]),(⟨1,0,0⟩,[r219,r220,r221,r222,r223,r224,r225,r226,r227,r228,r229,r230,r231,r232]),(⟨1,0,1⟩,[0,r285,r286,-1024,r287,r288,r289,r290,r291,r292,r293,r294,r295]),(⟨1,0,2⟩,[r296,r297,r298,r299,r300,r301,r302,r303,r304,r305,r306,r307]),(⟨1,0,3⟩,[0,r308,r309,r310,r311,r312,r313,r314,r315,r316,r317]),(⟨1,0,4⟩,[0,r318,r319,r320,r321,r322,r323,r324,r325,r326]),(⟨1,0,5⟩,[0,0,0,0,r327,r328,r329,r330,-2048]),(⟨1,1,0⟩,[0,r285,r286,-1024,r287,r288,r289,r290,r291,r292,r293,r294,r295]),(⟨1,1,1⟩,[0,0,0,0,r359,r360,r361,r362,r355,r363,r364,-15360]),(⟨1,1,2⟩,[0,0,0,0,r198,r365,r366,r179,r367,r368,7168]),(⟨1,1,3⟩,[0,0,0,0,r327,r369,r370,r202,r371,2048]),(⟨1,1,4⟩,[0,0,0,0,r327,r328,r329,r330,-2048]),(⟨1,2,0⟩,[r296,r297,r298,r299,r300,r301,r302,r303,r304,r305,r306,r307]),(⟨1,2,1⟩,[0,0,0,0,r198,r365,r366,r179,r367,r368,7168]),(⟨1,3,0⟩,[0,r308,r309,r310,r311,r312,r313,r314,r315,r316,r317]),(⟨1,3,1⟩,[0,0,0,0,r327,r369,r370,r202,r371,2048]),(⟨1,4,0⟩,[0,r318,r319,r320,r321,r322,r323,r324,r325,r326]),(⟨1,4,1⟩,[0,0,0,0,r327,r328,r329,r330,-2048]),(⟨1,5,0⟩,[0,0,0,0,r327,r328,r329,r330,-2048]),(⟨2,0,0⟩,[r219,r233,r234,r235,r236,r237,r238,r239,r240,r241,r242,r243,r244]),(⟨2,0,1⟩,[r296,r297,r298,r299,r300,r301,r302,r303,r304,r305,r306,r307]),(⟨2,0,2⟩,[r96,r331,r332,r333,r334,r335,r336,r180,r337,r338,r339]),(⟨2,0,3⟩,[r14,r340,r1,r188,r341,r342,r343,r344,r345,r346]),(⟨2,0,4⟩,[r14,r62,r347,r348,r349,r350,r351,r352,r353]),(⟨2,1,0⟩,[r296,r297,r298,r299,r300,r301,r302,r303,r304,r305,r306,r307]),(⟨2,1,1⟩,[0,0,0,0,r198,r365,r366,r179,r367,r368,7168]),(⟨2,2,0⟩,[r96,r331,r332,r333,r334,r335,r336,r180,r337,r338,r339]),(⟨2,2,2⟩,[0,r285,r202,r372,r373,r374,r375,r376,1536]),(⟨2,2,3⟩,[r61,r377,r378,r379,r380,r381,r382,1280]),(⟨2,2,4⟩,[r61,r159,r350,r200,r383,r384,-1792]),(⟨2,2,5⟩,[r385,r386,r387,r359,r388,-512]),(⟨2,2,6⟩,[r385,r389,r390,r391,512]),(⟨2,3,0⟩,[r14,r340,r1,r188,r341,r342,r343,r344,r345,r346]),(⟨2,3,2⟩,[r61,r377,r378,r379,r380,r381,r382,1280]),(⟨2,4,0⟩,[r14,r62,r347,r348,r349,r350,r351,r352,r353]),(⟨2,4,2⟩,[r61,r159,r350,r200,r383,r384,-1792]),(⟨2,5,2⟩,[r385,r386,r387,r359,r388,-512]),(⟨2,6,2⟩,[r385,r389,r390,r391,512]),(⟨3,0,0⟩,[r205,r245,r246,r247,r248,r249,r250,r251,r252,r253,r254,r255]),(⟨3,0,1⟩,[0,r308,r309,r310,r311,r312,r313,r314,r315,r316,r317]),(⟨3,0,2⟩,[r14,r340,r1,r188,r341,r342,r343,r344,r345,r346]),(⟨3,0,3⟩,[0,r78,r354,r355,r356,r128,r70,r357,r358]),(⟨3,0,4⟩,[0,r198,r51,r281,r155,r282,r283,r284]),(⟨3,1,0⟩,[0,r308,r309,r310,r311,r312,r313,r314,r315,r316,r317]),(⟨3,1,1⟩,[0,0,0,0,r327,r369,r370,r202,r371,2048]),(⟨3,2,0⟩,[r14,r340,r1,r188,r341,r342,r343,r344,r345,r346]),(⟨3,2,2⟩,[r61,r377,r378,r379,r380,r381,r382,1280]),(⟨3,3,0⟩,[0,r78,r354,r355,r356,r128,r70,r357,r358]),(⟨3,4,0⟩,[0,r198,r51,r281,r155,r282,r283,r284]),(⟨4,0,0⟩,[r205,r256,r257,r258,r259,r260,r261,r262,r263,r264,r265]),(⟨4,0,1⟩,[0,r318,r319,r320,r321,r322,r323,r324,r325,r326]),(⟨4,0,2⟩,[r14,r62,r347,r348,r349,r350,r351,r352,r353]),(⟨4,0,3⟩,[0,r198,r51,r281,r155,r282,r283,r284]),(⟨4,1,0⟩,[0,r318,r319,r320,r321,r322,r323,r324,r325,r326]),(⟨4,1,1⟩,[0,0,0,0,r327,r328,r329,r330,-2048]),(⟨4,2,0⟩,[r14,r62,r347,r348,r349,r350,r351,r352,r353]),(⟨4,2,2⟩,[r61,r159,r350,r200,r383,r384,-1792]),(⟨4,3,0⟩,[0,r198,r51,r281,r155,r282,r283,r284]),(⟨5,0,0⟩,[r14,r266,r267,r268,r269,r270,-1664,r271,r272,r273]),(⟨5,0,1⟩,[0,0,0,0,r327,r328,r329,r330,-2048]),(⟨5,1,0⟩,[0,0,0,0,r327,r328,r329,r330,-2048]),(⟨5,2,2⟩,[r385,r386,r387,r359,r388,-512]),(⟨6,0,0⟩,[r14,r63,r274,r275,r276,r277,r278,r279,r280]),(⟨6,2,2⟩,[r385,r389,r390,r391,512]),(⟨7,0,0⟩,[0,r198,r51,r281,r155,r282,r283,r284])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,3,-12,9,6]),(⟨0,0,1⟩,[-1,5,-9,5]),(⟨0,0,2⟩,[-1,4,-7]),(⟨0,0,3⟩,[2,-2]),(⟨0,0,4⟩,[2]),(⟨0,1,0⟩,[-1,5,-9,5]),(⟨0,2,0⟩,[-1,4,-7]),(⟨0,3,0⟩,[2,-2]),(⟨0,4,0⟩,[2]),(⟨1,0,0⟩,[-1,5,-9,5]),(⟨2,0,0⟩,[-1,4,-7]),(⟨3,0,0⟩,[2,-2]),(⟨4,0,0⟩,[2])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[-256,5120,-43008,199936,-545280,801024,-457728,253696,-1684736,2508544,-513024]),(⟨0,0,1⟩,[0,1536,-21760,121088,-327424,405248,-133888,235264,-1327360,1571584]),(⟨0,0,2⟩,[256,-4608,28416,-75264,67840,43520,25856,-250368,-32256]),(⟨0,0,3⟩,[0,-2048,20992,-74240,87040,37888,31232,-363008]),(⟨0,1,0⟩,[0,1536,-21760,121088,-327424,405248,-133888,235264,-1327360,1571584]),(⟨0,1,1⟩,[0,0,0,0,4096,-49152,122880,147456,-487424]),(⟨0,2,0⟩,[256,-4608,28416,-75264,67840,43520,25856,-250368,-32256]),(⟨0,3,0⟩,[0,-2048,20992,-74240,87040,37888,31232,-363008]),(⟨1,0,0⟩,[0,1536,-21760,121088,-327424,405248,-133888,235264,-1327360,1571584]),(⟨1,0,1⟩,[0,0,0,0,4096,-49152,122880,147456,-487424]),(⟨1,1,0⟩,[0,0,0,0,4096,-49152,122880,147456,-487424]),(⟨2,0,0⟩,[256,-4608,28416,-75264,67840,43520,25856,-250368,-32256]),(⟨2,2,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨3,0,0⟩,[0,-2048,20992,-74240,87040,37888,31232,-363008])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 0 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r392) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 13 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r393) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨4,0,0⟩,[2])]

noncomputable def partial12 : Poly := [(⟨4,0,0⟩,[-512,10240,-86016,399872,-1090560,1602048,-915456,507392,-3369472,5017088,-1026048]),(⟨4,0,1⟩,[0,3072,-43520,242176,-654848,810496,-267776,470528,-2654720,3143168]),(⟨4,0,2⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨4,0,3⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨4,1,0⟩,[0,3072,-43520,242176,-654848,810496,-267776,470528,-2654720,3143168]),(⟨4,1,1⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨4,2,0⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨4,3,0⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨5,0,0⟩,[0,3072,-43520,242176,-654848,810496,-267776,470528,-2654720,3143168]),(⟨5,0,1⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨5,1,0⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨6,0,0⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨6,2,2⟩,[-2048,24576,-61440,-73728,243712]),(⟨7,0,0⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016])]


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

noncomputable def partial8 : Poly := [(⟨0,4,0⟩,[-512,10240,-86016,399872,-1090560,1602048,-915456,507392,-3369472,5017088,-1026048]),(⟨0,4,1⟩,[0,3072,-43520,242176,-654848,810496,-267776,470528,-2654720,3143168]),(⟨0,4,2⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨0,4,3⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨0,5,0⟩,[0,3072,-43520,242176,-654848,810496,-267776,470528,-2654720,3143168]),(⟨0,5,1⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨0,6,0⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨0,7,0⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨1,0,0⟩,[256,-6400,70912,-462336,1957632,-5541888,10370048,-12477952,11077888,-15504128,29486848,-33565696,17159936,-2565120]),(⟨1,0,1⟩,[0,-1536,29440,-243712,1136384,-3240960,5712384,-6189056,5734912,-10995200,20980480,-20781056,7857920]),(⟨1,0,2⟩,[-256,5888,-53760,260096,-722944,1115136,-795136,327168,-1234688,2221312,-961536,-161280]),(⟨1,0,3⟩,[0,2048,-31232,197632,-657408,1170432,-996352,613376,-1906688,3423232,-1815040]),(⟨1,1,0⟩,[0,-1536,29440,-243712,1136384,-3240960,5712384,-6189056,5734912,-10995200,20980480,-20781056,7857920]),(⟨1,1,1⟩,[0,0,0,0,-4096,69632,-405504,929792,-126976,-3149824,5124096,-2437120]),(⟨1,2,0⟩,[-256,5888,-53760,260096,-722944,1115136,-795136,327168,-1234688,2221312,-961536,-161280]),(⟨1,3,0⟩,[0,2048,-31232,197632,-657408,1170432,-996352,613376,-1906688,3423232,-1815040]),(⟨1,4,0⟩,[0,3072,-43520,242176,-654848,810496,-267776,470528,-2654720,3143168]),(⟨1,4,1⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨1,5,0⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨2,0,0⟩,[256,-7680,94720,-651520,2782464,-7622656,13191168,-13880832,11638528,-22018560,43320832,-40392960,11449088]),(⟨2,0,1⟩,[0,-1536,27904,-218880,960000,-2492928,3641344,-2677760,3078656,-11677696,20701952,-13438208]),(⟨2,0,2⟩,[-256,5632,-48640,221184,-567808,754688,-326656,49152,-1150208,1623552,225792]),(⟨2,0,3⟩,[0,2048,-29184,172544,-530944,829952,-488960,222720,-1670656,2541056]),(⟨2,1,0⟩,[0,-1536,27904,-218880,960000,-2492928,3641344,-2677760,3078656,-11677696,20701952,-13438208]),(⟨2,1,1⟩,[0,0,0,0,-4096,65536,-348160,688128,217088,-2981888,3411968]),(⟨2,2,0⟩,[-256,5632,-48640,221184,-567808,754688,-326656,49152,-1150208,1623552,225792]),(⟨2,3,0⟩,[0,2048,-29184,172544,-530944,829952,-488960,222720,-1670656,2541056]),(⟨2,4,0⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨2,6,2⟩,[-2048,24576,-61440,-73728,243712]),(⟨3,0,0⟩,[-768,15104,-122112,527104,-1249280,1245184,734208,-1857536,-1905920,2080000,8573184,-10136320]),(⟨3,0,1⟩,[0,3072,-46592,285696,-901120,1530880,-1426432,1426432,-2908160,2816000,268800]),(⟨3,0,2⟩,[512,-9728,66048,-207360,286208,-48640,-35328,-552448,436224,64512]),(⟨3,0,3⟩,[0,-4096,46080,-190464,322560,-98304,-13312,-788480,726016]),(⟨3,1,0⟩,[0,3072,-46592,285696,-901120,1530880,-1426432,1426432,-2908160,2816000,268800]),(⟨3,1,1⟩,[0,0,0,0,8192,-106496,344064,49152,-1269760,974848]),(⟨3,2,0⟩,[512,-9728,66048,-207360,286208,-48640,-35328,-552448,436224,64512]),(⟨3,2,2⟩,[1024,-17408,101376,-232448,31744,787456,-1281024,609280]),(⟨3,3,0⟩,[0,-4096,46080,-190464,322560,-98304,-13312,-788480,726016]),(⟨3,4,0⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨4,0,0⟩,[-768,20992,-212480,1104384,-3212800,4992512,-3316736,1908224,-9551616,15861760,-5758464]),(⟨4,0,1⟩,[0,3072,-43520,242176,-646656,704000,76288,519680,-3924480,4118016]),(⟨4,0,2⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨4,0,3⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨4,1,0⟩,[0,3072,-43520,242176,-646656,704000,76288,519680,-3924480,4118016]),(⟨4,1,1⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨4,2,0⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨4,2,2⟩,[1024,-16384,87040,-172032,-54272,745472,-852992]),(⟨4,3,0⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨5,0,0⟩,[512,-4608,-6656,207360,-899584,1591808,-792064,140800,-3889152,5748736]),(⟨5,0,1⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨5,1,0⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨5,2,2⟩,[-2048,26624,-86016,-12288,317440,-243712]),(⟨6,0,0⟩,[512,-13312,102912,-340992,458240,-11264,38400,-1289216,661504]),(⟨6,2,2⟩,[-2048,24576,-61440,-73728,243712]),(⟨7,0,0⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016])]


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

noncomputable def partial4 : Poly := [(⟨0,0,4⟩,[-512,10240,-86016,399872,-1090560,1602048,-915456,507392,-3369472,5017088,-1026048]),(⟨0,0,5⟩,[0,3072,-43520,242176,-654848,810496,-267776,470528,-2654720,3143168]),(⟨0,0,6⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨0,0,7⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨0,1,0⟩,[256,-6400,70912,-462336,1957632,-5541888,10370048,-12477952,11077888,-15504128,29486848,-33565696,17159936,-2565120]),(⟨0,1,1⟩,[0,-1536,29440,-243712,1136384,-3240960,5712384,-6189056,5734912,-10995200,20980480,-20781056,7857920]),(⟨0,1,2⟩,[-256,5888,-53760,260096,-722944,1115136,-795136,327168,-1234688,2221312,-961536,-161280]),(⟨0,1,3⟩,[0,2048,-31232,197632,-657408,1170432,-996352,613376,-1906688,3423232,-1815040]),(⟨0,1,4⟩,[0,3072,-43520,242176,-654848,810496,-267776,470528,-2654720,3143168]),(⟨0,1,5⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨0,2,0⟩,[256,-7680,94720,-651520,2782464,-7622656,13191168,-13880832,11638528,-22018560,43320832,-40392960,11449088]),(⟨0,2,1⟩,[0,-1536,27904,-218880,960000,-2492928,3641344,-2677760,3078656,-11677696,20701952,-13438208]),(⟨0,2,2⟩,[-256,5632,-48640,221184,-567808,754688,-326656,49152,-1150208,1623552,225792]),(⟨0,2,3⟩,[0,2048,-29184,172544,-530944,829952,-488960,222720,-1670656,2541056]),(⟨0,2,4⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨0,3,0⟩,[-768,15104,-122112,527104,-1249280,1245184,734208,-1857536,-1905920,2080000,8573184,-10136320]),(⟨0,3,1⟩,[0,3072,-46592,285696,-901120,1530880,-1426432,1426432,-2908160,2816000,268800]),(⟨0,3,2⟩,[512,-9728,66048,-207360,286208,-48640,-35328,-552448,436224,64512]),(⟨0,3,3⟩,[0,-4096,46080,-190464,322560,-98304,-13312,-788480,726016]),(⟨0,3,4⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨0,4,0⟩,[-768,20992,-212480,1104384,-3212800,4992512,-3316736,1908224,-9551616,15861760,-5758464]),(⟨0,4,1⟩,[0,3072,-43520,242176,-646656,704000,76288,519680,-3924480,4118016]),(⟨0,4,2⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨0,4,3⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨0,5,0⟩,[512,-4608,-6656,207360,-899584,1591808,-792064,140800,-3889152,5748736]),(⟨0,5,1⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨0,6,0⟩,[512,-13312,102912,-340992,458240,-11264,38400,-1289216,661504]),(⟨0,7,0⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨1,0,0⟩,[256,-6400,70912,-462336,1957632,-5541888,10370048,-12477952,11077888,-15504128,29486848,-33565696,17159936,-2565120]),(⟨1,0,1⟩,[0,-1536,29440,-243712,1136384,-3240960,5712384,-6189056,5734912,-10995200,20980480,-20781056,7857920]),(⟨1,0,2⟩,[-256,5888,-53760,260096,-722944,1115136,-795136,327168,-1234688,2221312,-961536,-161280]),(⟨1,0,3⟩,[0,2048,-31232,197632,-657408,1170432,-996352,613376,-1906688,3423232,-1815040]),(⟨1,0,4⟩,[0,3072,-43520,242176,-654848,810496,-267776,470528,-2654720,3143168]),(⟨1,0,5⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨1,1,0⟩,[0,-3072,58880,-487424,2272768,-6481920,11424768,-12378112,11469824,-21990400,41960960,-41562112,15715840]),(⟨1,1,1⟩,[0,0,0,0,-8192,139264,-811008,1859584,-253952,-6299648,10248192,-4874240]),(⟨1,1,4⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨1,2,0⟩,[-256,4352,-25856,41216,237056,-1377792,2846208,-2350592,1843968,-9456384,19740416,-13599488]),(⟨1,2,1⟩,[0,0,0,0,-4096,65536,-348160,688128,217088,-2981888,3411968]),(⟨1,3,0⟩,[0,5120,-77824,483328,-1558528,2701312,-2422784,2039808,-4814848,6239232,-1546240]),(⟨1,3,1⟩,[0,0,0,0,8192,-106496,344064,49152,-1269760,974848]),(⟨1,4,0⟩,[0,3072,-43520,242176,-646656,704000,76288,519680,-3924480,4118016]),(⟨1,4,1⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨1,5,0⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨2,0,0⟩,[256,-7680,94720,-651520,2782464,-7622656,13191168,-13880832,11638528,-22018560,43320832,-40392960,11449088]),(⟨2,0,1⟩,[0,-1536,27904,-218880,960000,-2492928,3641344,-2677760,3078656,-11677696,20701952,-13438208]),(⟨2,0,2⟩,[-256,5632,-48640,221184,-567808,754688,-326656,49152,-1150208,1623552,225792]),(⟨2,0,3⟩,[0,2048,-29184,172544,-530944,829952,-488960,222720,-1670656,2541056]),(⟨2,0,4⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨2,1,0⟩,[-256,4352,-25856,41216,237056,-1377792,2846208,-2350592,1843968,-9456384,19740416,-13599488]),(⟨2,1,1⟩,[0,0,0,0,-4096,65536,-348160,688128,217088,-2981888,3411968]),(⟨2,2,0⟩,[-512,11264,-97280,442368,-1135616,1509376,-653312,98304,-2300416,3247104,451584]),(⟨2,2,6⟩,[-2048,24576,-61440,-73728,243712]),(⟨2,3,0⟩,[512,-7680,36864,-34816,-244736,781312,-524288,-329728,-1234432,2605568]),(⟨2,3,2⟩,[1024,-17408,101376,-232448,31744,787456,-1281024,609280]),(⟨2,4,0⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨2,4,2⟩,[1024,-16384,87040,-172032,-54272,745472,-852992]),(⟨2,5,2⟩,[-2048,26624,-86016,-12288,317440,-243712]),(⟨2,6,2⟩,[-2048,24576,-61440,-73728,243712]),(⟨3,0,0⟩,[-768,15104,-122112,527104,-1249280,1245184,734208,-1857536,-1905920,2080000,8573184,-10136320]),(⟨3,0,1⟩,[0,3072,-46592,285696,-901120,1530880,-1426432,1426432,-2908160,2816000,268800]),(⟨3,0,2⟩,[512,-9728,66048,-207360,286208,-48640,-35328,-552448,436224,64512]),(⟨3,0,3⟩,[0,-4096,46080,-190464,322560,-98304,-13312,-788480,726016]),(⟨3,0,4⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨3,1,0⟩,[0,5120,-77824,483328,-1558528,2701312,-2422784,2039808,-4814848,6239232,-1546240]),(⟨3,1,1⟩,[0,0,0,0,8192,-106496,344064,49152,-1269760,974848]),(⟨3,2,0⟩,[512,-7680,36864,-34816,-244736,781312,-524288,-329728,-1234432,2605568]),(⟨3,2,2⟩,[1024,-17408,101376,-232448,31744,787456,-1281024,609280]),(⟨3,3,0⟩,[0,-8192,92160,-380928,645120,-196608,-26624,-1576960,1452032]),(⟨3,4,0⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨4,0,0⟩,[-768,20992,-212480,1104384,-3212800,4992512,-3316736,1908224,-9551616,15861760,-5758464]),(⟨4,0,1⟩,[0,3072,-43520,242176,-646656,704000,76288,519680,-3924480,4118016]),(⟨4,0,2⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨4,0,3⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨4,1,0⟩,[0,3072,-43520,242176,-646656,704000,76288,519680,-3924480,4118016]),(⟨4,1,1⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨4,2,0⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨4,2,2⟩,[1024,-16384,87040,-172032,-54272,745472,-852992]),(⟨4,3,0⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨5,0,0⟩,[512,-4608,-6656,207360,-899584,1591808,-792064,140800,-3889152,5748736]),(⟨5,0,1⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨5,1,0⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨5,2,2⟩,[-2048,26624,-86016,-12288,317440,-243712]),(⟨6,0,0⟩,[512,-13312,102912,-340992,458240,-11264,38400,-1289216,661504]),(⟨6,2,2⟩,[-2048,24576,-61440,-73728,243712]),(⟨7,0,0⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,-768,18432,-192768,1160448,-4391424,10487808,-14693376,10191360,-7411968,27279360,-45282048,18624768,10434048,-3078144]),(⟨0,0,1⟩,[256,-6400,75520,-546048,2595840,-8163840,16474112,-19962880,15073024,-21082880,51443968,-62959360,23340032,6864384]),(⟨0,0,2⟩,[256,-6912,77824,-508672,2175744,-6287872,12000768,-14166528,11375872,-18617088,41609728,-42185472,11255552]),(⟨0,0,3⟩,[-768,15104,-128256,614656,-1742336,2573824,-738816,-1880576,-2506496,6944512,5493504,-12314368]),(⟨0,0,4⟩,[-768,20992,-212480,1104384,-3212800,4992512,-3316736,1908224,-9551616,15861760,-5758464]),(⟨0,0,5⟩,[512,-4608,-6656,207360,-899584,1591808,-792064,140800,-3889152,5748736]),(⟨0,0,6⟩,[512,-13312,102912,-340992,458240,-11264,38400,-1289216,661504]),(⟨0,0,7⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨0,1,0⟩,[256,-6400,75520,-546048,2595840,-8163840,16474112,-19962880,15073024,-21082880,51443968,-62959360,23340032,6864384]),(⟨0,1,1⟩,[0,-3072,58880,-487424,2272768,-6469632,11228160,-11382784,10019840,-24411136,49874432,-45064192,12791296]),(⟨0,1,2⟩,[-256,4352,-25856,41216,237056,-1377792,2846208,-2350592,1843968,-9456384,19740416,-13599488]),(⟨0,1,3⟩,[0,5120,-77824,483328,-1558528,2701312,-2422784,2039808,-4814848,6239232,-1546240]),(⟨0,1,4⟩,[0,3072,-43520,242176,-646656,704000,76288,519680,-3924480,4118016]),(⟨0,1,5⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨0,2,0⟩,[256,-6912,77824,-508672,2175744,-6287872,12000768,-14166528,11375872,-18617088,41609728,-42185472,11255552]),(⟨0,2,1⟩,[-256,4352,-25856,41216,237056,-1377792,2846208,-2350592,1843968,-9456384,19740416,-13599488]),(⟨0,2,2⟩,[-512,11264,-97280,442368,-1135616,1509376,-653312,98304,-2300416,3247104,451584]),(⟨0,2,3⟩,[512,-7680,36864,-34816,-244736,781312,-524288,-329728,-1234432,2605568]),(⟨0,2,4⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨0,3,0⟩,[-768,15104,-128256,614656,-1742336,2573824,-738816,-1880576,-2506496,6944512,5493504,-12314368]),(⟨0,3,1⟩,[0,5120,-77824,483328,-1558528,2701312,-2422784,2039808,-4814848,6239232,-1546240]),(⟨0,3,2⟩,[512,-7680,36864,-34816,-244736,781312,-524288,-329728,-1234432,2605568]),(⟨0,3,3⟩,[0,-8192,92160,-380928,645120,-196608,-26624,-1576960,1452032]),(⟨0,3,4⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨0,4,0⟩,[-768,20992,-212480,1104384,-3212800,4992512,-3316736,1908224,-9551616,15861760,-5758464]),(⟨0,4,1⟩,[0,3072,-43520,242176,-646656,704000,76288,519680,-3924480,4118016]),(⟨0,4,2⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨0,4,3⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨0,5,0⟩,[512,-4608,-6656,207360,-899584,1591808,-792064,140800,-3889152,5748736]),(⟨0,5,1⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨0,6,0⟩,[512,-13312,102912,-340992,458240,-11264,38400,-1289216,661504]),(⟨0,7,0⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨1,0,0⟩,[256,-6400,75520,-546048,2595840,-8163840,16474112,-19962880,15073024,-21082880,51443968,-62959360,23340032,6864384]),(⟨1,0,1⟩,[0,-3072,58880,-487424,2272768,-6469632,11228160,-11382784,10019840,-24411136,49874432,-45064192,12791296]),(⟨1,0,2⟩,[-256,4352,-25856,41216,237056,-1377792,2846208,-2350592,1843968,-9456384,19740416,-13599488]),(⟨1,0,3⟩,[0,5120,-77824,483328,-1558528,2701312,-2422784,2039808,-4814848,6239232,-1546240]),(⟨1,0,4⟩,[0,3072,-43520,242176,-646656,704000,76288,519680,-3924480,4118016]),(⟨1,0,5⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨1,1,0⟩,[0,-3072,58880,-487424,2272768,-6469632,11228160,-11382784,10019840,-24411136,49874432,-45064192,12791296]),(⟨1,1,1⟩,[0,0,0,0,-12288,208896,-1216512,2789376,-380928,-9449472,15372288,-7311360]),(⟨1,1,2⟩,[0,0,0,0,-4096,65536,-348160,688128,217088,-2981888,3411968]),(⟨1,1,3⟩,[0,0,0,0,8192,-106496,344064,49152,-1269760,974848]),(⟨1,1,4⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨1,2,0⟩,[-256,4352,-25856,41216,237056,-1377792,2846208,-2350592,1843968,-9456384,19740416,-13599488]),(⟨1,2,1⟩,[0,0,0,0,-4096,65536,-348160,688128,217088,-2981888,3411968]),(⟨1,3,0⟩,[0,5120,-77824,483328,-1558528,2701312,-2422784,2039808,-4814848,6239232,-1546240]),(⟨1,3,1⟩,[0,0,0,0,8192,-106496,344064,49152,-1269760,974848]),(⟨1,4,0⟩,[0,3072,-43520,242176,-646656,704000,76288,519680,-3924480,4118016]),(⟨1,4,1⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨1,5,0⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨2,0,0⟩,[256,-6912,77824,-508672,2175744,-6287872,12000768,-14166528,11375872,-18617088,41609728,-42185472,11255552]),(⟨2,0,1⟩,[-256,4352,-25856,41216,237056,-1377792,2846208,-2350592,1843968,-9456384,19740416,-13599488]),(⟨2,0,2⟩,[-512,11264,-97280,442368,-1135616,1509376,-653312,98304,-2300416,3247104,451584]),(⟨2,0,3⟩,[512,-7680,36864,-34816,-244736,781312,-524288,-329728,-1234432,2605568]),(⟨2,0,4⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨2,1,0⟩,[-256,4352,-25856,41216,237056,-1377792,2846208,-2350592,1843968,-9456384,19740416,-13599488]),(⟨2,1,1⟩,[0,0,0,0,-4096,65536,-348160,688128,217088,-2981888,3411968]),(⟨2,2,0⟩,[-512,11264,-97280,442368,-1135616,1509376,-653312,98304,-2300416,3247104,451584]),(⟨2,2,2⟩,[0,-3072,49152,-248832,362496,605184,-1978368,875520,731136]),(⟨2,2,3⟩,[1024,-17408,101376,-232448,31744,787456,-1281024,609280]),(⟨2,2,4⟩,[1024,-16384,87040,-172032,-54272,745472,-852992]),(⟨2,2,5⟩,[-2048,26624,-86016,-12288,317440,-243712]),(⟨2,2,6⟩,[-2048,24576,-61440,-73728,243712]),(⟨2,3,0⟩,[512,-7680,36864,-34816,-244736,781312,-524288,-329728,-1234432,2605568]),(⟨2,3,2⟩,[1024,-17408,101376,-232448,31744,787456,-1281024,609280]),(⟨2,4,0⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨2,4,2⟩,[1024,-16384,87040,-172032,-54272,745472,-852992]),(⟨2,5,2⟩,[-2048,26624,-86016,-12288,317440,-243712]),(⟨2,6,2⟩,[-2048,24576,-61440,-73728,243712]),(⟨3,0,0⟩,[-768,15104,-128256,614656,-1742336,2573824,-738816,-1880576,-2506496,6944512,5493504,-12314368]),(⟨3,0,1⟩,[0,5120,-77824,483328,-1558528,2701312,-2422784,2039808,-4814848,6239232,-1546240]),(⟨3,0,2⟩,[512,-7680,36864,-34816,-244736,781312,-524288,-329728,-1234432,2605568]),(⟨3,0,3⟩,[0,-8192,92160,-380928,645120,-196608,-26624,-1576960,1452032]),(⟨3,0,4⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨3,1,0⟩,[0,5120,-77824,483328,-1558528,2701312,-2422784,2039808,-4814848,6239232,-1546240]),(⟨3,1,1⟩,[0,0,0,0,8192,-106496,344064,49152,-1269760,974848]),(⟨3,2,0⟩,[512,-7680,36864,-34816,-244736,781312,-524288,-329728,-1234432,2605568]),(⟨3,2,2⟩,[1024,-17408,101376,-232448,31744,787456,-1281024,609280]),(⟨3,3,0⟩,[0,-8192,92160,-380928,645120,-196608,-26624,-1576960,1452032]),(⟨3,4,0⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨4,0,0⟩,[-768,20992,-212480,1104384,-3212800,4992512,-3316736,1908224,-9551616,15861760,-5758464]),(⟨4,0,1⟩,[0,3072,-43520,242176,-646656,704000,76288,519680,-3924480,4118016]),(⟨4,0,2⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨4,0,3⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨4,1,0⟩,[0,3072,-43520,242176,-646656,704000,76288,519680,-3924480,4118016]),(⟨4,1,1⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨4,2,0⟩,[512,-9216,56832,-150528,135680,87040,51712,-500736,-64512]),(⟨4,2,2⟩,[1024,-16384,87040,-172032,-54272,745472,-852992]),(⟨4,3,0⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016]),(⟨5,0,0⟩,[512,-4608,-6656,207360,-899584,1591808,-792064,140800,-3889152,5748736]),(⟨5,0,1⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨5,1,0⟩,[0,0,0,0,8192,-98304,245760,294912,-974848]),(⟨5,2,2⟩,[-2048,26624,-86016,-12288,317440,-243712]),(⟨6,0,0⟩,[512,-13312,102912,-340992,458240,-11264,38400,-1289216,661504]),(⟨6,2,2⟩,[-2048,24576,-61440,-73728,243712]),(⟨7,0,0⟩,[0,-4096,41984,-148480,174080,75776,62464,-726016])]


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
    (Poly.add (Poly.scale (K.ofRat r394) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 0 13).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r392*r393 : ℚ)=r394 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 0 13 r392 r393 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 0=13 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 0 13).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C058

#print axioms Coulomb8.Columns.C058.sound
