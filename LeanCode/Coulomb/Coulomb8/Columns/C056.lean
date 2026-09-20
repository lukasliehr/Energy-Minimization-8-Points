import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C056

def r0 : ℚ := { num := 192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -3840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 31872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -152832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 75264, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -1549824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 3856512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -6797568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 6669120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -264960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -1463040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 442368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := 192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := -12800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := 74624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := -44160, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 1026048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -2910464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 6625664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -10438208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 9339072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -2866944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := -873216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -11264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 59264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -248960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 864768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -2405888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 5147776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -7530816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 6010048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -227328, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -448, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 20864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -11392, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 228608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -578304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 1065600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -678528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -161856, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 1534272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -4096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 30336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -122624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 388352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -157184, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 320640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -2430720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 830528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 1024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -22272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 91776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -309760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := 105344, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -101632, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 2560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -12928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 32768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := -105856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := 31232, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := -6016, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := 768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := -5120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := 14848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := -7168, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := 88832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -7680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 50816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -211712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 725120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -133632, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 784512, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -1181952, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 6439808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -256512, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 768, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -16000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 28800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := 4864, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := -30976, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := 1779840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 234816, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 10496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := -56704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 214272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -36480, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 1175296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -1136768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := 316160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := 256, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := -11776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 40448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -238080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 35072, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := -72192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 9216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -23040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := -27648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -2304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 15104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := -53504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 141312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -332544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 617728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -87296, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 13440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := 1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := -4736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := 19072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := -76288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := 260224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := -42496, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := 256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := -7040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := 12800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := -40832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := 79616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := -1920, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 39936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := -130048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := 278016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := -177664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := 1152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := -1152, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := 114048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := -261504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := 35712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 885888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := -1441152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 384, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -37248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := 11136, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := 11136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := -15744, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := 388992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := -128, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 11904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -19072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := -1664, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := 93824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := -41088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -2048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 10112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := -12288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := -29824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := 65536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 3328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -1536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := -1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 39680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := 3072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := -9216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := 256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := -256, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := 25344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := -58112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 7936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := 196864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := -320256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := 640, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -3072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := -6784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := 13312, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := 96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := -1920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 15936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -76416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := 37632, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := -774912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := 1928256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := -3398784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := 3334560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := -132480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := -731520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := 221184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := 96, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -6400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 37312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -22080, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 513024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := -1455232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := 3312832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := -5219104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := 4669536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := -1433472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -436608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := -5632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := 29632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -124480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 432384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := -1202944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 2573888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -3765408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := 3005024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := -113664, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := -224, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := 10432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := -5696, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := 114304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := -289152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 532800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -339264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -80928, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 767136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := 15168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := -61312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := 194176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := -78592, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 160320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := -1215360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := 415264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := -11136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := 45888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := -154880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := 52672, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := -50816, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := 1280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := -6464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := 16384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := -52928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := 15616, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := -3008, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -2560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 7424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -3584, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := 44416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 25408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := 362560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -66816, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := 392256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -590976, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := 3219904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := -128256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := 32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := -480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := 384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := -8000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := 14400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := 2432, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := -15488, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := 889920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 117408, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -64, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := 5248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -28352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := 107136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -18240, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 587648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -568384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := 158080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := 128, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := -5888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := 20224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -119040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := 17536, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := -36096, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := 4608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := -11520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := -13824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -1152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 7552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := -26752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := 70656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := -166272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := 308864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := -43648, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := 6720, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := -2368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := 9536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := -38144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := 130112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := -21248, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := 128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := -3520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := 6400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -20416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := 39808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 19968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -65024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 139008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -88832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := 576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := -576, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := 57024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := -130752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := 17856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := 442944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := -720576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := 192, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := -18624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := 5568, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 5568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -7872, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 194496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -64, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 5952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -9536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := -832, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := 46912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := -20544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -1024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := 5056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := -6144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := -14912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := 1664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := -768, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := 19840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := -4608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := 12672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -29056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 3968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := 98432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := -160128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := 320, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := -3392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := 6656, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 1, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 1, den := 476, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11],[r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23],[r12,r13,r24,r25,r26,r27,r28,r29,r30,r31,r32],[r0,r33,r34,r35,r36,r37,r38,r39,r40,r41],[r0,r42,r43,r44,r45,r46,r47,r48,r49],[r50,r51,r52,r53,r54,r55,r56,r57],[r50,r58,r59,r60,r61,r62,r63],[0,r64,r65,r66,r67,r68],[],[],[],[],[],[0,r69,r70,r71,r72,r73,r74,r75,r76,r77,r78],[r79,r80,r81,r82,r83,r84,r85,r86,-22848,r87],[0,r88,r89,r90,r91,r92,r93,r94,r95],[0,r96,r97,r98,r99,r100,r101,r102],[0,0,r103,r104,r105,r106,768],[],[],[],[],[],[],[r107,r108,r109,r110,r111,r112,r113,r114,r115],[r50,r116,r117,r96,r118,r119,r120,r121],[r50,r122,r123,r124,r125,r126,r127],[],[],[],[],[],[],[0,r116,r98,r128,r129,r130,r131],[0,r64,r65,r66,r67,r68],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,0,r132,r133,r134,r135,r136,r137,r138,5760],[0,r139,r140,r141,r142,r143,r144,r145,-1920],[r107,r146,r147,r148,r149,r150,r151,-128],[r107,r152,r153,r154,r155,r156,-128],[r157,r158,r159,r160,r161,-256],[r157,r162,r70,r163,256],[],[],[],[],[r164,r165,r166,r167,r168,r169,r170,1280],[r107,r152,r171,r172,r173,r174,-896],[r157,r158,r159,r160,r161,-256],[r157,r162,r70,r163,256],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,r175,r176,r177,r178,r179,r180,r181,r182,r183,r184,r185,r186]),(⟨0,0,1⟩,[r187,r188,r189,r190,r191,r192,r193,r194,r195,r196,r197,r198]),(⟨0,0,2⟩,[r187,r188,r199,r200,r201,r202,r203,r204,r205,r206,r207]),(⟨0,0,3⟩,[r175,r208,r209,r210,r211,r212,r213,r214,r215,r216]),(⟨0,0,4⟩,[r175,r152,r217,r218,r219,r220,r221,r222,r223]),(⟨0,0,5⟩,[r12,r69,r0,r224,r225,r226,r227,r228]),(⟨0,0,6⟩,[r12,r229,r230,r231,r232,r233,r234]),(⟨0,0,7⟩,[0,r52,r235,r236,r237,r238]),(⟨0,1,0⟩,[r187,r188,r189,r190,r191,r192,r193,r194,r195,r196,r197,r198]),(⟨0,1,1⟩,[0,r164,r1,r239,r61,r240,r241,r242,r243,r244,r245]),(⟨0,1,2⟩,[r246,r247,r248,r249,r250,r251,r252,r253,-11424,r254]),(⟨0,1,3⟩,[0,r255,r256,r257,r258,r259,r260,r261,r262]),(⟨0,1,4⟩,[0,r157,r263,r264,r265,r266,r267,r268]),(⟨0,1,5⟩,[0,0,r139,r269,r270,r271,384]),(⟨0,2,0⟩,[r187,r188,r199,r200,r201,r202,r203,r204,r205,r206,r207]),(⟨0,2,1⟩,[r246,r247,r248,r249,r250,r251,r252,r253,-11424,r254]),(⟨0,2,2⟩,[r79,r272,r273,r274,r275,r276,r277,r278,r279]),(⟨0,2,3⟩,[r12,r64,r280,r157,r281,r282,r283,r284]),(⟨0,2,4⟩,[r12,r285,r286,r287,r288,r289,r290]),(⟨0,3,0⟩,[r175,r208,r209,r210,r211,r212,r213,r214,r215,r216]),(⟨0,3,1⟩,[0,r255,r256,r257,r258,r259,r260,r261,r262]),(⟨0,3,2⟩,[r12,r64,r280,r157,r281,r282,r283,r284]),(⟨0,3,3⟩,[0,r64,r264,r291,r292,r293,r294]),(⟨0,3,4⟩,[0,r52,r235,r236,r237,r238]),(⟨0,4,0⟩,[r175,r152,r217,r218,r219,r220,r221,r222,r223]),(⟨0,4,1⟩,[0,r157,r263,r264,r265,r266,r267,r268]),(⟨0,4,2⟩,[r12,r285,r286,r287,r288,r289,r290]),(⟨0,4,3⟩,[0,r52,r235,r236,r237,r238]),(⟨0,5,0⟩,[r12,r69,r0,r224,r225,r226,r227,r228]),(⟨0,5,1⟩,[0,0,r139,r269,r270,r271,384]),(⟨0,6,0⟩,[r12,r229,r230,r231,r232,r233,r234]),(⟨0,7,0⟩,[0,r52,r235,r236,r237,r238]),(⟨1,0,0⟩,[r187,r188,r189,r190,r191,r192,r193,r194,r195,r196,r197,r198]),(⟨1,0,1⟩,[0,r164,r1,r239,r61,r240,r241,r242,r243,r244,r245]),(⟨1,0,2⟩,[r246,r247,r248,r249,r250,r251,r252,r253,-11424,r254]),(⟨1,0,3⟩,[0,r255,r256,r257,r258,r259,r260,r261,r262]),(⟨1,0,4⟩,[0,r157,r263,r264,r265,r266,r267,r268]),(⟨1,0,5⟩,[0,0,r139,r269,r270,r271,384]),(⟨1,1,0⟩,[0,r164,r1,r239,r61,r240,r241,r242,r243,r244,r245]),(⟨1,1,1⟩,[0,0,r295,r296,r297,r298,r299,r300,r301,2880]),(⟨1,1,2⟩,[0,r302,r303,r304,r305,r306,r307,r308,-960]),(⟨1,1,3⟩,[r79,r309,r310,r311,r312,r313,r314,-64]),(⟨1,1,4⟩,[r79,r315,r316,r317,r318,r60,-64]),(⟨1,1,5⟩,[r50,r319,r320,r103,r321,-128]),(⟨1,1,6⟩,[r50,r116,r1,r322,128]),(⟨1,2,0⟩,[r246,r247,r248,r249,r250,r251,r252,r253,-11424,r254]),(⟨1,2,1⟩,[0,r302,r303,r304,r305,r306,r307,r308,-960]),(⟨1,2,2⟩,[r107,r146,r323,r324,r325,r326,r327,640]),(⟨1,2,3⟩,[r79,r315,r328,r159,r329,r330,-448]),(⟨1,2,4⟩,[r50,r319,r320,r103,r321,-128]),(⟨1,2,5⟩,[r50,r116,r1,r322,128]),(⟨1,3,0⟩,[0,r255,r256,r257,r258,r259,r260,r261,r262]),(⟨1,3,1⟩,[r79,r309,r310,r311,r312,r313,r314,-64]),(⟨1,3,2⟩,[r79,r315,r328,r159,r329,r330,-448]),(⟨1,4,0⟩,[0,r157,r263,r264,r265,r266,r267,r268]),(⟨1,4,1⟩,[r79,r315,r316,r317,r318,r60,-64]),(⟨1,4,2⟩,[r50,r319,r320,r103,r321,-128]),(⟨1,5,0⟩,[0,0,r139,r269,r270,r271,384]),(⟨1,5,1⟩,[r50,r319,r320,r103,r321,-128]),(⟨1,5,2⟩,[r50,r116,r1,r322,128]),(⟨1,6,1⟩,[r50,r116,r1,r322,128]),(⟨2,0,0⟩,[r187,r188,r199,r200,r201,r202,r203,r204,r205,r206,r207]),(⟨2,0,1⟩,[r246,r247,r248,r249,r250,r251,r252,r253,-11424,r254]),(⟨2,0,2⟩,[r79,r272,r273,r274,r275,r276,r277,r278,r279]),(⟨2,0,3⟩,[r12,r64,r280,r157,r281,r282,r283,r284]),(⟨2,0,4⟩,[r12,r285,r286,r287,r288,r289,r290]),(⟨2,1,0⟩,[r246,r247,r248,r249,r250,r251,r252,r253,-11424,r254]),(⟨2,1,1⟩,[0,r302,r303,r304,r305,r306,r307,r308,-960]),(⟨2,1,2⟩,[r107,r146,r323,r324,r325,r326,r327,640]),(⟨2,1,3⟩,[r79,r315,r328,r159,r329,r330,-448]),(⟨2,1,4⟩,[r50,r319,r320,r103,r321,-128]),(⟨2,1,5⟩,[r50,r116,r1,r322,128]),(⟨2,2,0⟩,[r79,r272,r273,r274,r275,r276,r277,r278,r279]),(⟨2,2,1⟩,[r107,r146,r323,r324,r325,r326,r327,640]),(⟨2,3,0⟩,[r12,r64,r280,r157,r281,r282,r283,r284]),(⟨2,3,1⟩,[r79,r315,r328,r159,r329,r330,-448]),(⟨2,4,0⟩,[r12,r285,r286,r287,r288,r289,r290]),(⟨2,4,1⟩,[r50,r319,r320,r103,r321,-128]),(⟨2,5,1⟩,[r50,r116,r1,r322,128]),(⟨3,0,0⟩,[r175,r208,r209,r210,r211,r212,r213,r214,r215,r216]),(⟨3,0,1⟩,[0,r255,r256,r257,r258,r259,r260,r261,r262]),(⟨3,0,2⟩,[r12,r64,r280,r157,r281,r282,r283,r284]),(⟨3,0,3⟩,[0,r64,r264,r291,r292,r293,r294]),(⟨3,0,4⟩,[0,r52,r235,r236,r237,r238]),(⟨3,1,0⟩,[0,r255,r256,r257,r258,r259,r260,r261,r262]),(⟨3,1,1⟩,[r79,r309,r310,r311,r312,r313,r314,-64]),(⟨3,1,2⟩,[r79,r315,r328,r159,r329,r330,-448]),(⟨3,2,0⟩,[r12,r64,r280,r157,r281,r282,r283,r284]),(⟨3,2,1⟩,[r79,r315,r328,r159,r329,r330,-448]),(⟨3,3,0⟩,[0,r64,r264,r291,r292,r293,r294]),(⟨3,4,0⟩,[0,r52,r235,r236,r237,r238]),(⟨4,0,0⟩,[r175,r152,r217,r218,r219,r220,r221,r222,r223]),(⟨4,0,1⟩,[0,r157,r263,r264,r265,r266,r267,r268]),(⟨4,0,2⟩,[r12,r285,r286,r287,r288,r289,r290]),(⟨4,0,3⟩,[0,r52,r235,r236,r237,r238]),(⟨4,1,0⟩,[0,r157,r263,r264,r265,r266,r267,r268]),(⟨4,1,1⟩,[r79,r315,r316,r317,r318,r60,-64]),(⟨4,1,2⟩,[r50,r319,r320,r103,r321,-128]),(⟨4,2,0⟩,[r12,r285,r286,r287,r288,r289,r290]),(⟨4,2,1⟩,[r50,r319,r320,r103,r321,-128]),(⟨4,3,0⟩,[0,r52,r235,r236,r237,r238]),(⟨5,0,0⟩,[r12,r69,r0,r224,r225,r226,r227,r228]),(⟨5,0,1⟩,[0,0,r139,r269,r270,r271,384]),(⟨5,1,0⟩,[0,0,r139,r269,r270,r271,384]),(⟨5,1,1⟩,[r50,r319,r320,r103,r321,-128]),(⟨5,1,2⟩,[r50,r116,r1,r322,128]),(⟨5,2,1⟩,[r50,r116,r1,r322,128]),(⟨6,0,0⟩,[r12,r229,r230,r231,r232,r233,r234]),(⟨6,1,1⟩,[r50,r116,r1,r322,128]),(⟨7,0,0⟩,[0,r52,r235,r236,r237,r238])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,3,-12,9,6]),(⟨0,0,1⟩,[-1,5,-9,5]),(⟨0,0,2⟩,[-1,4,-7]),(⟨0,0,3⟩,[2,-2]),(⟨0,0,4⟩,[2]),(⟨0,1,0⟩,[-1,5,-9,5]),(⟨0,2,0⟩,[-1,4,-7]),(⟨0,3,0⟩,[2,-2]),(⟨0,4,0⟩,[2]),(⟨1,0,0⟩,[-1,5,-9,5]),(⟨2,0,0⟩,[-1,4,-7]),(⟨3,0,0⟩,[2,-2]),(⟨4,0,0⟩,[2])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[128,-2048,12672,-45312,136064,-378368,739968,-708864,147456]),(⟨0,0,1⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨0,0,2⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨0,0,3⟩,[0,768,-5120,14848,-50176,88832]),(⟨0,1,0⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨0,1,1⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨0,2,0⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨0,3,0⟩,[0,768,-5120,14848,-50176,88832]),(⟨1,0,0⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨1,0,1⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨1,1,0⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨1,1,2⟩,[-256,3072,-7680,-9216,30464]),(⟨1,2,1⟩,[-256,3072,-7680,-9216,30464]),(⟨2,0,0⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨2,1,1⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[0,768,-5120,14848,-50176,88832])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 0 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r331) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 11 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r332) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨4,0,0⟩,[2])]

noncomputable def partial12 : Poly := [(⟨4,0,0⟩,[256,-4096,25344,-90624,272128,-756736,1479936,-1417728,294912]),(⟨4,0,1⟩,[0,-1024,10240,-43520,145408,-466944,954368,-827904]),(⟨4,0,2⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨4,0,3⟩,[0,1536,-10240,29696,-100352,177664]),(⟨4,1,0⟩,[0,-1024,10240,-43520,145408,-466944,954368,-827904]),(⟨4,1,1⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨4,2,0⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨4,3,0⟩,[0,1536,-10240,29696,-100352,177664]),(⟨5,0,0⟩,[0,-1024,10240,-43520,145408,-466944,954368,-827904]),(⟨5,0,1⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨5,1,0⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨5,1,2⟩,[-512,6144,-15360,-18432,60928]),(⟨5,2,1⟩,[-512,6144,-15360,-18432,60928]),(⟨6,0,0⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨6,1,1⟩,[-512,6144,-15360,-18432,60928]),(⟨7,0,0⟩,[0,1536,-10240,29696,-100352,177664])]


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

noncomputable def partial8 : Poly := [(⟨0,4,0⟩,[256,-4096,25344,-90624,272128,-756736,1479936,-1417728,294912]),(⟨0,4,1⟩,[0,-1024,10240,-43520,145408,-466944,954368,-827904]),(⟨0,4,2⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨0,4,3⟩,[0,1536,-10240,29696,-100352,177664]),(⟨0,5,0⟩,[0,-1024,10240,-43520,145408,-466944,954368,-827904]),(⟨0,5,1⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨0,6,0⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨0,7,0⟩,[0,1536,-10240,29696,-100352,177664]),(⟨1,0,0⟩,[-128,2688,-24064,127744,-486912,1529856,-4082944,8494336,-12243328,10816896,-4871424,737280]),(⟨1,0,1⟩,[0,512,-7680,51968,-230144,818432,-2407680,5264640,-7531776,6111488,-2069760]),(⟨1,0,2⟩,[128,-2432,17152,-64768,177152,-434176,843008,-987904,519040,-67200]),(⟨1,0,3⟩,[0,-768,8960,-47360,174336,-498944,969984,-1050368,444160]),(⟨1,1,0⟩,[0,512,-7680,51968,-230144,818432,-2407680,5264640,-7531776,6111488,-2069760]),(⟨1,1,1⟩,[0,0,768,-13056,76032,-174336,23808,590592,-960768,456960]),(⟨1,2,0⟩,[128,-2432,17152,-64768,177152,-434176,843008,-987904,519040,-67200]),(⟨1,3,0⟩,[0,-768,8960,-47360,174336,-498944,969984,-1050368,444160]),(⟨1,4,0⟩,[0,-1024,10240,-43520,145408,-466944,954368,-827904]),(⟨1,4,1⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨1,5,0⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨1,5,2⟩,[-512,6144,-15360,-18432,60928]),(⟨1,6,1⟩,[-512,6144,-15360,-18432,60928]),(⟨2,0,0⟩,[-128,3072,-29440,162304,-636160,2058240,-5613568,11581952,-15694464,11663360,-3101952]),(⟨2,0,1⟩,[0,512,-6400,32768,-119552,502272,-1896192,4547584,-5956864,3354624]),(⟨2,0,2⟩,[128,-2304,15104,-53504,141312,-332544,617728,-611072,94080]),(⟨2,0,3⟩,[0,-768,8192,-40704,145408,-393472,706560,-621824]),(⟨2,1,0⟩,[0,512,-6400,32768,-119552,502272,-1896192,4547584,-5956864,3354624]),(⟨2,1,1⟩,[0,0,768,-12288,65280,-129024,-40704,559104,-639744]),(⟨2,1,2⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨2,2,0⟩,[128,-2304,15104,-53504,141312,-332544,617728,-611072,94080]),(⟨2,2,1⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨2,3,0⟩,[0,-768,8192,-40704,145408,-393472,706560,-621824]),(⟨2,4,0⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨2,5,1⟩,[-512,6144,-15360,-18432,60928]),(⟨3,0,0⟩,[384,-6272,39424,-134912,344320,-786432,1159680,71424,-2764416,2535552]),(⟨3,0,1⟩,[0,-1024,12032,-66048,254208,-741376,1380608,-1223168,188160]),(⟨3,0,2⟩,[-256,3840,-17664,39680,-107264,240896,-186112,26880]),(⟨3,0,3⟩,[0,1536,-11776,39936,-130048,278016,-177664]),(⟨3,1,0⟩,[0,-1024,12032,-66048,254208,-741376,1380608,-1223168,188160]),(⟨3,1,1⟩,[256,-4352,23808,-38144,-56576,187648,-82176,-30464]),(⟨3,1,2⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨3,2,0⟩,[-256,3840,-17664,39680,-107264,240896,-186112,26880]),(⟨3,2,1⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨3,3,0⟩,[0,1536,-11776,39936,-130048,278016,-177664]),(⟨3,4,0⟩,[0,1536,-10240,29696,-100352,177664]),(⟨4,0,0⟩,[384,-8192,60672,-245248,776704,-2200576,4488960,-4861440,1661056]),(⟨4,0,1⟩,[0,-1024,8704,-23552,80896,-476160,1192448,-1010688]),(⟨4,0,2⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨4,0,3⟩,[0,1536,-10240,29696,-100352,177664]),(⟨4,1,0⟩,[0,-1024,8704,-23552,80896,-476160,1192448,-1010688]),(⟨4,1,1⟩,[256,-4096,20224,-24576,-59648,131072,-30464]),(⟨4,1,2⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨4,2,0⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨4,2,1⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨4,3,0⟩,[0,1536,-10240,29696,-100352,177664]),(⟨5,0,0⟩,[-256,2048,768,-44544,183552,-619520,1474816,-1422848]),(⟨5,0,1⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨5,1,0⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨5,1,1⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨5,1,2⟩,[-512,6144,-15360,-18432,60928]),(⟨5,2,1⟩,[-512,6144,-15360,-18432,60928]),(⟨6,0,0⟩,[-256,5120,-25856,65536,-211712,437248,-204544]),(⟨6,1,1⟩,[-512,6144,-15360,-18432,60928]),(⟨7,0,0⟩,[0,1536,-10240,29696,-100352,177664])]


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

noncomputable def partial4 : Poly := [(⟨0,0,4⟩,[256,-4096,25344,-90624,272128,-756736,1479936,-1417728,294912]),(⟨0,0,5⟩,[0,-1024,10240,-43520,145408,-466944,954368,-827904]),(⟨0,0,6⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨0,0,7⟩,[0,1536,-10240,29696,-100352,177664]),(⟨0,1,0⟩,[-128,2688,-24064,127744,-486912,1529856,-4082944,8494336,-12243328,10816896,-4871424,737280]),(⟨0,1,1⟩,[0,512,-7680,51968,-230144,818432,-2407680,5264640,-7531776,6111488,-2069760]),(⟨0,1,2⟩,[128,-2432,17152,-64768,177152,-434176,843008,-987904,519040,-67200]),(⟨0,1,3⟩,[0,-768,8960,-47360,174336,-498944,969984,-1050368,444160]),(⟨0,1,4⟩,[0,-1024,10240,-43520,145408,-466944,954368,-827904]),(⟨0,1,5⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨0,2,0⟩,[-128,3072,-29440,162304,-636160,2058240,-5613568,11581952,-15694464,11663360,-3101952]),(⟨0,2,1⟩,[0,512,-6400,32768,-119552,502272,-1896192,4547584,-5956864,3354624]),(⟨0,2,2⟩,[128,-2304,15104,-53504,141312,-332544,617728,-611072,94080]),(⟨0,2,3⟩,[0,-768,8192,-40704,145408,-393472,706560,-621824]),(⟨0,2,4⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨0,3,0⟩,[384,-6272,39424,-134912,344320,-786432,1159680,71424,-2764416,2535552]),(⟨0,3,1⟩,[0,-1024,12032,-66048,254208,-741376,1380608,-1223168,188160]),(⟨0,3,2⟩,[-256,3840,-17664,39680,-107264,240896,-186112,26880]),(⟨0,3,3⟩,[0,1536,-11776,39936,-130048,278016,-177664]),(⟨0,3,4⟩,[0,1536,-10240,29696,-100352,177664]),(⟨0,4,0⟩,[384,-8192,60672,-245248,776704,-2200576,4488960,-4861440,1661056]),(⟨0,4,1⟩,[0,-1024,8704,-23552,80896,-476160,1192448,-1010688]),(⟨0,4,2⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨0,4,3⟩,[0,1536,-10240,29696,-100352,177664]),(⟨0,5,0⟩,[-256,2048,768,-44544,183552,-619520,1474816,-1422848]),(⟨0,5,1⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨0,6,0⟩,[-256,5120,-25856,65536,-211712,437248,-204544]),(⟨0,7,0⟩,[0,1536,-10240,29696,-100352,177664]),(⟨1,0,0⟩,[-128,2688,-24064,127744,-486912,1529856,-4082944,8494336,-12243328,10816896,-4871424,737280]),(⟨1,0,1⟩,[0,512,-7680,51968,-230144,818432,-2407680,5264640,-7531776,6111488,-2069760]),(⟨1,0,2⟩,[128,-2432,17152,-64768,177152,-434176,843008,-987904,519040,-67200]),(⟨1,0,3⟩,[0,-768,8960,-47360,174336,-498944,969984,-1050368,444160]),(⟨1,0,4⟩,[0,-1024,10240,-43520,145408,-466944,954368,-827904]),(⟨1,0,5⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨1,1,0⟩,[0,1024,-15360,103936,-460288,1636864,-4815360,10529280,-15063552,12222976,-4139520]),(⟨1,1,1⟩,[0,0,1536,-26112,152064,-348672,47616,1181184,-1921536,913920]),(⟨1,1,4⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨1,1,6⟩,[-512,6144,-15360,-18432,60928]),(⟨1,2,0⟩,[128,-1920,10752,-32000,57600,68096,-1053184,3559680,-5437824,3287424]),(⟨1,2,1⟩,[0,0,768,-12288,65280,-129024,-40704,559104,-639744]),(⟨1,2,2⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨1,2,5⟩,[-512,6144,-15360,-18432,60928]),(⟨1,3,0⟩,[0,-1792,20992,-113408,428544,-1240320,2350592,-2273536,632320]),(⟨1,3,1⟩,[256,-4352,23808,-38144,-56576,187648,-82176,-30464]),(⟨1,3,2⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨1,4,0⟩,[0,-1024,8704,-23552,80896,-476160,1192448,-1010688]),(⟨1,4,1⟩,[256,-4096,20224,-24576,-59648,131072,-30464]),(⟨1,4,2⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨1,5,0⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨1,5,1⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨1,5,2⟩,[-512,6144,-15360,-18432,60928]),(⟨1,6,1⟩,[-512,6144,-15360,-18432,60928]),(⟨2,0,0⟩,[-128,3072,-29440,162304,-636160,2058240,-5613568,11581952,-15694464,11663360,-3101952]),(⟨2,0,1⟩,[0,512,-6400,32768,-119552,502272,-1896192,4547584,-5956864,3354624]),(⟨2,0,2⟩,[128,-2304,15104,-53504,141312,-332544,617728,-611072,94080]),(⟨2,0,3⟩,[0,-768,8192,-40704,145408,-393472,706560,-621824]),(⟨2,0,4⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨2,1,0⟩,[128,-1920,10752,-32000,57600,68096,-1053184,3559680,-5437824,3287424]),(⟨2,1,1⟩,[0,0,768,-12288,65280,-129024,-40704,559104,-639744]),(⟨2,1,2⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨2,1,5⟩,[-512,6144,-15360,-18432,60928]),(⟨2,2,0⟩,[256,-4608,30208,-107008,282624,-665088,1235456,-1222144,188160]),(⟨2,2,1⟩,[512,-8704,50688,-116224,15872,393728,-640512,304640]),(⟨2,3,0⟩,[-256,3072,-9472,-1024,38144,-152576,520448,-594944]),(⟨2,3,1⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨2,4,0⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨2,4,1⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨2,5,1⟩,[-512,6144,-15360,-18432,60928]),(⟨3,0,0⟩,[384,-6272,39424,-134912,344320,-786432,1159680,71424,-2764416,2535552]),(⟨3,0,1⟩,[0,-1024,12032,-66048,254208,-741376,1380608,-1223168,188160]),(⟨3,0,2⟩,[-256,3840,-17664,39680,-107264,240896,-186112,26880]),(⟨3,0,3⟩,[0,1536,-11776,39936,-130048,278016,-177664]),(⟨3,0,4⟩,[0,1536,-10240,29696,-100352,177664]),(⟨3,1,0⟩,[0,-1792,20992,-113408,428544,-1240320,2350592,-2273536,632320]),(⟨3,1,1⟩,[256,-4352,23808,-38144,-56576,187648,-82176,-30464]),(⟨3,1,2⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨3,2,0⟩,[-256,3072,-9472,-1024,38144,-152576,520448,-594944]),(⟨3,2,1⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨3,3,0⟩,[0,3072,-23552,79872,-260096,556032,-355328]),(⟨3,4,0⟩,[0,1536,-10240,29696,-100352,177664]),(⟨4,0,0⟩,[384,-8192,60672,-245248,776704,-2200576,4488960,-4861440,1661056]),(⟨4,0,1⟩,[0,-1024,8704,-23552,80896,-476160,1192448,-1010688]),(⟨4,0,2⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨4,0,3⟩,[0,1536,-10240,29696,-100352,177664]),(⟨4,1,0⟩,[0,-1024,8704,-23552,80896,-476160,1192448,-1010688]),(⟨4,1,1⟩,[256,-4096,20224,-24576,-59648,131072,-30464]),(⟨4,1,2⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨4,2,0⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨4,2,1⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨4,3,0⟩,[0,1536,-10240,29696,-100352,177664]),(⟨5,0,0⟩,[-256,2048,768,-44544,183552,-619520,1474816,-1422848]),(⟨5,0,1⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨5,1,0⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨5,1,1⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨5,1,2⟩,[-512,6144,-15360,-18432,60928]),(⟨5,2,1⟩,[-512,6144,-15360,-18432,60928]),(⟨6,0,0⟩,[-256,5120,-25856,65536,-211712,437248,-204544]),(⟨6,1,1⟩,[-512,6144,-15360,-18432,60928]),(⟨7,0,0⟩,[0,1536,-10240,29696,-100352,177664])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,384,-7680,63744,-305664,1053696,-3099648,7713024,-13595136,13338240,-3709440,-2926080,884736]),(⟨0,0,1⟩,[-128,2688,-25600,149248,-618240,2052096,-5820928,13251328,-20876416,18678144,-5733888,-1746432]),(⟨0,0,2⟩,[-128,2688,-22528,118528,-497920,1729536,-4811776,10295552,-15061632,12020096,-3182592]),(⟨0,0,3⟩,[384,-6272,41728,-159488,457216,-1156608,2131200,-1357056,-2265984,3068544]),(⟨0,0,4⟩,[384,-8192,60672,-245248,776704,-2200576,4488960,-4861440,1661056]),(⟨0,0,5⟩,[-256,2048,768,-44544,183552,-619520,1474816,-1422848]),(⟨0,0,6⟩,[-256,5120,-25856,65536,-211712,437248,-204544]),(⟨0,0,7⟩,[0,1536,-10240,29696,-100352,177664]),(⟨0,1,0⟩,[-128,2688,-25600,149248,-618240,2052096,-5820928,13251328,-20876416,18678144,-5733888,-1746432]),(⟨0,1,1⟩,[0,1024,-15360,101632,-423424,1450240,-4543488,10983168,-16547328,12879616,-3591168]),(⟨0,1,2⟩,[128,-1920,10752,-32000,57600,68096,-1053184,3559680,-5437824,3287424]),(⟨0,1,3⟩,[0,-1792,20992,-113408,428544,-1240320,2350592,-2273536,632320]),(⟨0,1,4⟩,[0,-1024,8704,-23552,80896,-476160,1192448,-1010688]),(⟨0,1,5⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨0,2,0⟩,[-128,2688,-22528,118528,-497920,1729536,-4811776,10295552,-15061632,12020096,-3182592]),(⟨0,2,1⟩,[128,-1920,10752,-32000,57600,68096,-1053184,3559680,-5437824,3287424]),(⟨0,2,2⟩,[256,-4608,30208,-107008,282624,-665088,1235456,-1222144,188160]),(⟨0,2,3⟩,[-256,3072,-9472,-1024,38144,-152576,520448,-594944]),(⟨0,2,4⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨0,3,0⟩,[384,-6272,41728,-159488,457216,-1156608,2131200,-1357056,-2265984,3068544]),(⟨0,3,1⟩,[0,-1792,20992,-113408,428544,-1240320,2350592,-2273536,632320]),(⟨0,3,2⟩,[-256,3072,-9472,-1024,38144,-152576,520448,-594944]),(⟨0,3,3⟩,[0,3072,-23552,79872,-260096,556032,-355328]),(⟨0,3,4⟩,[0,1536,-10240,29696,-100352,177664]),(⟨0,4,0⟩,[384,-8192,60672,-245248,776704,-2200576,4488960,-4861440,1661056]),(⟨0,4,1⟩,[0,-1024,8704,-23552,80896,-476160,1192448,-1010688]),(⟨0,4,2⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨0,4,3⟩,[0,1536,-10240,29696,-100352,177664]),(⟨0,5,0⟩,[-256,2048,768,-44544,183552,-619520,1474816,-1422848]),(⟨0,5,1⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨0,6,0⟩,[-256,5120,-25856,65536,-211712,437248,-204544]),(⟨0,7,0⟩,[0,1536,-10240,29696,-100352,177664]),(⟨1,0,0⟩,[-128,2688,-25600,149248,-618240,2052096,-5820928,13251328,-20876416,18678144,-5733888,-1746432]),(⟨1,0,1⟩,[0,1024,-15360,101632,-423424,1450240,-4543488,10983168,-16547328,12879616,-3591168]),(⟨1,0,2⟩,[128,-1920,10752,-32000,57600,68096,-1053184,3559680,-5437824,3287424]),(⟨1,0,3⟩,[0,-1792,20992,-113408,428544,-1240320,2350592,-2273536,632320]),(⟨1,0,4⟩,[0,-1024,8704,-23552,80896,-476160,1192448,-1010688]),(⟨1,0,5⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨1,1,0⟩,[0,1024,-15360,101632,-423424,1450240,-4543488,10983168,-16547328,12879616,-3591168]),(⟨1,1,1⟩,[0,0,2304,-39168,228096,-523008,71424,1771776,-2882304,1370880]),(⟨1,1,2⟩,[0,-768,13056,-74496,155904,22272,-535296,777984,-456960]),(⟨1,1,3⟩,[256,-4352,23808,-38144,-56576,187648,-82176,-30464]),(⟨1,1,4⟩,[256,-4096,20224,-24576,-59648,131072,-30464]),(⟨1,1,5⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨1,1,6⟩,[-512,6144,-15360,-18432,60928]),(⟨1,2,0⟩,[128,-1920,10752,-32000,57600,68096,-1053184,3559680,-5437824,3287424]),(⟨1,2,1⟩,[0,-768,13056,-74496,155904,22272,-535296,777984,-456960]),(⟨1,2,2⟩,[512,-8704,50688,-116224,15872,393728,-640512,304640]),(⟨1,2,3⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨1,2,4⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨1,2,5⟩,[-512,6144,-15360,-18432,60928]),(⟨1,3,0⟩,[0,-1792,20992,-113408,428544,-1240320,2350592,-2273536,632320]),(⟨1,3,1⟩,[256,-4352,23808,-38144,-56576,187648,-82176,-30464]),(⟨1,3,2⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨1,4,0⟩,[0,-1024,8704,-23552,80896,-476160,1192448,-1010688]),(⟨1,4,1⟩,[256,-4096,20224,-24576,-59648,131072,-30464]),(⟨1,4,2⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨1,5,0⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨1,5,1⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨1,5,2⟩,[-512,6144,-15360,-18432,60928]),(⟨1,6,1⟩,[-512,6144,-15360,-18432,60928]),(⟨2,0,0⟩,[-128,2688,-22528,118528,-497920,1729536,-4811776,10295552,-15061632,12020096,-3182592]),(⟨2,0,1⟩,[128,-1920,10752,-32000,57600,68096,-1053184,3559680,-5437824,3287424]),(⟨2,0,2⟩,[256,-4608,30208,-107008,282624,-665088,1235456,-1222144,188160]),(⟨2,0,3⟩,[-256,3072,-9472,-1024,38144,-152576,520448,-594944]),(⟨2,0,4⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨2,1,0⟩,[128,-1920,10752,-32000,57600,68096,-1053184,3559680,-5437824,3287424]),(⟨2,1,1⟩,[0,-768,13056,-74496,155904,22272,-535296,777984,-456960]),(⟨2,1,2⟩,[512,-8704,50688,-116224,15872,393728,-640512,304640]),(⟨2,1,3⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨2,1,4⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨2,1,5⟩,[-512,6144,-15360,-18432,60928]),(⟨2,2,0⟩,[256,-4608,30208,-107008,282624,-665088,1235456,-1222144,188160]),(⟨2,2,1⟩,[512,-8704,50688,-116224,15872,393728,-640512,304640]),(⟨2,3,0⟩,[-256,3072,-9472,-1024,38144,-152576,520448,-594944]),(⟨2,3,1⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨2,4,0⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨2,4,1⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨2,5,1⟩,[-512,6144,-15360,-18432,60928]),(⟨3,0,0⟩,[384,-6272,41728,-159488,457216,-1156608,2131200,-1357056,-2265984,3068544]),(⟨3,0,1⟩,[0,-1792,20992,-113408,428544,-1240320,2350592,-2273536,632320]),(⟨3,0,2⟩,[-256,3072,-9472,-1024,38144,-152576,520448,-594944]),(⟨3,0,3⟩,[0,3072,-23552,79872,-260096,556032,-355328]),(⟨3,0,4⟩,[0,1536,-10240,29696,-100352,177664]),(⟨3,1,0⟩,[0,-1792,20992,-113408,428544,-1240320,2350592,-2273536,632320]),(⟨3,1,1⟩,[256,-4352,23808,-38144,-56576,187648,-82176,-30464]),(⟨3,1,2⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨3,2,0⟩,[-256,3072,-9472,-1024,38144,-152576,520448,-594944]),(⟨3,2,1⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨3,3,0⟩,[0,3072,-23552,79872,-260096,556032,-355328]),(⟨3,4,0⟩,[0,1536,-10240,29696,-100352,177664]),(⟨4,0,0⟩,[384,-8192,60672,-245248,776704,-2200576,4488960,-4861440,1661056]),(⟨4,0,1⟩,[0,-1024,8704,-23552,80896,-476160,1192448,-1010688]),(⟨4,0,2⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨4,0,3⟩,[0,1536,-10240,29696,-100352,177664]),(⟨4,1,0⟩,[0,-1024,8704,-23552,80896,-476160,1192448,-1010688]),(⟨4,1,1⟩,[256,-4096,20224,-24576,-59648,131072,-30464]),(⟨4,1,2⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨4,2,0⟩,[-256,3584,-14080,25600,-81664,159232,-26880]),(⟨4,2,1⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨4,3,0⟩,[0,1536,-10240,29696,-100352,177664]),(⟨5,0,0⟩,[-256,2048,768,-44544,183552,-619520,1474816,-1422848]),(⟨5,0,1⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨5,1,0⟩,[0,0,-1536,18432,-46080,-55296,182784]),(⟨5,1,1⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨5,1,2⟩,[-512,6144,-15360,-18432,60928]),(⟨5,2,1⟩,[-512,6144,-15360,-18432,60928]),(⟨6,0,0⟩,[-256,5120,-25856,65536,-211712,437248,-204544]),(⟨6,1,1⟩,[-512,6144,-15360,-18432,60928]),(⟨7,0,0⟩,[0,1536,-10240,29696,-100352,177664])]


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
    (Poly.add (Poly.scale (K.ofRat r333) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 0 11).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r331*r332 : ℚ)=r333 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 0 11 r331 r332 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 0=11 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 0 11).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C056

#print axioms Coulomb8.Columns.C056.sound
