import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C083

def r0 : ℚ := { num := -576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 15360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -183168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 1297344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -355776, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 19259712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -5982336, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 8661120, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -59001792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 8316288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -105197184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 165911232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -131308608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := 18729024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 29632896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -6925824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -5184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 66816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := -539776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := 2983360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := -11617856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := 32044032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := -3652480, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := 84149824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := -87940800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := 108881152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := -185450368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := 248521536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -181825216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 41038336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 2133120, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -2496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 36416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -303488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 1687360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -6650688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 18809408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -37534208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 51873984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -54937920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 71498944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -124209280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 158246848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -106368448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 3585856, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 13504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -140160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 852864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -3331520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 8469056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -13405696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 11757056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -372928, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 13526080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -28823168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 917120, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 20411584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -21726016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 5632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -88896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 658304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -2821376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 7515136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -12581760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 13363968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -12546880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 21946880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -38080832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 35915136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -1813632, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -7808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 8576, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -221824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 347392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := 200960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := -1525504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := 1726208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := -43392, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := 1550720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := -5664640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := 660608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := -256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := 2048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := -46336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := 29184, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -441600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 615936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -581376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := 400128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := -1111808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := 1483520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := 1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -1280, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := 121088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := -327424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 405248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -133888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 235264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := -78080, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := 224512, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -4608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 28416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := -10752, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := 67840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 2560, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 25856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -250368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -4608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -2048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := 20992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := -74240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := 5120, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 37888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := 31232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := -363008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -2304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 48768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := -460800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := 2571264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -9407744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 23565440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -41020416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 7388160, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := -60768000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := 99594112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -171355136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 200081408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := -128060160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := 4560512, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 4416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -40448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 188416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := -60224, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := 11328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 2419968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -364800, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := 7595712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -9082688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 24668416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -7579904, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 8280384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := -3659712, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := 3840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := -67584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := 515584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := -2235136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := 6034944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := -10503168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 12442624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := -13298176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := 19464960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -27528192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 23076352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -1017088, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 6144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := -96256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := 493568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := -944128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -6144, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 3405824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -5441536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := 4096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := -49152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := 122880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 147456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := 512, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := -42624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := 285440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -1174528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 3005440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := -4550400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := 508416, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := -1917568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := -1245568, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := 715008, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 112896, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -6144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 85504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := -492544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := 1499136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -2485248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := 2147328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -238592, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 4169728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -7240704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 3993088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := -9216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := 175104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := -73728, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := 4399104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := -7378944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := 436224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := 24403968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := -7397376, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := 6988800, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := -1024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := 22528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := -196608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := 858112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -1710080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := -2048, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := 884736, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -1476608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := 6144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := -291840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := 880128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := -830976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -1878528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := 5975040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := -5654016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := 507648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -14592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := 6144, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := -366592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := 614912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -36352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := -2033664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := 616448, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := -582400, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -5632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 49152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := -214528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := 427520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := -221184, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := 369152, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := -1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := 24064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -123392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 236032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := 1536, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -851456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 1360384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := 12288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -30720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := -36864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := 7680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := -91584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := 648672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := -177888, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := 9629856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := -2991168, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := 4330560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -29500896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := 4158144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := -52598592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 82955616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -65654304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := 9364512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := 14816448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := -3462912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := 96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := -2592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := 33408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := -269888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := 1491680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := -5808928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := 16022016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -1826240, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := 42074912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := -43970400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := 54440576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := -92725184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := 124260768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -90912608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 20519168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := 1066560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := 32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := -1248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := 18208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := -151744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := 843680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := -3325344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := 9404704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := -18767104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := 25936992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := -27468960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := 35749472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := -62104640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := 79123424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -53184224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := 1792928, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := 6752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := -70080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := 426432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := -1665760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := 4234528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := -6702848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := 5878528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -186464, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := 6763040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := -14411584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := 458560, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := 10205792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -10863008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := -32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := 2816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -44448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 329152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -1410688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 3757568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -6290880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 6681984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -6273440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 10973440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := -19040416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 17957568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -906816, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := -3904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := 4288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := -110912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := 173696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := 100480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := -762752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := 863104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := -21696, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := 775360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := -2832320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := 330304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 1024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := -23168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := 14592, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -220800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 307968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -290688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 200064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -555904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 741760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -640, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 60544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := -163712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := 202624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := -66944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := 117632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := -39040, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := 112256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := 128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := 14208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := -5376, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := 33920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := 1280, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := 12928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := -125184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := -2304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := 10496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := -37120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := 18944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := 15616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := -181504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -1152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := 24384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := -230400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := 1285632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := -4703872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := 11782720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := -20510208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := 3694080, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := -30384000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := 49797056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := -85677568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := 100040704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := -64030080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := 2280256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := -96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := 2208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := -20224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := 94208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := -30112, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := 5664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := 1209984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := -182400, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := 3797856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := -4541344, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := 12334208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := -3789952, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := 4140192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := -1829856, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := 1920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := -33792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := 257792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := -1117568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := 3017472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := -5251584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := 6221312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := -6649088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 9732480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := -13764096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := 11538176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := -508544, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := 3072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := -48128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := 246784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := -472064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := -3072, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := 1702912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := -2720768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := -24576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := 61440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := 73728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := 256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := -21312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := 142720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := -587264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := 1502720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := -2275200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := 254208, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := -958784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := -622784, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := 357504, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := 56448, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := -3072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := 42752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := -246272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := 749568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := -1242624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := 1073664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := -119296, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := 2084864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := -3620352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := 1996544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := 87552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := -36864, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := 2199552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := -3689472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := 218112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := 12201984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := -3698688, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := 3494400, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := -512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := 11264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := -98304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := 429056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := -855040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := -1024, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := 442368, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := -738304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := 3072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := -145920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := 440064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := -415488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := -939264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := 2987520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r450 : ℚ := { num := -2827008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r451 : ℚ := { num := 253824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r452 : ℚ := { num := -7296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r453 : ℚ := { num := 3072, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r454 : ℚ := { num := -183296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r455 : ℚ := { num := 307456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r456 : ℚ := { num := -18176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r457 : ℚ := { num := -1016832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r458 : ℚ := { num := 308224, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r459 : ℚ := { num := -291200, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r460 : ℚ := { num := -2816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r461 : ℚ := { num := 24576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r462 : ℚ := { num := -107264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r463 : ℚ := { num := 213760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r464 : ℚ := { num := -110592, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r465 : ℚ := { num := 184576, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r466 : ℚ := { num := -768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r467 : ℚ := { num := 12032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r468 : ℚ := { num := -61696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r469 : ℚ := { num := 118016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r470 : ℚ := { num := 768, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r471 : ℚ := { num := -425728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r472 : ℚ := { num := 680192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r473 : ℚ := { num := -15360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r474 : ℚ := { num := -18432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r475 : ℚ := { num := 1, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r476 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r477 : ℚ := { num := 1, den := 952, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15],[r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31],[r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46],[r0,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59],[r60,r61,r62,r63,r64,r65,r66,r67,r68,r69,r70,r71,r72],[r73,r74,r75,r76,r77,r78,r79,r80,r81,r82,r83,r84],[r85,r86,r85,r87,r88,r89,r90,r91,r92,r93,r94],[0,r95,r96,r97,r98,r99,r100,r101,r102,r103],[r104,r105,r106,r107,r108,r109,r110,r111,r112],[0,r113,r114,r115,r116,r117,r118,r119],[],[],[],[0,r120,r121,r122,r123,r124,r125,r126,r127,r128,r129,r130,r131,r132,r133],[r134,r135,r136,r137,r138,r139,r140,r141,r142,r143,r144,r145,r146,r147],[0,r148,r149,r150,r151,r152,r153,r154,r155,r156,r157,r158,r159],[0,0,0,0,r160,r161,r162,r163,r164,r165,r166,22528],[],[0,r95,r96,r97,r98,r99,r100,r101,r102,r103],[0,0,0,0,r167,r168,r169,r170,-4096],[],[],[],[],[r171,r172,r173,r174,r175,r176,r177,r178,r179,41472,r180,r181,r182],[r73,r74,r75,r76,r77,r78,r79,r80,r81,r82,r83,r84],[],[],[r104,r105,r106,r107,r108,r109,r110,r111,r112],[],[],[],[],[0,r183,r184,r185,r186,r187,r188,r189,r190,r191,r192],[],[],[0,r113,r114,r115,r116,r117,r118,r119],[],[],[],[],[],[],[],[],[],[],[],[],[0,0,0,0,r193,r194,r195,r196,r197,r198,r199,r200,r201,-150528],[0,0,0,0,r202,r203,r204,r205,r206,r207,r208,r209,50176],[0,0,0,0,r160,r161,r162,r163,r164,r165,r166,22528],[],[],[0,0,0,0,r167,r168,r169,r170,-4096],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,r120,r210,r211,r212,r213,r214,r215,r216,r217,13824],[r218,r219,r220,r221,r222,r223,r224,r225,r226,12544],[r104,r227,r228,r229,r230,r172,r231,r232,-12544],[r233,r234,r235,r236,r237,r238,r239,-5632],[],[],[r202,r240,r241,r242,1024],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,r243,r244,r245,r246,r247,r248,r249,r250,r251,r252,r253,r254,r255,r256,r257,r258]),(⟨0,0,1⟩,[r259,r260,r261,r262,r263,r264,r265,r266,r267,r268,r269,r270,r271,r272,r273,r274]),(⟨0,0,2⟩,[r275,r276,r277,r278,r279,r280,r281,r282,r283,r284,r285,r286,r287,r288,r289]),(⟨0,0,3⟩,[r243,r290,r291,r292,r293,r294,r295,r296,r297,r298,r299,r300,r301,r302]),(⟨0,0,4⟩,[r303,r304,r305,r306,r307,r308,r309,r310,r311,r312,r313,r314,r315]),(⟨0,0,5⟩,[r16,r316,r317,r318,r319,r320,r321,r322,r323,r324,r325,r326]),(⟨0,0,6⟩,[r171,r327,r171,r328,r329,r330,r331,r332,r333,r334,r335]),(⟨0,0,7⟩,[0,r218,r336,r337,r338,r339,r340,r341,r342,r343]),(⟨0,0,8⟩,[r344,r120,r345,r346,r347,r348,r349,r350,r351]),(⟨0,0,9⟩,[0,r202,r352,r353,r109,r354,r355,r356]),(⟨0,1,0⟩,[r259,r260,r261,r262,r263,r264,r265,r266,r267,r268,r269,r270,r271,r272,r273,r274]),(⟨0,1,1⟩,[0,r357,r358,r359,r360,r361,r362,r363,r364,r365,r366,r367,r368,r369,r370]),(⟨0,1,2⟩,[r371,r372,r373,r374,r375,r376,r377,r378,r379,r380,r381,r382,r383,r384]),(⟨0,1,3⟩,[0,r385,r386,r387,r388,r389,r390,r391,r392,r393,r394,r395,r396]),(⟨0,1,4⟩,[0,0,0,0,r397,r398,r399,r400,r401,r402,r403,11264]),(⟨0,1,6⟩,[0,r218,r336,r337,r338,r339,r340,r341,r342,r343]),(⟨0,1,7⟩,[0,0,0,0,r86,r404,r405,r406,-2048]),(⟨0,2,0⟩,[r275,r276,r277,r278,r279,r280,r281,r282,r283,r284,r285,r286,r287,r288,r289]),(⟨0,2,1⟩,[r371,r372,r373,r374,r375,r376,r377,r378,r379,r380,r381,r382,r383,r384]),(⟨0,2,2⟩,[r60,r407,r408,r409,r410,r411,r412,r413,r414,20736,r415,r416,r417]),(⟨0,2,3⟩,[r16,r316,r317,r318,r319,r320,r321,r322,r323,r324,r325,r326]),(⟨0,2,6⟩,[r344,r120,r345,r346,r347,r348,r349,r350,r351]),(⟨0,3,0⟩,[r243,r290,r291,r292,r293,r294,r295,r296,r297,r298,r299,r300,r301,r302]),(⟨0,3,1⟩,[0,r385,r386,r387,r388,r389,r390,r391,r392,r393,r394,r395,r396]),(⟨0,3,2⟩,[r16,r316,r317,r318,r319,r320,r321,r322,r323,r324,r325,r326]),(⟨0,3,3⟩,[0,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427]),(⟨0,3,6⟩,[0,r202,r352,r353,r109,r354,r355,r356]),(⟨0,4,0⟩,[r303,r304,r305,r306,r307,r308,r309,r310,r311,r312,r313,r314,r315]),(⟨0,4,1⟩,[0,0,0,0,r397,r398,r399,r400,r401,r402,r403,11264]),(⟨0,5,0⟩,[r16,r316,r317,r318,r319,r320,r321,r322,r323,r324,r325,r326]),(⟨0,6,0⟩,[r171,r327,r171,r328,r329,r330,r331,r332,r333,r334,r335]),(⟨0,6,1⟩,[0,r218,r336,r337,r338,r339,r340,r341,r342,r343]),(⟨0,6,2⟩,[r344,r120,r345,r346,r347,r348,r349,r350,r351]),(⟨0,6,3⟩,[0,r202,r352,r353,r109,r354,r355,r356]),(⟨0,7,0⟩,[0,r218,r336,r337,r338,r339,r340,r341,r342,r343]),(⟨0,7,1⟩,[0,0,0,0,r86,r404,r405,r406,-2048]),(⟨0,8,0⟩,[r344,r120,r345,r346,r347,r348,r349,r350,r351]),(⟨0,9,0⟩,[0,r202,r352,r353,r109,r354,r355,r356]),(⟨1,0,0⟩,[r259,r260,r261,r262,r263,r264,r265,r266,r267,r268,r269,r270,r271,r272,r273,r274]),(⟨1,0,1⟩,[0,r357,r358,r359,r360,r361,r362,r363,r364,r365,r366,r367,r368,r369,r370]),(⟨1,0,2⟩,[r371,r372,r373,r374,r375,r376,r377,r378,r379,r380,r381,r382,r383,r384]),(⟨1,0,3⟩,[0,r385,r386,r387,r388,r389,r390,r391,r392,r393,r394,r395,r396]),(⟨1,0,4⟩,[0,0,0,0,r397,r398,r399,r400,r401,r402,r403,11264]),(⟨1,0,6⟩,[0,r218,r336,r337,r338,r339,r340,r341,r342,r343]),(⟨1,0,7⟩,[0,0,0,0,r86,r404,r405,r406,-2048]),(⟨1,1,0⟩,[0,r357,r358,r359,r360,r361,r362,r363,r364,r365,r366,r367,r368,r369,r370]),(⟨1,1,1⟩,[0,0,0,0,r105,r428,r429,r430,r431,r432,r433,r434,r435,-75264]),(⟨1,1,2⟩,[0,0,0,0,r436,r437,r438,r439,r440,r441,r442,r443,25088]),(⟨1,1,3⟩,[0,0,0,0,r397,r398,r399,r400,r401,r402,r403,11264]),(⟨1,1,6⟩,[0,0,0,0,r86,r404,r405,r406,-2048]),(⟨1,2,0⟩,[r371,r372,r373,r374,r375,r376,r377,r378,r379,r380,r381,r382,r383,r384]),(⟨1,2,1⟩,[0,0,0,0,r436,r437,r438,r439,r440,r441,r442,r443,25088]),(⟨1,3,0⟩,[0,r385,r386,r387,r388,r389,r390,r391,r392,r393,r394,r395,r396]),(⟨1,3,1⟩,[0,0,0,0,r397,r398,r399,r400,r401,r402,r403,11264]),(⟨1,4,0⟩,[0,0,0,0,r397,r398,r399,r400,r401,r402,r403,11264]),(⟨1,6,0⟩,[0,r218,r336,r337,r338,r339,r340,r341,r342,r343]),(⟨1,6,1⟩,[0,0,0,0,r86,r404,r405,r406,-2048]),(⟨1,7,0⟩,[0,0,0,0,r86,r404,r405,r406,-2048]),(⟨2,0,0⟩,[r275,r276,r277,r278,r279,r280,r281,r282,r283,r284,r285,r286,r287,r288,r289]),(⟨2,0,1⟩,[r371,r372,r373,r374,r375,r376,r377,r378,r379,r380,r381,r382,r383,r384]),(⟨2,0,2⟩,[r60,r407,r408,r409,r410,r411,r412,r413,r414,20736,r415,r416,r417]),(⟨2,0,3⟩,[r16,r316,r317,r318,r319,r320,r321,r322,r323,r324,r325,r326]),(⟨2,0,6⟩,[r344,r120,r345,r346,r347,r348,r349,r350,r351]),(⟨2,1,0⟩,[r371,r372,r373,r374,r375,r376,r377,r378,r379,r380,r381,r382,r383,r384]),(⟨2,1,1⟩,[0,0,0,0,r436,r437,r438,r439,r440,r441,r442,r443,25088]),(⟨2,2,0⟩,[r60,r407,r408,r409,r410,r411,r412,r413,r414,20736,r415,r416,r417]),(⟨2,2,2⟩,[0,r357,r444,r445,r446,r447,r448,r449,r450,r451,6912]),(⟨2,2,3⟩,[r73,r452,r453,r454,r455,r456,r457,r458,r459,6272]),(⟨2,2,4⟩,[r344,r460,r461,r462,r463,r407,r464,r465,-6272]),(⟨2,2,5⟩,[r466,r467,r468,r469,r470,r471,r472,-2816]),(⟨2,2,8⟩,[r436,r160,r473,r474,512]),(⟨2,3,0⟩,[r16,r316,r317,r318,r319,r320,r321,r322,r323,r324,r325,r326]),(⟨2,3,2⟩,[r73,r452,r453,r454,r455,r456,r457,r458,r459,6272]),(⟨2,4,2⟩,[r344,r460,r461,r462,r463,r407,r464,r465,-6272]),(⟨2,5,2⟩,[r466,r467,r468,r469,r470,r471,r472,-2816]),(⟨2,6,0⟩,[r344,r120,r345,r346,r347,r348,r349,r350,r351]),(⟨2,8,2⟩,[r436,r160,r473,r474,512]),(⟨3,0,0⟩,[r243,r290,r291,r292,r293,r294,r295,r296,r297,r298,r299,r300,r301,r302]),(⟨3,0,1⟩,[0,r385,r386,r387,r388,r389,r390,r391,r392,r393,r394,r395,r396]),(⟨3,0,2⟩,[r16,r316,r317,r318,r319,r320,r321,r322,r323,r324,r325,r326]),(⟨3,0,3⟩,[0,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427]),(⟨3,0,6⟩,[0,r202,r352,r353,r109,r354,r355,r356]),(⟨3,1,0⟩,[0,r385,r386,r387,r388,r389,r390,r391,r392,r393,r394,r395,r396]),(⟨3,1,1⟩,[0,0,0,0,r397,r398,r399,r400,r401,r402,r403,11264]),(⟨3,2,0⟩,[r16,r316,r317,r318,r319,r320,r321,r322,r323,r324,r325,r326]),(⟨3,2,2⟩,[r73,r452,r453,r454,r455,r456,r457,r458,r459,6272]),(⟨3,3,0⟩,[0,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427]),(⟨3,6,0⟩,[0,r202,r352,r353,r109,r354,r355,r356]),(⟨4,0,0⟩,[r303,r304,r305,r306,r307,r308,r309,r310,r311,r312,r313,r314,r315]),(⟨4,0,1⟩,[0,0,0,0,r397,r398,r399,r400,r401,r402,r403,11264]),(⟨4,1,0⟩,[0,0,0,0,r397,r398,r399,r400,r401,r402,r403,11264]),(⟨4,2,2⟩,[r344,r460,r461,r462,r463,r407,r464,r465,-6272]),(⟨5,0,0⟩,[r16,r316,r317,r318,r319,r320,r321,r322,r323,r324,r325,r326]),(⟨5,2,2⟩,[r466,r467,r468,r469,r470,r471,r472,-2816]),(⟨6,0,0⟩,[r171,r327,r171,r328,r329,r330,r331,r332,r333,r334,r335]),(⟨6,0,1⟩,[0,r218,r336,r337,r338,r339,r340,r341,r342,r343]),(⟨6,0,2⟩,[r344,r120,r345,r346,r347,r348,r349,r350,r351]),(⟨6,0,3⟩,[0,r202,r352,r353,r109,r354,r355,r356]),(⟨6,1,0⟩,[0,r218,r336,r337,r338,r339,r340,r341,r342,r343]),(⟨6,1,1⟩,[0,0,0,0,r86,r404,r405,r406,-2048]),(⟨6,2,0⟩,[r344,r120,r345,r346,r347,r348,r349,r350,r351]),(⟨6,3,0⟩,[0,r202,r352,r353,r109,r354,r355,r356]),(⟨7,0,0⟩,[0,r218,r336,r337,r338,r339,r340,r341,r342,r343]),(⟨7,0,1⟩,[0,0,0,0,r86,r404,r405,r406,-2048]),(⟨7,1,0⟩,[0,0,0,0,r86,r404,r405,r406,-2048]),(⟨8,0,0⟩,[r344,r120,r345,r346,r347,r348,r349,r350,r351]),(⟨8,2,2⟩,[r436,r160,r473,r474,512]),(⟨9,0,0⟩,[0,r202,r352,r353,r109,r354,r355,r356])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,9,-60,150,-162,33,54]),(⟨0,0,1⟩,[-3,21,-66,118,-119,49]),(⟨0,0,2⟩,[-1,10,-42,70,-49]),(⟨0,0,3⟩,[6,-22,38,-22]),(⟨0,0,6⟩,[4]),(⟨0,1,0⟩,[-3,21,-66,118,-119,49]),(⟨0,2,0⟩,[-1,10,-42,70,-49]),(⟨0,3,0⟩,[6,-22,38,-22]),(⟨0,6,0⟩,[4]),(⟨1,0,0⟩,[-3,21,-66,118,-119,49]),(⟨2,0,0⟩,[-1,10,-42,70,-49]),(⟨3,0,0⟩,[6,-22,38,-22]),(⟨6,0,0⟩,[4])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[-256,5120,-43008,199936,-545280,801024,-457728,253696,-1684736,2508544,-513024]),(⟨0,0,1⟩,[0,1536,-21760,121088,-327424,405248,-133888,235264,-1327360,1571584]),(⟨0,0,2⟩,[256,-4608,28416,-75264,67840,43520,25856,-250368,-32256]),(⟨0,0,3⟩,[0,-2048,20992,-74240,87040,37888,31232,-363008]),(⟨0,1,0⟩,[0,1536,-21760,121088,-327424,405248,-133888,235264,-1327360,1571584]),(⟨0,1,1⟩,[0,0,0,0,4096,-49152,122880,147456,-487424]),(⟨0,2,0⟩,[256,-4608,28416,-75264,67840,43520,25856,-250368,-32256]),(⟨0,3,0⟩,[0,-2048,20992,-74240,87040,37888,31232,-363008]),(⟨1,0,0⟩,[0,1536,-21760,121088,-327424,405248,-133888,235264,-1327360,1571584]),(⟨1,0,1⟩,[0,0,0,0,4096,-49152,122880,147456,-487424]),(⟨1,1,0⟩,[0,0,0,0,4096,-49152,122880,147456,-487424]),(⟨2,0,0⟩,[256,-4608,28416,-75264,67840,43520,25856,-250368,-32256]),(⟨2,2,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨3,0,0⟩,[0,-2048,20992,-74240,87040,37888,31232,-363008])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 2 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r475) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 13 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r476) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨6,0,0⟩,[4])]

noncomputable def partial12 : Poly := [(⟨6,0,0⟩,[-1024,20480,-172032,799744,-2181120,3204096,-1830912,1014784,-6738944,10034176,-2052096]),(⟨6,0,1⟩,[0,6144,-87040,484352,-1309696,1620992,-535552,941056,-5309440,6286336]),(⟨6,0,2⟩,[1024,-18432,113664,-301056,271360,174080,103424,-1001472,-129024]),(⟨6,0,3⟩,[0,-8192,83968,-296960,348160,151552,124928,-1452032]),(⟨6,1,0⟩,[0,6144,-87040,484352,-1309696,1620992,-535552,941056,-5309440,6286336]),(⟨6,1,1⟩,[0,0,0,0,16384,-196608,491520,589824,-1949696]),(⟨6,2,0⟩,[1024,-18432,113664,-301056,271360,174080,103424,-1001472,-129024]),(⟨6,3,0⟩,[0,-8192,83968,-296960,348160,151552,124928,-1452032]),(⟨7,0,0⟩,[0,6144,-87040,484352,-1309696,1620992,-535552,941056,-5309440,6286336]),(⟨7,0,1⟩,[0,0,0,0,16384,-196608,491520,589824,-1949696]),(⟨7,1,0⟩,[0,0,0,0,16384,-196608,491520,589824,-1949696]),(⟨8,0,0⟩,[1024,-18432,113664,-301056,271360,174080,103424,-1001472,-129024]),(⟨8,2,2⟩,[-4096,49152,-122880,-147456,487424]),(⟨9,0,0⟩,[0,-8192,83968,-296960,348160,151552,124928,-1452032])]


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

noncomputable def partial8 : Poly := [(⟨0,6,0⟩,[-1024,20480,-172032,799744,-2181120,3204096,-1830912,1014784,-6738944,10034176,-2052096]),(⟨0,6,1⟩,[0,6144,-87040,484352,-1309696,1620992,-535552,941056,-5309440,6286336]),(⟨0,6,2⟩,[1024,-18432,113664,-301056,271360,174080,103424,-1001472,-129024]),(⟨0,6,3⟩,[0,-8192,83968,-296960,348160,151552,124928,-1452032]),(⟨0,7,0⟩,[0,6144,-87040,484352,-1309696,1620992,-535552,941056,-5309440,6286336]),(⟨0,7,1⟩,[0,0,0,0,16384,-196608,491520,589824,-1949696]),(⟨0,8,0⟩,[1024,-18432,113664,-301056,271360,174080,103424,-1001472,-129024]),(⟨0,9,0⟩,[0,-8192,83968,-296960,348160,151552,124928,-1452032]),(⟨1,0,0⟩,[768,-20736,253440,-1871104,9307648,-32746496,83144448,-153483776,209797888,-235701504,289067008,-427754752,542782464,-441605632,183968512,-25138176]),(⟨1,0,1⟩,[0,-4608,97536,-921600,5142528,-18833920,47474944,-84375552,110475264,-128183808,184160000,-294909952,354930688,-252059136,77007616]),(⟨1,0,2⟩,[-768,19200,-198912,1156864,-4233728,10175488,-16129536,16775680,-13492992,17043200,-28358912,27254528,-8429568,-1580544]),(⟨1,0,3⟩,[0,6144,-105984,798720,-3447296,9334784,-16401408,19378176,-19209216,27400192,-44695040,44728320,-17787392]),(⟨1,1,0⟩,[0,-4608,97536,-921600,5142528,-18833920,47474944,-84375552,110475264,-128183808,184160000,-294909952,354930688,-252059136,77007616]),(⟨1,1,1⟩,[0,0,0,0,-12288,233472,-1671168,5865472,-9838592,581632,32538624,-69042176,65228800,-23883776]),(⟨1,2,0⟩,[-768,19200,-198912,1156864,-4233728,10175488,-16129536,16775680,-13492992,17043200,-28358912,27254528,-8429568,-1580544]),(⟨1,3,0⟩,[0,6144,-105984,798720,-3447296,9334784,-16401408,19378176,-19209216,27400192,-44695040,44728320,-17787392]),(⟨1,6,0⟩,[0,6144,-87040,484352,-1309696,1620992,-535552,941056,-5309440,6286336]),(⟨1,6,1⟩,[0,0,0,0,16384,-196608,491520,589824,-1949696]),(⟨1,7,0⟩,[0,0,0,0,16384,-196608,491520,589824,-1949696]),(⟨2,0,0⟩,[256,-12288,202496,-1784576,9864448,-36746496,94947584,-170816000,216711936,-229486080,320704768,-535761664,634627840,-410889472,102145792]),(⟨2,0,1⟩,[0,-1536,37120,-403200,2547456,-10130176,25809408,-41582080,43875840,-53373952,127032576,-239491840,240280320,-100891392]),(⟨2,0,2⟩,[-256,7168,-85248,570880,-2349056,6010880,-9100800,7117824,-3835136,9870336,-17437952,10010112,1580544]),(⟨2,0,3⟩,[0,2048,-41472,370176,-1854464,5520384,-9533440,8814592,-6554624,15576064,-26940928,17787392]),(⟨2,1,0⟩,[0,-1536,37120,-403200,2547456,-10130176,25809408,-41582080,43875840,-53373952,127032576,-239491840,240280320,-100891392]),(⟨2,1,1⟩,[0,0,0,0,-4096,90112,-786432,3432448,-6840320,-57344,24772608,-41345024,23883776]),(⟨2,2,0⟩,[-256,7168,-85248,570880,-2349056,6010880,-9100800,7117824,-3835136,9870336,-17437952,10010112,1580544]),(⟨2,3,0⟩,[0,2048,-41472,370176,-1854464,5520384,-9533440,8814592,-6554624,15576064,-26940928,17787392]),(⟨2,6,0⟩,[1024,-18432,113664,-301056,271360,174080,103424,-1001472,-129024]),(⟨2,8,2⟩,[-4096,49152,-122880,-147456,487424]),(⟨3,0,0⟩,[-2304,54016,-542208,3099648,-11091200,25157888,-34137088,23355392,-10484480,34913536,-61732352,480256,91939072,-67301632]),(⟨3,0,1⟩,[0,9216,-164352,1263616,-5493248,14804992,-25611264,30392320,-33983488,50459648,-65417728,47577088,-10691072]),(⟨3,0,2⟩,[1536,-33280,281600,-1257472,3244032,-4716544,3431424,-1909760,5339648,-9373184,4282368,709632]),(⟨3,0,3⟩,[0,-12288,171008,-985088,2998272,-4970496,4294656,-3340288,8339456,-14481408,7986176]),(⟨3,1,0⟩,[0,9216,-164352,1263616,-5493248,14804992,-25611264,30392320,-33983488,50459648,-65417728,47577088,-10691072]),(⟨3,1,1⟩,[0,0,0,0,24576,-385024,1974272,-3776512,-417792,13623296,-21766144,10723328]),(⟨3,2,0⟩,[1536,-33280,281600,-1257472,3244032,-4716544,3431424,-1909760,5339648,-9373184,4282368,709632]),(⟨3,2,2⟩,[3072,-58368,417792,-1466368,2459648,-145408,-8134656,17260544,-16307200,5970944]),(⟨3,3,0⟩,[0,-12288,171008,-985088,2998272,-4970496,4294656,-3340288,8339456,-14481408,7986176]),(⟨3,6,0⟩,[0,-8192,83968,-296960,348160,151552,124928,-1452032]),(⟨4,0,0⟩,[-256,22528,-355584,2633216,-11285504,30060544,-50327040,53455872,-50187520,87787520,-152323328,143660544,-50781696]),(⟨4,0,1⟩,[0,0,0,0,24576,-385024,1974272,-3776512,-417792,13623296,-21766144,10723328]),(⟨4,1,0⟩,[0,0,0,0,24576,-385024,1974272,-3776512,-417792,13623296,-21766144,10723328]),(⟨4,2,2⟩,[1024,-22528,196608,-858112,1710080,14336,-6193152,10336256,-5970944]),(⟨5,0,0⟩,[1536,-31232,240128,-887296,1389568,803840,-6102016,6904832,-1214976,6202880,-22658560,18497024]),(⟨5,2,2⟩,[-6144,96256,-493568,944128,104448,-3405824,5441536,-2680832]),(⟨6,0,0⟩,[-1024,8192,-1024,-185344,817152,-1766400,2463744,-2325504,1600512,-4447232,5934080]),(⟨6,0,1⟩,[0,6144,-87040,484352,-1309696,1620992,-535552,941056,-5309440,6286336]),(⟨6,0,2⟩,[1024,-18432,113664,-301056,271360,174080,103424,-1001472,-129024]),(⟨6,0,3⟩,[0,-8192,83968,-296960,348160,151552,124928,-1452032]),(⟨6,1,0⟩,[0,6144,-87040,484352,-1309696,1620992,-535552,941056,-5309440,6286336]),(⟨6,1,1⟩,[0,0,0,0,16384,-196608,491520,589824,-1949696]),(⟨6,2,0⟩,[1024,-18432,113664,-301056,271360,174080,103424,-1001472,-129024]),(⟨6,3,0⟩,[0,-8192,83968,-296960,348160,151552,124928,-1452032]),(⟨7,0,0⟩,[0,6144,-87040,484352,-1309696,1620992,-535552,941056,-5309440,6286336]),(⟨7,0,1⟩,[0,0,0,0,16384,-196608,491520,589824,-1949696]),(⟨7,1,0⟩,[0,0,0,0,16384,-196608,491520,589824,-1949696]),(⟨8,0,0⟩,[1024,-18432,113664,-301056,271360,174080,103424,-1001472,-129024]),(⟨8,2,2⟩,[-4096,49152,-122880,-147456,487424]),(⟨9,0,0⟩,[0,-8192,83968,-296960,348160,151552,124928,-1452032])]


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

noncomputable def partial4 : Poly := [(⟨0,0,6⟩,[-1024,20480,-172032,799744,-2181120,3204096,-1830912,1014784,-6738944,10034176,-2052096]),(⟨0,0,7⟩,[0,6144,-87040,484352,-1309696,1620992,-535552,941056,-5309440,6286336]),(⟨0,0,8⟩,[1024,-18432,113664,-301056,271360,174080,103424,-1001472,-129024]),(⟨0,0,9⟩,[0,-8192,83968,-296960,348160,151552,124928,-1452032]),(⟨0,1,0⟩,[768,-20736,253440,-1871104,9307648,-32746496,83144448,-153483776,209797888,-235701504,289067008,-427754752,542782464,-441605632,183968512,-25138176]),(⟨0,1,1⟩,[0,-4608,97536,-921600,5142528,-18833920,47474944,-84375552,110475264,-128183808,184160000,-294909952,354930688,-252059136,77007616]),(⟨0,1,2⟩,[-768,19200,-198912,1156864,-4233728,10175488,-16129536,16775680,-13492992,17043200,-28358912,27254528,-8429568,-1580544]),(⟨0,1,3⟩,[0,6144,-105984,798720,-3447296,9334784,-16401408,19378176,-19209216,27400192,-44695040,44728320,-17787392]),(⟨0,1,6⟩,[0,6144,-87040,484352,-1309696,1620992,-535552,941056,-5309440,6286336]),(⟨0,1,7⟩,[0,0,0,0,16384,-196608,491520,589824,-1949696]),(⟨0,2,0⟩,[256,-12288,202496,-1784576,9864448,-36746496,94947584,-170816000,216711936,-229486080,320704768,-535761664,634627840,-410889472,102145792]),(⟨0,2,1⟩,[0,-1536,37120,-403200,2547456,-10130176,25809408,-41582080,43875840,-53373952,127032576,-239491840,240280320,-100891392]),(⟨0,2,2⟩,[-256,7168,-85248,570880,-2349056,6010880,-9100800,7117824,-3835136,9870336,-17437952,10010112,1580544]),(⟨0,2,3⟩,[0,2048,-41472,370176,-1854464,5520384,-9533440,8814592,-6554624,15576064,-26940928,17787392]),(⟨0,2,6⟩,[1024,-18432,113664,-301056,271360,174080,103424,-1001472,-129024]),(⟨0,3,0⟩,[-2304,54016,-542208,3099648,-11091200,25157888,-34137088,23355392,-10484480,34913536,-61732352,480256,91939072,-67301632]),(⟨0,3,1⟩,[0,9216,-164352,1263616,-5493248,14804992,-25611264,30392320,-33983488,50459648,-65417728,47577088,-10691072]),(⟨0,3,2⟩,[1536,-33280,281600,-1257472,3244032,-4716544,3431424,-1909760,5339648,-9373184,4282368,709632]),(⟨0,3,3⟩,[0,-12288,171008,-985088,2998272,-4970496,4294656,-3340288,8339456,-14481408,7986176]),(⟨0,3,6⟩,[0,-8192,83968,-296960,348160,151552,124928,-1452032]),(⟨0,4,0⟩,[-256,22528,-355584,2633216,-11285504,30060544,-50327040,53455872,-50187520,87787520,-152323328,143660544,-50781696]),(⟨0,4,1⟩,[0,0,0,0,24576,-385024,1974272,-3776512,-417792,13623296,-21766144,10723328]),(⟨0,5,0⟩,[1536,-31232,240128,-887296,1389568,803840,-6102016,6904832,-1214976,6202880,-22658560,18497024]),(⟨0,6,0⟩,[-1024,8192,-1024,-185344,817152,-1766400,2463744,-2325504,1600512,-4447232,5934080]),(⟨0,6,1⟩,[0,6144,-87040,484352,-1309696,1620992,-535552,941056,-5309440,6286336]),(⟨0,6,2⟩,[1024,-18432,113664,-301056,271360,174080,103424,-1001472,-129024]),(⟨0,6,3⟩,[0,-8192,83968,-296960,348160,151552,124928,-1452032]),(⟨0,7,0⟩,[0,6144,-87040,484352,-1309696,1620992,-535552,941056,-5309440,6286336]),(⟨0,7,1⟩,[0,0,0,0,16384,-196608,491520,589824,-1949696]),(⟨0,8,0⟩,[1024,-18432,113664,-301056,271360,174080,103424,-1001472,-129024]),(⟨0,9,0⟩,[0,-8192,83968,-296960,348160,151552,124928,-1452032]),(⟨1,0,0⟩,[768,-20736,253440,-1871104,9307648,-32746496,83144448,-153483776,209797888,-235701504,289067008,-427754752,542782464,-441605632,183968512,-25138176]),(⟨1,0,1⟩,[0,-4608,97536,-921600,5142528,-18833920,47474944,-84375552,110475264,-128183808,184160000,-294909952,354930688,-252059136,77007616]),(⟨1,0,2⟩,[-768,19200,-198912,1156864,-4233728,10175488,-16129536,16775680,-13492992,17043200,-28358912,27254528,-8429568,-1580544]),(⟨1,0,3⟩,[0,6144,-105984,798720,-3447296,9334784,-16401408,19378176,-19209216,27400192,-44695040,44728320,-17787392]),(⟨1,0,6⟩,[0,6144,-87040,484352,-1309696,1620992,-535552,941056,-5309440,6286336]),(⟨1,0,7⟩,[0,0,0,0,16384,-196608,491520,589824,-1949696]),(⟨1,1,0⟩,[0,-9216,195072,-1843200,10285056,-37667840,94949888,-168751104,220950528,-256367616,368320000,-589819904,709861376,-504118272,154015232]),(⟨1,1,1⟩,[0,0,0,0,-24576,466944,-3342336,11730944,-19677184,1163264,65077248,-138084352,130457600,-47767552]),(⟨1,1,6⟩,[0,0,0,0,16384,-196608,491520,589824,-1949696]),(⟨1,2,0⟩,[-768,17664,-161792,753664,-1686272,45312,9679872,-24806400,30382848,-36330752,98673664,-212237312,231850752,-102471936]),(⟨1,2,1⟩,[0,0,0,0,-4096,90112,-786432,3432448,-6840320,-57344,24772608,-41345024,23883776]),(⟨1,3,0⟩,[0,15360,-270336,2062336,-8940544,24139776,-42012672,49770496,-53192704,77859840,-110112768,92305408,-28478464]),(⟨1,3,1⟩,[0,0,0,0,24576,-385024,1974272,-3776512,-417792,13623296,-21766144,10723328]),(⟨1,4,0⟩,[0,0,0,0,24576,-385024,1974272,-3776512,-417792,13623296,-21766144,10723328]),(⟨1,6,0⟩,[0,6144,-87040,484352,-1309696,1620992,-535552,941056,-5309440,6286336]),(⟨1,6,1⟩,[0,0,0,0,16384,-196608,491520,589824,-1949696]),(⟨1,7,0⟩,[0,0,0,0,16384,-196608,491520,589824,-1949696]),(⟨2,0,0⟩,[256,-12288,202496,-1784576,9864448,-36746496,94947584,-170816000,216711936,-229486080,320704768,-535761664,634627840,-410889472,102145792]),(⟨2,0,1⟩,[0,-1536,37120,-403200,2547456,-10130176,25809408,-41582080,43875840,-53373952,127032576,-239491840,240280320,-100891392]),(⟨2,0,2⟩,[-256,7168,-85248,570880,-2349056,6010880,-9100800,7117824,-3835136,9870336,-17437952,10010112,1580544]),(⟨2,0,3⟩,[0,2048,-41472,370176,-1854464,5520384,-9533440,8814592,-6554624,15576064,-26940928,17787392]),(⟨2,0,6⟩,[1024,-18432,113664,-301056,271360,174080,103424,-1001472,-129024]),(⟨2,1,0⟩,[-768,17664,-161792,753664,-1686272,45312,9679872,-24806400,30382848,-36330752,98673664,-212237312,231850752,-102471936]),(⟨2,1,1⟩,[0,0,0,0,-4096,90112,-786432,3432448,-6840320,-57344,24772608,-41345024,23883776]),(⟨2,2,0⟩,[-512,14336,-170496,1141760,-4698112,12021760,-18201600,14235648,-7670272,19740672,-34875904,20020224,3161088]),(⟨2,2,8⟩,[-4096,49152,-122880,-147456,487424]),(⟨2,3,0⟩,[1536,-31232,240128,-887296,1389568,803840,-6102016,6904832,-1214976,6202880,-22658560,18497024]),(⟨2,3,2⟩,[3072,-58368,417792,-1466368,2459648,-145408,-8134656,17260544,-16307200,5970944]),(⟨2,4,2⟩,[1024,-22528,196608,-858112,1710080,14336,-6193152,10336256,-5970944]),(⟨2,5,2⟩,[-6144,96256,-493568,944128,104448,-3405824,5441536,-2680832]),(⟨2,6,0⟩,[1024,-18432,113664,-301056,271360,174080,103424,-1001472,-129024]),(⟨2,8,2⟩,[-4096,49152,-122880,-147456,487424]),(⟨3,0,0⟩,[-2304,54016,-542208,3099648,-11091200,25157888,-34137088,23355392,-10484480,34913536,-61732352,480256,91939072,-67301632]),(⟨3,0,1⟩,[0,9216,-164352,1263616,-5493248,14804992,-25611264,30392320,-33983488,50459648,-65417728,47577088,-10691072]),(⟨3,0,2⟩,[1536,-33280,281600,-1257472,3244032,-4716544,3431424,-1909760,5339648,-9373184,4282368,709632]),(⟨3,0,3⟩,[0,-12288,171008,-985088,2998272,-4970496,4294656,-3340288,8339456,-14481408,7986176]),(⟨3,0,6⟩,[0,-8192,83968,-296960,348160,151552,124928,-1452032]),(⟨3,1,0⟩,[0,15360,-270336,2062336,-8940544,24139776,-42012672,49770496,-53192704,77859840,-110112768,92305408,-28478464]),(⟨3,1,1⟩,[0,0,0,0,24576,-385024,1974272,-3776512,-417792,13623296,-21766144,10723328]),(⟨3,2,0⟩,[1536,-31232,240128,-887296,1389568,803840,-6102016,6904832,-1214976,6202880,-22658560,18497024]),(⟨3,2,2⟩,[3072,-58368,417792,-1466368,2459648,-145408,-8134656,17260544,-16307200,5970944]),(⟨3,3,0⟩,[0,-24576,342016,-1970176,5996544,-9940992,8589312,-6680576,16678912,-28962816,15972352]),(⟨3,6,0⟩,[0,-8192,83968,-296960,348160,151552,124928,-1452032]),(⟨4,0,0⟩,[-256,22528,-355584,2633216,-11285504,30060544,-50327040,53455872,-50187520,87787520,-152323328,143660544,-50781696]),(⟨4,0,1⟩,[0,0,0,0,24576,-385024,1974272,-3776512,-417792,13623296,-21766144,10723328]),(⟨4,1,0⟩,[0,0,0,0,24576,-385024,1974272,-3776512,-417792,13623296,-21766144,10723328]),(⟨4,2,2⟩,[1024,-22528,196608,-858112,1710080,14336,-6193152,10336256,-5970944]),(⟨5,0,0⟩,[1536,-31232,240128,-887296,1389568,803840,-6102016,6904832,-1214976,6202880,-22658560,18497024]),(⟨5,2,2⟩,[-6144,96256,-493568,944128,104448,-3405824,5441536,-2680832]),(⟨6,0,0⟩,[-1024,8192,-1024,-185344,817152,-1766400,2463744,-2325504,1600512,-4447232,5934080]),(⟨6,0,1⟩,[0,6144,-87040,484352,-1309696,1620992,-535552,941056,-5309440,6286336]),(⟨6,0,2⟩,[1024,-18432,113664,-301056,271360,174080,103424,-1001472,-129024]),(⟨6,0,3⟩,[0,-8192,83968,-296960,348160,151552,124928,-1452032]),(⟨6,1,0⟩,[0,6144,-87040,484352,-1309696,1620992,-535552,941056,-5309440,6286336]),(⟨6,1,1⟩,[0,0,0,0,16384,-196608,491520,589824,-1949696]),(⟨6,2,0⟩,[1024,-18432,113664,-301056,271360,174080,103424,-1001472,-129024]),(⟨6,3,0⟩,[0,-8192,83968,-296960,348160,151552,124928,-1452032]),(⟨7,0,0⟩,[0,6144,-87040,484352,-1309696,1620992,-535552,941056,-5309440,6286336]),(⟨7,0,1⟩,[0,0,0,0,16384,-196608,491520,589824,-1949696]),(⟨7,1,0⟩,[0,0,0,0,16384,-196608,491520,589824,-1949696]),(⟨8,0,0⟩,[1024,-18432,113664,-301056,271360,174080,103424,-1001472,-129024]),(⟨8,2,2⟩,[-4096,49152,-122880,-147456,487424]),(⟨9,0,0⟩,[0,-8192,83968,-296960,348160,151552,124928,-1452032])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,-2304,61440,-732672,5189376,-24192768,77038848,-167505408,242511360,-236007168,232856064,-420788736,663644928,-525234432,74916096,118531584,-27703296]),(⟨0,0,1⟩,[768,-20736,267264,-2159104,11933440,-46471424,128176128,-248368640,336599296,-351763200,435524608,-741801472,994086144,-727300864,164153344,59727360]),(⟨0,0,2⟩,[256,-9984,145664,-1213952,6749440,-26602752,75237632,-150136832,207495936,-219751680,285995776,-496837120,632987392,-425473792,100403968]),(⟨0,0,3⟩,[-2304,54016,-560640,3411456,-13326080,33876224,-53622784,47028224,-25359104,54104320,-115292672,62364160,81646336,-86904064]),(⟨0,0,4⟩,[-256,22528,-355584,2633216,-11285504,30060544,-50327040,53455872,-50187520,87787520,-152323328,143660544,-50781696]),(⟨0,0,5⟩,[1536,-31232,240128,-887296,1389568,803840,-6102016,6904832,-1214976,6202880,-22658560,18497024]),(⟨0,0,6⟩,[-1024,8192,-1024,-185344,817152,-1766400,2463744,-2325504,1600512,-4447232,5934080]),(⟨0,0,7⟩,[0,6144,-87040,484352,-1309696,1620992,-535552,941056,-5309440,6286336]),(⟨0,0,8⟩,[1024,-18432,113664,-301056,271360,174080,103424,-1001472,-129024]),(⟨0,0,9⟩,[0,-8192,83968,-296960,348160,151552,124928,-1452032]),(⟨0,1,0⟩,[768,-20736,267264,-2159104,11933440,-46471424,128176128,-248368640,336599296,-351763200,435524608,-741801472,994086144,-727300864,164153344,59727360]),(⟨0,1,1⟩,[0,-9216,195072,-1843200,10285056,-37630976,94261760,-164081664,206868480,-243072000,398376448,-685420544,800325632,-512240640,127694336]),(⟨0,1,2⟩,[-768,17664,-161792,753664,-1686272,45312,9679872,-24806400,30382848,-36330752,98673664,-212237312,231850752,-102471936]),(⟨0,1,3⟩,[0,15360,-270336,2062336,-8940544,24139776,-42012672,49770496,-53192704,77859840,-110112768,92305408,-28478464]),(⟨0,1,4⟩,[0,0,0,0,24576,-385024,1974272,-3776512,-417792,13623296,-21766144,10723328]),(⟨0,1,6⟩,[0,6144,-87040,484352,-1309696,1620992,-535552,941056,-5309440,6286336]),(⟨0,1,7⟩,[0,0,0,0,16384,-196608,491520,589824,-1949696]),(⟨0,2,0⟩,[256,-9984,145664,-1213952,6749440,-26602752,75237632,-150136832,207495936,-219751680,285995776,-496837120,632987392,-425473792,100403968]),(⟨0,2,1⟩,[-768,17664,-161792,753664,-1686272,45312,9679872,-24806400,30382848,-36330752,98673664,-212237312,231850752,-102471936]),(⟨0,2,2⟩,[-512,14336,-170496,1141760,-4698112,12021760,-18201600,14235648,-7670272,19740672,-34875904,20020224,3161088]),(⟨0,2,3⟩,[1536,-31232,240128,-887296,1389568,803840,-6102016,6904832,-1214976,6202880,-22658560,18497024]),(⟨0,2,6⟩,[1024,-18432,113664,-301056,271360,174080,103424,-1001472,-129024]),(⟨0,3,0⟩,[-2304,54016,-560640,3411456,-13326080,33876224,-53622784,47028224,-25359104,54104320,-115292672,62364160,81646336,-86904064]),(⟨0,3,1⟩,[0,15360,-270336,2062336,-8940544,24139776,-42012672,49770496,-53192704,77859840,-110112768,92305408,-28478464]),(⟨0,3,2⟩,[1536,-31232,240128,-887296,1389568,803840,-6102016,6904832,-1214976,6202880,-22658560,18497024]),(⟨0,3,3⟩,[0,-24576,342016,-1970176,5996544,-9940992,8589312,-6680576,16678912,-28962816,15972352]),(⟨0,3,6⟩,[0,-8192,83968,-296960,348160,151552,124928,-1452032]),(⟨0,4,0⟩,[-256,22528,-355584,2633216,-11285504,30060544,-50327040,53455872,-50187520,87787520,-152323328,143660544,-50781696]),(⟨0,4,1⟩,[0,0,0,0,24576,-385024,1974272,-3776512,-417792,13623296,-21766144,10723328]),(⟨0,5,0⟩,[1536,-31232,240128,-887296,1389568,803840,-6102016,6904832,-1214976,6202880,-22658560,18497024]),(⟨0,6,0⟩,[-1024,8192,-1024,-185344,817152,-1766400,2463744,-2325504,1600512,-4447232,5934080]),(⟨0,6,1⟩,[0,6144,-87040,484352,-1309696,1620992,-535552,941056,-5309440,6286336]),(⟨0,6,2⟩,[1024,-18432,113664,-301056,271360,174080,103424,-1001472,-129024]),(⟨0,6,3⟩,[0,-8192,83968,-296960,348160,151552,124928,-1452032]),(⟨0,7,0⟩,[0,6144,-87040,484352,-1309696,1620992,-535552,941056,-5309440,6286336]),(⟨0,7,1⟩,[0,0,0,0,16384,-196608,491520,589824,-1949696]),(⟨0,8,0⟩,[1024,-18432,113664,-301056,271360,174080,103424,-1001472,-129024]),(⟨0,9,0⟩,[0,-8192,83968,-296960,348160,151552,124928,-1452032]),(⟨1,0,0⟩,[768,-20736,267264,-2159104,11933440,-46471424,128176128,-248368640,336599296,-351763200,435524608,-741801472,994086144,-727300864,164153344,59727360]),(⟨1,0,1⟩,[0,-9216,195072,-1843200,10285056,-37630976,94261760,-164081664,206868480,-243072000,398376448,-685420544,800325632,-512240640,127694336]),(⟨1,0,2⟩,[-768,17664,-161792,753664,-1686272,45312,9679872,-24806400,30382848,-36330752,98673664,-212237312,231850752,-102471936]),(⟨1,0,3⟩,[0,15360,-270336,2062336,-8940544,24139776,-42012672,49770496,-53192704,77859840,-110112768,92305408,-28478464]),(⟨1,0,4⟩,[0,0,0,0,24576,-385024,1974272,-3776512,-417792,13623296,-21766144,10723328]),(⟨1,0,6⟩,[0,6144,-87040,484352,-1309696,1620992,-535552,941056,-5309440,6286336]),(⟨1,0,7⟩,[0,0,0,0,16384,-196608,491520,589824,-1949696]),(⟨1,1,0⟩,[0,-9216,195072,-1843200,10285056,-37630976,94261760,-164081664,206868480,-243072000,398376448,-685420544,800325632,-512240640,127694336]),(⟨1,1,1⟩,[0,0,0,0,-36864,700416,-5013504,17596416,-29515776,1744896,97615872,-207126528,195686400,-71651328]),(⟨1,1,2⟩,[0,0,0,0,-4096,90112,-786432,3432448,-6840320,-57344,24772608,-41345024,23883776]),(⟨1,1,3⟩,[0,0,0,0,24576,-385024,1974272,-3776512,-417792,13623296,-21766144,10723328]),(⟨1,1,6⟩,[0,0,0,0,16384,-196608,491520,589824,-1949696]),(⟨1,2,0⟩,[-768,17664,-161792,753664,-1686272,45312,9679872,-24806400,30382848,-36330752,98673664,-212237312,231850752,-102471936]),(⟨1,2,1⟩,[0,0,0,0,-4096,90112,-786432,3432448,-6840320,-57344,24772608,-41345024,23883776]),(⟨1,3,0⟩,[0,15360,-270336,2062336,-8940544,24139776,-42012672,49770496,-53192704,77859840,-110112768,92305408,-28478464]),(⟨1,3,1⟩,[0,0,0,0,24576,-385024,1974272,-3776512,-417792,13623296,-21766144,10723328]),(⟨1,4,0⟩,[0,0,0,0,24576,-385024,1974272,-3776512,-417792,13623296,-21766144,10723328]),(⟨1,6,0⟩,[0,6144,-87040,484352,-1309696,1620992,-535552,941056,-5309440,6286336]),(⟨1,6,1⟩,[0,0,0,0,16384,-196608,491520,589824,-1949696]),(⟨1,7,0⟩,[0,0,0,0,16384,-196608,491520,589824,-1949696]),(⟨2,0,0⟩,[256,-9984,145664,-1213952,6749440,-26602752,75237632,-150136832,207495936,-219751680,285995776,-496837120,632987392,-425473792,100403968]),(⟨2,0,1⟩,[-768,17664,-161792,753664,-1686272,45312,9679872,-24806400,30382848,-36330752,98673664,-212237312,231850752,-102471936]),(⟨2,0,2⟩,[-512,14336,-170496,1141760,-4698112,12021760,-18201600,14235648,-7670272,19740672,-34875904,20020224,3161088]),(⟨2,0,3⟩,[1536,-31232,240128,-887296,1389568,803840,-6102016,6904832,-1214976,6202880,-22658560,18497024]),(⟨2,0,6⟩,[1024,-18432,113664,-301056,271360,174080,103424,-1001472,-129024]),(⟨2,1,0⟩,[-768,17664,-161792,753664,-1686272,45312,9679872,-24806400,30382848,-36330752,98673664,-212237312,231850752,-102471936]),(⟨2,1,1⟩,[0,0,0,0,-4096,90112,-786432,3432448,-6840320,-57344,24772608,-41345024,23883776]),(⟨2,2,0⟩,[-512,14336,-170496,1141760,-4698112,12021760,-18201600,14235648,-7670272,19740672,-34875904,20020224,3161088]),(⟨2,2,2⟩,[0,-9216,172032,-1167360,3520512,-3323904,-7514112,23900160,-22616064,2030592,6580224]),(⟨2,2,3⟩,[3072,-58368,417792,-1466368,2459648,-145408,-8134656,17260544,-16307200,5970944]),(⟨2,2,4⟩,[1024,-22528,196608,-858112,1710080,14336,-6193152,10336256,-5970944]),(⟨2,2,5⟩,[-6144,96256,-493568,944128,104448,-3405824,5441536,-2680832]),(⟨2,2,8⟩,[-4096,49152,-122880,-147456,487424]),(⟨2,3,0⟩,[1536,-31232,240128,-887296,1389568,803840,-6102016,6904832,-1214976,6202880,-22658560,18497024]),(⟨2,3,2⟩,[3072,-58368,417792,-1466368,2459648,-145408,-8134656,17260544,-16307200,5970944]),(⟨2,4,2⟩,[1024,-22528,196608,-858112,1710080,14336,-6193152,10336256,-5970944]),(⟨2,5,2⟩,[-6144,96256,-493568,944128,104448,-3405824,5441536,-2680832]),(⟨2,6,0⟩,[1024,-18432,113664,-301056,271360,174080,103424,-1001472,-129024]),(⟨2,8,2⟩,[-4096,49152,-122880,-147456,487424]),(⟨3,0,0⟩,[-2304,54016,-560640,3411456,-13326080,33876224,-53622784,47028224,-25359104,54104320,-115292672,62364160,81646336,-86904064]),(⟨3,0,1⟩,[0,15360,-270336,2062336,-8940544,24139776,-42012672,49770496,-53192704,77859840,-110112768,92305408,-28478464]),(⟨3,0,2⟩,[1536,-31232,240128,-887296,1389568,803840,-6102016,6904832,-1214976,6202880,-22658560,18497024]),(⟨3,0,3⟩,[0,-24576,342016,-1970176,5996544,-9940992,8589312,-6680576,16678912,-28962816,15972352]),(⟨3,0,6⟩,[0,-8192,83968,-296960,348160,151552,124928,-1452032]),(⟨3,1,0⟩,[0,15360,-270336,2062336,-8940544,24139776,-42012672,49770496,-53192704,77859840,-110112768,92305408,-28478464]),(⟨3,1,1⟩,[0,0,0,0,24576,-385024,1974272,-3776512,-417792,13623296,-21766144,10723328]),(⟨3,2,0⟩,[1536,-31232,240128,-887296,1389568,803840,-6102016,6904832,-1214976,6202880,-22658560,18497024]),(⟨3,2,2⟩,[3072,-58368,417792,-1466368,2459648,-145408,-8134656,17260544,-16307200,5970944]),(⟨3,3,0⟩,[0,-24576,342016,-1970176,5996544,-9940992,8589312,-6680576,16678912,-28962816,15972352]),(⟨3,6,0⟩,[0,-8192,83968,-296960,348160,151552,124928,-1452032]),(⟨4,0,0⟩,[-256,22528,-355584,2633216,-11285504,30060544,-50327040,53455872,-50187520,87787520,-152323328,143660544,-50781696]),(⟨4,0,1⟩,[0,0,0,0,24576,-385024,1974272,-3776512,-417792,13623296,-21766144,10723328]),(⟨4,1,0⟩,[0,0,0,0,24576,-385024,1974272,-3776512,-417792,13623296,-21766144,10723328]),(⟨4,2,2⟩,[1024,-22528,196608,-858112,1710080,14336,-6193152,10336256,-5970944]),(⟨5,0,0⟩,[1536,-31232,240128,-887296,1389568,803840,-6102016,6904832,-1214976,6202880,-22658560,18497024]),(⟨5,2,2⟩,[-6144,96256,-493568,944128,104448,-3405824,5441536,-2680832]),(⟨6,0,0⟩,[-1024,8192,-1024,-185344,817152,-1766400,2463744,-2325504,1600512,-4447232,5934080]),(⟨6,0,1⟩,[0,6144,-87040,484352,-1309696,1620992,-535552,941056,-5309440,6286336]),(⟨6,0,2⟩,[1024,-18432,113664,-301056,271360,174080,103424,-1001472,-129024]),(⟨6,0,3⟩,[0,-8192,83968,-296960,348160,151552,124928,-1452032]),(⟨6,1,0⟩,[0,6144,-87040,484352,-1309696,1620992,-535552,941056,-5309440,6286336]),(⟨6,1,1⟩,[0,0,0,0,16384,-196608,491520,589824,-1949696]),(⟨6,2,0⟩,[1024,-18432,113664,-301056,271360,174080,103424,-1001472,-129024]),(⟨6,3,0⟩,[0,-8192,83968,-296960,348160,151552,124928,-1452032]),(⟨7,0,0⟩,[0,6144,-87040,484352,-1309696,1620992,-535552,941056,-5309440,6286336]),(⟨7,0,1⟩,[0,0,0,0,16384,-196608,491520,589824,-1949696]),(⟨7,1,0⟩,[0,0,0,0,16384,-196608,491520,589824,-1949696]),(⟨8,0,0⟩,[1024,-18432,113664,-301056,271360,174080,103424,-1001472,-129024]),(⟨8,2,2⟩,[-4096,49152,-122880,-147456,487424]),(⟨9,0,0⟩,[0,-8192,83968,-296960,348160,151552,124928,-1452032])]


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
    (Poly.add (Poly.scale (K.ofRat r477) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 2 13).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r475*r476 : ℚ)=r477 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 2 13 r475 r476 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 2=13 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 2 13).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C083

#print axioms Coulomb8.Columns.C083.sound
