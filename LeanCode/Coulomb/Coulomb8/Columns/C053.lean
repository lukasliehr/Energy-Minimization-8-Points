import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C053

def r0 : ℚ := { num := -576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 14880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -169920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 1169568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -790272, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 19125312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -49371648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 94376640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -128779968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 115519008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -53224512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -5412192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 15894528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -1839744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -5248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 66112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -74048, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 2848064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := -11600768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := 35938304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := -85002496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := 8898752, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := -195866368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := 172751296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := -88562240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := 11753792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 8491776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := 32, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -5696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 64576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -462528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 2400480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -9443072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 28558336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -66258432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 115216160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -143686848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 119959488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -57930048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 1388512, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 12864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -124736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 719424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -2802944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 7703296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -14657280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 16998144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -5659328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := -15274816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := 3661248, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := -14377792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 18176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -187360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 1132928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -664512, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 13678464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -28929856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 42809472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -41977056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 1435520, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -5247712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -4160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 11136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := 4736, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := -772608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := 3307008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := -8622976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 14005632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -13643584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := 955328, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -12160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 96896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -432000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 1312512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -2650752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 3297664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -2463360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 36544, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := 128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := -3712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := 33920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := -163456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := 531840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := -1113984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := 1334656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -881536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -2816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := 44672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := -389632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := 2213824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -9009152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 27669760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -65019392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 16417856, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := -147406080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := 128892032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -67219456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 2073536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 3904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -32448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 20800, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := -331136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -198528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 4426368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := -2397056, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 35744320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -47337408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 5354944, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -2024896, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := -128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := 4736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := -61952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := 445440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := -297728, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := 6751488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := -15261696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := 23595008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := -23776896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := 13898880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := -2986496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 2496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := -4224, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := 181120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -767488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 2496768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := -5804160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := 9008256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -8635840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 581824, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := 2048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := -4096, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 116736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -122880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := -206848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := 708608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := -64, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := 10112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := -95680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := 529920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := -1970560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 730880, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -540544, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 10677760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -6671552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 98432, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := 260288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := -6656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 42752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -131328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := 140288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 570624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -170752, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 5912832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := -379264, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := 477952, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 64, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -512, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 9344, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -265728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := 662528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := -929280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := 601728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := -137728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -24128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -128, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 12672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -29056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := 3968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 98432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := -160128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -2048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := 640, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := -3072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -6784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 13312, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 3328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := -1536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := -1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := 39680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := 3072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -7680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := -9216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := 256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 10752, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := -394752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := 198656, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := -3291648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := 4897280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := -4432384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := 1763072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := -5888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := 6656, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -192512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 76544, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := -1015552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 1174528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -805376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -4096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := 1280, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := -6144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -13568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := 26624, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := -3072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := 58368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := -24576, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -141312, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -79872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 8282112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := -2371584, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 15184896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -1024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := 18432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 395264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := -550912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -337920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 147456, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -563200, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := -30720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := 145408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := -239616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := -83968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := 915456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := -1439744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := -512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := 6144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := -15360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -18432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := -288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := 7440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -84960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 584784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := -395136, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := 9562656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := -24685824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := 47188320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := -64389984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := 57759504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := -26612256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := -2706096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := 7947264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := -919872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := 96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -2624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := 33056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := -37024, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 1424032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -5800384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := 17969152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -42501248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := 4449376, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -97933184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 86375648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -44281120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := 5876896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := 4245888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := 16, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -2848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := 32288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := -231264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := 1200240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := -4721536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := 14279168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := -33129216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := 57608080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := -71843424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := 59979744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := -28965024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := 694256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := 6432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := -62368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := 359712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := -1401472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := 3851648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := -7328640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := 8499072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := -2829664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := -7637408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := 1830624, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := -7188896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := 9088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -93680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 566464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -332256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 6839232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -14464928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := 21404736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := -20988528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := 717760, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := -2623856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := 160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := -2080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := 5568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := 2368, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := -386304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := 1653504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -4311488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 7002816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -6821792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 477664, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := 288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := -6080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := 48448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := -216000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := 656256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := -1325376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := 1648832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := -1231680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := 18272, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := -1856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := 16960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := -81728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := 265920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := -556992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := 667328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -440768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -1408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 22336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := -194816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := 1106912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -4504576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 13834880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -32509696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 8208928, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -73703040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 64446016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -33609728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 1036768, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := -96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := 1952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := -16224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := 10400, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := -165568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := -99264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := 2213184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := -1198528, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := 17872160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := -23668704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := 2677472, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := -1012448, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := 2368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := -30976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := 222720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := -148864, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := 3375744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := -7630848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := 11797504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -11888448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := 6949440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := -1493248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := -32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := 1248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := -2112, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := 90560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := -383744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := 1248384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := -2902080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := 4504128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := -4317920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := 290912, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := 1024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := -2048, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := -61440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := -103424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := 354304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := -32, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := 5056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := -47840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := 264960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := -985280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := 365440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := -270272, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := 5338880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := -3335776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := 49216, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := 130144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := -3328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := 21376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := -65664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := 70144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := 285312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := -85376, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := 2956416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := -189632, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := 238976, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := -256, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := 4672, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := -132864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := 331264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := -464640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := 300864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := -68864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := -12064, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := -64, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := 6336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := -14528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := 1984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := 49216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := -80064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := 320, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := -3392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := 1664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := -768, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := -768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := 19840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := 1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := -3840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := -4608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := 5376, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := -197376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := 99328, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := -1645824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := 2448640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := -2216192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := 881536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := -2944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := 3328, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := -96256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := 38272, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := -507776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := 587264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := -402688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := 29184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := -12288, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := -70656, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := -39936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := 4141056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := -1185792, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := 7592448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := 9216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := 197632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := -275456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := -168960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := 73728, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := -281600, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := 72704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := -119808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := -41984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := 457728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := -719872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r450 : ℚ := { num := 1, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r451 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r452 : ℚ := { num := 1, den := 476, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13],[r14,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27],[r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40],[r0,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51],[r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62],[r63,r64,r65,r66,r67,r68,r69,r70,r71,r72],[r73,r74,r75,r76,r77,r78,r79,r80,r81],[r82,r83,r84,r85,r86,r87,r88,r89],[],[],[],[],[],[r90,r91,r92,r93,r94,r95,r96,r97,r98,r99,r100,r101,r102],[r103,r104,r105,r106,r107,r108,r109,r110,r111,r112,r113,r114],[r115,r116,r117,r118,r119,r120,r121,r122,r123,r124,r125],[r126,r127,r128,r129,r130,r131,r132,r133,r134,r135],[0,0,r136,r137,r138,r139,r140,r141,-6144],[],[],[],[],[],[],[r142,r143,r144,r145,r146,r147,r148,r149,r150,r151,r152],[r153,r154,r155,r156,r157,r158,r159,r160,r161,r162],[r163,r164,r165,r166,r167,r168,r169,r170,r171],[r82,r172,r173,r174,r175,r176,r177,640],[r82,r178,r179,r180,r181,r182,-896],[r183,r184,r185,r186,r187,-256],[r183,r188,r189,r190,256],[],[],[r191,r189,r192,r193,r194,r195,r196,r197,r198],[r191,r199,r200,r201,r202,r203,r204,r205],[],[],[],[],[],[r191,r206,r207,r208,r209,r210,-1792],[r183,r184,r185,r186,r187,-256],[r183,r188,r189,r190,256],[],[],[],[],[],[],[0,0,r211,r212,r213,12288,r214,r215,r216,r217,r218,-46080],[0,0,r219,r220,r139,r221,r222,r223,r224,r225,21504],[0,0,r136,r226,r227,r228,r229,r230,r231,6144],[0,0,r136,r137,r138,r139,r140,r141,-6144],[],[],[],[],[],[],[],[],[r82,r172,r173,r174,r175,r176,r177,640],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[r191,r206,r207,r208,r209,r210,-1792],[],[],[],[],[],[r183,r184,r185,r186,r187,-256],[],[],[],[r232,r233,r234,r235,512],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,r236,r237,r238,r239,r240,r241,r242,r243,r244,r245,r246,r247,r248,r249]),(⟨0,0,1⟩,[r250,r251,r252,r253,r254,r255,r256,r257,r258,r259,r260,r261,r262,r263]),(⟨0,0,2⟩,[r264,r265,r266,r267,r268,r269,r270,r271,r272,r273,r274,r275,r276]),(⟨0,0,3⟩,[r236,r277,r278,r279,r280,r281,r282,r283,r284,r285,r286,r287]),(⟨0,0,4⟩,[r288,r289,r290,r291,r292,r293,r294,r295,r296,r297,r298]),(⟨0,0,5⟩,[r299,r300,r301,r302,r303,r304,r305,r306,r307,r308]),(⟨0,0,6⟩,[r309,r310,r311,r312,r313,r314,r315,r316,r317]),(⟨0,0,7⟩,[r90,r318,r319,r320,r321,r322,r323,r324]),(⟨0,1,0⟩,[r250,r251,r252,r253,r254,r255,r256,r257,r258,r259,r260,r261,r262,r263]),(⟨0,1,1⟩,[r325,r326,r327,r328,r329,r330,r331,r332,r333,r334,r335,r336,r337]),(⟨0,1,2⟩,[r338,r339,r340,r341,r342,r343,r344,r345,r346,r347,r348,r349]),(⟨0,1,3⟩,[r126,r350,r351,r352,r353,r354,r355,r356,r357,r358,r359]),(⟨0,1,4⟩,[r360,r361,r362,r363,r364,r365,r366,r367,r368,r369]),(⟨0,1,5⟩,[0,0,r370,r371,r212,r372,r373,r374,-3072]),(⟨0,2,0⟩,[r264,r265,r266,r267,r268,r269,r270,r271,r272,r273,r274,r275,r276]),(⟨0,2,1⟩,[r338,r339,r340,r341,r342,r343,r344,r345,r346,r347,r348,r349]),(⟨0,2,2⟩,[r375,r376,r377,r378,r379,r380,r381,r382,r383,r384,r385]),(⟨0,2,3⟩,[r14,r386,r387,r388,r389,r390,r391,r392,r393,r394]),(⟨0,2,4⟩,[r28,r395,r396,r397,r398,r399,r400,r401,r402]),(⟨0,2,5⟩,[r90,r403,r404,r405,r406,r407,r408,320]),(⟨0,2,6⟩,[r90,r219,r409,r185,r410,r200,-448]),(⟨0,2,7⟩,[r115,r411,r412,r413,r414,-128]),(⟨0,2,8⟩,[r115,r415,r416,r417,128]),(⟨0,3,0⟩,[r236,r277,r278,r279,r280,r281,r282,r283,r284,r285,r286,r287]),(⟨0,3,1⟩,[r126,r350,r351,r352,r353,r354,r355,r356,r357,r358,r359]),(⟨0,3,2⟩,[r14,r386,r387,r388,r389,r390,r391,r392,r393,r394]),(⟨0,3,3⟩,[r82,r416,r418,r419,r420,r421,r422,r423,r424]),(⟨0,3,4⟩,[r82,r425,r426,r427,r428,r429,r430,r431]),(⟨0,4,0⟩,[r288,r289,r290,r291,r292,r293,r294,r295,r296,r297,r298]),(⟨0,4,1⟩,[r360,r361,r362,r363,r364,r365,r366,r367,r368,r369]),(⟨0,4,2⟩,[r28,r395,r396,r397,r398,r399,r400,r401,r402]),(⟨0,4,3⟩,[r82,r425,r426,r427,r428,r429,r430,r431]),(⟨0,4,4⟩,[r82,r178,r179,r180,r181,r182,-896]),(⟨0,4,5⟩,[r115,r411,r412,r413,r414,-128]),(⟨0,4,6⟩,[r115,r415,r416,r417,128]),(⟨0,5,0⟩,[r299,r300,r301,r302,r303,r304,r305,r306,r307,r308]),(⟨0,5,1⟩,[0,0,r370,r371,r212,r372,r373,r374,-3072]),(⟨0,5,2⟩,[r90,r403,r404,r405,r406,r407,r408,320]),(⟨0,5,4⟩,[r115,r411,r412,r413,r414,-128]),(⟨0,6,0⟩,[r309,r310,r311,r312,r313,r314,r315,r316,r317]),(⟨0,6,2⟩,[r90,r219,r409,r185,r410,r200,-448]),(⟨0,6,4⟩,[r115,r415,r416,r417,128]),(⟨0,7,0⟩,[r90,r318,r319,r320,r321,r322,r323,r324]),(⟨0,7,2⟩,[r115,r411,r412,r413,r414,-128]),(⟨0,8,2⟩,[r115,r415,r416,r417,128]),(⟨1,0,0⟩,[r250,r251,r252,r253,r254,r255,r256,r257,r258,r259,r260,r261,r262,r263]),(⟨1,0,1⟩,[r325,r326,r327,r328,r329,r330,r331,r332,r333,r334,r335,r336,r337]),(⟨1,0,2⟩,[r338,r339,r340,r341,r342,r343,r344,r345,r346,r347,r348,r349]),(⟨1,0,3⟩,[r126,r350,r351,r352,r353,r354,r355,r356,r357,r358,r359]),(⟨1,0,4⟩,[r360,r361,r362,r363,r364,r365,r366,r367,r368,r369]),(⟨1,0,5⟩,[0,0,r370,r371,r212,r372,r373,r374,-3072]),(⟨1,1,0⟩,[r325,r326,r327,r328,r329,r330,r331,r332,r333,r334,r335,r336,r337]),(⟨1,1,1⟩,[0,0,r186,r432,r433,6144,r434,r435,r436,r437,r438,-23040]),(⟨1,1,2⟩,[0,0,r232,r439,r372,r440,r441,r442,r443,r444,10752]),(⟨1,1,3⟩,[0,0,r370,r234,r445,r446,r447,r448,r449,3072]),(⟨1,1,4⟩,[0,0,r370,r371,r212,r372,r373,r374,-3072]),(⟨1,2,0⟩,[r338,r339,r340,r341,r342,r343,r344,r345,r346,r347,r348,r349]),(⟨1,2,1⟩,[0,0,r232,r439,r372,r440,r441,r442,r443,r444,10752]),(⟨1,2,4⟩,[r90,r403,r404,r405,r406,r407,r408,320]),(⟨1,3,0⟩,[r126,r350,r351,r352,r353,r354,r355,r356,r357,r358,r359]),(⟨1,3,1⟩,[0,0,r370,r234,r445,r446,r447,r448,r449,3072]),(⟨1,4,0⟩,[r360,r361,r362,r363,r364,r365,r366,r367,r368,r369]),(⟨1,4,1⟩,[0,0,r370,r371,r212,r372,r373,r374,-3072]),(⟨1,4,2⟩,[r90,r403,r404,r405,r406,r407,r408,320]),(⟨1,5,0⟩,[0,0,r370,r371,r212,r372,r373,r374,-3072]),(⟨2,0,0⟩,[r264,r265,r266,r267,r268,r269,r270,r271,r272,r273,r274,r275,r276]),(⟨2,0,1⟩,[r338,r339,r340,r341,r342,r343,r344,r345,r346,r347,r348,r349]),(⟨2,0,2⟩,[r375,r376,r377,r378,r379,r380,r381,r382,r383,r384,r385]),(⟨2,0,3⟩,[r14,r386,r387,r388,r389,r390,r391,r392,r393,r394]),(⟨2,0,4⟩,[r28,r395,r396,r397,r398,r399,r400,r401,r402]),(⟨2,0,5⟩,[r90,r403,r404,r405,r406,r407,r408,320]),(⟨2,0,6⟩,[r90,r219,r409,r185,r410,r200,-448]),(⟨2,0,7⟩,[r115,r411,r412,r413,r414,-128]),(⟨2,0,8⟩,[r115,r415,r416,r417,128]),(⟨2,1,0⟩,[r338,r339,r340,r341,r342,r343,r344,r345,r346,r347,r348,r349]),(⟨2,1,1⟩,[0,0,r232,r439,r372,r440,r441,r442,r443,r444,10752]),(⟨2,1,4⟩,[r90,r403,r404,r405,r406,r407,r408,320]),(⟨2,2,0⟩,[r375,r376,r377,r378,r379,r380,r381,r382,r383,r384,r385]),(⟨2,2,4⟩,[r82,r178,r179,r180,r181,r182,-896]),(⟨2,3,0⟩,[r14,r386,r387,r388,r389,r390,r391,r392,r393,r394]),(⟨2,3,4⟩,[r115,r411,r412,r413,r414,-128]),(⟨2,4,0⟩,[r28,r395,r396,r397,r398,r399,r400,r401,r402]),(⟨2,4,1⟩,[r90,r403,r404,r405,r406,r407,r408,320]),(⟨2,4,2⟩,[r82,r178,r179,r180,r181,r182,-896]),(⟨2,4,3⟩,[r115,r411,r412,r413,r414,-128]),(⟨2,4,4⟩,[r183,r188,r189,r190,256]),(⟨2,5,0⟩,[r90,r403,r404,r405,r406,r407,r408,320]),(⟨2,6,0⟩,[r90,r219,r409,r185,r410,r200,-448]),(⟨2,7,0⟩,[r115,r411,r412,r413,r414,-128]),(⟨2,8,0⟩,[r115,r415,r416,r417,128]),(⟨3,0,0⟩,[r236,r277,r278,r279,r280,r281,r282,r283,r284,r285,r286,r287]),(⟨3,0,1⟩,[r126,r350,r351,r352,r353,r354,r355,r356,r357,r358,r359]),(⟨3,0,2⟩,[r14,r386,r387,r388,r389,r390,r391,r392,r393,r394]),(⟨3,0,3⟩,[r82,r416,r418,r419,r420,r421,r422,r423,r424]),(⟨3,0,4⟩,[r82,r425,r426,r427,r428,r429,r430,r431]),(⟨3,1,0⟩,[r126,r350,r351,r352,r353,r354,r355,r356,r357,r358,r359]),(⟨3,1,1⟩,[0,0,r370,r234,r445,r446,r447,r448,r449,3072]),(⟨3,2,0⟩,[r14,r386,r387,r388,r389,r390,r391,r392,r393,r394]),(⟨3,2,4⟩,[r115,r411,r412,r413,r414,-128]),(⟨3,3,0⟩,[r82,r416,r418,r419,r420,r421,r422,r423,r424]),(⟨3,4,0⟩,[r82,r425,r426,r427,r428,r429,r430,r431]),(⟨3,4,2⟩,[r115,r411,r412,r413,r414,-128]),(⟨4,0,0⟩,[r288,r289,r290,r291,r292,r293,r294,r295,r296,r297,r298]),(⟨4,0,1⟩,[r360,r361,r362,r363,r364,r365,r366,r367,r368,r369]),(⟨4,0,2⟩,[r28,r395,r396,r397,r398,r399,r400,r401,r402]),(⟨4,0,3⟩,[r82,r425,r426,r427,r428,r429,r430,r431]),(⟨4,0,4⟩,[r82,r178,r179,r180,r181,r182,-896]),(⟨4,0,5⟩,[r115,r411,r412,r413,r414,-128]),(⟨4,0,6⟩,[r115,r415,r416,r417,128]),(⟨4,1,0⟩,[r360,r361,r362,r363,r364,r365,r366,r367,r368,r369]),(⟨4,1,1⟩,[0,0,r370,r371,r212,r372,r373,r374,-3072]),(⟨4,1,2⟩,[r90,r403,r404,r405,r406,r407,r408,320]),(⟨4,2,0⟩,[r28,r395,r396,r397,r398,r399,r400,r401,r402]),(⟨4,2,1⟩,[r90,r403,r404,r405,r406,r407,r408,320]),(⟨4,2,2⟩,[r82,r178,r179,r180,r181,r182,-896]),(⟨4,2,3⟩,[r115,r411,r412,r413,r414,-128]),(⟨4,2,4⟩,[r183,r188,r189,r190,256]),(⟨4,3,0⟩,[r82,r425,r426,r427,r428,r429,r430,r431]),(⟨4,3,2⟩,[r115,r411,r412,r413,r414,-128]),(⟨4,4,0⟩,[r82,r178,r179,r180,r181,r182,-896]),(⟨4,4,2⟩,[r183,r188,r189,r190,256]),(⟨4,5,0⟩,[r115,r411,r412,r413,r414,-128]),(⟨4,6,0⟩,[r115,r415,r416,r417,128]),(⟨5,0,0⟩,[r299,r300,r301,r302,r303,r304,r305,r306,r307,r308]),(⟨5,0,1⟩,[0,0,r370,r371,r212,r372,r373,r374,-3072]),(⟨5,0,2⟩,[r90,r403,r404,r405,r406,r407,r408,320]),(⟨5,0,4⟩,[r115,r411,r412,r413,r414,-128]),(⟨5,1,0⟩,[0,0,r370,r371,r212,r372,r373,r374,-3072]),(⟨5,2,0⟩,[r90,r403,r404,r405,r406,r407,r408,320]),(⟨5,4,0⟩,[r115,r411,r412,r413,r414,-128]),(⟨6,0,0⟩,[r309,r310,r311,r312,r313,r314,r315,r316,r317]),(⟨6,0,2⟩,[r90,r219,r409,r185,r410,r200,-448]),(⟨6,0,4⟩,[r115,r415,r416,r417,128]),(⟨6,2,0⟩,[r90,r219,r409,r185,r410,r200,-448]),(⟨6,4,0⟩,[r115,r415,r416,r417,128]),(⟨7,0,0⟩,[r90,r318,r319,r320,r321,r322,r323,r324]),(⟨7,0,2⟩,[r115,r411,r412,r413,r414,-128]),(⟨7,2,0⟩,[r115,r411,r412,r413,r414,-128]),(⟨8,0,2⟩,[r115,r415,r416,r417,128]),(⟨8,2,0⟩,[r115,r415,r416,r417,128])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,3,-12,9,6]),(⟨0,0,1⟩,[-1,5,-9,5]),(⟨0,0,2⟩,[-1,4,-7]),(⟨0,0,3⟩,[2,-2]),(⟨0,0,4⟩,[2]),(⟨0,1,0⟩,[-1,5,-9,5]),(⟨0,2,0⟩,[-1,4,-7]),(⟨0,3,0⟩,[2,-2]),(⟨0,4,0⟩,[2]),(⟨1,0,0⟩,[-1,5,-9,5]),(⟨2,0,0⟩,[-1,4,-7]),(⟨3,0,0⟩,[2,-2]),(⟨4,0,0⟩,[2])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[-384,8384,-78592,440960,-1705088,4764160,-9624448,13537664,-12357632,6218048,-613248]),(⟨0,0,1⟩,[-64,2496,-31616,211840,-912896,2736384,-5720192,8092800,-7196096,3341632]),(⟨0,0,2⟩,[448,-8320,59264,-234624,617216,-1004928,849024,-247168,-260288]),(⟨0,0,3⟩,[128,-3712,33920,-163456,531840,-1113984,1334656,-881536]),(⟨0,1,0⟩,[-64,2496,-31616,211840,-912896,2736384,-5720192,8092800,-7196096,3341632]),(⟨0,1,1⟩,[0,0,2048,-28672,116736,-122880,-206848,708608,-731136]),(⟨0,2,0⟩,[448,-8320,59264,-234624,617216,-1004928,849024,-247168,-260288]),(⟨0,2,4⟩,[-256,3072,-7680,-9216,30464]),(⟨0,3,0⟩,[128,-3712,33920,-163456,531840,-1113984,1334656,-881536]),(⟨0,4,2⟩,[-256,3072,-7680,-9216,30464]),(⟨1,0,0⟩,[-64,2496,-31616,211840,-912896,2736384,-5720192,8092800,-7196096,3341632]),(⟨1,0,1⟩,[0,0,2048,-28672,116736,-122880,-206848,708608,-731136]),(⟨1,1,0⟩,[0,0,2048,-28672,116736,-122880,-206848,708608,-731136]),(⟨2,0,0⟩,[448,-8320,59264,-234624,617216,-1004928,849024,-247168,-260288]),(⟨2,0,4⟩,[-256,3072,-7680,-9216,30464]),(⟨2,4,0⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[128,-3712,33920,-163456,531840,-1113984,1334656,-881536]),(⟨4,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨4,2,0⟩,[-256,3072,-7680,-9216,30464])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 0 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r450) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 8 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r451) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨4,0,0⟩,[2])]

noncomputable def partial12 : Poly := [(⟨4,0,0⟩,[-768,16768,-157184,881920,-3410176,9528320,-19248896,27075328,-24715264,12436096,-1226496]),(⟨4,0,1⟩,[-128,4992,-63232,423680,-1825792,5472768,-11440384,16185600,-14392192,6683264]),(⟨4,0,2⟩,[896,-16640,118528,-469248,1234432,-2009856,1698048,-494336,-520576]),(⟨4,0,3⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨4,1,0⟩,[-128,4992,-63232,423680,-1825792,5472768,-11440384,16185600,-14392192,6683264]),(⟨4,1,1⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨4,2,0⟩,[896,-16640,118528,-469248,1234432,-2009856,1698048,-494336,-520576]),(⟨4,2,4⟩,[-512,6144,-15360,-18432,60928]),(⟨4,3,0⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨4,4,2⟩,[-512,6144,-15360,-18432,60928]),(⟨5,0,0⟩,[-128,4992,-63232,423680,-1825792,5472768,-11440384,16185600,-14392192,6683264]),(⟨5,0,1⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨5,1,0⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨6,0,0⟩,[896,-16640,118528,-469248,1234432,-2009856,1698048,-494336,-520576]),(⟨6,0,4⟩,[-512,6144,-15360,-18432,60928]),(⟨6,4,0⟩,[-512,6144,-15360,-18432,60928]),(⟨7,0,0⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨8,0,2⟩,[-512,6144,-15360,-18432,60928]),(⟨8,2,0⟩,[-512,6144,-15360,-18432,60928])]


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

noncomputable def partial8 : Poly := [(⟨0,4,0⟩,[-768,16768,-157184,881920,-3410176,9528320,-19248896,27075328,-24715264,12436096,-1226496]),(⟨0,4,1⟩,[-128,4992,-63232,423680,-1825792,5472768,-11440384,16185600,-14392192,6683264]),(⟨0,4,2⟩,[896,-16640,118528,-469248,1234432,-2009856,1698048,-494336,-520576]),(⟨0,4,3⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨0,5,0⟩,[-128,4992,-63232,423680,-1825792,5472768,-11440384,16185600,-14392192,6683264]),(⟨0,5,1⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨0,6,0⟩,[896,-16640,118528,-469248,1234432,-2009856,1698048,-494336,-520576]),(⟨0,6,4⟩,[-512,6144,-15360,-18432,60928]),(⟨0,7,0⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨0,8,2⟩,[-512,6144,-15360,-18432,60928]),(⟨1,0,0⟩,[384,-10304,123968,-911296,4659136,-17651200,50995840,-113062784,190486784,-237967424,210610496,-120816832,36609472,-3066240]),(⟨1,0,1⟩,[64,-2816,44672,-392704,2269120,-9365504,28677376,-65885696,112823744,-140758272,121937024,-66055168,16708160]),(⟨1,0,2⟩,[-448,10560,-104896,608064,-2365312,6498944,-12601728,16622720,-13641408,5168192,1106752,-1301440]),(⟨1,0,3⟩,[-128,4352,-53632,367104,-1672960,5413888,-12508416,20239872,-21989504,14607104,-4407680]),(⟨1,1,0⟩,[64,-2816,44672,-392704,2269120,-9365504,28677376,-65885696,112823744,-140758272,121937024,-66055168,16708160]),(⟨1,1,1⟩,[0,0,-2048,38912,-278528,974848,-1601536,-53248,5521408,-11067392,10123264,-3655680]),(⟨1,2,0⟩,[-448,10560,-104896,608064,-2365312,6498944,-12601728,16622720,-13641408,5168192,1106752,-1301440]),(⟨1,2,4⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨1,3,0⟩,[-128,4352,-53632,367104,-1672960,5413888,-12508416,20239872,-21989504,14607104,-4407680]),(⟨1,4,0⟩,[-128,4992,-63232,423680,-1825792,5472768,-11440384,16185600,-14392192,6683264]),(⟨1,4,1⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨1,4,2⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨1,5,0⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨2,0,0⟩,[448,-12736,159488,-1206720,6288192,-24036736,69294080,-151270272,246703168,-291170496,233925888,-112034496,21000896]),(⟨2,0,1⟩,[64,-2752,40000,-316864,1703040,-6896000,21454464,-50181504,85130048,-99843008,73862464,-27047104]),(⟨2,0,2⟩,[-448,10112,-95680,529920,-1970560,5116160,-9189248,10677760,-6671552,689024,1822016]),(⟨2,0,3⟩,[-128,4224,-49664,325120,-1423104,4385536,-9513472,14018048,-12868736,6170752]),(⟨2,1,0⟩,[64,-2752,40000,-316864,1703040,-6896000,21454464,-50181504,85130048,-99843008,73862464,-27047104]),(⟨2,1,1⟩,[0,0,-2048,36864,-245760,790528,-1101824,-675840,5013504,-7884800,5117952]),(⟨2,2,0⟩,[-448,10112,-95680,529920,-1970560,5116160,-9189248,10677760,-6671552,689024,1822016]),(⟨2,2,4⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨2,3,0⟩,[-128,4224,-49664,325120,-1423104,4385536,-9513472,14018048,-12868736,6170752]),(⟨2,4,0⟩,[896,-16640,118528,-469248,1234432,-2009856,1698048,-494336,-520576]),(⟨2,4,2⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨2,4,4⟩,[-512,6144,-15360,-18432,60928]),(⟨2,8,0⟩,[-512,6144,-15360,-18432,60928]),(⟨3,0,0⟩,[-1152,25344,-236800,1291392,-4675840,11566592,-18322944,12818688,14176640,-46456064,51183360,-23466368]),(⟨3,0,1⟩,[-128,5120,-70272,523776,-2495232,8089088,-18014976,26950144,-25564288,13190656,-1565312]),(⟨3,0,2⟩,[896,-17536,135168,-587776,1703680,-3244288,3707904,-2192384,-26240,520576]),(⟨3,0,3⟩,[256,-7680,75264,-394752,1390592,-3291648,4897280,-4432384,1763072]),(⟨3,0,4⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨3,1,0⟩,[-128,5120,-70272,523776,-2495232,8089088,-18014976,26950144,-25564288,13190656,-1565312]),(⟨3,1,1⟩,[0,0,4096,-61440,290816,-479232,-167936,1830912,-2879488,1462272]),(⟨3,2,0⟩,[896,-17536,135168,-587776,1703680,-3244288,3707904,-2192384,-26240,520576]),(⟨3,2,4⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨3,3,0⟩,[256,-7680,75264,-394752,1390592,-3291648,4897280,-4432384,1763072]),(⟨3,4,0⟩,[512,-11776,93184,-385024,1071616,-2031104,2349056,-1610752]),(⟨3,4,2⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨4,0,0⟩,[-1472,36352,-374720,2265856,-9303168,27356928,-57859712,85618944,-83954112,48807680,-10495424]),(⟨4,0,1⟩,[-128,4992,-59136,362240,-1534976,4993536,-11608320,18016512,-17271680,8145536]),(⟨4,0,2⟩,[896,-16640,118528,-469248,1234432,-2009856,1698048,-494336,-520576]),(⟨4,0,3⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨4,0,4⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨4,1,0⟩,[-128,4992,-59136,362240,-1534976,4993536,-11608320,18016512,-17271680,8145536]),(⟨4,1,1⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨4,2,0⟩,[896,-16640,118528,-469248,1234432,-2009856,1698048,-494336,-520576]),(⟨4,2,4⟩,[-512,6144,-15360,-18432,60928]),(⟨4,3,0⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨4,4,0⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨4,4,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨4,6,0⟩,[-512,6144,-15360,-18432,60928]),(⟨5,0,0⟩,[640,-8320,22272,161024,-1545216,6614016,-17245952,28011264,-27287168,13374592]),(⟨5,0,1⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨5,0,2⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨5,0,4⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨5,1,0⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨5,2,0⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨5,4,0⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨6,0,0⟩,[1152,-24320,193792,-864000,2625024,-5301504,6595328,-4926720,1242496]),(⟨6,0,2⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨6,0,4⟩,[-512,6144,-15360,-18432,60928]),(⟨6,2,0⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨6,4,0⟩,[-512,6144,-15360,-18432,60928]),(⟨7,0,0⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨7,0,2⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨7,2,0⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨8,0,2⟩,[-512,6144,-15360,-18432,60928]),(⟨8,2,0⟩,[-512,6144,-15360,-18432,60928])]


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

noncomputable def partial4 : Poly := [(⟨0,0,4⟩,[-768,16768,-157184,881920,-3410176,9528320,-19248896,27075328,-24715264,12436096,-1226496]),(⟨0,0,5⟩,[-128,4992,-63232,423680,-1825792,5472768,-11440384,16185600,-14392192,6683264]),(⟨0,0,6⟩,[896,-16640,118528,-469248,1234432,-2009856,1698048,-494336,-520576]),(⟨0,0,7⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨0,1,0⟩,[384,-10304,123968,-911296,4659136,-17651200,50995840,-113062784,190486784,-237967424,210610496,-120816832,36609472,-3066240]),(⟨0,1,1⟩,[64,-2816,44672,-392704,2269120,-9365504,28677376,-65885696,112823744,-140758272,121937024,-66055168,16708160]),(⟨0,1,2⟩,[-448,10560,-104896,608064,-2365312,6498944,-12601728,16622720,-13641408,5168192,1106752,-1301440]),(⟨0,1,3⟩,[-128,4352,-53632,367104,-1672960,5413888,-12508416,20239872,-21989504,14607104,-4407680]),(⟨0,1,4⟩,[-128,4992,-63232,423680,-1825792,5472768,-11440384,16185600,-14392192,6683264]),(⟨0,1,5⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨0,2,0⟩,[448,-12736,159488,-1206720,6288192,-24036736,69294080,-151270272,246703168,-291170496,233925888,-112034496,21000896]),(⟨0,2,1⟩,[64,-2752,40000,-316864,1703040,-6896000,21454464,-50181504,85130048,-99843008,73862464,-27047104]),(⟨0,2,2⟩,[-448,10112,-95680,529920,-1970560,5116160,-9189248,10677760,-6671552,689024,1822016]),(⟨0,2,3⟩,[-128,4224,-49664,325120,-1423104,4385536,-9513472,14018048,-12868736,6170752]),(⟨0,2,4⟩,[896,-16640,118528,-469248,1234432,-2009856,1698048,-494336,-520576]),(⟨0,2,8⟩,[-512,6144,-15360,-18432,60928]),(⟨0,3,0⟩,[-1152,25344,-236800,1291392,-4675840,11566592,-18322944,12818688,14176640,-46456064,51183360,-23466368]),(⟨0,3,1⟩,[-128,5120,-70272,523776,-2495232,8089088,-18014976,26950144,-25564288,13190656,-1565312]),(⟨0,3,2⟩,[896,-17536,135168,-587776,1703680,-3244288,3707904,-2192384,-26240,520576]),(⟨0,3,3⟩,[256,-7680,75264,-394752,1390592,-3291648,4897280,-4432384,1763072]),(⟨0,3,4⟩,[512,-11776,93184,-385024,1071616,-2031104,2349056,-1610752]),(⟨0,4,0⟩,[-1472,36352,-374720,2265856,-9303168,27356928,-57859712,85618944,-83954112,48807680,-10495424]),(⟨0,4,1⟩,[-128,4992,-59136,362240,-1534976,4993536,-11608320,18016512,-17271680,8145536]),(⟨0,4,2⟩,[896,-16640,118528,-469248,1234432,-2009856,1698048,-494336,-520576]),(⟨0,4,3⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨0,4,4⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨0,4,6⟩,[-512,6144,-15360,-18432,60928]),(⟨0,5,0⟩,[640,-8320,22272,161024,-1545216,6614016,-17245952,28011264,-27287168,13374592]),(⟨0,5,1⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨0,5,2⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨0,5,4⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨0,6,0⟩,[1152,-24320,193792,-864000,2625024,-5301504,6595328,-4926720,1242496]),(⟨0,6,2⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨0,6,4⟩,[-512,6144,-15360,-18432,60928]),(⟨0,7,0⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨0,7,2⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨0,8,2⟩,[-512,6144,-15360,-18432,60928]),(⟨1,0,0⟩,[384,-10304,123968,-911296,4659136,-17651200,50995840,-113062784,190486784,-237967424,210610496,-120816832,36609472,-3066240]),(⟨1,0,1⟩,[64,-2816,44672,-392704,2269120,-9365504,28677376,-65885696,112823744,-140758272,121937024,-66055168,16708160]),(⟨1,0,2⟩,[-448,10560,-104896,608064,-2365312,6498944,-12601728,16622720,-13641408,5168192,1106752,-1301440]),(⟨1,0,3⟩,[-128,4352,-53632,367104,-1672960,5413888,-12508416,20239872,-21989504,14607104,-4407680]),(⟨1,0,4⟩,[-128,4992,-63232,423680,-1825792,5472768,-11440384,16185600,-14392192,6683264]),(⟨1,0,5⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨1,1,0⟩,[128,-5632,89344,-785408,4538240,-18731008,57354752,-131771392,225647488,-281516544,243874048,-132110336,33416320]),(⟨1,1,1⟩,[0,0,-4096,77824,-557056,1949696,-3203072,-106496,11042816,-22134784,20246528,-7311360]),(⟨1,1,4⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨1,2,0⟩,[-384,7808,-64896,291200,-662272,-397056,8852736,-33558784,71488640,-94674816,74969216,-28348544]),(⟨1,2,1⟩,[0,0,-2048,36864,-245760,790528,-1101824,-675840,5013504,-7884800,5117952]),(⟨1,2,4⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨1,3,0⟩,[-256,9472,-123904,890880,-4168192,13502976,-30523392,47190016,-47553792,27797760,-5972992]),(⟨1,3,1⟩,[0,0,4096,-61440,290816,-479232,-167936,1830912,-2879488,1462272]),(⟨1,4,0⟩,[-128,4992,-59136,362240,-1534976,4993536,-11608320,18016512,-17271680,8145536]),(⟨1,4,1⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨1,4,2⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨1,5,0⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨2,0,0⟩,[448,-12736,159488,-1206720,6288192,-24036736,69294080,-151270272,246703168,-291170496,233925888,-112034496,21000896]),(⟨2,0,1⟩,[64,-2752,40000,-316864,1703040,-6896000,21454464,-50181504,85130048,-99843008,73862464,-27047104]),(⟨2,0,2⟩,[-448,10112,-95680,529920,-1970560,5116160,-9189248,10677760,-6671552,689024,1822016]),(⟨2,0,3⟩,[-128,4224,-49664,325120,-1423104,4385536,-9513472,14018048,-12868736,6170752]),(⟨2,0,4⟩,[896,-16640,118528,-469248,1234432,-2009856,1698048,-494336,-520576]),(⟨2,0,8⟩,[-512,6144,-15360,-18432,60928]),(⟨2,1,0⟩,[-384,7808,-64896,291200,-662272,-397056,8852736,-33558784,71488640,-94674816,74969216,-28348544]),(⟨2,1,1⟩,[0,0,-2048,36864,-245760,790528,-1101824,-675840,5013504,-7884800,5117952]),(⟨2,1,4⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨2,2,0⟩,[-896,20224,-191360,1059840,-3941120,10232320,-18378496,21355520,-13343104,1378048,3644032]),(⟨2,2,4⟩,[512,-8192,43520,-86016,-27136,372736,-426496]),(⟨2,3,0⟩,[768,-13312,85504,-262656,280576,1141248,-5805568,11825664,-12894976,6691328]),(⟨2,3,4⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨2,4,0⟩,[896,-16640,118528,-469248,1234432,-2009856,1698048,-494336,-520576]),(⟨2,4,2⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨2,4,4⟩,[-1024,12288,-30720,-36864,121856]),(⟨2,5,0⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨2,6,0⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨2,7,0⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨2,8,0⟩,[-512,6144,-15360,-18432,60928]),(⟨3,0,0⟩,[-1152,25344,-236800,1291392,-4675840,11566592,-18322944,12818688,14176640,-46456064,51183360,-23466368]),(⟨3,0,1⟩,[-128,5120,-70272,523776,-2495232,8089088,-18014976,26950144,-25564288,13190656,-1565312]),(⟨3,0,2⟩,[896,-17536,135168,-587776,1703680,-3244288,3707904,-2192384,-26240,520576]),(⟨3,0,3⟩,[256,-7680,75264,-394752,1390592,-3291648,4897280,-4432384,1763072]),(⟨3,0,4⟩,[512,-11776,93184,-385024,1071616,-2031104,2349056,-1610752]),(⟨3,1,0⟩,[-256,9472,-123904,890880,-4168192,13502976,-30523392,47190016,-47553792,27797760,-5972992]),(⟨3,1,1⟩,[0,0,4096,-61440,290816,-479232,-167936,1830912,-2879488,1462272]),(⟨3,2,0⟩,[768,-13312,85504,-262656,280576,1141248,-5805568,11825664,-12894976,6691328]),(⟨3,2,4⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨3,3,0⟩,[512,-15360,150528,-789504,2781184,-6583296,9794560,-8864768,3526144]),(⟨3,4,0⟩,[512,-11776,93184,-385024,1071616,-2031104,2349056,-1610752]),(⟨3,4,2⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨4,0,0⟩,[-1472,36352,-374720,2265856,-9303168,27356928,-57859712,85618944,-83954112,48807680,-10495424]),(⟨4,0,1⟩,[-128,4992,-59136,362240,-1534976,4993536,-11608320,18016512,-17271680,8145536]),(⟨4,0,2⟩,[896,-16640,118528,-469248,1234432,-2009856,1698048,-494336,-520576]),(⟨4,0,3⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨4,0,4⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨4,0,6⟩,[-512,6144,-15360,-18432,60928]),(⟨4,1,0⟩,[-128,4992,-59136,362240,-1534976,4993536,-11608320,18016512,-17271680,8145536]),(⟨4,1,1⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨4,1,2⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨4,2,0⟩,[896,-16640,118528,-469248,1234432,-2009856,1698048,-494336,-520576]),(⟨4,2,2⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨4,2,4⟩,[-1024,12288,-30720,-36864,121856]),(⟨4,3,0⟩,[512,-11776,93184,-385024,1071616,-2031104,2349056,-1610752]),(⟨4,3,2⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨4,4,0⟩,[512,-8192,43520,-86016,-27136,372736,-426496]),(⟨4,4,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨4,5,0⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨4,6,0⟩,[-512,6144,-15360,-18432,60928]),(⟨5,0,0⟩,[640,-8320,22272,161024,-1545216,6614016,-17245952,28011264,-27287168,13374592]),(⟨5,0,1⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨5,0,2⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨5,0,4⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨5,1,0⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨5,2,0⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨5,4,0⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨6,0,0⟩,[1152,-24320,193792,-864000,2625024,-5301504,6595328,-4926720,1242496]),(⟨6,0,2⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨6,0,4⟩,[-512,6144,-15360,-18432,60928]),(⟨6,2,0⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨6,4,0⟩,[-512,6144,-15360,-18432,60928]),(⟨7,0,0⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨7,0,2⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨7,2,0⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨8,0,2⟩,[-512,6144,-15360,-18432,60928]),(⟨8,2,0⟩,[-512,6144,-15360,-18432,60928])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,-1152,29760,-339840,2339136,-11063808,38250624,-98743296,188753280,-257559936,231038016,-106449024,-10824384,31789056,-3679488]),(⟨0,0,1⟩,[384,-10496,132224,-1036672,5696128,-23201536,71876608,-170004992,302557568,-391732736,345502592,-177124480,23507584,16983552]),(⟨0,0,2⟩,[448,-11392,129152,-925056,4800960,-18886144,57116672,-132516864,230432320,-287373696,239918976,-115860096,19439168]),(⟨0,0,3⟩,[-1152,25728,-249472,1438848,-5605888,15406592,-29314560,33996288,-11318656,-30549632,51257472,-28755584]),(⟨0,0,4⟩,[-1472,36352,-374720,2265856,-9303168,27356928,-57859712,85618944,-83954112,48807680,-10495424]),(⟨0,0,5⟩,[640,-8320,22272,161024,-1545216,6614016,-17245952,28011264,-27287168,13374592]),(⟨0,0,6⟩,[1152,-24320,193792,-864000,2625024,-5301504,6595328,-4926720,1242496]),(⟨0,0,7⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨0,1,0⟩,[384,-10496,132224,-1036672,5696128,-23201536,71876608,-170004992,302557568,-391732736,345502592,-177124480,23507584,16983552]),(⟨0,1,1⟩,[128,-5632,89344,-779264,4427648,-18018304,55339520,-130038784,229849984,-294812160,257784064,-134438912,29029504]),(⟨0,1,2⟩,[-384,7808,-64896,291200,-662272,-397056,8852736,-33558784,71488640,-94674816,74969216,-28348544]),(⟨0,1,3⟩,[-256,9472,-123904,890880,-4168192,13502976,-30523392,47190016,-47553792,27797760,-5972992]),(⟨0,1,4⟩,[-128,4992,-59136,362240,-1534976,4993536,-11608320,18016512,-17271680,8145536]),(⟨0,1,5⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨0,2,0⟩,[448,-11392,129152,-925056,4800960,-18886144,57116672,-132516864,230432320,-287373696,239918976,-115860096,19439168]),(⟨0,2,1⟩,[-384,7808,-64896,291200,-662272,-397056,8852736,-33558784,71488640,-94674816,74969216,-28348544]),(⟨0,2,2⟩,[-896,20224,-191360,1059840,-3941120,10232320,-18378496,21355520,-13343104,1378048,3644032]),(⟨0,2,3⟩,[768,-13312,85504,-262656,280576,1141248,-5805568,11825664,-12894976,6691328]),(⟨0,2,4⟩,[896,-17408,130816,-531456,1325056,-1858560,1203456,-275456,-337792]),(⟨0,2,5⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨0,2,6⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨0,2,7⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨0,2,8⟩,[-512,6144,-15360,-18432,60928]),(⟨0,3,0⟩,[-1152,25728,-249472,1438848,-5605888,15406592,-29314560,33996288,-11318656,-30549632,51257472,-28755584]),(⟨0,3,1⟩,[-256,9472,-123904,890880,-4168192,13502976,-30523392,47190016,-47553792,27797760,-5972992]),(⟨0,3,2⟩,[768,-13312,85504,-262656,280576,1141248,-5805568,11825664,-12894976,6691328]),(⟨0,3,3⟩,[512,-15360,150528,-789504,2781184,-6583296,9794560,-8864768,3526144]),(⟨0,3,4⟩,[512,-11776,93184,-385024,1071616,-2031104,2349056,-1610752]),(⟨0,4,0⟩,[-1472,36352,-374720,2265856,-9303168,27356928,-57859712,85618944,-83954112,48807680,-10495424]),(⟨0,4,1⟩,[-128,4992,-59136,362240,-1534976,4993536,-11608320,18016512,-17271680,8145536]),(⟨0,4,2⟩,[896,-17408,130816,-531456,1325056,-1858560,1203456,-275456,-337792]),(⟨0,4,3⟩,[512,-11776,93184,-385024,1071616,-2031104,2349056,-1610752]),(⟨0,4,4⟩,[512,-8192,43520,-86016,-27136,372736,-426496]),(⟨0,4,5⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨0,4,6⟩,[-512,6144,-15360,-18432,60928]),(⟨0,5,0⟩,[640,-8320,22272,161024,-1545216,6614016,-17245952,28011264,-27287168,13374592]),(⟨0,5,1⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨0,5,2⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨0,5,4⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨0,6,0⟩,[1152,-24320,193792,-864000,2625024,-5301504,6595328,-4926720,1242496]),(⟨0,6,2⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨0,6,4⟩,[-512,6144,-15360,-18432,60928]),(⟨0,7,0⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨0,7,2⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨0,8,2⟩,[-512,6144,-15360,-18432,60928]),(⟨1,0,0⟩,[384,-10496,132224,-1036672,5696128,-23201536,71876608,-170004992,302557568,-391732736,345502592,-177124480,23507584,16983552]),(⟨1,0,1⟩,[128,-5632,89344,-779264,4427648,-18018304,55339520,-130038784,229849984,-294812160,257784064,-134438912,29029504]),(⟨1,0,2⟩,[-384,7808,-64896,291200,-662272,-397056,8852736,-33558784,71488640,-94674816,74969216,-28348544]),(⟨1,0,3⟩,[-256,9472,-123904,890880,-4168192,13502976,-30523392,47190016,-47553792,27797760,-5972992]),(⟨1,0,4⟩,[-128,4992,-59136,362240,-1534976,4993536,-11608320,18016512,-17271680,8145536]),(⟨1,0,5⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨1,1,0⟩,[128,-5632,89344,-779264,4427648,-18018304,55339520,-130038784,229849984,-294812160,257784064,-134438912,29029504]),(⟨1,1,1⟩,[0,0,-6144,116736,-835584,2924544,-4804608,-159744,16564224,-33202176,30369792,-10967040]),(⟨1,1,2⟩,[0,0,-2048,36864,-245760,790528,-1101824,-675840,5013504,-7884800,5117952]),(⟨1,1,3⟩,[0,0,4096,-61440,290816,-479232,-167936,1830912,-2879488,1462272]),(⟨1,1,4⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨1,2,0⟩,[-384,7808,-64896,291200,-662272,-397056,8852736,-33558784,71488640,-94674816,74969216,-28348544]),(⟨1,2,1⟩,[0,0,-2048,36864,-245760,790528,-1101824,-675840,5013504,-7884800,5117952]),(⟨1,2,4⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨1,3,0⟩,[-256,9472,-123904,890880,-4168192,13502976,-30523392,47190016,-47553792,27797760,-5972992]),(⟨1,3,1⟩,[0,0,4096,-61440,290816,-479232,-167936,1830912,-2879488,1462272]),(⟨1,4,0⟩,[-128,4992,-59136,362240,-1534976,4993536,-11608320,18016512,-17271680,8145536]),(⟨1,4,1⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨1,4,2⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨1,5,0⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨2,0,0⟩,[448,-11392,129152,-925056,4800960,-18886144,57116672,-132516864,230432320,-287373696,239918976,-115860096,19439168]),(⟨2,0,1⟩,[-384,7808,-64896,291200,-662272,-397056,8852736,-33558784,71488640,-94674816,74969216,-28348544]),(⟨2,0,2⟩,[-896,20224,-191360,1059840,-3941120,10232320,-18378496,21355520,-13343104,1378048,3644032]),(⟨2,0,3⟩,[768,-13312,85504,-262656,280576,1141248,-5805568,11825664,-12894976,6691328]),(⟨2,0,4⟩,[896,-17408,130816,-531456,1325056,-1858560,1203456,-275456,-337792]),(⟨2,0,5⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨2,0,6⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨2,0,7⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨2,0,8⟩,[-512,6144,-15360,-18432,60928]),(⟨2,1,0⟩,[-384,7808,-64896,291200,-662272,-397056,8852736,-33558784,71488640,-94674816,74969216,-28348544]),(⟨2,1,1⟩,[0,0,-2048,36864,-245760,790528,-1101824,-675840,5013504,-7884800,5117952]),(⟨2,1,4⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨2,2,0⟩,[-896,20224,-191360,1059840,-3941120,10232320,-18378496,21355520,-13343104,1378048,3644032]),(⟨2,2,4⟩,[512,-8192,43520,-86016,-27136,372736,-426496]),(⟨2,3,0⟩,[768,-13312,85504,-262656,280576,1141248,-5805568,11825664,-12894976,6691328]),(⟨2,3,4⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨2,4,0⟩,[896,-17408,130816,-531456,1325056,-1858560,1203456,-275456,-337792]),(⟨2,4,1⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨2,4,2⟩,[512,-8192,43520,-86016,-27136,372736,-426496]),(⟨2,4,3⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨2,4,4⟩,[-1024,12288,-30720,-36864,121856]),(⟨2,5,0⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨2,6,0⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨2,7,0⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨2,8,0⟩,[-512,6144,-15360,-18432,60928]),(⟨3,0,0⟩,[-1152,25728,-249472,1438848,-5605888,15406592,-29314560,33996288,-11318656,-30549632,51257472,-28755584]),(⟨3,0,1⟩,[-256,9472,-123904,890880,-4168192,13502976,-30523392,47190016,-47553792,27797760,-5972992]),(⟨3,0,2⟩,[768,-13312,85504,-262656,280576,1141248,-5805568,11825664,-12894976,6691328]),(⟨3,0,3⟩,[512,-15360,150528,-789504,2781184,-6583296,9794560,-8864768,3526144]),(⟨3,0,4⟩,[512,-11776,93184,-385024,1071616,-2031104,2349056,-1610752]),(⟨3,1,0⟩,[-256,9472,-123904,890880,-4168192,13502976,-30523392,47190016,-47553792,27797760,-5972992]),(⟨3,1,1⟩,[0,0,4096,-61440,290816,-479232,-167936,1830912,-2879488,1462272]),(⟨3,2,0⟩,[768,-13312,85504,-262656,280576,1141248,-5805568,11825664,-12894976,6691328]),(⟨3,2,4⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨3,3,0⟩,[512,-15360,150528,-789504,2781184,-6583296,9794560,-8864768,3526144]),(⟨3,4,0⟩,[512,-11776,93184,-385024,1071616,-2031104,2349056,-1610752]),(⟨3,4,2⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨4,0,0⟩,[-1472,36352,-374720,2265856,-9303168,27356928,-57859712,85618944,-83954112,48807680,-10495424]),(⟨4,0,1⟩,[-128,4992,-59136,362240,-1534976,4993536,-11608320,18016512,-17271680,8145536]),(⟨4,0,2⟩,[896,-17408,130816,-531456,1325056,-1858560,1203456,-275456,-337792]),(⟨4,0,3⟩,[512,-11776,93184,-385024,1071616,-2031104,2349056,-1610752]),(⟨4,0,4⟩,[512,-8192,43520,-86016,-27136,372736,-426496]),(⟨4,0,5⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨4,0,6⟩,[-512,6144,-15360,-18432,60928]),(⟨4,1,0⟩,[-128,4992,-59136,362240,-1534976,4993536,-11608320,18016512,-17271680,8145536]),(⟨4,1,1⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨4,1,2⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨4,2,0⟩,[896,-17408,130816,-531456,1325056,-1858560,1203456,-275456,-337792]),(⟨4,2,1⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨4,2,2⟩,[512,-8192,43520,-86016,-27136,372736,-426496]),(⟨4,2,3⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨4,2,4⟩,[-1024,12288,-30720,-36864,121856]),(⟨4,3,0⟩,[512,-11776,93184,-385024,1071616,-2031104,2349056,-1610752]),(⟨4,3,2⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨4,4,0⟩,[512,-8192,43520,-86016,-27136,372736,-426496]),(⟨4,4,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨4,5,0⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨4,6,0⟩,[-512,6144,-15360,-18432,60928]),(⟨5,0,0⟩,[640,-8320,22272,161024,-1545216,6614016,-17245952,28011264,-27287168,13374592]),(⟨5,0,1⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨5,0,2⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨5,0,4⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨5,1,0⟩,[0,0,4096,-57344,233472,-245760,-413696,1417216,-1462272]),(⟨5,2,0⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨5,4,0⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨6,0,0⟩,[1152,-24320,193792,-864000,2625024,-5301504,6595328,-4926720,1242496]),(⟨6,0,2⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨6,0,4⟩,[-512,6144,-15360,-18432,60928]),(⟨6,2,0⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨6,4,0⟩,[-512,6144,-15360,-18432,60928]),(⟨7,0,0⟩,[256,-7424,67840,-326912,1063680,-2227968,2669312,-1763072]),(⟨7,0,2⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨7,2,0⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨8,0,2⟩,[-512,6144,-15360,-18432,60928]),(⟨8,2,0⟩,[-512,6144,-15360,-18432,60928])]


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
    (Poly.add (Poly.scale (K.ofRat r452) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 0 8).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r450*r451 : ℚ)=r452 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 0 8 r450 r451 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 0=8 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 0 8).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C053

#print axioms Coulomb8.Columns.C053.sound
