import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C074

def r0 : ℚ := { num := -864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 23904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -279936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 1836768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -7511424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 19928064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -34045824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 34646784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -14792928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -6474336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 8475648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -581856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -153792, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := 288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := -8928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := 118752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := -897504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 4321056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -13977920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 30900864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := 42357920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := -18720992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -2326368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 4635552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -28960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -9504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 14336, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -628960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 2704320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -8372608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 18393280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -1600640, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 24508864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -10012000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -206400, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 264096, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 19136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -27968, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 1080704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -3550208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 7031040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -7711232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 2800768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 2711040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -138688, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -20928, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 22432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -210752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 1075712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -3337280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 6481984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -1086784, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 4623104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -520192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -71712, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -9088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 59200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := -21248, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := 40704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 508544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -997184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 93696, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -5152, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -576, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 27072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -80448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 152640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -259136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 253248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -9280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := -384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := 1024, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := -6912, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := 155136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := -34432, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := 127488, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 8192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -6400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 33024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -3072, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := 1792, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := -6656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := 4864, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -49664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := -384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -20736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 209760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -1220544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := 658880, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -11875072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := 20924480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := -3485312, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 17066080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -5238784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -45920, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := -4928, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 1824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -13312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 54048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := -172160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := 542656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -206528, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 2517184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -294624, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -114720, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 437696, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -264992, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := -32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := 2496, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := -174912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := 866112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := -2551872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := 4854784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := -367040, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := 5517280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := -465088, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := 166208, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := -5216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := 5120, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := -18176, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 34368, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := -14016, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -659968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 1708288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := -266784, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := 32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 6144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -26816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 53440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 64, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -27648, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 46144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := 2624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -8256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := -18880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := 158400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := -347456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 297536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -3776, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 7808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -13824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 2432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 8960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := -128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := 1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -3840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := -4608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := 5120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := -3328, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 339072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -70016, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 346496, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -381184, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 47040, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -43904, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := 96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := -192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := 3968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 13376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -71872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := 36160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 254336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -457792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := 20896, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 21504, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := -11904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := 18432, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -547328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 1259264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -1675648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 1141248, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := -49088, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := 3008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -15424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := 29504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := 192, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := -106432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := 170048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := -288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := 864, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -52128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 254112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -779712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 1437120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -878784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := -3048000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := 1443360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -2134944, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 1688736, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := 768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := -7776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := 44032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -21440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := 294144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := -25664, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -101888, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := 312480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := -376320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := -7040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 48896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -173056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := 317440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := -102656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := -914176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 2247680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -339584, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := 6016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := -30848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := 59008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := 384, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := -212864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := 340096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := -432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := 11952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := -139968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := 918384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := -3755712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := 9964032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := -17022912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := 17323392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := -7396464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -3237168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 4237824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -290928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -76896, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := -4464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := 59376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := -448752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := 2160528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := -6988960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := 15450432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := 21178960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := -9360496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := -1163184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := 2317776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := -14480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -4752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := 7168, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := -314480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 1352160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -4186304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := 9196640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -800320, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := 12254432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -5006000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := -103200, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := 132048, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := 9568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := -13984, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := 540352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -1775104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := 3515520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := -3855616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := 1400384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := 1355520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := -69344, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := -10464, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 11216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := -105376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := 537856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := -1668640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := 3240992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := -543392, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := 2311552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := -260096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := -35856, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := 240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -4544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := 29600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := -10624, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := 20352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := 254272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -498592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := 46848, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -2576, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := -288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := 13536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := -40224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := 76320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := -129568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := 126624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -4640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := 512, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := -3456, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := 77568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := -17216, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := 63744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := 4096, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := -3200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := 16512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := -1536, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := 320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 896, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -3328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 2432, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -24832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := -10368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 104880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -610272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := 329440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := -5937536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := 10462240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := -1742656, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := 8533040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := -2619392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := -22960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := -2464, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -48, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := 27024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := -86080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := 271328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := -103264, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := 1258592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := -147312, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -57360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 218848, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -132496, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := -16, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := 1248, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := -87456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := 433056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := -1275936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := 2427392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := -183520, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := 2758640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := -232544, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := 83104, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := -2608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := 2560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := -9088, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := 17184, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := -7008, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := -329984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := 854144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := -133392, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := 16, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := -352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := 3072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := -13408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := 26720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := 32, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := -13824, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := 23072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := 1312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := -4128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := -9440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := 79200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := -173728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := 148768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := -1888, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := -128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := 3904, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := -6912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := 1216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := 4480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := -64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := -1920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := -2304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := 2560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := -1664, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := 169536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := -35008, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := 173248, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := -190592, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := 23520, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := -21952, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := 48, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := -96, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := 1984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := 6688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := -35936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := 18080, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := 127168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := -228896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := 10448, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 10752, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := -5952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := 9216, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := -273664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := 629632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := -837824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := 570624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := -24544, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := 1504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := -7712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := 14752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := 96, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := -53216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := 85024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := -144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := 432, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := -26064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := 127056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := -389856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := 718560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := -439392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := -1524000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := 721680, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := -1067472, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := 844368, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := -3888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := 22016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := -10720, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := 147072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := -12832, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := -50944, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := 156240, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := -188160, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := -3520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := 24448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := -86528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := 158720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := -51328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := -457088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := 1123840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := -169792, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := 1, den := 8, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := 1, den := 952, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12],[0,r13,r14,r15,r16,r17,r18,r19,-385344,r20,r21,r22,r23,r24],[0,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35,r36],[0,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47],[0,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57],[0,r58,r59,r60,r61,r62,r63,r64,r65,r66],[0,r67,r68,r69,r70,r71,r72,r73,r74],[0,r75,r76,r77,r78,r79,r80,r81],[0,r25,r82,r83,r84,r85,r86],[0,r25,r87,r88,r89,r90],[],[],[],[0,r91,r92,r93,r94,r95,r96,r97,r98,r99,r100,r101,r102],[r103,r104,r105,r106,r107,r108,r109,r110,r111,r112,r113,r114],[r115,r75,r116,r117,r118,r119,r120,r121,r122,r123,r124],[r13,r125,r126,r127,r128,r129,r130,r131,r132,6496],[r133,r134,r135,r136,r137,r138,r139,r140,-1568],[r141,r142,r143,r144,r145,r146,r147,r148],[r149,r150,r151,r152,r153,r154,-896],[],[r155,r156,r157,r158,128],[],[],[0,r141,r159,r160,r161,r162,r163,r164,9856,r165,r166],[r167,r168,r169,r170,r171,r172,r173,r174,r175,r176],[],[],[0,r25,r82,r83,r84,r85,r86],[],[],[],[],[r177,r178,r179,r180,r181,r182,r183,r184,r185],[r141,r186,r187,r188,r189,r190,r191,-704],[],[0,r25,r87,r88,r89,r90],[r155,r156,r157,r158,128],[],[],[],[],[],[],[],[],[],[],[],[r192,r193,r194,r195,r196,r197,r198,r199,r200,r201,r202,-32928],[r115,r203,r204,r205,r206,r207,r208,r209,r210,r211,10976],[r25,r212,r213,r214,r215,r216,r217,r218,r219,8064],[],[],[r149,r150,r151,r152,r153,r154,-896],[],[],[],[],[],[r133,r134,r135,r136,r137,r138,r139,r140,-1568],[],[],[],[],[],[],[r75,r220,r221,r222,r223,r224,r225,-1408],[],[],[r155,r156,r157,r158,128],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,0,r226,r227,r228,r229,r230,r231,r232,r233,r234,r235,r236,r237,r238]),(⟨0,0,1⟩,[0,r239,r240,r241,r242,r243,r244,r245,-192672,r246,r247,r248,r249,r250]),(⟨0,0,2⟩,[0,r67,r251,r252,r253,r254,r255,r256,r257,r258,r259,r260,r261]),(⟨0,0,3⟩,[0,r75,r262,r263,r264,r265,r266,r267,r268,r269,r270,r271]),(⟨0,0,4⟩,[0,r272,r273,r274,r275,r276,r277,r278,r279,r280,r281]),(⟨0,0,5⟩,[0,r282,r283,r284,r285,r286,r287,r288,r289,r290]),(⟨0,0,6⟩,[0,r167,r291,r292,r293,r294,r295,r296,r297]),(⟨0,0,7⟩,[0,r141,r298,r299,r300,r301,r302,r303]),(⟨0,0,8⟩,[0,r67,r304,r305,r306,r307,r308]),(⟨0,0,9⟩,[0,r67,r309,r310,r311,r168]),(⟨0,1,0⟩,[0,r239,r240,r241,r242,r243,r244,r245,-192672,r246,r247,r248,r249,r250]),(⟨0,1,1⟩,[0,r312,r313,r314,r315,r316,r317,r318,r319,r320,r321,r322,r323]),(⟨0,1,2⟩,[r324,r325,r87,r326,r327,r328,r329,r330,r331,r332,r333,r334]),(⟨0,1,3⟩,[r335,r141,r336,r337,r338,r339,r340,r341,r342,r343,r344]),(⟨0,1,4⟩,[r239,r345,r346,r347,r348,r349,r350,r351,r352,3248]),(⟨0,1,5⟩,[r353,r354,r355,r356,r357,r358,r359,r360,-784]),(⟨0,1,6⟩,[r103,r361,r362,r363,r364,r365,r366,r367]),(⟨0,1,7⟩,[r177,r368,r369,r370,r371,r372,-448]),(⟨0,1,9⟩,[r373,r203,r374,r375,64]),(⟨0,2,0⟩,[0,r67,r251,r252,r253,r254,r255,r256,r257,r258,r259,r260,r261]),(⟨0,2,1⟩,[r324,r325,r87,r326,r327,r328,r329,r330,r331,r332,r333,r334]),(⟨0,2,2⟩,[0,r103,r376,r377,r378,r379,r380,r381,4928,r382,r383]),(⟨0,2,3⟩,[r384,r385,r386,r387,r388,r389,r390,r391,r392,r393]),(⟨0,2,6⟩,[0,r67,r304,r305,r306,r307,r308]),(⟨0,3,0⟩,[0,r75,r262,r263,r264,r265,r266,r267,r268,r269,r270,r271]),(⟨0,3,1⟩,[r335,r141,r336,r337,r338,r339,r340,r341,r342,r343,r344]),(⟨0,3,2⟩,[r384,r385,r386,r387,r388,r389,r390,r391,r392,r393]),(⟨0,3,3⟩,[r133,r155,r394,r395,r396,r397,r398,r399,r400]),(⟨0,3,4⟩,[r103,r401,r402,r403,r404,r405,r406,-352]),(⟨0,3,6⟩,[0,r67,r309,r310,r311,r168]),(⟨0,3,7⟩,[r373,r203,r374,r375,64]),(⟨0,4,0⟩,[0,r272,r273,r274,r275,r276,r277,r278,r279,r280,r281]),(⟨0,4,1⟩,[r239,r345,r346,r347,r348,r349,r350,r351,r352,3248]),(⟨0,4,3⟩,[r103,r401,r402,r403,r404,r405,r406,-352]),(⟨0,5,0⟩,[0,r282,r283,r284,r285,r286,r287,r288,r289,r290]),(⟨0,5,1⟩,[r353,r354,r355,r356,r357,r358,r359,r360,-784]),(⟨0,6,0⟩,[0,r167,r291,r292,r293,r294,r295,r296,r297]),(⟨0,6,1⟩,[r103,r361,r362,r363,r364,r365,r366,r367]),(⟨0,6,2⟩,[0,r67,r304,r305,r306,r307,r308]),(⟨0,6,3⟩,[0,r67,r309,r310,r311,r168]),(⟨0,7,0⟩,[0,r141,r298,r299,r300,r301,r302,r303]),(⟨0,7,1⟩,[r177,r368,r369,r370,r371,r372,-448]),(⟨0,7,3⟩,[r373,r203,r374,r375,64]),(⟨0,8,0⟩,[0,r67,r304,r305,r306,r307,r308]),(⟨0,9,0⟩,[0,r67,r309,r310,r311,r168]),(⟨0,9,1⟩,[r373,r203,r374,r375,64]),(⟨1,0,0⟩,[0,r239,r240,r241,r242,r243,r244,r245,-192672,r246,r247,r248,r249,r250]),(⟨1,0,1⟩,[0,r312,r313,r314,r315,r316,r317,r318,r319,r320,r321,r322,r323]),(⟨1,0,2⟩,[r324,r325,r87,r326,r327,r328,r329,r330,r331,r332,r333,r334]),(⟨1,0,3⟩,[r335,r141,r336,r337,r338,r339,r340,r341,r342,r343,r344]),(⟨1,0,4⟩,[r239,r345,r346,r347,r348,r349,r350,r351,r352,3248]),(⟨1,0,5⟩,[r353,r354,r355,r356,r357,r358,r359,r360,-784]),(⟨1,0,6⟩,[r103,r361,r362,r363,r364,r365,r366,r367]),(⟨1,0,7⟩,[r177,r368,r369,r370,r371,r372,-448]),(⟨1,0,9⟩,[r373,r203,r374,r375,64]),(⟨1,1,0⟩,[0,r312,r313,r314,r315,r316,r317,r318,r319,r320,r321,r322,r323]),(⟨1,1,1⟩,[r407,r408,r409,r410,r411,r412,r413,r414,r415,r416,r417,-16464]),(⟨1,1,2⟩,[r335,r25,r418,r419,r420,r421,r422,r423,r424,r425,5488]),(⟨1,1,3⟩,[r67,r426,r427,r428,r429,r430,r431,r432,r433,4032]),(⟨1,1,6⟩,[r177,r368,r369,r370,r371,r372,-448]),(⟨1,2,0⟩,[r324,r325,r87,r326,r327,r328,r329,r330,r331,r332,r333,r334]),(⟨1,2,1⟩,[r335,r25,r418,r419,r420,r421,r422,r423,r424,r425,5488]),(⟨1,2,3⟩,[r353,r354,r355,r356,r357,r358,r359,r360,-784]),(⟨1,3,0⟩,[r335,r141,r336,r337,r338,r339,r340,r341,r342,r343,r344]),(⟨1,3,1⟩,[r67,r426,r427,r428,r429,r430,r431,r432,r433,4032]),(⟨1,3,2⟩,[r353,r354,r355,r356,r357,r358,r359,r360,-784]),(⟨1,3,3⟩,[r141,r186,r187,r188,r189,r190,r191,-704]),(⟨1,3,6⟩,[r373,r203,r374,r375,64]),(⟨1,4,0⟩,[r239,r345,r346,r347,r348,r349,r350,r351,r352,3248]),(⟨1,5,0⟩,[r353,r354,r355,r356,r357,r358,r359,r360,-784]),(⟨1,6,0⟩,[r103,r361,r362,r363,r364,r365,r366,r367]),(⟨1,6,1⟩,[r177,r368,r369,r370,r371,r372,-448]),(⟨1,6,3⟩,[r373,r203,r374,r375,64]),(⟨1,7,0⟩,[r177,r368,r369,r370,r371,r372,-448]),(⟨1,9,0⟩,[r373,r203,r374,r375,64]),(⟨2,0,0⟩,[0,r67,r251,r252,r253,r254,r255,r256,r257,r258,r259,r260,r261]),(⟨2,0,1⟩,[r324,r325,r87,r326,r327,r328,r329,r330,r331,r332,r333,r334]),(⟨2,0,2⟩,[0,r103,r376,r377,r378,r379,r380,r381,4928,r382,r383]),(⟨2,0,3⟩,[r384,r385,r386,r387,r388,r389,r390,r391,r392,r393]),(⟨2,0,6⟩,[0,r67,r304,r305,r306,r307,r308]),(⟨2,1,0⟩,[r324,r325,r87,r326,r327,r328,r329,r330,r331,r332,r333,r334]),(⟨2,1,1⟩,[r335,r25,r418,r419,r420,r421,r422,r423,r424,r425,5488]),(⟨2,1,3⟩,[r353,r354,r355,r356,r357,r358,r359,r360,-784]),(⟨2,2,0⟩,[0,r103,r376,r377,r378,r379,r380,r381,4928,r382,r383]),(⟨2,3,0⟩,[r384,r385,r386,r387,r388,r389,r390,r391,r392,r393]),(⟨2,3,1⟩,[r353,r354,r355,r356,r357,r358,r359,r360,-784]),(⟨2,6,0⟩,[0,r67,r304,r305,r306,r307,r308]),(⟨3,0,0⟩,[0,r75,r262,r263,r264,r265,r266,r267,r268,r269,r270,r271]),(⟨3,0,1⟩,[r335,r141,r336,r337,r338,r339,r340,r341,r342,r343,r344]),(⟨3,0,2⟩,[r384,r385,r386,r387,r388,r389,r390,r391,r392,r393]),(⟨3,0,3⟩,[r133,r155,r394,r395,r396,r397,r398,r399,r400]),(⟨3,0,4⟩,[r103,r401,r402,r403,r404,r405,r406,-352]),(⟨3,0,6⟩,[0,r67,r309,r310,r311,r168]),(⟨3,0,7⟩,[r373,r203,r374,r375,64]),(⟨3,1,0⟩,[r335,r141,r336,r337,r338,r339,r340,r341,r342,r343,r344]),(⟨3,1,1⟩,[r67,r426,r427,r428,r429,r430,r431,r432,r433,4032]),(⟨3,1,2⟩,[r353,r354,r355,r356,r357,r358,r359,r360,-784]),(⟨3,1,3⟩,[r141,r186,r187,r188,r189,r190,r191,-704]),(⟨3,1,6⟩,[r373,r203,r374,r375,64]),(⟨3,2,0⟩,[r384,r385,r386,r387,r388,r389,r390,r391,r392,r393]),(⟨3,2,1⟩,[r353,r354,r355,r356,r357,r358,r359,r360,-784]),(⟨3,3,0⟩,[r133,r155,r394,r395,r396,r397,r398,r399,r400]),(⟨3,3,1⟩,[r141,r186,r187,r188,r189,r190,r191,-704]),(⟨3,4,0⟩,[r103,r401,r402,r403,r404,r405,r406,-352]),(⟨3,6,0⟩,[0,r67,r309,r310,r311,r168]),(⟨3,6,1⟩,[r373,r203,r374,r375,64]),(⟨3,7,0⟩,[r373,r203,r374,r375,64]),(⟨4,0,0⟩,[0,r272,r273,r274,r275,r276,r277,r278,r279,r280,r281]),(⟨4,0,1⟩,[r239,r345,r346,r347,r348,r349,r350,r351,r352,3248]),(⟨4,0,3⟩,[r103,r401,r402,r403,r404,r405,r406,-352]),(⟨4,1,0⟩,[r239,r345,r346,r347,r348,r349,r350,r351,r352,3248]),(⟨4,3,0⟩,[r103,r401,r402,r403,r404,r405,r406,-352]),(⟨5,0,0⟩,[0,r282,r283,r284,r285,r286,r287,r288,r289,r290]),(⟨5,0,1⟩,[r353,r354,r355,r356,r357,r358,r359,r360,-784]),(⟨5,1,0⟩,[r353,r354,r355,r356,r357,r358,r359,r360,-784]),(⟨6,0,0⟩,[0,r167,r291,r292,r293,r294,r295,r296,r297]),(⟨6,0,1⟩,[r103,r361,r362,r363,r364,r365,r366,r367]),(⟨6,0,2⟩,[0,r67,r304,r305,r306,r307,r308]),(⟨6,0,3⟩,[0,r67,r309,r310,r311,r168]),(⟨6,1,0⟩,[r103,r361,r362,r363,r364,r365,r366,r367]),(⟨6,1,1⟩,[r177,r368,r369,r370,r371,r372,-448]),(⟨6,1,3⟩,[r373,r203,r374,r375,64]),(⟨6,2,0⟩,[0,r67,r304,r305,r306,r307,r308]),(⟨6,3,0⟩,[0,r67,r309,r310,r311,r168]),(⟨6,3,1⟩,[r373,r203,r374,r375,64]),(⟨7,0,0⟩,[0,r141,r298,r299,r300,r301,r302,r303]),(⟨7,0,1⟩,[r177,r368,r369,r370,r371,r372,-448]),(⟨7,0,3⟩,[r373,r203,r374,r375,64]),(⟨7,1,0⟩,[r177,r368,r369,r370,r371,r372,-448]),(⟨7,3,0⟩,[r373,r203,r374,r375,64]),(⟨8,0,0⟩,[0,r67,r304,r305,r306,r307,r308]),(⟨9,0,0⟩,[0,r67,r309,r310,r311,r168]),(⟨9,0,1⟩,[r373,r203,r374,r375,64]),(⟨9,1,0⟩,[r373,r203,r374,r375,64])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,9,-60,150,-162,33,54]),(⟨0,0,1⟩,[-3,21,-66,118,-119,49]),(⟨0,0,2⟩,[-1,10,-42,70,-49]),(⟨0,0,3⟩,[6,-22,38,-22]),(⟨0,0,6⟩,[4]),(⟨0,1,0⟩,[-3,21,-66,118,-119,49]),(⟨0,2,0⟩,[-1,10,-42,70,-49]),(⟨0,3,0⟩,[6,-22,38,-22]),(⟨0,6,0⟩,[4]),(⟨1,0,0⟩,[-3,21,-66,118,-119,49]),(⟨2,0,0⟩,[-1,10,-42,70,-49]),(⟨3,0,0⟩,[6,-22,38,-22]),(⟨6,0,0⟩,[4])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[0,-384,8064,-64256,246656,-476544,385152,5632,-79744]),(⟨0,0,1⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨0,0,2⟩,[0,384,-6400,33024,-52224,4480,12544]),(⟨0,0,3⟩,[0,384,-6656,34048,-49664,-2688]),(⟨0,1,0⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨0,1,1⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨0,1,3⟩,[-128,1536,-3840,-4608,15232]),(⟨0,2,0⟩,[0,384,-6400,33024,-52224,4480,12544]),(⟨0,3,0⟩,[0,384,-6656,34048,-49664,-2688]),(⟨0,3,1⟩,[-128,1536,-3840,-4608,15232]),(⟨1,0,0⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨1,0,1⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨1,0,3⟩,[-128,1536,-3840,-4608,15232]),(⟨1,1,0⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨1,3,0⟩,[-128,1536,-3840,-4608,15232]),(⟨2,0,0⟩,[0,384,-6400,33024,-52224,4480,12544]),(⟨3,0,0⟩,[0,384,-6656,34048,-49664,-2688]),(⟨3,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨3,1,0⟩,[-128,1536,-3840,-4608,15232])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 2 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r434) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 4 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r435) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨6,0,0⟩,[4])]

noncomputable def partial12 : Poly := [(⟨6,0,0⟩,[0,-1536,32256,-257024,986624,-1906176,1540608,22528,-318976]),(⟨6,0,1⟩,[0,-1536,28672,-193536,620544,-964096,509952,229376]),(⟨6,0,2⟩,[0,1536,-25600,132096,-208896,17920,50176]),(⟨6,0,3⟩,[0,1536,-26624,136192,-198656,-10752]),(⟨6,1,0⟩,[0,-1536,28672,-193536,620544,-964096,509952,229376]),(⟨6,1,1⟩,[512,-7168,31232,-55296,9728,250880,-426496]),(⟨6,1,3⟩,[-512,6144,-15360,-18432,60928]),(⟨6,2,0⟩,[0,1536,-25600,132096,-208896,17920,50176]),(⟨6,3,0⟩,[0,1536,-26624,136192,-198656,-10752]),(⟨6,3,1⟩,[-512,6144,-15360,-18432,60928]),(⟨7,0,0⟩,[0,-1536,28672,-193536,620544,-964096,509952,229376]),(⟨7,0,1⟩,[512,-7168,31232,-55296,9728,250880,-426496]),(⟨7,0,3⟩,[-512,6144,-15360,-18432,60928]),(⟨7,1,0⟩,[512,-7168,31232,-55296,9728,250880,-426496]),(⟨7,3,0⟩,[-512,6144,-15360,-18432,60928]),(⟨8,0,0⟩,[0,1536,-25600,132096,-208896,17920,50176]),(⟨9,0,0⟩,[0,1536,-26624,136192,-198656,-10752]),(⟨9,0,1⟩,[-512,6144,-15360,-18432,60928]),(⟨9,1,0⟩,[-512,6144,-15360,-18432,60928])]


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

noncomputable def partial8 : Poly := [(⟨0,6,0⟩,[0,-1536,32256,-257024,986624,-1906176,1540608,22528,-318976]),(⟨0,6,1⟩,[0,-1536,28672,-193536,620544,-964096,509952,229376]),(⟨0,6,2⟩,[0,1536,-25600,132096,-208896,17920,50176]),(⟨0,6,3⟩,[0,1536,-26624,136192,-198656,-10752]),(⟨0,7,0⟩,[0,-1536,28672,-193536,620544,-964096,509952,229376]),(⟨0,7,1⟩,[512,-7168,31232,-55296,9728,250880,-426496]),(⟨0,7,3⟩,[-512,6144,-15360,-18432,60928]),(⟨0,8,0⟩,[0,1536,-25600,132096,-208896,17920,50176]),(⟨0,9,0⟩,[0,1536,-26624,136192,-198656,-10752]),(⟨0,9,1⟩,[-512,6144,-15360,-18432,60928]),(⟨1,0,0⟩,[0,1152,-32256,387456,-2666880,11847552,-36002816,76670208,-113795328,112196480,-63256064,8792448,9765504,-3907456]),(⟨1,0,1⟩,[0,1152,-29568,321024,-1999872,8065792,-22264064,42827776,-56482816,47542400,-20214656,-577024,2809856]),(⟨1,0,2⟩,[0,-1152,27264,-258816,1317888,-4090624,8180480,-10438144,7533568,-1611904,-1273216,614656]),(⟨1,0,3⟩,[0,-1152,28032,-267264,1348608,-4113152,8049920,-10060800,7261184,-2113664,-131712]),(⟨1,1,0⟩,[0,1152,-29568,321024,-1999872,8065792,-22264064,42827776,-56482816,47542400,-20214656,-577024,2809856]),(⟨1,1,1⟩,[-384,8064,-69504,338816,-1039616,1916160,-1171712,-4064000,13471360,-19926144,15761536,-5224576]),(⟨1,1,3⟩,[384,-7296,52224,-183296,307456,-18176,-1016832,2157568,-2038400,746368]),(⟨1,2,0⟩,[0,-1152,27264,-258816,1317888,-4090624,8180480,-10438144,7533568,-1611904,-1273216,614656]),(⟨1,3,0⟩,[0,-1152,28032,-267264,1348608,-4113152,8049920,-10060800,7261184,-2113664,-131712]),(⟨1,3,1⟩,[384,-7296,52224,-183296,307456,-18176,-1016832,2157568,-2038400,746368]),(⟨1,6,0⟩,[0,-1536,28672,-193536,620544,-964096,509952,229376]),(⟨1,6,1⟩,[512,-7168,31232,-55296,9728,250880,-426496]),(⟨1,6,3⟩,[-512,6144,-15360,-18432,60928]),(⟨1,7,0⟩,[512,-7168,31232,-55296,9728,250880,-426496]),(⟨1,9,0⟩,[-512,6144,-15360,-18432,60928]),(⟨2,0,0⟩,[0,1536,-41472,482048,-3254656,14290944,-42667264,87102976,-117967360,96819712,-35343616,-6435072,6717312]),(⟨2,0,1⟩,[-384,8448,-80512,475008,-2006528,6261248,-13963264,20506880,-15783040,-1600256,13528704,-8034432]),(⟨2,0,2⟩,[0,-384,10240,-113152,678144,-2380544,4850944,-5336576,2345728,658560,-614656]),(⟨2,0,3⟩,[384,-7680,62720,-300032,1004032,-2426880,3751680,-2874368,206976,878080]),(⟨2,1,0⟩,[-384,8448,-80512,475008,-2006528,6261248,-13963264,20506880,-15783040,-1600256,13528704,-8034432]),(⟨2,1,1⟩,[-128,3072,-31104,176128,-600320,1176576,-718592,-2852864,8749440,-10536960,5224576]),(⟨2,1,3⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨2,2,0⟩,[0,-384,10240,-113152,678144,-2380544,4850944,-5336576,2345728,658560,-614656]),(⟨2,3,0⟩,[384,-7680,62720,-300032,1004032,-2426880,3751680,-2874368,206976,878080]),(⟨2,3,1⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨2,6,0⟩,[0,1536,-25600,132096,-208896,17920,50176]),(⟨3,0,0⟩,[0,-3072,73088,-700160,3559424,-10650368,18970368,-17841920,2796544,10209024,-6660224,-440832]),(⟨3,0,1⟩,[-128,768,20352,-286464,1675776,-5678848,12308480,-17885440,17634944,-11162624,3963008]),(⟨3,0,2⟩,[0,2304,-46848,353536,-1291520,2571520,-2734336,1043200,378112,-275968]),(⟨3,0,3⟩,[128,-512,-23808,258048,-1094656,2518528,-3351296,2282496,-687232]),(⟨3,1,0⟩,[-128,768,20352,-286464,1675776,-5678848,12308480,-17885440,17634944,-11162624,3963008]),(⟨3,1,1⟩,[768,-13568,91136,-325632,654848,-374272,-1623040,4675584,-5431552,2345728]),(⟨3,1,3⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨3,2,0⟩,[0,2304,-46848,353536,-1291520,2571520,-2734336,1043200,378112,-275968]),(⟨3,3,0⟩,[128,-512,-23808,258048,-1094656,2518528,-3351296,2282496,-687232]),(⟨3,3,1⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨3,6,0⟩,[0,1536,-26624,136192,-198656,-10752]),(⟨3,6,1⟩,[-512,6144,-15360,-18432,60928]),(⟨3,7,0⟩,[-512,6144,-15360,-18432,60928]),(⟨4,0,0⟩,[0,-3840,89728,-843008,4302848,-13349120,25927936,-30429952,18492416,-2080768,-2007936]),(⟨4,0,1⟩,[1152,-20864,143360,-508928,962304,-392448,-2639872,6833152,-7469952,3092096]),(⟨4,0,3⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨4,1,0⟩,[1152,-20864,143360,-508928,962304,-392448,-2639872,6833152,-7469952,3092096]),(⟨4,3,0⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨5,0,0⟩,[0,1920,-36352,236800,-594944,162816,2034176,-3988736,2623488,-144256]),(⟨5,0,1⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨5,1,0⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨6,0,0⟩,[0,768,-16128,108288,-321792,610560,-1036544,1012992,-259840]),(⟨6,0,1⟩,[-768,10496,-33024,-75520,633600,-1389824,1190144,-105728]),(⟨6,0,2⟩,[0,1536,-25600,132096,-208896,17920,50176]),(⟨6,0,3⟩,[0,1536,-26624,136192,-198656,-10752]),(⟨6,1,0⟩,[-768,10496,-33024,-75520,633600,-1389824,1190144,-105728]),(⟨6,1,1⟩,[512,-7168,31232,-55296,9728,250880,-426496]),(⟨6,1,3⟩,[-512,6144,-15360,-18432,60928]),(⟨6,2,0⟩,[0,1536,-25600,132096,-208896,17920,50176]),(⟨6,3,0⟩,[0,1536,-26624,136192,-198656,-10752]),(⟨6,3,1⟩,[-512,6144,-15360,-18432,60928]),(⟨7,0,0⟩,[0,-1536,28672,-193536,620544,-964096,509952,229376]),(⟨7,0,1⟩,[512,-7168,31232,-55296,9728,250880,-426496]),(⟨7,0,3⟩,[-512,6144,-15360,-18432,60928]),(⟨7,1,0⟩,[512,-7168,31232,-55296,9728,250880,-426496]),(⟨7,3,0⟩,[-512,6144,-15360,-18432,60928]),(⟨8,0,0⟩,[0,1536,-25600,132096,-208896,17920,50176]),(⟨9,0,0⟩,[0,1536,-26624,136192,-198656,-10752]),(⟨9,0,1⟩,[-512,6144,-15360,-18432,60928]),(⟨9,1,0⟩,[-512,6144,-15360,-18432,60928])]


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

noncomputable def partial4 : Poly := [(⟨0,0,6⟩,[0,-1536,32256,-257024,986624,-1906176,1540608,22528,-318976]),(⟨0,0,7⟩,[0,-1536,28672,-193536,620544,-964096,509952,229376]),(⟨0,0,8⟩,[0,1536,-25600,132096,-208896,17920,50176]),(⟨0,0,9⟩,[0,1536,-26624,136192,-198656,-10752]),(⟨0,1,0⟩,[0,1152,-32256,387456,-2666880,11847552,-36002816,76670208,-113795328,112196480,-63256064,8792448,9765504,-3907456]),(⟨0,1,1⟩,[0,1152,-29568,321024,-1999872,8065792,-22264064,42827776,-56482816,47542400,-20214656,-577024,2809856]),(⟨0,1,2⟩,[0,-1152,27264,-258816,1317888,-4090624,8180480,-10438144,7533568,-1611904,-1273216,614656]),(⟨0,1,3⟩,[0,-1152,28032,-267264,1348608,-4113152,8049920,-10060800,7261184,-2113664,-131712]),(⟨0,1,6⟩,[0,-1536,28672,-193536,620544,-964096,509952,229376]),(⟨0,1,7⟩,[512,-7168,31232,-55296,9728,250880,-426496]),(⟨0,1,9⟩,[-512,6144,-15360,-18432,60928]),(⟨0,2,0⟩,[0,1536,-41472,482048,-3254656,14290944,-42667264,87102976,-117967360,96819712,-35343616,-6435072,6717312]),(⟨0,2,1⟩,[-384,8448,-80512,475008,-2006528,6261248,-13963264,20506880,-15783040,-1600256,13528704,-8034432]),(⟨0,2,2⟩,[0,-384,10240,-113152,678144,-2380544,4850944,-5336576,2345728,658560,-614656]),(⟨0,2,3⟩,[384,-7680,62720,-300032,1004032,-2426880,3751680,-2874368,206976,878080]),(⟨0,2,6⟩,[0,1536,-25600,132096,-208896,17920,50176]),(⟨0,3,0⟩,[0,-3072,73088,-700160,3559424,-10650368,18970368,-17841920,2796544,10209024,-6660224,-440832]),(⟨0,3,1⟩,[-128,768,20352,-286464,1675776,-5678848,12308480,-17885440,17634944,-11162624,3963008]),(⟨0,3,2⟩,[0,2304,-46848,353536,-1291520,2571520,-2734336,1043200,378112,-275968]),(⟨0,3,3⟩,[128,-512,-23808,258048,-1094656,2518528,-3351296,2282496,-687232]),(⟨0,3,6⟩,[0,1536,-26624,136192,-198656,-10752]),(⟨0,3,7⟩,[-512,6144,-15360,-18432,60928]),(⟨0,4,0⟩,[0,-3840,89728,-843008,4302848,-13349120,25927936,-30429952,18492416,-2080768,-2007936]),(⟨0,4,1⟩,[1152,-20864,143360,-508928,962304,-392448,-2639872,6833152,-7469952,3092096]),(⟨0,4,3⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨0,5,0⟩,[0,1920,-36352,236800,-594944,162816,2034176,-3988736,2623488,-144256]),(⟨0,5,1⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨0,6,0⟩,[0,768,-16128,108288,-321792,610560,-1036544,1012992,-259840]),(⟨0,6,1⟩,[-768,10496,-33024,-75520,633600,-1389824,1190144,-105728]),(⟨0,6,2⟩,[0,1536,-25600,132096,-208896,17920,50176]),(⟨0,6,3⟩,[0,1536,-26624,136192,-198656,-10752]),(⟨0,7,0⟩,[0,-1536,28672,-193536,620544,-964096,509952,229376]),(⟨0,7,1⟩,[512,-7168,31232,-55296,9728,250880,-426496]),(⟨0,7,3⟩,[-512,6144,-15360,-18432,60928]),(⟨0,8,0⟩,[0,1536,-25600,132096,-208896,17920,50176]),(⟨0,9,0⟩,[0,1536,-26624,136192,-198656,-10752]),(⟨0,9,1⟩,[-512,6144,-15360,-18432,60928]),(⟨1,0,0⟩,[0,1152,-32256,387456,-2666880,11847552,-36002816,76670208,-113795328,112196480,-63256064,8792448,9765504,-3907456]),(⟨1,0,1⟩,[0,1152,-29568,321024,-1999872,8065792,-22264064,42827776,-56482816,47542400,-20214656,-577024,2809856]),(⟨1,0,2⟩,[0,-1152,27264,-258816,1317888,-4090624,8180480,-10438144,7533568,-1611904,-1273216,614656]),(⟨1,0,3⟩,[0,-1152,28032,-267264,1348608,-4113152,8049920,-10060800,7261184,-2113664,-131712]),(⟨1,0,6⟩,[0,-1536,28672,-193536,620544,-964096,509952,229376]),(⟨1,0,7⟩,[512,-7168,31232,-55296,9728,250880,-426496]),(⟨1,0,9⟩,[-512,6144,-15360,-18432,60928]),(⟨1,1,0⟩,[0,2304,-59136,642048,-3999744,16131584,-44528128,85655552,-112965632,95084800,-40429312,-1154048,5619712]),(⟨1,1,1⟩,[-768,16128,-139008,677632,-2079232,3832320,-2343424,-8128000,26942720,-39852288,31523072,-10449152]),(⟨1,1,3⟩,[768,-14592,104448,-366592,614912,-36352,-2033664,4315136,-4076800,1492736]),(⟨1,1,6⟩,[512,-7168,31232,-55296,9728,250880,-426496]),(⟨1,2,0⟩,[-384,7296,-53248,216192,-688640,2170624,-5782784,10068736,-8249472,-3212160,12255488,-7419776]),(⟨1,2,1⟩,[-128,3072,-31104,176128,-600320,1176576,-718592,-2852864,8749440,-10536960,5224576]),(⟨1,2,3⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨1,3,0⟩,[-128,-384,48384,-553728,3024384,-9792000,20358400,-27946240,24896128,-13276288,3831296]),(⟨1,3,1⟩,[1152,-20864,143360,-508928,962304,-392448,-2639872,6833152,-7469952,3092096]),(⟨1,3,3⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨1,3,6⟩,[-512,6144,-15360,-18432,60928]),(⟨1,4,0⟩,[1152,-20864,143360,-508928,962304,-392448,-2639872,6833152,-7469952,3092096]),(⟨1,5,0⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨1,6,0⟩,[-768,10496,-33024,-75520,633600,-1389824,1190144,-105728]),(⟨1,6,1⟩,[512,-7168,31232,-55296,9728,250880,-426496]),(⟨1,6,3⟩,[-512,6144,-15360,-18432,60928]),(⟨1,7,0⟩,[512,-7168,31232,-55296,9728,250880,-426496]),(⟨1,9,0⟩,[-512,6144,-15360,-18432,60928]),(⟨2,0,0⟩,[0,1536,-41472,482048,-3254656,14290944,-42667264,87102976,-117967360,96819712,-35343616,-6435072,6717312]),(⟨2,0,1⟩,[-384,8448,-80512,475008,-2006528,6261248,-13963264,20506880,-15783040,-1600256,13528704,-8034432]),(⟨2,0,2⟩,[0,-384,10240,-113152,678144,-2380544,4850944,-5336576,2345728,658560,-614656]),(⟨2,0,3⟩,[384,-7680,62720,-300032,1004032,-2426880,3751680,-2874368,206976,878080]),(⟨2,0,6⟩,[0,1536,-25600,132096,-208896,17920,50176]),(⟨2,1,0⟩,[-384,7296,-53248,216192,-688640,2170624,-5782784,10068736,-8249472,-3212160,12255488,-7419776]),(⟨2,1,1⟩,[-128,3072,-31104,176128,-600320,1176576,-718592,-2852864,8749440,-10536960,5224576]),(⟨2,1,3⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨2,2,0⟩,[0,-768,20480,-226304,1356288,-4761088,9701888,-10673152,4691456,1317120,-1229312]),(⟨2,3,0⟩,[384,-5376,15872,53504,-287488,144640,1017344,-1831168,585088,602112]),(⟨2,3,1⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨2,6,0⟩,[0,1536,-25600,132096,-208896,17920,50176]),(⟨3,0,0⟩,[0,-3072,73088,-700160,3559424,-10650368,18970368,-17841920,2796544,10209024,-6660224,-440832]),(⟨3,0,1⟩,[-128,768,20352,-286464,1675776,-5678848,12308480,-17885440,17634944,-11162624,3963008]),(⟨3,0,2⟩,[0,2304,-46848,353536,-1291520,2571520,-2734336,1043200,378112,-275968]),(⟨3,0,3⟩,[128,-512,-23808,258048,-1094656,2518528,-3351296,2282496,-687232]),(⟨3,0,6⟩,[0,1536,-26624,136192,-198656,-10752]),(⟨3,0,7⟩,[-512,6144,-15360,-18432,60928]),(⟨3,1,0⟩,[-128,-384,48384,-553728,3024384,-9792000,20358400,-27946240,24896128,-13276288,3831296]),(⟨3,1,1⟩,[1152,-20864,143360,-508928,962304,-392448,-2639872,6833152,-7469952,3092096]),(⟨3,1,3⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨3,1,6⟩,[-512,6144,-15360,-18432,60928]),(⟨3,2,0⟩,[384,-5376,15872,53504,-287488,144640,1017344,-1831168,585088,602112]),(⟨3,2,1⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨3,3,0⟩,[256,-1024,-47616,516096,-2189312,5037056,-6702592,4564992,-1374464]),(⟨3,3,1⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨3,4,0⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨3,6,0⟩,[0,1536,-26624,136192,-198656,-10752]),(⟨3,6,1⟩,[-512,6144,-15360,-18432,60928]),(⟨3,7,0⟩,[-512,6144,-15360,-18432,60928]),(⟨4,0,0⟩,[0,-3840,89728,-843008,4302848,-13349120,25927936,-30429952,18492416,-2080768,-2007936]),(⟨4,0,1⟩,[1152,-20864,143360,-508928,962304,-392448,-2639872,6833152,-7469952,3092096]),(⟨4,0,3⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨4,1,0⟩,[1152,-20864,143360,-508928,962304,-392448,-2639872,6833152,-7469952,3092096]),(⟨4,3,0⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨5,0,0⟩,[0,1920,-36352,236800,-594944,162816,2034176,-3988736,2623488,-144256]),(⟨5,0,1⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨5,1,0⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨6,0,0⟩,[0,768,-16128,108288,-321792,610560,-1036544,1012992,-259840]),(⟨6,0,1⟩,[-768,10496,-33024,-75520,633600,-1389824,1190144,-105728]),(⟨6,0,2⟩,[0,1536,-25600,132096,-208896,17920,50176]),(⟨6,0,3⟩,[0,1536,-26624,136192,-198656,-10752]),(⟨6,1,0⟩,[-768,10496,-33024,-75520,633600,-1389824,1190144,-105728]),(⟨6,1,1⟩,[512,-7168,31232,-55296,9728,250880,-426496]),(⟨6,1,3⟩,[-512,6144,-15360,-18432,60928]),(⟨6,2,0⟩,[0,1536,-25600,132096,-208896,17920,50176]),(⟨6,3,0⟩,[0,1536,-26624,136192,-198656,-10752]),(⟨6,3,1⟩,[-512,6144,-15360,-18432,60928]),(⟨7,0,0⟩,[0,-1536,28672,-193536,620544,-964096,509952,229376]),(⟨7,0,1⟩,[512,-7168,31232,-55296,9728,250880,-426496]),(⟨7,0,3⟩,[-512,6144,-15360,-18432,60928]),(⟨7,1,0⟩,[512,-7168,31232,-55296,9728,250880,-426496]),(⟨7,3,0⟩,[-512,6144,-15360,-18432,60928]),(⟨8,0,0⟩,[0,1536,-25600,132096,-208896,17920,50176]),(⟨9,0,0⟩,[0,1536,-26624,136192,-198656,-10752]),(⟨9,0,1⟩,[-512,6144,-15360,-18432,60928]),(⟨9,1,0⟩,[-512,6144,-15360,-18432,60928])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,0,-3456,95616,-1119744,7347072,-30045696,79712256,-136183296,138587136,-59171712,-25897344,33902592,-2327424,-4306176]),(⟨0,0,1⟩,[0,1152,-35712,475008,-3590016,17284224,-55911680,123603456,-183423744,169431680,-74883968,-9305472,18542208,-810880]),(⟨0,0,2⟩,[0,1536,-38016,401408,-2515840,10817280,-33490432,73573120,-108843520,98035456,-40048000,-5779200,7394688]),(⟨0,0,3⟩,[0,-3072,76544,-783104,4322816,-14200832,28124160,-30844928,11203072,10844160,-9430784,-585984]),(⟨0,0,4⟩,[0,-3840,89728,-843008,4302848,-13349120,25927936,-30429952,18492416,-2080768,-2007936]),(⟨0,0,5⟩,[0,1920,-36352,236800,-594944,162816,2034176,-3988736,2623488,-144256]),(⟨0,0,6⟩,[0,768,-16128,108288,-321792,610560,-1036544,1012992,-259840]),(⟨0,0,7⟩,[0,-1536,28672,-193536,620544,-964096,509952,229376]),(⟨0,0,8⟩,[0,1536,-25600,132096,-208896,17920,50176]),(⟨0,0,9⟩,[0,1536,-26624,136192,-198656,-10752]),(⟨0,1,0⟩,[0,1152,-35712,475008,-3590016,17284224,-55911680,123603456,-183423744,169431680,-74883968,-9305472,18542208,-810880]),(⟨0,1,1⟩,[0,3456,-82944,839040,-4882176,18448640,-47500288,83697920,-97588736,68264320,-20955136,-1285760,-137984]),(⟨0,1,2⟩,[-384,7296,-53248,216192,-688640,2170624,-5782784,10068736,-8249472,-3212160,12255488,-7419776]),(⟨0,1,3⟩,[-128,-1536,69888,-699648,3464448,-10207488,19419136,-24958720,22069120,-13022464,4653824]),(⟨0,1,4⟩,[1152,-20864,143360,-508928,962304,-392448,-2639872,6833152,-7469952,3092096]),(⟨0,1,5⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨0,1,6⟩,[-768,10496,-33024,-75520,633600,-1389824,1190144,-105728]),(⟨0,1,7⟩,[512,-7168,31232,-55296,9728,250880,-426496]),(⟨0,1,9⟩,[-512,6144,-15360,-18432,60928]),(⟨0,2,0⟩,[0,1536,-38016,401408,-2515840,10817280,-33490432,73573120,-108843520,98035456,-40048000,-5779200,7394688]),(⟨0,2,1⟩,[-384,7296,-53248,216192,-688640,2170624,-5782784,10068736,-8249472,-3212160,12255488,-7419776]),(⟨0,2,2⟩,[0,-768,20480,-226304,1356288,-4761088,9701888,-10673152,4691456,1317120,-1229312]),(⟨0,2,3⟩,[384,-5376,15872,53504,-287488,144640,1017344,-1831168,585088,602112]),(⟨0,2,6⟩,[0,1536,-25600,132096,-208896,17920,50176]),(⟨0,3,0⟩,[0,-3072,76544,-783104,4322816,-14200832,28124160,-30844928,11203072,10844160,-9430784,-585984]),(⟨0,3,1⟩,[-128,-1536,69888,-699648,3464448,-10207488,19419136,-24958720,22069120,-13022464,4653824]),(⟨0,3,2⟩,[384,-5376,15872,53504,-287488,144640,1017344,-1831168,585088,602112]),(⟨0,3,3⟩,[256,-1024,-47616,516096,-2189312,5037056,-6702592,4564992,-1374464]),(⟨0,3,4⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨0,3,6⟩,[0,1536,-26624,136192,-198656,-10752]),(⟨0,3,7⟩,[-512,6144,-15360,-18432,60928]),(⟨0,4,0⟩,[0,-3840,89728,-843008,4302848,-13349120,25927936,-30429952,18492416,-2080768,-2007936]),(⟨0,4,1⟩,[1152,-20864,143360,-508928,962304,-392448,-2639872,6833152,-7469952,3092096]),(⟨0,4,3⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨0,5,0⟩,[0,1920,-36352,236800,-594944,162816,2034176,-3988736,2623488,-144256]),(⟨0,5,1⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨0,6,0⟩,[0,768,-16128,108288,-321792,610560,-1036544,1012992,-259840]),(⟨0,6,1⟩,[-768,10496,-33024,-75520,633600,-1389824,1190144,-105728]),(⟨0,6,2⟩,[0,1536,-25600,132096,-208896,17920,50176]),(⟨0,6,3⟩,[0,1536,-26624,136192,-198656,-10752]),(⟨0,7,0⟩,[0,-1536,28672,-193536,620544,-964096,509952,229376]),(⟨0,7,1⟩,[512,-7168,31232,-55296,9728,250880,-426496]),(⟨0,7,3⟩,[-512,6144,-15360,-18432,60928]),(⟨0,8,0⟩,[0,1536,-25600,132096,-208896,17920,50176]),(⟨0,9,0⟩,[0,1536,-26624,136192,-198656,-10752]),(⟨0,9,1⟩,[-512,6144,-15360,-18432,60928]),(⟨1,0,0⟩,[0,1152,-35712,475008,-3590016,17284224,-55911680,123603456,-183423744,169431680,-74883968,-9305472,18542208,-810880]),(⟨1,0,1⟩,[0,3456,-82944,839040,-4882176,18448640,-47500288,83697920,-97588736,68264320,-20955136,-1285760,-137984]),(⟨1,0,2⟩,[-384,7296,-53248,216192,-688640,2170624,-5782784,10068736,-8249472,-3212160,12255488,-7419776]),(⟨1,0,3⟩,[-128,-1536,69888,-699648,3464448,-10207488,19419136,-24958720,22069120,-13022464,4653824]),(⟨1,0,4⟩,[1152,-20864,143360,-508928,962304,-392448,-2639872,6833152,-7469952,3092096]),(⟨1,0,5⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨1,0,6⟩,[-768,10496,-33024,-75520,633600,-1389824,1190144,-105728]),(⟨1,0,7⟩,[512,-7168,31232,-55296,9728,250880,-426496]),(⟨1,0,9⟩,[-512,6144,-15360,-18432,60928]),(⟨1,1,0⟩,[0,3456,-82944,839040,-4882176,18448640,-47500288,83697920,-97588736,68264320,-20955136,-1285760,-137984]),(⟨1,1,1⟩,[-1152,24192,-208512,1016448,-3118848,5748480,-3515136,-12192000,40414080,-59778432,47284608,-15673728]),(⟨1,1,2⟩,[-128,3072,-31104,176128,-600320,1176576,-718592,-2852864,8749440,-10536960,5224576]),(⟨1,1,3⟩,[1536,-28160,195584,-692224,1269760,-410624,-3656704,8990720,-9508352,3838464]),(⟨1,1,6⟩,[512,-7168,31232,-55296,9728,250880,-426496]),(⟨1,2,0⟩,[-384,7296,-53248,216192,-688640,2170624,-5782784,10068736,-8249472,-3212160,12255488,-7419776]),(⟨1,2,1⟩,[-128,3072,-31104,176128,-600320,1176576,-718592,-2852864,8749440,-10536960,5224576]),(⟨1,2,3⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨1,3,0⟩,[-128,-1536,69888,-699648,3464448,-10207488,19419136,-24958720,22069120,-13022464,4653824]),(⟨1,3,1⟩,[1536,-28160,195584,-692224,1269760,-410624,-3656704,8990720,-9508352,3838464]),(⟨1,3,2⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨1,3,3⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨1,3,6⟩,[-512,6144,-15360,-18432,60928]),(⟨1,4,0⟩,[1152,-20864,143360,-508928,962304,-392448,-2639872,6833152,-7469952,3092096]),(⟨1,5,0⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨1,6,0⟩,[-768,10496,-33024,-75520,633600,-1389824,1190144,-105728]),(⟨1,6,1⟩,[512,-7168,31232,-55296,9728,250880,-426496]),(⟨1,6,3⟩,[-512,6144,-15360,-18432,60928]),(⟨1,7,0⟩,[512,-7168,31232,-55296,9728,250880,-426496]),(⟨1,9,0⟩,[-512,6144,-15360,-18432,60928]),(⟨2,0,0⟩,[0,1536,-38016,401408,-2515840,10817280,-33490432,73573120,-108843520,98035456,-40048000,-5779200,7394688]),(⟨2,0,1⟩,[-384,7296,-53248,216192,-688640,2170624,-5782784,10068736,-8249472,-3212160,12255488,-7419776]),(⟨2,0,2⟩,[0,-768,20480,-226304,1356288,-4761088,9701888,-10673152,4691456,1317120,-1229312]),(⟨2,0,3⟩,[384,-5376,15872,53504,-287488,144640,1017344,-1831168,585088,602112]),(⟨2,0,6⟩,[0,1536,-25600,132096,-208896,17920,50176]),(⟨2,1,0⟩,[-384,7296,-53248,216192,-688640,2170624,-5782784,10068736,-8249472,-3212160,12255488,-7419776]),(⟨2,1,1⟩,[-128,3072,-31104,176128,-600320,1176576,-718592,-2852864,8749440,-10536960,5224576]),(⟨2,1,3⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨2,2,0⟩,[0,-768,20480,-226304,1356288,-4761088,9701888,-10673152,4691456,1317120,-1229312]),(⟨2,3,0⟩,[384,-5376,15872,53504,-287488,144640,1017344,-1831168,585088,602112]),(⟨2,3,1⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨2,6,0⟩,[0,1536,-25600,132096,-208896,17920,50176]),(⟨3,0,0⟩,[0,-3072,76544,-783104,4322816,-14200832,28124160,-30844928,11203072,10844160,-9430784,-585984]),(⟨3,0,1⟩,[-128,-1536,69888,-699648,3464448,-10207488,19419136,-24958720,22069120,-13022464,4653824]),(⟨3,0,2⟩,[384,-5376,15872,53504,-287488,144640,1017344,-1831168,585088,602112]),(⟨3,0,3⟩,[256,-1024,-47616,516096,-2189312,5037056,-6702592,4564992,-1374464]),(⟨3,0,4⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨3,0,6⟩,[0,1536,-26624,136192,-198656,-10752]),(⟨3,0,7⟩,[-512,6144,-15360,-18432,60928]),(⟨3,1,0⟩,[-128,-1536,69888,-699648,3464448,-10207488,19419136,-24958720,22069120,-13022464,4653824]),(⟨3,1,1⟩,[1536,-28160,195584,-692224,1269760,-410624,-3656704,8990720,-9508352,3838464]),(⟨3,1,2⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨3,1,3⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨3,1,6⟩,[-512,6144,-15360,-18432,60928]),(⟨3,2,0⟩,[384,-5376,15872,53504,-287488,144640,1017344,-1831168,585088,602112]),(⟨3,2,1⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨3,3,0⟩,[256,-1024,-47616,516096,-2189312,5037056,-6702592,4564992,-1374464]),(⟨3,3,1⟩,[-1536,24064,-123392,236032,26112,-851456,1360384,-670208]),(⟨3,4,0⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨3,6,0⟩,[0,1536,-26624,136192,-198656,-10752]),(⟨3,6,1⟩,[-512,6144,-15360,-18432,60928]),(⟨3,7,0⟩,[-512,6144,-15360,-18432,60928]),(⟨4,0,0⟩,[0,-3840,89728,-843008,4302848,-13349120,25927936,-30429952,18492416,-2080768,-2007936]),(⟨4,0,1⟩,[1152,-20864,143360,-508928,962304,-392448,-2639872,6833152,-7469952,3092096]),(⟨4,0,3⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨4,1,0⟩,[1152,-20864,143360,-508928,962304,-392448,-2639872,6833152,-7469952,3092096]),(⟨4,3,0⟩,[-768,12032,-61696,118016,13056,-425728,680192,-335104]),(⟨5,0,0⟩,[0,1920,-36352,236800,-594944,162816,2034176,-3988736,2623488,-144256]),(⟨5,0,1⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨5,1,0⟩,[128,-2816,24576,-107264,213760,1792,-774144,1292032,-746368]),(⟨6,0,0⟩,[0,768,-16128,108288,-321792,610560,-1036544,1012992,-259840]),(⟨6,0,1⟩,[-768,10496,-33024,-75520,633600,-1389824,1190144,-105728]),(⟨6,0,2⟩,[0,1536,-25600,132096,-208896,17920,50176]),(⟨6,0,3⟩,[0,1536,-26624,136192,-198656,-10752]),(⟨6,1,0⟩,[-768,10496,-33024,-75520,633600,-1389824,1190144,-105728]),(⟨6,1,1⟩,[512,-7168,31232,-55296,9728,250880,-426496]),(⟨6,1,3⟩,[-512,6144,-15360,-18432,60928]),(⟨6,2,0⟩,[0,1536,-25600,132096,-208896,17920,50176]),(⟨6,3,0⟩,[0,1536,-26624,136192,-198656,-10752]),(⟨6,3,1⟩,[-512,6144,-15360,-18432,60928]),(⟨7,0,0⟩,[0,-1536,28672,-193536,620544,-964096,509952,229376]),(⟨7,0,1⟩,[512,-7168,31232,-55296,9728,250880,-426496]),(⟨7,0,3⟩,[-512,6144,-15360,-18432,60928]),(⟨7,1,0⟩,[512,-7168,31232,-55296,9728,250880,-426496]),(⟨7,3,0⟩,[-512,6144,-15360,-18432,60928]),(⟨8,0,0⟩,[0,1536,-25600,132096,-208896,17920,50176]),(⟨9,0,0⟩,[0,1536,-26624,136192,-198656,-10752]),(⟨9,0,1⟩,[-512,6144,-15360,-18432,60928]),(⟨9,1,0⟩,[-512,6144,-15360,-18432,60928])]


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
    (Poly.add (Poly.scale (K.ofRat r436) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 2 4).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r434*r435 : ℚ)=r436 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 2 4 r434 r435 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 2=4 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 2 4).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C074

#print axioms Coulomb8.Columns.C074.sound
