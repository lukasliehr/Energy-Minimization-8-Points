import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C125

def r0 : ℚ := { num := 4096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -18432, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 1761280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -13711360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 66330624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -193929216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 229912576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 99344384, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -4304191488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 11409971200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -18685448192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 19445667840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -11794853888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := 193691648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := -46530560, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := 2048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := -98304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 249856, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -16291840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 89694208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -293703680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 442830848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := 665337856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := -5488232448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := 15046184960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := -24193712128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := 23544813568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := -12126117888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := 277381120, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -8192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 219136, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -2260992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 641024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -17412096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -70979584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 456245248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -1045393408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 714293248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 2036611072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -6109642752, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 6881060864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -416649216, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -4096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 194560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -3022848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 3143680, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -80896000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 108736512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 306479104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := -1823535104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := 4213108736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := -5330544640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 464117760, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -45344768, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -73728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 147456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := 4190208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -32444416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 85045248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 184320, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -81186816, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 1646215168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -2238763008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 181653504, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -96256, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 1249280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -356352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 7086080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := 33792000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := -145133568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 264695808, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -208971776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -3151872, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := -16384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := 376832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := -2605056, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := 5521408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 1294336, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -66830336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 147701760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -19906560, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := -40960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := 1200128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := -14266368, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := 90750976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := -329891840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := 590036992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 45883392, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -4811137024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 13462757376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := -20438716416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 17202008064, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -900653056, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := -2048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := 90112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -1269760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 7620608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -16236544, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := -38400000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 313544704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -791027712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 114849792, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 483201024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -2153017344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 251521024, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := 45056, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := -1163264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 10960896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -6782976, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 81666048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 104529920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -125124608, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 2107801600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -2507755520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := 177815552, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := -188416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := 344064, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := -12361728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := 24846336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 10739712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -24461312, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 410492928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := -3035136, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := 8192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -204800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 262144, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -6725632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 5120000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 31760384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := -113352704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := 209002496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := -246530048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := 33030144, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := -31596544, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := 6144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 32768, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -876544, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := -6557696, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 45600768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -113786880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 24043520, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -122365952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := -5380096, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := 24576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := -475136, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := 3350528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := -10354688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 9216000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := 3555328, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := -68952064, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := 425984, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := -94208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := 741376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := -2109440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := -118784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 9023488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -1175552, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -28672, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := -32768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := 491520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := -2162688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 1769472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := 7438336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := -98304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := 16384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := -196608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := 212992, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := -9666560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 36552704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := -83886080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 157499392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -25329664, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -12288, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 561152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -741376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -3952640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 9277440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 6533120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -167936, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := -245760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := 3244032, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -24489984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 16048128, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -295182336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 253485056, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := 1112375296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := -5008965632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := 10039910400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := -10954006528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := 44453888, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 1388544, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -73728, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 33161216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := -65241088, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -3096576, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 492429312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -1403490304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 2110869504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -11964416, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := 28672, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := -1875968, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := 8167424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := -14114816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := -16334848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 147005440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -401448960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := 598802432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := -3256320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := 122880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -1294336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := 5611520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := -5775360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := -33218560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 142852096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -259563520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := 1658880, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 393216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := -3571712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 15663104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -34996224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := 25165824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 88637440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := -2293760, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -180224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 1368064, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -3833856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 253952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := 868352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := -360448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := 2736128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := -7667712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := 507904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := 1736704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := 180224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := -1368064, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := 3833856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := -253952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -868352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := 1482752, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := -4218880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := -237568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := 18046976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := -2351104, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -57344, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := -65536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := 983040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := -4325376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := 3538944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := 14876672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := -196608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := -9216, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := 880640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := -6855680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := 33165312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := -96964608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := 114956288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := 49672192, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -2152095744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := 5704985600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -9342724096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 9722833920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -5897426944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := 96845824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := -23265280, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := 1024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -49152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := 124928, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := -8145920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := 44847104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := -146851840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := 221415424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := 332668928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -2744116224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 7523092480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := -12096856064, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := 11772406784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := -6063058944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := 138690560, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := 109568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := -1130496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := 320512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := -8706048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := -35489792, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := 228122624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := -522696704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := 357146624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := 1018305536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := -3054821376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := 3440530432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := -208324608, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := 97280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := -1511424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := 1571840, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := -40448000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := 54368256, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := 153239552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := -911767552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := 2106554368, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := -2665272320, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := 232058880, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := -22672384, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := -36864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := 73728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := 2095104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := -16222208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := 42522624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 92160, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -40593408, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 823107584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -1119381504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 90826752, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -48128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 624640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := -178176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 3543040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := 16896000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := -72566784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := 132347904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := -104485888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := -1575936, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := 188416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := -1302528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := 2760704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := 647168, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -33415168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 73850880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -9953280, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := -20480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := 600064, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := -7133184, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := 45375488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := -164945920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := 295018496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 22941696, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -2405568512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 6731378688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -10219358208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 8601004032, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := -450326528, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := -1024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := -634880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := 3810304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := -8118272, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := -19200000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := 156772352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := -395513856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := 57424896, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := 241600512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := -1076508672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := 125760512, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := 22528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := -581632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := 5480448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := -3391488, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := 40833024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := 52264960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := -62562304, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := 1053900800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := -1253877760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := 88907776, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := 172032, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := -6180864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := 12423168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := 5369856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := -12230656, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := 205246464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := -1517568, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := -102400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := 131072, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := -3362816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := 2560000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := 15880192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := -56676352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := 104501248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := -123265024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := 16515072, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := -15798272, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := 3072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := 16384, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := -438272, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := -3278848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := 22800384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := -56893440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := 12021760, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := -61182976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := -2690048, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := 12288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := 1675264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := -5177344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := 4608000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := 1777664, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := -34476032, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := 212992, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := -47104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := 370688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := -1054720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := -59392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := 4511744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := -587776, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := -14336, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := 245760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := -1081344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := 884736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := 3719168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := -49152, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := 106496, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := -4833280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := 18276352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := -41943040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := 78749696, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := -12664832, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := -6144, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := 280576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := -370688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := -1976320, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := 4638720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := 3266560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := -83968, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := -122880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := 1622016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := -12244992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := 8024064, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := -147591168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := 126742528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := 556187648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := -2504482816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := 5019955200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := -5477003264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := 22226944, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := 694272, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := -36864, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := 16580608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := -32620544, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := -1548288, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := 246214656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := -701745152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := 1055434752, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := -5982208, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := 14336, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := -937984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := 4083712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := -7057408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := -8167424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := 73502720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := -200724480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := 299401216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := -1628160, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := 61440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := -647168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := 2805760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r450 : ℚ := { num := -2887680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r451 : ℚ := { num := -16609280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r452 : ℚ := { num := 71426048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r453 : ℚ := { num := -129781760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r454 : ℚ := { num := 829440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r455 : ℚ := { num := 196608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r456 : ℚ := { num := -1785856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r457 : ℚ := { num := 7831552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r458 : ℚ := { num := -17498112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r459 : ℚ := { num := 12582912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r460 : ℚ := { num := 44318720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r461 : ℚ := { num := -1146880, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r462 : ℚ := { num := -90112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r463 : ℚ := { num := 684032, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r464 : ℚ := { num := -1916928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r465 : ℚ := { num := 126976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r466 : ℚ := { num := 434176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r467 : ℚ := { num := -684032, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r468 : ℚ := { num := 1916928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r469 : ℚ := { num := -126976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r470 : ℚ := { num := -434176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r471 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r472 : ℚ := { num := 1, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r473 : ℚ := { num := 1, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14],[r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28],[r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41],[r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53],[r0,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63],[r15,r64,r65,r66,r67,r68,r69,r70,r71,r72],[0,r73,r74,r75,r76,r77,r78,r79,r80],[],[],[],[],[],[],[0,r81,r82,r83,r84,r85,r86,r87,r88,r89,r90,r91,r92],[r93,r94,r95,r96,r97,r98,r99,r100,r101,r102,r103,r104],[0,r105,r106,r107,r108,r109,r110,r111,r112,r113,r114],[0,r0,r115,r116,r117,r118,r119,r120,r121,r122],[],[],[],[],[],[],[],[r123,r124,r125,r126,r127,r128,r129,r130,r131,r132,r133],[r93,r134,r135,r136,r137,r138,r139,r140,r141,r142],[0,r143,r144,r145,r146,r147,r148,r149,r150],[r0,r151,r152,r153,r154,r155,r156,r157],[0,r158,r159,r160,r161,r162,r163],[],[],[],[],[0,r164,r165,r166,r167,r168,r169,r170,r171],[r0,r172,r173,r174,r175,r176,r177,r178],[0,r158,r159,r160,r161,r162,r163],[],[],[],[],[],[],[],[],[],[],[],[],[],[r123,r179,r180,r181,r182,r183,r184,r185,r186,r187,r188,r189],[r0,r154,r190,r191,r192,r193,r194,r195,r196,r197,r198],[r29,r199,r200,r201,r202,r203,r204,r205,r206,r207],[r42,r208,r209,r210,r211,r212,r213,r214,r215],[],[],[],[],[],[],[0,r73,r216,r217,r218,r219,r220,r221,r222,114688],[0,r143,r144,r145,r146,r147,r148,r149,r150],[0,r123,r223,r224,r225,r226,r227,-8192],[],[],[],[],[],[0,r164,r228,r229,r230,r231,r232,-16384],[r29,r233,r234,r235,r236,r237,8192],[],[],[],[],[],[],[],[],[],[],[],[r123,r115,r238,r239,r240,r241,r242,r243],[],[],[],[],[],[0,r244,r245,r246,r247,r248,r249],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[r15,r250,r251,r252,r253,r254,r255,r256,r257,r258,r259,r260,r261,r262,r263]),(⟨0,0,1⟩,[r264,r265,r266,r267,r268,r269,r270,r271,r272,r273,r274,r275,r276,r277]),(⟨0,0,2⟩,[r42,r278,r279,r280,r281,r282,r283,r284,r285,r286,r287,r288,r289]),(⟨0,0,3⟩,[r93,r290,r291,r292,r293,r294,r295,r296,r297,r298,r299,r300]),(⟨0,0,4⟩,[r15,r301,r302,r303,r304,r305,r306,r307,r308,r309,r310]),(⟨0,0,5⟩,[r264,r311,r312,r313,r314,r315,r316,r317,r318,r319]),(⟨0,0,6⟩,[0,r29,r320,r321,r322,r323,r324,r325,r326]),(⟨0,1,0⟩,[r264,r265,r266,r267,r268,r269,r270,r271,r272,r273,r274,r275,r276,r277]),(⟨0,1,1⟩,[0,r327,r328,r329,r330,r331,r332,r333,r334,r335,r336,r337,r338]),(⟨0,1,2⟩,[r339,r105,r340,r341,r342,r343,r344,r345,r346,r347,r348,r349]),(⟨0,1,3⟩,[0,r350,r351,r352,r353,r354,r355,r356,r357,r358,r359]),(⟨0,1,4⟩,[0,r15,r151,r360,r361,r362,r363,r364,r365,r366]),(⟨0,2,0⟩,[r42,r278,r279,r280,r281,r282,r283,r284,r285,r286,r287,r288,r289]),(⟨0,2,1⟩,[r339,r105,r340,r341,r342,r343,r344,r345,r346,r347,r348,r349]),(⟨0,2,2⟩,[r0,r367,r368,r369,r370,r371,r372,r373,r374,r375,r376]),(⟨0,2,3⟩,[r339,r377,r378,r379,r380,r381,r382,r383,r384,r385]),(⟨0,2,4⟩,[0,r386,r240,r387,r388,r389,r390,r391,r392]),(⟨0,2,5⟩,[r15,r393,r394,r395,r396,r397,r398,r399]),(⟨0,2,6⟩,[0,r73,r400,r401,r402,r403,r404]),(⟨0,3,0⟩,[r93,r290,r291,r292,r293,r294,r295,r296,r297,r298,r299,r300]),(⟨0,3,1⟩,[0,r350,r351,r352,r353,r354,r355,r356,r357,r358,r359]),(⟨0,3,2⟩,[r339,r377,r378,r379,r380,r381,r382,r383,r384,r385]),(⟨0,3,3⟩,[0,r123,r16,r405,r406,r407,r408,r409,r410]),(⟨0,3,4⟩,[r15,r411,r412,r413,r414,r415,r416,r417]),(⟨0,3,5⟩,[0,r73,r400,r401,r402,r403,r404]),(⟨0,4,0⟩,[r15,r301,r302,r303,r304,r305,r306,r307,r308,r309,r310]),(⟨0,4,1⟩,[0,r15,r151,r360,r361,r362,r363,r364,r365,r366]),(⟨0,4,2⟩,[0,r386,r240,r387,r388,r389,r390,r391,r392]),(⟨0,4,3⟩,[r15,r411,r412,r413,r414,r415,r416,r417]),(⟨0,5,0⟩,[r264,r311,r312,r313,r314,r315,r316,r317,r318,r319]),(⟨0,5,2⟩,[r15,r393,r394,r395,r396,r397,r398,r399]),(⟨0,5,3⟩,[0,r73,r400,r401,r402,r403,r404]),(⟨0,6,0⟩,[0,r29,r320,r321,r322,r323,r324,r325,r326]),(⟨0,6,2⟩,[0,r73,r400,r401,r402,r403,r404]),(⟨1,0,0⟩,[r264,r265,r266,r267,r268,r269,r270,r271,r272,r273,r274,r275,r276,r277]),(⟨1,0,1⟩,[0,r327,r328,r329,r330,r331,r332,r333,r334,r335,r336,r337,r338]),(⟨1,0,2⟩,[r339,r105,r340,r341,r342,r343,r344,r345,r346,r347,r348,r349]),(⟨1,0,3⟩,[0,r350,r351,r352,r353,r354,r355,r356,r357,r358,r359]),(⟨1,0,4⟩,[0,r15,r151,r360,r361,r362,r363,r364,r365,r366]),(⟨1,1,0⟩,[0,r327,r328,r329,r330,r331,r332,r333,r334,r335,r336,r337,r338]),(⟨1,1,1⟩,[r0,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427,r428]),(⟨1,1,2⟩,[r15,r396,r429,r430,r431,r432,r433,r434,r435,r436,r437]),(⟨1,1,3⟩,[r42,r438,r439,r440,r441,r442,r443,r444,r445,r446]),(⟨1,1,4⟩,[r93,r447,r448,r449,r450,r451,r452,r453,r454]),(⟨1,2,0⟩,[r339,r105,r340,r341,r342,r343,r344,r345,r346,r347,r348,r349]),(⟨1,2,1⟩,[r15,r396,r429,r430,r431,r432,r433,r434,r435,r436,r437]),(⟨1,2,2⟩,[0,r29,r455,r456,r457,r458,r459,r460,r461,57344]),(⟨1,2,3⟩,[0,r386,r240,r387,r388,r389,r390,r391,r392]),(⟨1,2,4⟩,[0,r0,r462,r463,r464,r465,r466,-4096]),(⟨1,3,0⟩,[0,r350,r351,r352,r353,r354,r355,r356,r357,r358,r359]),(⟨1,3,1⟩,[r42,r438,r439,r440,r441,r442,r443,r444,r445,r446]),(⟨1,3,2⟩,[0,r386,r240,r387,r388,r389,r390,r391,r392]),(⟨1,3,3⟩,[0,r123,r223,r224,r225,r226,r227,-8192]),(⟨1,3,4⟩,[r42,r94,r467,r468,r469,r470,4096]),(⟨1,4,0⟩,[0,r15,r151,r360,r361,r362,r363,r364,r365,r366]),(⟨1,4,1⟩,[r93,r447,r448,r449,r450,r451,r452,r453,r454]),(⟨1,4,2⟩,[0,r0,r462,r463,r464,r465,r466,-4096]),(⟨1,4,3⟩,[r42,r94,r467,r468,r469,r470,4096]),(⟨2,0,0⟩,[r42,r278,r279,r280,r281,r282,r283,r284,r285,r286,r287,r288,r289]),(⟨2,0,1⟩,[r339,r105,r340,r341,r342,r343,r344,r345,r346,r347,r348,r349]),(⟨2,0,2⟩,[r0,r367,r368,r369,r370,r371,r372,r373,r374,r375,r376]),(⟨2,0,3⟩,[r339,r377,r378,r379,r380,r381,r382,r383,r384,r385]),(⟨2,0,4⟩,[0,r386,r240,r387,r388,r389,r390,r391,r392]),(⟨2,0,5⟩,[r15,r393,r394,r395,r396,r397,r398,r399]),(⟨2,0,6⟩,[0,r73,r400,r401,r402,r403,r404]),(⟨2,1,0⟩,[r339,r105,r340,r341,r342,r343,r344,r345,r346,r347,r348,r349]),(⟨2,1,1⟩,[r15,r396,r429,r430,r431,r432,r433,r434,r435,r436,r437]),(⟨2,1,2⟩,[0,r29,r455,r456,r457,r458,r459,r460,r461,57344]),(⟨2,1,3⟩,[0,r386,r240,r387,r388,r389,r390,r391,r392]),(⟨2,1,4⟩,[0,r0,r462,r463,r464,r465,r466,-4096]),(⟨2,2,0⟩,[r0,r367,r368,r369,r370,r371,r372,r373,r374,r375,r376]),(⟨2,2,1⟩,[0,r29,r455,r456,r457,r458,r459,r460,r461,57344]),(⟨2,2,3⟩,[r0,r151,r152,r153,r154,r155,r156,r157]),(⟨2,3,0⟩,[r339,r377,r378,r379,r380,r381,r382,r383,r384,r385]),(⟨2,3,1⟩,[0,r386,r240,r387,r388,r389,r390,r391,r392]),(⟨2,3,2⟩,[r0,r151,r152,r153,r154,r155,r156,r157]),(⟨2,3,3⟩,[0,r158,r159,r160,r161,r162,r163]),(⟨2,4,0⟩,[0,r386,r240,r387,r388,r389,r390,r391,r392]),(⟨2,4,1⟩,[0,r0,r462,r463,r464,r465,r466,-4096]),(⟨2,5,0⟩,[r15,r393,r394,r395,r396,r397,r398,r399]),(⟨2,6,0⟩,[0,r73,r400,r401,r402,r403,r404]),(⟨3,0,0⟩,[r93,r290,r291,r292,r293,r294,r295,r296,r297,r298,r299,r300]),(⟨3,0,1⟩,[0,r350,r351,r352,r353,r354,r355,r356,r357,r358,r359]),(⟨3,0,2⟩,[r339,r377,r378,r379,r380,r381,r382,r383,r384,r385]),(⟨3,0,3⟩,[0,r123,r16,r405,r406,r407,r408,r409,r410]),(⟨3,0,4⟩,[r15,r411,r412,r413,r414,r415,r416,r417]),(⟨3,0,5⟩,[0,r73,r400,r401,r402,r403,r404]),(⟨3,1,0⟩,[0,r350,r351,r352,r353,r354,r355,r356,r357,r358,r359]),(⟨3,1,1⟩,[r42,r438,r439,r440,r441,r442,r443,r444,r445,r446]),(⟨3,1,2⟩,[0,r386,r240,r387,r388,r389,r390,r391,r392]),(⟨3,1,3⟩,[0,r123,r223,r224,r225,r226,r227,-8192]),(⟨3,1,4⟩,[r42,r94,r467,r468,r469,r470,4096]),(⟨3,2,0⟩,[r339,r377,r378,r379,r380,r381,r382,r383,r384,r385]),(⟨3,2,1⟩,[0,r386,r240,r387,r388,r389,r390,r391,r392]),(⟨3,2,2⟩,[r0,r151,r152,r153,r154,r155,r156,r157]),(⟨3,2,3⟩,[0,r158,r159,r160,r161,r162,r163]),(⟨3,3,0⟩,[0,r123,r16,r405,r406,r407,r408,r409,r410]),(⟨3,3,1⟩,[0,r123,r223,r224,r225,r226,r227,-8192]),(⟨3,3,2⟩,[0,r158,r159,r160,r161,r162,r163]),(⟨3,4,0⟩,[r15,r411,r412,r413,r414,r415,r416,r417]),(⟨3,4,1⟩,[r42,r94,r467,r468,r469,r470,4096]),(⟨3,5,0⟩,[0,r73,r400,r401,r402,r403,r404]),(⟨4,0,0⟩,[r15,r301,r302,r303,r304,r305,r306,r307,r308,r309,r310]),(⟨4,0,1⟩,[0,r15,r151,r360,r361,r362,r363,r364,r365,r366]),(⟨4,0,2⟩,[0,r386,r240,r387,r388,r389,r390,r391,r392]),(⟨4,0,3⟩,[r15,r411,r412,r413,r414,r415,r416,r417]),(⟨4,1,0⟩,[0,r15,r151,r360,r361,r362,r363,r364,r365,r366]),(⟨4,1,1⟩,[r93,r447,r448,r449,r450,r451,r452,r453,r454]),(⟨4,1,2⟩,[0,r0,r462,r463,r464,r465,r466,-4096]),(⟨4,1,3⟩,[r42,r94,r467,r468,r469,r470,4096]),(⟨4,2,0⟩,[0,r386,r240,r387,r388,r389,r390,r391,r392]),(⟨4,2,1⟩,[0,r0,r462,r463,r464,r465,r466,-4096]),(⟨4,3,0⟩,[r15,r411,r412,r413,r414,r415,r416,r417]),(⟨4,3,1⟩,[r42,r94,r467,r468,r469,r470,4096]),(⟨5,0,0⟩,[r264,r311,r312,r313,r314,r315,r316,r317,r318,r319]),(⟨5,0,2⟩,[r15,r393,r394,r395,r396,r397,r398,r399]),(⟨5,0,3⟩,[0,r73,r400,r401,r402,r403,r404]),(⟨5,2,0⟩,[r15,r393,r394,r395,r396,r397,r398,r399]),(⟨5,3,0⟩,[0,r73,r400,r401,r402,r403,r404]),(⟨6,0,0⟩,[0,r29,r320,r321,r322,r323,r324,r325,r326]),(⟨6,0,2⟩,[0,r73,r400,r401,r402,r403,r404]),(⟨6,2,0⟩,[0,r73,r400,r401,r402,r403,r404])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[128,-2368,16192,-48960,27712,296128,-1096256,1862976,-1545664,318080]),(⟨0,0,1⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨0,0,2⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨0,0,3⟩,[-64,1280,-6336,2560,43072,-131840,181440]),(⟨0,1,0⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨0,1,1⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248]),(⟨0,2,0⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨0,2,3⟩,[-128,1536,-3840,-4608,15232]),(⟨0,3,0⟩,[-64,1280,-6336,2560,43072,-131840,181440]),(⟨0,3,2⟩,[-128,1536,-3840,-4608,15232]),(⟨1,0,0⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨1,0,1⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248]),(⟨1,1,0⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248]),(⟨2,0,0⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨2,0,3⟩,[-128,1536,-3840,-4608,15232]),(⟨2,3,0⟩,[-128,1536,-3840,-4608,15232]),(⟨3,0,0⟩,[-64,1280,-6336,2560,43072,-131840,181440]),(⟨3,0,2⟩,[-128,1536,-3840,-4608,15232]),(⟨3,2,0⟩,[-128,1536,-3840,-4608,15232])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[16,-208,1008,-2480,2688,-512]),(⟨0,0,1⟩,[0,-96,704,-1760,1664]),(⟨0,0,2⟩,[-16,176,-304,-112]),(⟨0,0,3⟩,[0,128,-384]),(⟨0,1,0⟩,[0,-96,704,-1760,1664]),(⟨0,1,1⟩,[0,-32,320,-544]),(⟨0,2,0⟩,[-16,176,-304,-112]),(⟨0,3,0⟩,[0,128,-384]),(⟨1,0,0⟩,[0,-96,704,-1760,1664]),(⟨1,0,1⟩,[0,-32,320,-544]),(⟨1,1,0⟩,[0,-32,320,-544]),(⟨1,1,1⟩,[32,-320,544]),(⟨2,0,0⟩,[-16,176,-304,-112]),(⟨3,0,0⟩,[0,128,-384])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 7 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r471) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 10 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r472) sourceRight))).isZero := by decide +kernel

noncomputable def partial19 : Poly := []

theorem partial_sound19 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 19)
      sourceRight).eval u v t=partial19.eval u v t := by rfl

noncomputable def chunk16 : Poly := [(⟨3,0,0⟩,[-64,1280,-6336,2560,43072,-131840,181440]),(⟨3,0,2⟩,[-128,1536,-3840,-4608,15232]),(⟨3,2,0⟩,[-128,1536,-3840,-4608,15232])]

noncomputable def partial16 : Poly := [(⟨3,0,0⟩,[-1024,33792,-432128,2807808,-9576448,10698752,49707008,-267327488,624321536,-826409984,555212800,-92897280]),(⟨3,0,1⟩,[0,6144,-167936,1622016,-7065600,10948608,27930624,-181780480,431443968,-538716160,301916160]),(⟨3,0,2⟩,[-1024,19456,-163840,1052672,-5277696,15525888,-23814144,18993152,2911232,-28120064]),(⟨3,0,3⟩,[0,4096,-49152,372736,-2416640,9138176,-20971520,39374848,-44326912]),(⟨3,0,4⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨3,0,5⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨3,1,0⟩,[0,6144,-167936,1622016,-7065600,10948608,27930624,-181780480,431443968,-538716160,301916160]),(⟨3,1,1⟩,[0,2048,-61440,647168,-2805760,2887680,16609280,-71426048,129781760,-98703360]),(⟨3,1,2⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨3,1,3⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨3,2,0⟩,[-1024,19456,-163840,1052672,-5277696,15525888,-23814144,18993152,2911232,-28120064]),(⟨3,2,1⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨3,2,2⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨3,2,3⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨3,3,0⟩,[0,4096,-49152,372736,-2416640,9138176,-20971520,39374848,-44326912]),(⟨3,3,1⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨3,3,2⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨3,4,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨3,5,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨4,0,0⟩,[0,6144,-167936,1622016,-7065600,10948608,27930624,-181780480,431443968,-538716160,301916160]),(⟨4,0,1⟩,[0,2048,-61440,647168,-2805760,2887680,16609280,-71426048,129781760,-98703360]),(⟨4,0,2⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨4,0,3⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨4,1,0⟩,[0,2048,-61440,647168,-2805760,2887680,16609280,-71426048,129781760,-98703360]),(⟨4,1,1⟩,[-2048,61440,-647168,2805760,-2887680,-16609280,71426048,-129781760,98703360]),(⟨4,1,2⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨4,1,3⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨4,2,0⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨4,2,1⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨4,3,0⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨4,3,1⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨5,0,0⟩,[1024,-31744,346112,-1538048,1544192,9621504,-39487488,67188736,-40391680,-20321280]),(⟨5,0,2⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨5,2,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨6,0,0⟩,[0,-8192,188416,-1302528,2760704,4530176,-33415168,73850880,-69672960]),(⟨6,0,2⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨6,2,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088])]


theorem partial_checked16 :
    (Poly.add (Poly.add (Poly.mul chunk16 sourceRight) partial19)
      (Poly.scale (K.ofRat (-1)) partial16)).isZero := by decide +kernel

theorem partial_sound16 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 16)
      sourceRight).eval u v t=partial16.eval u v t := by
  change (Poly.mul (chunk16++(sourceLeft.drop 19))
    sourceRight).eval u v t=partial16.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound19 partial_checked16 u v t


noncomputable def chunk12 : Poly := [(⟨1,1,0⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248]),(⟨2,0,0⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨2,0,3⟩,[-128,1536,-3840,-4608,15232]),(⟨2,3,0⟩,[-128,1536,-3840,-4608,15232])]

noncomputable def partial12 : Poly := [(⟨1,1,0⟩,[0,-4096,110592,-1253376,7938048,-31145984,75366400,-87777280,-76423168,498814976,-863547392,637435904,-109182976]),(⟨1,1,1⟩,[0,0,24576,-524288,4472832,-20381696,53379072,-66027520,-54214656,362807296,-584048640,354844672]),(⟨1,1,2⟩,[0,4096,-102400,958464,-4251648,9289728,-5505024,-27107328,76210176,-50778112,-23883776]),(⟨1,1,3⟩,[0,0,-32768,557056,-3375104,9535488,-11239424,-14188544,75464704,-81887232]),(⟨1,2,0⟩,[0,0,24576,-524288,4472832,-20381696,53379072,-66027520,-54214656,362807296,-584048640,354844672]),(⟨1,2,1⟩,[0,0,8192,-196608,1785856,-7831552,17498112,-12582912,-44318720,136478720,-116006912]),(⟨1,3,0⟩,[0,4096,-102400,958464,-4251648,9289728,-5505024,-27107328,76210176,-50778112,-23883776]),(⟨1,4,0⟩,[0,0,-32768,557056,-3375104,9535488,-11239424,-14188544,75464704,-81887232]),(⟨2,0,0⟩,[-2048,55296,-602112,3377152,-9689088,5519360,64591872,-273623040,583254016,-756297728,546748416,-146358272,12386304]),(⟨2,0,1⟩,[0,12288,-262144,2088960,-7475200,7233536,39653376,-185884672,398200832,-490852352,306900992,-40255488]),(⟨2,0,2⟩,[2048,-51200,454656,-1583104,387072,11855872,-37087232,58542080,-39473152,-10436608,2709504]),(⟨2,0,3⟩,[-2048,34816,-231424,1099776,-4823040,13178880,-17405952,16963584,-20791296,1490944]),(⟨2,0,4⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨2,0,5⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨2,0,6⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨2,1,0⟩,[0,12288,-237568,1564672,-3002368,-13148160,93032448,-251912192,343986176,-128045056,-277147648,314589184]),(⟨2,1,1⟩,[0,4096,-90112,647168,-1093632,-6955008,38088704,-80715776,70791168,42323968,-102846464]),(⟨2,1,3⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨2,1,4⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨2,2,0⟩,[2048,-51200,462848,-1779712,2172928,4024320,-19589120,45959168,-83791872,126042112,-113297408]),(⟨2,2,1⟩,[0,-8192,196608,-1785856,7831552,-17498112,12582912,44318720,-136478720,116006912]),(⟨2,2,3⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨2,3,0⟩,[-2048,34816,-231424,1099776,-4823040,13178880,-17405952,16963584,-20791296,1490944]),(⟨2,3,1⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨2,3,2⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨2,3,3⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨2,4,0⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨2,4,1⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨2,5,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨2,6,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨3,0,0⟩,[-1024,46080,-694272,4896768,-17051648,17932288,89360384,-453212160,1022522368,-1317262336,862113792,-133152768]),(⟨3,0,1⟩,[0,10240,-266240,2465792,-9945088,11825152,48521216,-249913344,546553856,-632870912,315076608]),(⟨3,0,2⟩,[-1024,19456,-163840,1052672,-5277696,15525888,-23814144,18993152,2911232,-28120064]),(⟨3,0,3⟩,[0,16384,-286720,2048000,-7593984,13746176,-8527872,4898816,-18980864]),(⟨3,0,4⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨3,0,5⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨3,1,0⟩,[0,14336,-368640,3424256,-14196736,21114880,43016192,-277020672,622764032,-683649024,291192832]),(⟨3,1,1⟩,[-4096,100352,-905216,3526656,-3682304,-17702912,84742144,-186535936,223936512,-111863808]),(⟨3,1,2⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨3,1,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,1,4⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨3,2,0⟩,[-1024,19456,-163840,1052672,-5277696,15525888,-23814144,18993152,2911232,-28120064]),(⟨3,2,1⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨3,2,2⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨3,2,3⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨3,3,0⟩,[0,16384,-286720,2048000,-7593984,13746176,-8527872,4898816,-18980864]),(⟨3,3,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,3,2⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨3,4,0⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨3,4,1⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨3,5,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨4,0,0⟩,[2048,-45056,286720,38912,-6678528,22804480,-9156608,-123238400,391970816,-549152768,304625664]),(⟨4,0,1⟩,[0,2048,-61440,647168,-2805760,2887680,16609280,-71426048,129781760,-98703360]),(⟨4,0,2⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨4,0,3⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨4,1,0⟩,[0,2048,-94208,1204224,-6180864,12423168,5369856,-85614592,205246464,-180590592]),(⟨4,1,1⟩,[-2048,61440,-647168,2805760,-2887680,-16609280,71426048,-129781760,98703360]),(⟨4,1,2⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨4,1,3⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨4,2,0⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨4,2,1⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨4,3,0⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨4,3,1⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨5,0,0⟩,[1024,-48128,624640,-3028992,3543040,16896000,-72566784,132347904,-104485888,-11031552]),(⟨5,0,2⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨5,0,3⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨5,2,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨5,3,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨6,0,0⟩,[0,-8192,188416,-1302528,2760704,4530176,-33415168,73850880,-69672960]),(⟨6,0,2⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨6,2,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088])]


theorem partial_checked12 :
    (Poly.add (Poly.add (Poly.mul chunk12 sourceRight) partial16)
      (Poly.scale (K.ofRat (-1)) partial12)).isZero := by decide +kernel

theorem partial_sound12 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 12)
      sourceRight).eval u v t=partial12.eval u v t := by
  change (Poly.mul (chunk12++(sourceLeft.drop 16))
    sourceRight).eval u v t=partial12.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound16 partial_checked12 u v t


noncomputable def chunk8 : Poly := [(⟨0,3,0⟩,[-64,1280,-6336,2560,43072,-131840,181440]),(⟨0,3,2⟩,[-128,1536,-3840,-4608,15232]),(⟨1,0,0⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨1,0,1⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248])]

noncomputable def partial8 : Poly := [(⟨0,3,0⟩,[-1024,33792,-432128,2807808,-9576448,10698752,49707008,-267327488,624321536,-826409984,555212800,-92897280]),(⟨0,3,1⟩,[0,6144,-167936,1622016,-7065600,10948608,27930624,-181780480,431443968,-538716160,301916160]),(⟨0,3,2⟩,[-1024,19456,-163840,1052672,-5277696,15525888,-23814144,18993152,2911232,-28120064]),(⟨0,3,3⟩,[0,4096,-49152,372736,-2416640,9138176,-20971520,39374848,-44326912]),(⟨0,3,4⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨0,3,5⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨0,4,0⟩,[0,6144,-167936,1622016,-7065600,10948608,27930624,-181780480,431443968,-538716160,301916160]),(⟨0,4,1⟩,[0,2048,-61440,647168,-2805760,2887680,16609280,-71426048,129781760,-98703360]),(⟨0,4,2⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨0,4,3⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨0,5,0⟩,[1024,-31744,346112,-1538048,1544192,9621504,-39487488,67188736,-40391680,-20321280]),(⟨0,5,2⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨0,6,0⟩,[0,-8192,188416,-1302528,2760704,4530176,-33415168,73850880,-69672960]),(⟨0,6,2⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨1,0,0⟩,[1024,-36864,557056,-4699136,24367104,-77285376,117221376,149196800,-1318433792,3641006080,-5875165184,5728117760,-2931253248,441548800]),(⟨1,0,1⟩,[0,-10240,296960,-3520512,22638592,-85364736,172179456,-20975616,-955240448,2994108416,-4782327808,4147906560,-1544216576]),(⟨1,0,2⟩,[-1024,34816,-440320,2599936,-6438912,-6293504,89995264,-270548992,370394112,-71974912,-455999488,451433472]),(⟨1,0,3⟩,[0,12288,-315392,3014656,-13795328,29007872,3743744,-188022784,507346944,-621006848,307277824]),(⟨1,0,4⟩,[0,0,-32768,557056,-3375104,9535488,-11239424,-14188544,75464704,-81887232]),(⟨1,1,0⟩,[0,-10240,296960,-3520512,22638592,-85364736,172179456,-20975616,-955240448,2994108416,-4782327808,4147906560,-1544216576]),(⟨1,1,1⟩,[0,-2048,116736,-1927168,14741504,-60903424,133881856,-71135232,-475049984,1530042368,-2095507456,1178834944]),(⟨1,1,2⟩,[0,4096,-94208,761856,-2465792,1458176,11993088,-39690240,31891456,85700608,-139890688]),(⟨1,1,3⟩,[0,0,-32768,557056,-3375104,9535488,-11239424,-14188544,75464704,-81887232]),(⟨1,2,0⟩,[-1024,34816,-440320,2599936,-6438912,-6293504,89995264,-270548992,370394112,-71974912,-455999488,451433472]),(⟨1,2,1⟩,[0,4096,-94208,761856,-2465792,1458176,11993088,-39690240,31891456,85700608,-139890688]),(⟨1,3,0⟩,[0,18432,-483328,4636672,-20860928,39956480,31674368,-369803264,938790912,-1159723008,609193984]),(⟨1,3,1⟩,[0,2048,-94208,1204224,-6180864,12423168,5369856,-85614592,205246464,-180590592]),(⟨1,3,2⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨1,3,3⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨1,4,0⟩,[0,2048,-94208,1204224,-6180864,12423168,5369856,-85614592,205246464,-180590592]),(⟨1,4,1⟩,[-2048,61440,-647168,2805760,-2887680,-16609280,71426048,-129781760,98703360]),(⟨1,4,2⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨1,4,3⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨2,0,0⟩,[-2048,49152,-415744,1110016,5011456,-48699392,161404928,-206821376,-295563264,1738995712,-3372032000,3364112384,-1422647296]),(⟨2,0,1⟩,[0,10240,-169984,686080,2793472,-33288192,120156160,-190992384,-22634496,676382720,-1204557824,783734784]),(⟨2,0,2⟩,[2048,-51200,462848,-1779712,2172928,4024320,-19589120,45959168,-83791872,126042112,-113297408]),(⟨2,0,3⟩,[-2048,34816,-231424,1099776,-4823040,13178880,-17405952,16963584,-20791296,1490944]),(⟨2,0,4⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨2,0,5⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨2,0,6⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨2,1,0⟩,[0,10240,-169984,686080,2793472,-33288192,120156160,-190992384,-22634496,676382720,-1204557824,783734784]),(⟨2,1,1⟩,[2048,-63488,796672,-5345280,20832256,-41910272,-5332992,273321984,-777955328,1106212864,-687998976]),(⟨2,1,2⟩,[0,-8192,196608,-1785856,7831552,-17498112,12582912,44318720,-136478720,116006912]),(⟨2,1,3⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨2,1,4⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨2,2,0⟩,[2048,-51200,462848,-1779712,2172928,4024320,-19589120,45959168,-83791872,126042112,-113297408]),(⟨2,2,1⟩,[0,-8192,196608,-1785856,7831552,-17498112,12582912,44318720,-136478720,116006912]),(⟨2,2,3⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨2,3,0⟩,[-1024,3072,114688,-438272,-3278848,22800384,-56893440,84152320,-61182976,-18830336]),(⟨2,3,1⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨2,3,2⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨2,3,3⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨2,4,0⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨2,4,1⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨2,5,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨2,6,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨3,0,0⟩,[-2048,80896,-1159168,8020992,-27963392,32020480,125976576,-657733632,1447131136,-1752044544,990162944,-36563968]),(⟨3,0,1⟩,[0,14336,-368640,3424256,-14196736,21114880,43016192,-277020672,622764032,-683649024,291192832]),(⟨3,0,2⟩,[-1024,19456,-163840,1052672,-5277696,15525888,-23814144,18993152,2911232,-28120064]),(⟨3,0,3⟩,[0,16384,-286720,2048000,-7593984,13746176,-8527872,4898816,-18980864]),(⟨3,0,4⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨3,0,5⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨3,1,0⟩,[0,14336,-368640,3424256,-14196736,21114880,43016192,-277020672,622764032,-683649024,291192832]),(⟨3,1,1⟩,[-4096,100352,-905216,3526656,-3682304,-17702912,84742144,-186535936,223936512,-111863808]),(⟨3,1,2⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨3,1,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,1,4⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨3,2,0⟩,[-1024,19456,-163840,1052672,-5277696,15525888,-23814144,18993152,2911232,-28120064]),(⟨3,2,1⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨3,2,2⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨3,2,3⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨3,3,0⟩,[0,8192,-98304,745472,-4833280,18276352,-41943040,78749696,-88653824]),(⟨3,3,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,3,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨3,4,0⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨3,4,1⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨3,5,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨4,0,0⟩,[2048,-36864,73728,2095104,-16222208,42522624,92160,-284153856,823107584,-1119381504,635787264]),(⟨4,0,1⟩,[0,2048,-94208,1204224,-6180864,12423168,5369856,-85614592,205246464,-180590592]),(⟨4,0,2⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨4,0,3⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨4,1,0⟩,[0,2048,-94208,1204224,-6180864,12423168,5369856,-85614592,205246464,-180590592]),(⟨4,1,1⟩,[-2048,61440,-647168,2805760,-2887680,-16609280,71426048,-129781760,98703360]),(⟨4,1,2⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨4,1,3⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨4,2,0⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨4,2,1⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨4,3,0⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨4,3,1⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨5,0,0⟩,[1024,-48128,624640,-3028992,3543040,16896000,-72566784,132347904,-104485888,-11031552]),(⟨5,0,2⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨5,0,3⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨5,2,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨5,3,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨6,0,0⟩,[0,-8192,188416,-1302528,2760704,4530176,-33415168,73850880,-69672960]),(⟨6,0,2⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨6,2,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088])]


theorem partial_checked8 :
    (Poly.add (Poly.add (Poly.mul chunk8 sourceRight) partial12)
      (Poly.scale (K.ofRat (-1)) partial8)).isZero := by decide +kernel

theorem partial_sound8 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 8)
      sourceRight).eval u v t=partial8.eval u v t := by
  change (Poly.mul (chunk8++(sourceLeft.drop 12))
    sourceRight).eval u v t=partial8.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound12 partial_checked8 u v t


noncomputable def chunk4 : Poly := [(⟨0,1,0⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨0,1,1⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248]),(⟨0,2,0⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨0,2,3⟩,[-128,1536,-3840,-4608,15232])]

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[1024,-36864,557056,-4699136,24367104,-77285376,117221376,149196800,-1318433792,3641006080,-5875165184,5728117760,-2931253248,441548800]),(⟨0,1,1⟩,[0,-10240,296960,-3520512,22638592,-85364736,172179456,-20975616,-955240448,2994108416,-4782327808,4147906560,-1544216576]),(⟨0,1,2⟩,[-1024,34816,-440320,2599936,-6438912,-6293504,89995264,-270548992,370394112,-71974912,-455999488,451433472]),(⟨0,1,3⟩,[0,12288,-315392,3014656,-13795328,29007872,3743744,-188022784,507346944,-621006848,307277824]),(⟨0,1,4⟩,[0,0,-32768,557056,-3375104,9535488,-11239424,-14188544,75464704,-81887232]),(⟨0,2,0⟩,[-2048,49152,-415744,1110016,5011456,-48699392,161404928,-206821376,-295563264,1738995712,-3372032000,3364112384,-1422647296]),(⟨0,2,1⟩,[0,10240,-169984,686080,2793472,-33288192,120156160,-190992384,-22634496,676382720,-1204557824,783734784]),(⟨0,2,2⟩,[2048,-51200,462848,-1779712,2172928,4024320,-19589120,45959168,-83791872,126042112,-113297408]),(⟨0,2,3⟩,[-2048,34816,-231424,1099776,-4823040,13178880,-17405952,16963584,-20791296,1490944]),(⟨0,2,4⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨0,2,5⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨0,2,6⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨0,3,0⟩,[-2048,80896,-1159168,8020992,-27963392,32020480,125976576,-657733632,1447131136,-1752044544,990162944,-36563968]),(⟨0,3,1⟩,[0,14336,-368640,3424256,-14196736,21114880,43016192,-277020672,622764032,-683649024,291192832]),(⟨0,3,2⟩,[-1024,19456,-163840,1052672,-5277696,15525888,-23814144,18993152,2911232,-28120064]),(⟨0,3,3⟩,[0,16384,-286720,2048000,-7593984,13746176,-8527872,4898816,-18980864]),(⟨0,3,4⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨0,3,5⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨0,4,0⟩,[2048,-36864,73728,2095104,-16222208,42522624,92160,-284153856,823107584,-1119381504,635787264]),(⟨0,4,1⟩,[0,2048,-94208,1204224,-6180864,12423168,5369856,-85614592,205246464,-180590592]),(⟨0,4,2⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨0,4,3⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨0,5,0⟩,[1024,-48128,624640,-3028992,3543040,16896000,-72566784,132347904,-104485888,-11031552]),(⟨0,5,2⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨0,5,3⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨0,6,0⟩,[0,-8192,188416,-1302528,2760704,4530176,-33415168,73850880,-69672960]),(⟨0,6,2⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨1,0,0⟩,[1024,-36864,557056,-4699136,24367104,-77285376,117221376,149196800,-1318433792,3641006080,-5875165184,5728117760,-2931253248,441548800]),(⟨1,0,1⟩,[0,-10240,296960,-3520512,22638592,-85364736,172179456,-20975616,-955240448,2994108416,-4782327808,4147906560,-1544216576]),(⟨1,0,2⟩,[-1024,34816,-440320,2599936,-6438912,-6293504,89995264,-270548992,370394112,-71974912,-455999488,451433472]),(⟨1,0,3⟩,[0,12288,-315392,3014656,-13795328,29007872,3743744,-188022784,507346944,-621006848,307277824]),(⟨1,0,4⟩,[0,0,-32768,557056,-3375104,9535488,-11239424,-14188544,75464704,-81887232]),(⟨1,1,0⟩,[0,-16384,483328,-5787648,37339136,-139583488,268992512,45826048,-1834057728,5489401856,-8701108224,7658377216,-2979250176]),(⟨1,1,1⟩,[0,-4096,208896,-3330048,25010176,-101425152,214384640,-76242944,-895885312,2697277440,-3606966272,2002825216]),(⟨1,1,2⟩,[0,4096,-86016,565248,-679936,-6373376,29491200,-52273152,-12427264,222179328,-255897600]),(⟨1,1,3⟩,[0,0,-32768,557056,-3375104,9535488,-11239424,-14188544,75464704,-81887232]),(⟨1,2,0⟩,[-1024,45056,-634880,3810304,-8118272,-19200000,156772352,-395513856,401974272,241600512,-1076508672,880323584]),(⟨1,2,1⟩,[2048,-59392,694272,-4386816,16580608,-32620544,-10838016,246214656,-701745152,1055434752,-711882752]),(⟨1,2,2⟩,[0,-8192,196608,-1785856,7831552,-17498112,12582912,44318720,-136478720,116006912]),(⟨1,2,3⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨1,2,4⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨1,3,0⟩,[0,22528,-581632,5480448,-23740416,40833024,52264960,-437936128,1053900800,-1253877760,622354432]),(⟨1,3,1⟩,[-4096,100352,-937984,4083712,-7057408,-8167424,73502720,-200724480,299401216,-193751040]),(⟨1,3,2⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨1,3,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨1,3,4⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨1,4,0⟩,[0,2048,-94208,1204224,-6180864,12423168,5369856,-85614592,205246464,-180590592]),(⟨1,4,1⟩,[-2048,61440,-647168,2805760,-2887680,-16609280,71426048,-129781760,98703360]),(⟨1,4,2⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨1,4,3⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨2,0,0⟩,[-2048,49152,-415744,1110016,5011456,-48699392,161404928,-206821376,-295563264,1738995712,-3372032000,3364112384,-1422647296]),(⟨2,0,1⟩,[0,10240,-169984,686080,2793472,-33288192,120156160,-190992384,-22634496,676382720,-1204557824,783734784]),(⟨2,0,2⟩,[2048,-51200,462848,-1779712,2172928,4024320,-19589120,45959168,-83791872,126042112,-113297408]),(⟨2,0,3⟩,[-2048,34816,-231424,1099776,-4823040,13178880,-17405952,16963584,-20791296,1490944]),(⟨2,0,4⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨2,0,5⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨2,0,6⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨2,1,0⟩,[-1024,45056,-634880,3810304,-8118272,-19200000,156772352,-395513856,401974272,241600512,-1076508672,880323584]),(⟨2,1,1⟩,[2048,-59392,694272,-4386816,16580608,-32620544,-10838016,246214656,-701745152,1055434752,-711882752]),(⟨2,1,2⟩,[0,-8192,196608,-1785856,7831552,-17498112,12582912,44318720,-136478720,116006912]),(⟨2,1,3⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨2,1,4⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨2,2,0⟩,[4096,-102400,917504,-3362816,2560000,15880192,-56676352,104501248,-123265024,115605504,-110587904]),(⟨2,2,1⟩,[0,-8192,196608,-1785856,7831552,-17498112,12582912,44318720,-136478720,116006912]),(⟨2,2,3⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨2,3,0⟩,[-1024,3072,114688,-438272,-3278848,22800384,-56893440,84152320,-61182976,-18830336]),(⟨2,3,1⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨2,3,2⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨2,3,3⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨2,4,0⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨2,4,1⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨2,5,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨2,6,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨3,0,0⟩,[-2048,80896,-1159168,8020992,-27963392,32020480,125976576,-657733632,1447131136,-1752044544,990162944,-36563968]),(⟨3,0,1⟩,[0,14336,-368640,3424256,-14196736,21114880,43016192,-277020672,622764032,-683649024,291192832]),(⟨3,0,2⟩,[-1024,19456,-163840,1052672,-5277696,15525888,-23814144,18993152,2911232,-28120064]),(⟨3,0,3⟩,[0,16384,-286720,2048000,-7593984,13746176,-8527872,4898816,-18980864]),(⟨3,0,4⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨3,0,5⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨3,1,0⟩,[0,22528,-581632,5480448,-23740416,40833024,52264960,-437936128,1053900800,-1253877760,622354432]),(⟨3,1,1⟩,[-4096,100352,-937984,4083712,-7057408,-8167424,73502720,-200724480,299401216,-193751040]),(⟨3,1,2⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨3,1,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,1,4⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨3,2,0⟩,[-1024,3072,114688,-438272,-3278848,22800384,-56893440,84152320,-61182976,-18830336]),(⟨3,2,1⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨3,2,2⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨3,2,3⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨3,3,0⟩,[0,8192,-98304,745472,-4833280,18276352,-41943040,78749696,-88653824]),(⟨3,3,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,3,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨3,4,0⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨3,4,1⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨3,5,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨4,0,0⟩,[2048,-36864,73728,2095104,-16222208,42522624,92160,-284153856,823107584,-1119381504,635787264]),(⟨4,0,1⟩,[0,2048,-94208,1204224,-6180864,12423168,5369856,-85614592,205246464,-180590592]),(⟨4,0,2⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨4,0,3⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨4,1,0⟩,[0,2048,-94208,1204224,-6180864,12423168,5369856,-85614592,205246464,-180590592]),(⟨4,1,1⟩,[-2048,61440,-647168,2805760,-2887680,-16609280,71426048,-129781760,98703360]),(⟨4,1,2⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨4,1,3⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨4,2,0⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨4,2,1⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨4,3,0⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨4,3,1⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨5,0,0⟩,[1024,-48128,624640,-3028992,3543040,16896000,-72566784,132347904,-104485888,-11031552]),(⟨5,0,2⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨5,0,3⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨5,2,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨5,3,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨6,0,0⟩,[0,-8192,188416,-1302528,2760704,4530176,-33415168,73850880,-69672960]),(⟨6,0,2⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨6,2,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088])]


theorem partial_checked4 :
    (Poly.add (Poly.add (Poly.mul chunk4 sourceRight) partial8)
      (Poly.scale (K.ofRat (-1)) partial4)).isZero := by decide +kernel

theorem partial_sound4 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 4)
      sourceRight).eval u v t=partial4.eval u v t := by
  change (Poly.mul (chunk4++(sourceLeft.drop 8))
    sourceRight).eval u v t=partial4.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound8 partial_checked4 u v t


noncomputable def chunk0 : Poly := [(⟨0,0,0⟩,[128,-2368,16192,-48960,27712,296128,-1096256,1862976,-1545664,318080]),(⟨0,0,1⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨0,0,2⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨0,0,3⟩,[-64,1280,-6336,2560,43072,-131840,181440])]

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[2048,-64512,880640,-6855680,33165312,-96964608,114956288,347705344,-2152095744,5704985600,-9342724096,9722833920,-5897426944,1646379008,-162856960]),(⟨0,0,1⟩,[1024,-49152,874496,-8145920,44847104,-146851840,221415424,332668928,-2744116224,7523092480,-12096856064,11772406784,-6063058944,970833920]),(⟨0,0,2⟩,[-4096,109568,-1130496,5448704,-8706048,-35489792,228122624,-522696704,357146624,1018305536,-3054821376,3440530432,-1458272256]),(⟨0,0,3⟩,[-2048,97280,-1511424,11002880,-40448000,54368256,153239552,-911767552,2106554368,-2665272320,1624412160,-158706688]),(⟨0,0,4⟩,[2048,-36864,73728,2095104,-16222208,42522624,92160,-284153856,823107584,-1119381504,635787264]),(⟨0,0,5⟩,[1024,-48128,624640,-3028992,3543040,16896000,-72566784,132347904,-104485888,-11031552]),(⟨0,0,6⟩,[0,-8192,188416,-1302528,2760704,4530176,-33415168,73850880,-69672960]),(⟨0,1,0⟩,[1024,-49152,874496,-8145920,44847104,-146851840,221415424,332668928,-2744116224,7523092480,-12096856064,11772406784,-6063058944,970833920]),(⟨0,1,1⟩,[0,-20480,600064,-7133184,45375488,-164945920,295018496,160591872,-2405568512,6731378688,-10219358208,8601004032,-3152285696]),(⟨0,1,2⟩,[-1024,45056,-634880,3810304,-8118272,-19200000,156772352,-395513856,401974272,241600512,-1076508672,880323584]),(⟨0,1,3⟩,[0,22528,-581632,5480448,-23740416,40833024,52264960,-437936128,1053900800,-1253877760,622354432]),(⟨0,1,4⟩,[0,2048,-94208,1204224,-6180864,12423168,5369856,-85614592,205246464,-180590592]),(⟨0,2,0⟩,[-4096,109568,-1130496,5448704,-8706048,-35489792,228122624,-522696704,357146624,1018305536,-3054821376,3440530432,-1458272256]),(⟨0,2,1⟩,[-1024,45056,-634880,3810304,-8118272,-19200000,156772352,-395513856,401974272,241600512,-1076508672,880323584]),(⟨0,2,2⟩,[4096,-102400,917504,-3362816,2560000,15880192,-56676352,104501248,-123265024,115605504,-110587904]),(⟨0,2,3⟩,[-1024,3072,114688,-438272,-3278848,22800384,-56893440,84152320,-61182976,-18830336]),(⟨0,2,4⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨0,2,5⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨0,2,6⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨0,3,0⟩,[-2048,97280,-1511424,11002880,-40448000,54368256,153239552,-911767552,2106554368,-2665272320,1624412160,-158706688]),(⟨0,3,1⟩,[0,22528,-581632,5480448,-23740416,40833024,52264960,-437936128,1053900800,-1253877760,622354432]),(⟨0,3,2⟩,[-1024,3072,114688,-438272,-3278848,22800384,-56893440,84152320,-61182976,-18830336]),(⟨0,3,3⟩,[0,8192,-98304,745472,-4833280,18276352,-41943040,78749696,-88653824]),(⟨0,3,4⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨0,3,5⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨0,4,0⟩,[2048,-36864,73728,2095104,-16222208,42522624,92160,-284153856,823107584,-1119381504,635787264]),(⟨0,4,1⟩,[0,2048,-94208,1204224,-6180864,12423168,5369856,-85614592,205246464,-180590592]),(⟨0,4,2⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨0,4,3⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨0,5,0⟩,[1024,-48128,624640,-3028992,3543040,16896000,-72566784,132347904,-104485888,-11031552]),(⟨0,5,2⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨0,5,3⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨0,6,0⟩,[0,-8192,188416,-1302528,2760704,4530176,-33415168,73850880,-69672960]),(⟨0,6,2⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨1,0,0⟩,[1024,-49152,874496,-8145920,44847104,-146851840,221415424,332668928,-2744116224,7523092480,-12096856064,11772406784,-6063058944,970833920]),(⟨1,0,1⟩,[0,-20480,600064,-7133184,45375488,-164945920,295018496,160591872,-2405568512,6731378688,-10219358208,8601004032,-3152285696]),(⟨1,0,2⟩,[-1024,45056,-634880,3810304,-8118272,-19200000,156772352,-395513856,401974272,241600512,-1076508672,880323584]),(⟨1,0,3⟩,[0,22528,-581632,5480448,-23740416,40833024,52264960,-437936128,1053900800,-1253877760,622354432]),(⟨1,0,4⟩,[0,2048,-94208,1204224,-6180864,12423168,5369856,-85614592,205246464,-180590592]),(⟨1,1,0⟩,[0,-20480,600064,-7133184,45375488,-164945920,295018496,160591872,-2405568512,6731378688,-10219358208,8601004032,-3152285696]),(⟨1,1,1⟩,[4096,-122880,1622016,-12244992,56168448,-147591168,126742528,556187648,-2504482816,5019955200,-5477003264,2645006336]),(⟨1,1,2⟩,[2048,-59392,694272,-4386816,16580608,-32620544,-10838016,246214656,-701745152,1055434752,-711882752]),(⟨1,1,3⟩,[-4096,100352,-937984,4083712,-7057408,-8167424,73502720,-200724480,299401216,-193751040]),(⟨1,1,4⟩,[-2048,61440,-647168,2805760,-2887680,-16609280,71426048,-129781760,98703360]),(⟨1,2,0⟩,[-1024,45056,-634880,3810304,-8118272,-19200000,156772352,-395513856,401974272,241600512,-1076508672,880323584]),(⟨1,2,1⟩,[2048,-59392,694272,-4386816,16580608,-32620544,-10838016,246214656,-701745152,1055434752,-711882752]),(⟨1,2,2⟩,[0,-8192,196608,-1785856,7831552,-17498112,12582912,44318720,-136478720,116006912]),(⟨1,2,3⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨1,2,4⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨1,3,0⟩,[0,22528,-581632,5480448,-23740416,40833024,52264960,-437936128,1053900800,-1253877760,622354432]),(⟨1,3,1⟩,[-4096,100352,-937984,4083712,-7057408,-8167424,73502720,-200724480,299401216,-193751040]),(⟨1,3,2⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨1,3,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨1,3,4⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨1,4,0⟩,[0,2048,-94208,1204224,-6180864,12423168,5369856,-85614592,205246464,-180590592]),(⟨1,4,1⟩,[-2048,61440,-647168,2805760,-2887680,-16609280,71426048,-129781760,98703360]),(⟨1,4,2⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨1,4,3⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨2,0,0⟩,[-4096,109568,-1130496,5448704,-8706048,-35489792,228122624,-522696704,357146624,1018305536,-3054821376,3440530432,-1458272256]),(⟨2,0,1⟩,[-1024,45056,-634880,3810304,-8118272,-19200000,156772352,-395513856,401974272,241600512,-1076508672,880323584]),(⟨2,0,2⟩,[4096,-102400,917504,-3362816,2560000,15880192,-56676352,104501248,-123265024,115605504,-110587904]),(⟨2,0,3⟩,[-1024,3072,114688,-438272,-3278848,22800384,-56893440,84152320,-61182976,-18830336]),(⟨2,0,4⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨2,0,5⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨2,0,6⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨2,1,0⟩,[-1024,45056,-634880,3810304,-8118272,-19200000,156772352,-395513856,401974272,241600512,-1076508672,880323584]),(⟨2,1,1⟩,[2048,-59392,694272,-4386816,16580608,-32620544,-10838016,246214656,-701745152,1055434752,-711882752]),(⟨2,1,2⟩,[0,-8192,196608,-1785856,7831552,-17498112,12582912,44318720,-136478720,116006912]),(⟨2,1,3⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨2,1,4⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨2,2,0⟩,[4096,-102400,917504,-3362816,2560000,15880192,-56676352,104501248,-123265024,115605504,-110587904]),(⟨2,2,1⟩,[0,-8192,196608,-1785856,7831552,-17498112,12582912,44318720,-136478720,116006912]),(⟨2,2,3⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨2,3,0⟩,[-1024,3072,114688,-438272,-3278848,22800384,-56893440,84152320,-61182976,-18830336]),(⟨2,3,1⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨2,3,2⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨2,3,3⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨2,4,0⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨2,4,1⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨2,5,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨2,6,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨3,0,0⟩,[-2048,97280,-1511424,11002880,-40448000,54368256,153239552,-911767552,2106554368,-2665272320,1624412160,-158706688]),(⟨3,0,1⟩,[0,22528,-581632,5480448,-23740416,40833024,52264960,-437936128,1053900800,-1253877760,622354432]),(⟨3,0,2⟩,[-1024,3072,114688,-438272,-3278848,22800384,-56893440,84152320,-61182976,-18830336]),(⟨3,0,3⟩,[0,8192,-98304,745472,-4833280,18276352,-41943040,78749696,-88653824]),(⟨3,0,4⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨3,0,5⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨3,1,0⟩,[0,22528,-581632,5480448,-23740416,40833024,52264960,-437936128,1053900800,-1253877760,622354432]),(⟨3,1,1⟩,[-4096,100352,-937984,4083712,-7057408,-8167424,73502720,-200724480,299401216,-193751040]),(⟨3,1,2⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨3,1,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,1,4⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨3,2,0⟩,[-1024,3072,114688,-438272,-3278848,22800384,-56893440,84152320,-61182976,-18830336]),(⟨3,2,1⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨3,2,2⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨3,2,3⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨3,3,0⟩,[0,8192,-98304,745472,-4833280,18276352,-41943040,78749696,-88653824]),(⟨3,3,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,3,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨3,4,0⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨3,4,1⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨3,5,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨4,0,0⟩,[2048,-36864,73728,2095104,-16222208,42522624,92160,-284153856,823107584,-1119381504,635787264]),(⟨4,0,1⟩,[0,2048,-94208,1204224,-6180864,12423168,5369856,-85614592,205246464,-180590592]),(⟨4,0,2⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨4,0,3⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨4,1,0⟩,[0,2048,-94208,1204224,-6180864,12423168,5369856,-85614592,205246464,-180590592]),(⟨4,1,1⟩,[-2048,61440,-647168,2805760,-2887680,-16609280,71426048,-129781760,98703360]),(⟨4,1,2⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨4,1,3⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨4,2,0⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨4,2,1⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨4,3,0⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨4,3,1⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨5,0,0⟩,[1024,-48128,624640,-3028992,3543040,16896000,-72566784,132347904,-104485888,-11031552]),(⟨5,0,2⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨5,0,3⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨5,2,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨5,3,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨6,0,0⟩,[0,-8192,188416,-1302528,2760704,4530176,-33415168,73850880,-69672960]),(⟨6,0,2⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨6,2,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088])]


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
    (Poly.add (Poly.scale (K.ofRat r473) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 7 10).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r471*r472 : ℚ)=r473 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 7 10 r471 r472 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 7=10 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 7 10).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C125

#print axioms Coulomb8.Columns.C125.sound
