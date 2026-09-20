import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C091

def r0 : ℚ := { num := 4096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -110592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 1167360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -5394432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -299008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 141578240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -49844224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 2706903040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -5317443584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 6372171776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -4215406592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 1208221696, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -119537664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -20480, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 1896448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -1683456, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 26169344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 15364096, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -142987264, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 3513716736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -6944432128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 7874666496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -4462477312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 727973888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -8192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 24576, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -1048576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := -1458176, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := 44875776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -1769472, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 386072576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 89931776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -1547280384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 2326552576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -159514624, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 270336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -2932736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 10878976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 1277952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -318390272, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 1121959936, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 1309253632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -135651328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -4096, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -610304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 7049216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -17379328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -63754240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 411373568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := -773738496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := 512581632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := -126976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 1036288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -274432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -3715072, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 13455360, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -94834688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -1077248, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -32768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 491520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -65536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := -9764864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := 48332800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := -58884096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -73728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 1753088, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -15507456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 58195968, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -9510912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := -107855872, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 439902208, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -5932744704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := 836616192, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := -2395996160, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := 32768, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := -2195456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := 7069696, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 14123008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -157442048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 56360960, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -263249920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := -414048256, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := 82911232, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 106496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -2113536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 13426688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -18972672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := -128884736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := 594395136, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -55959552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 560463872, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -12288, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := 61440, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 962560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -1126400, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -13004800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 111259648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -7860224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := -2162688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 1769472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := 7438336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -98304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 8192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -122880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 8192, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := 7610368, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := -46325760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 94593024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -26959872, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -94740480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 5816320, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -212992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 1597440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -1015808, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -29958144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 103464960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -88301568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := -3932160, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -65536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 983040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -131072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := -19529728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := 96665600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := -117768192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -221184, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 2547712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -14884864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 31629312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 116760576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := -133996544, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := 2559942656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := -3373875200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := 106905600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := -8192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := 548864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 2318336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -24043520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 90021888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := -35856384, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := 481894400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := -3293184, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := 188416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := -221184, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := 4153344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 12689408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -104685568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 232660992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := -10412032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := 180224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := -1105920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -884736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 1712128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -89735168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 4907008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := -204800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 1843200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -6955008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := 7430144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 17539072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -45981696, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 221184, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 147456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -876544, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 98304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := 1515520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := -7323648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := 40960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := 2048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := -55296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := 583680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := -2697216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -149504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := 70789120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := -24922112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := 1353451520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -2658721792, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 3186085888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := -2107703296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := 604110848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := -59768832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := -10240, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := 948224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := -841728, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := 13084672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 7682048, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := -71493632, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := 1756858368, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -3472216064, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := 3937333248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -2231238656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 363986944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -4096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 12288, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := -524288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -729088, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 22437888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -884736, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 193036288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := 44965888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := -773640192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := 1163276288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -79757312, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 135168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := -1466368, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 5439488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := 638976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -159195136, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := 560979968, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := 654626816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -67825664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := -2048, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := -305152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := 3524608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := -8689664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -31877120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := 205686784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := -386869248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := 256290816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := -63488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := 518144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := -137216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := -1857536, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := 6727680, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -47417344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := -538624, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -16384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 245760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -32768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := -4882432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := 24166400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := -29442048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := -36864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := 876544, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := -7753728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := 29097984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -4755456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := -53927936, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := 219951104, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -2966372352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 418308096, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := -1197998080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := 16384, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := -1097728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := 3534848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := 7061504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := -78721024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := 28180480, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := -131624960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := -207024128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := 41455616, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := 53248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -1056768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := 6713344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := -9486336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := -64442368, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := 297197568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := -27979776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := 280231936, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := -6144, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := 30720, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 481280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -563200, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := -6502400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := 55629824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := -3930112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -1081344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := 884736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := 3719168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := -49152, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := -61440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := 4096, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := 3805184, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -23162880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 47296512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := -13479936, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := -47370240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := 2908160, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := -106496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := 798720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := -507904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := -14979072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := 51732480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := -44150784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -1966080, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := 1273856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := -7442432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := 15814656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := 58380288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -66998272, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := 1279971328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -1686937600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 53452800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -4096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 274432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := 1159168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := -12021760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := 45010944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -17928192, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := 240947200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := -1646592, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := 94208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := -110592, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := 2076672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := 6344704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := -52342784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := 116330496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := -5206016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := 90112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := -552960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -442368, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 856064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -44867584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 2453504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := -102400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 921600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -3477504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := 3715072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := 8769536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := -22990848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := 110592, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := 73728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := -438272, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := 49152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := 757760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -3661824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 20480, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 1, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := 1, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12],[r0,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23],[r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34],[r24,r35,r36,r37,r38,r39,r40,-917504,r41,r42],[r0,r43,r44,r45,r46,r47,r48,r49,r50],[r0,r51,r52,r53,r54,r55,r56,r57],[0,r58,r59,r60,r61,r62,r63],[],[],[],[],[],[],[0,r64,r65,r66,r67,r68,r69,r70,r71,r72,r73],[r24,r74,r75,r76,r77,r78,r79,r80,r81,r82],[0,r83,r84,r85,r86,r87,r88,r89,r90],[r0,r91,r92,r93,r94,r95,r96,r97],[0,r58,r59,r98,r99,r100,r101],[],[],[],[],[],[],[r102,r103,r104,r105,r106,r107,r108,r109,r110],[r102,r111,r112,r113,r114,r115,r116,r117],[0,r58,r59,r98,r99,r100,r101],[],[],[],[],[],[],[0,r118,r119,r120,r121,r122,r123],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[r102,r124,r125,r126,r127,r128,r129,r130,r131,r132],[r102,r133,r134,r135,r136,r137,r138,r139,r140],[r24,r141,r142,r143,r144,r145,r146,r147],[r24,r148,r149,r150,r151,r152,r153],[],[],[],[],[],[],[r102,r154,r155,r156,r157,r158,r159,r160],[r24,r161,r162,r163,r164,r165,r166],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[r167,r168,r169,r170,r171,r172,r173,r174,r175,r176,r177,r178,r179]),(⟨0,0,1⟩,[r167,r180,r181,r182,r183,r184,r185,r186,r187,r188,r189,r190]),(⟨0,0,2⟩,[r191,r192,r193,r194,r195,r196,r197,r198,r199,r200,r201]),(⟨0,0,3⟩,[r191,r202,r203,r204,r205,r206,r207,-458752,r208,r209]),(⟨0,0,4⟩,[r167,r210,r211,r212,r213,r214,r215,r216,r217]),(⟨0,0,5⟩,[r167,r218,r219,r220,r221,r222,r223,r224]),(⟨0,0,6⟩,[0,r225,r226,r227,r228,r229,r230]),(⟨0,1,0⟩,[r167,r180,r181,r182,r183,r184,r185,r186,r187,r188,r189,r190]),(⟨0,1,1⟩,[0,r231,r232,r233,r234,r235,r236,r237,r238,r239,r240]),(⟨0,1,2⟩,[r191,r241,r242,r243,r244,r245,r246,r247,r248,r249]),(⟨0,1,3⟩,[0,r250,r251,r252,r253,r254,r255,r256,r257]),(⟨0,1,4⟩,[r167,r258,r259,r260,r261,r262,r263,r264]),(⟨0,1,5⟩,[0,r225,r226,r265,r266,r267,r268]),(⟨0,2,0⟩,[r191,r192,r193,r194,r195,r196,r197,r198,r199,r200,r201]),(⟨0,2,1⟩,[r191,r241,r242,r243,r244,r245,r246,r247,r248,r249]),(⟨0,2,2⟩,[r0,r269,r270,r271,r272,r273,r274,r275,r276]),(⟨0,2,3⟩,[r0,r277,r278,r279,r280,r281,r282,r283]),(⟨0,2,4⟩,[0,r225,r226,r265,r266,r267,r268]),(⟨0,3,0⟩,[r191,r202,r203,r204,r205,r206,r207,-458752,r208,r209]),(⟨0,3,1⟩,[0,r250,r251,r252,r253,r254,r255,r256,r257]),(⟨0,3,2⟩,[r0,r277,r278,r279,r280,r281,r282,r283]),(⟨0,3,3⟩,[0,r58,r59,r60,r61,r62,r63]),(⟨0,4,0⟩,[r167,r210,r211,r212,r213,r214,r215,r216,r217]),(⟨0,4,1⟩,[r167,r258,r259,r260,r261,r262,r263,r264]),(⟨0,4,2⟩,[0,r225,r226,r265,r266,r267,r268]),(⟨0,5,0⟩,[r167,r218,r219,r220,r221,r222,r223,r224]),(⟨0,5,1⟩,[0,r225,r226,r265,r266,r267,r268]),(⟨0,6,0⟩,[0,r225,r226,r227,r228,r229,r230]),(⟨1,0,0⟩,[r167,r180,r181,r182,r183,r184,r185,r186,r187,r188,r189,r190]),(⟨1,0,1⟩,[0,r231,r232,r233,r234,r235,r236,r237,r238,r239,r240]),(⟨1,0,2⟩,[r191,r241,r242,r243,r244,r245,r246,r247,r248,r249]),(⟨1,0,3⟩,[0,r250,r251,r252,r253,r254,r255,r256,r257]),(⟨1,0,4⟩,[r167,r258,r259,r260,r261,r262,r263,r264]),(⟨1,0,5⟩,[0,r225,r226,r265,r266,r267,r268]),(⟨1,1,0⟩,[0,r231,r232,r233,r234,r235,r236,r237,r238,r239,r240]),(⟨1,1,1⟩,[r0,r1,r284,r285,r286,r287,r288,r289,r290,r291]),(⟨1,1,2⟩,[r0,r292,r293,r294,r295,r296,r297,r298,r299]),(⟨1,1,3⟩,[r191,r300,r301,r302,r303,r304,r305,r306]),(⟨1,1,4⟩,[r191,r307,r308,r309,r310,r311,r312]),(⟨1,2,0⟩,[r191,r241,r242,r243,r244,r245,r246,r247,r248,r249]),(⟨1,2,1⟩,[r0,r292,r293,r294,r295,r296,r297,r298,r299]),(⟨1,2,2⟩,[r0,r313,r314,r315,r316,r317,r318,r319]),(⟨1,2,3⟩,[r191,r320,r321,r322,r323,r324,r325]),(⟨1,3,0⟩,[0,r250,r251,r252,r253,r254,r255,r256,r257]),(⟨1,3,1⟩,[r191,r300,r301,r302,r303,r304,r305,r306]),(⟨1,3,2⟩,[r191,r320,r321,r322,r323,r324,r325]),(⟨1,4,0⟩,[r167,r258,r259,r260,r261,r262,r263,r264]),(⟨1,4,1⟩,[r191,r307,r308,r309,r310,r311,r312]),(⟨1,5,0⟩,[0,r225,r226,r265,r266,r267,r268]),(⟨2,0,0⟩,[r191,r192,r193,r194,r195,r196,r197,r198,r199,r200,r201]),(⟨2,0,1⟩,[r191,r241,r242,r243,r244,r245,r246,r247,r248,r249]),(⟨2,0,2⟩,[r0,r269,r270,r271,r272,r273,r274,r275,r276]),(⟨2,0,3⟩,[r0,r277,r278,r279,r280,r281,r282,r283]),(⟨2,0,4⟩,[0,r225,r226,r265,r266,r267,r268]),(⟨2,1,0⟩,[r191,r241,r242,r243,r244,r245,r246,r247,r248,r249]),(⟨2,1,1⟩,[r0,r292,r293,r294,r295,r296,r297,r298,r299]),(⟨2,1,2⟩,[r0,r313,r314,r315,r316,r317,r318,r319]),(⟨2,1,3⟩,[r191,r320,r321,r322,r323,r324,r325]),(⟨2,2,0⟩,[r0,r269,r270,r271,r272,r273,r274,r275,r276]),(⟨2,2,1⟩,[r0,r313,r314,r315,r316,r317,r318,r319]),(⟨2,3,0⟩,[r0,r277,r278,r279,r280,r281,r282,r283]),(⟨2,3,1⟩,[r191,r320,r321,r322,r323,r324,r325]),(⟨2,4,0⟩,[0,r225,r226,r265,r266,r267,r268]),(⟨3,0,0⟩,[r191,r202,r203,r204,r205,r206,r207,-458752,r208,r209]),(⟨3,0,1⟩,[0,r250,r251,r252,r253,r254,r255,r256,r257]),(⟨3,0,2⟩,[r0,r277,r278,r279,r280,r281,r282,r283]),(⟨3,0,3⟩,[0,r58,r59,r60,r61,r62,r63]),(⟨3,1,0⟩,[0,r250,r251,r252,r253,r254,r255,r256,r257]),(⟨3,1,1⟩,[r191,r300,r301,r302,r303,r304,r305,r306]),(⟨3,1,2⟩,[r191,r320,r321,r322,r323,r324,r325]),(⟨3,2,0⟩,[r0,r277,r278,r279,r280,r281,r282,r283]),(⟨3,2,1⟩,[r191,r320,r321,r322,r323,r324,r325]),(⟨3,3,0⟩,[0,r58,r59,r60,r61,r62,r63]),(⟨4,0,0⟩,[r167,r210,r211,r212,r213,r214,r215,r216,r217]),(⟨4,0,1⟩,[r167,r258,r259,r260,r261,r262,r263,r264]),(⟨4,0,2⟩,[0,r225,r226,r265,r266,r267,r268]),(⟨4,1,0⟩,[r167,r258,r259,r260,r261,r262,r263,r264]),(⟨4,1,1⟩,[r191,r307,r308,r309,r310,r311,r312]),(⟨4,2,0⟩,[0,r225,r226,r265,r266,r267,r268]),(⟨5,0,0⟩,[r167,r218,r219,r220,r221,r222,r223,r224]),(⟨5,0,1⟩,[0,r225,r226,r265,r266,r267,r268]),(⟨5,1,0⟩,[0,r225,r226,r265,r266,r267,r268]),(⟨6,0,0⟩,[0,r225,r226,r227,r228,r229,r230])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[128,-1792,5120,30720,-231808,574208,-567040,116736]),(⟨0,0,1⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨0,0,2⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨0,0,3⟩,[-128,1536,256,-37376,76672]),(⟨0,1,0⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨0,1,1⟩,[0,-512,6144,-15360,-18432,60928]),(⟨0,1,2⟩,[-128,1536,-3840,-4608,15232]),(⟨0,2,0⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨0,2,1⟩,[-128,1536,-3840,-4608,15232]),(⟨0,3,0⟩,[-128,1536,256,-37376,76672]),(⟨1,0,0⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨1,0,1⟩,[0,-512,6144,-15360,-18432,60928]),(⟨1,0,2⟩,[-128,1536,-3840,-4608,15232]),(⟨1,1,0⟩,[0,-512,6144,-15360,-18432,60928]),(⟨1,2,0⟩,[-128,1536,-3840,-4608,15232]),(⟨2,0,0⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨2,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨2,1,0⟩,[-128,1536,-3840,-4608,15232]),(⟨3,0,0⟩,[-128,1536,256,-37376,76672])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[16,-208,1008,-2480,2688,-512]),(⟨0,0,1⟩,[0,-96,704,-1760,1664]),(⟨0,0,2⟩,[-16,176,-304,-112]),(⟨0,0,3⟩,[0,128,-384]),(⟨0,1,0⟩,[0,-96,704,-1760,1664]),(⟨0,1,1⟩,[0,-32,320,-544]),(⟨0,2,0⟩,[-16,176,-304,-112]),(⟨0,3,0⟩,[0,128,-384]),(⟨1,0,0⟩,[0,-96,704,-1760,1664]),(⟨1,0,1⟩,[0,-32,320,-544]),(⟨1,1,0⟩,[0,-32,320,-544]),(⟨1,1,1⟩,[32,-320,544]),(⟨2,0,0⟩,[-16,176,-304,-112]),(⟨3,0,0⟩,[0,128,-384])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 3 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r326) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 10 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r327) sourceRight))).isZero := by decide +kernel

noncomputable def partial19 : Poly := []

theorem partial_sound19 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 19)
      sourceRight).eval u v t=partial19.eval u v t := by rfl

noncomputable def chunk16 : Poly := [(⟨2,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨2,1,0⟩,[-128,1536,-3840,-4608,15232]),(⟨3,0,0⟩,[-128,1536,256,-37376,76672])]

noncomputable def partial16 : Poly := [(⟨2,0,1⟩,[-2048,51200,-509952,2590720,-6821888,5904384,15673344,-48195584,43302912,-7798784]),(⟨2,0,2⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨2,0,3⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨2,0,4⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨2,1,0⟩,[-2048,51200,-509952,2590720,-6821888,5904384,15673344,-48195584,43302912,-7798784]),(⟨2,1,1⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨2,1,2⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨2,1,3⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨2,2,0⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨2,2,1⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨2,3,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨2,3,1⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨2,4,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨3,0,0⟩,[-2048,51200,-444416,1214464,5105664,-50063360,169879552,-290744320,225230848,-39256064]),(⟨3,0,1⟩,[0,24576,-475136,2957312,-4325376,-26959872,132628480,-231612416,152928256]),(⟨3,0,2⟩,[2048,-43008,215040,874496,-9971712,24954880,-11741184,-16873472]),(⟨3,0,3⟩,[0,-16384,245760,-557056,-4882432,24166400,-29442048]),(⟨3,1,0⟩,[0,24576,-475136,2957312,-4325376,-26959872,132628480,-231612416,152928256]),(⟨3,1,1⟩,[0,12288,-270336,1921024,-3391488,-14299136,59629568,-58281984]),(⟨3,1,2⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨3,2,0⟩,[2048,-43008,215040,874496,-9971712,24954880,-11741184,-16873472]),(⟨3,2,1⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨3,3,0⟩,[0,-16384,245760,-557056,-4882432,24166400,-29442048]),(⟨4,0,0⟩,[0,12288,-237568,1282048,851968,-31567872,120184832,-197136384,127582208]),(⟨4,0,1⟩,[2048,-43008,280576,-501760,382976,-10041344,40753152,-43415552]),(⟨4,1,0⟩,[2048,-43008,280576,-501760,382976,-10041344,40753152,-43415552]),(⟨4,1,1⟩,[-4096,90112,-552960,-442368,14553088,-44867584,41709568]),(⟨5,0,0⟩,[2048,-47104,305152,190464,-8054784,24827904,-19122176,-8587264]),(⟨5,0,1⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨5,1,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨6,0,0⟩,[0,-16384,245760,-557056,-4882432,24166400,-29442048])]


theorem partial_checked16 :
    (Poly.add (Poly.add (Poly.mul chunk16 sourceRight) partial19)
      (Poly.scale (K.ofRat (-1)) partial16)).isZero := by decide +kernel

theorem partial_sound16 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 16)
      sourceRight).eval u v t=partial16.eval u v t := by
  change (Poly.mul (chunk16++(sourceLeft.drop 19))
    sourceRight).eval u v t=partial16.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound19 partial_checked16 u v t


noncomputable def chunk12 : Poly := [(⟨1,0,2⟩,[-128,1536,-3840,-4608,15232]),(⟨1,1,0⟩,[0,-512,6144,-15360,-18432,60928]),(⟨1,2,0⟩,[-128,1536,-3840,-4608,15232]),(⟨2,0,0⟩,[-128,1280,1280,-34816,69504,-12544])]

noncomputable def partial12 : Poly := [(⟨1,0,2⟩,[-2048,51200,-509952,2590720,-6821888,5904384,15673344,-48195584,43302912,-7798784]),(⟨1,0,3⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨1,0,4⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨1,0,5⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨1,1,0⟩,[0,-8192,204800,-2039808,10362880,-27287552,23617536,62693376,-192782336,173211648,-31195136]),(⟨1,1,1⟩,[0,0,49152,-950272,6701056,-20709376,18432000,49774592,-137904128,101384192]),(⟨1,1,2⟩,[0,20480,-425984,3158016,-9396224,4370432,30490624,-50933760,18522112]),(⟨1,1,3⟩,[0,4096,-155648,1667072,-6242304,3665920,22257664,-31682560]),(⟨1,2,0⟩,[-2048,51200,-460800,1640448,-120832,-14804992,34105344,1579008,-94601216,93585408]),(⟨1,2,1⟩,[0,12288,-221184,1314816,-2441216,-3059712,12951552,-4952064,-7798784]),(⟨1,2,2⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨1,2,3⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨1,3,0⟩,[0,20480,-425984,3158016,-9396224,4370432,30490624,-50933760,18522112]),(⟨1,3,1⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨1,3,2⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨1,4,0⟩,[2048,-47104,305152,-71680,-4384768,8050688,10762240,-25102336]),(⟨1,5,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨2,0,0⟩,[-2048,47104,-374784,784384,6125568,-49420288,161798144,-279255040,235761664,-69304320,6422528]),(⟨2,0,1⟩,[-2048,63488,-722944,3594240,-5044224,-25401344,129214464,-237287424,181035008,-28672000]),(⟨2,0,2⟩,[2048,-18432,-231424,3758080,-18126848,32090112,5449728,-72923136,52097024]),(⟨2,0,3⟩,[2048,-59392,493568,-698368,-6924288,26904576,-25028608,-5175296]),(⟨2,0,4⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨2,1,0⟩,[-2048,63488,-673792,2643968,1656832,-46110720,147646464,-187512832,43130880,72712192]),(⟨2,1,1⟩,[0,28672,-540672,3428352,-6791168,-12513280,66977792,-81252352,24371200]),(⟨2,1,2⟩,[2048,-38912,190464,313344,-3893248,4765696,10647552,-18278400]),(⟨2,1,3⟩,[-4096,73728,-438272,835584,757760,-3661824,2437120]),(⟨2,2,0⟩,[2048,-18432,-215040,3397632,-15390720,24422400,5957632,-43399168,18952192]),(⟨2,2,1⟩,[2048,-55296,550912,-2422784,3774464,4257792,-18876416,14866432]),(⟨2,3,0⟩,[2048,-59392,493568,-698368,-6924288,26904576,-25028608,-5175296]),(⟨2,3,1⟩,[-4096,73728,-438272,835584,757760,-3661824,2437120]),(⟨2,4,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨3,0,0⟩,[-2048,63488,-657408,2217984,6883328,-81369088,283420672,-479836160,362962944,-60129280]),(⟨3,0,1⟩,[0,28672,-557056,3395584,-3497984,-41021440,174211072,-273436672,159752192]),(⟨3,0,2⟩,[4096,-90112,585728,-180224,-10031104,29466624,-15855616,-18579456]),(⟨3,0,3⟩,[0,-16384,245760,-557056,-4882432,24166400,-29442048]),(⟨3,1,0⟩,[0,36864,-745472,4878336,-7716864,-41259008,192258048,-289894400,152928256]),(⟨3,1,1⟩,[-4096,94208,-708608,1093632,10670080,-55881728,101453824,-65105920]),(⟨3,1,2⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨3,2,0⟩,[4096,-90112,585728,-180224,-10031104,29466624,-15855616,-18579456]),(⟨3,2,1⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨3,3,0⟩,[0,-16384,245760,-557056,-4882432,24166400,-29442048]),(⟨4,0,0⟩,[2048,-30720,6144,1689600,-6920192,-8693760,100747264,-201107456,128987136]),(⟨4,0,1⟩,[2048,-43008,280576,-501760,382976,-10041344,40753152,-43415552]),(⟨4,0,2⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨4,1,0⟩,[2048,-43008,215040,481280,-3942400,-6502400,55629824,-66811904]),(⟨4,1,1⟩,[-4096,90112,-552960,-442368,14553088,-44867584,41709568]),(⟨4,2,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨5,0,0⟩,[2048,-63488,518144,-137216,-13002752,47093760,-47417344,-3770368]),(⟨5,0,1⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨5,1,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨6,0,0⟩,[0,-16384,245760,-557056,-4882432,24166400,-29442048])]


theorem partial_checked12 :
    (Poly.add (Poly.add (Poly.mul chunk12 sourceRight) partial16)
      (Poly.scale (K.ofRat (-1)) partial12)).isZero := by decide +kernel

theorem partial_sound12 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 12)
      sourceRight).eval u v t=partial12.eval u v t := by
  change (Poly.mul (chunk12++(sourceLeft.drop 16))
    sourceRight).eval u v t=partial12.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound16 partial_checked12 u v t


noncomputable def chunk8 : Poly := [(⟨0,2,1⟩,[-128,1536,-3840,-4608,15232]),(⟨0,3,0⟩,[-128,1536,256,-37376,76672]),(⟨1,0,0⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨1,0,1⟩,[0,-512,6144,-15360,-18432,60928])]

noncomputable def partial8 : Poly := [(⟨0,2,1⟩,[-2048,51200,-509952,2590720,-6821888,5904384,15673344,-48195584,43302912,-7798784]),(⟨0,2,2⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨0,2,3⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨0,2,4⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨0,3,0⟩,[-2048,51200,-444416,1214464,5105664,-50063360,169879552,-290744320,225230848,-39256064]),(⟨0,3,1⟩,[0,24576,-475136,2957312,-4325376,-26959872,132628480,-231612416,152928256]),(⟨0,3,2⟩,[2048,-43008,215040,874496,-9971712,24954880,-11741184,-16873472]),(⟨0,3,3⟩,[0,-16384,245760,-557056,-4882432,24166400,-29442048]),(⟨0,4,0⟩,[0,12288,-237568,1282048,851968,-31567872,120184832,-197136384,127582208]),(⟨0,4,1⟩,[2048,-43008,280576,-501760,382976,-10041344,40753152,-43415552]),(⟨0,5,0⟩,[2048,-47104,305152,190464,-8054784,24827904,-19122176,-8587264]),(⟨0,5,1⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨0,6,0⟩,[0,-16384,245760,-557056,-4882432,24166400,-29442048]),(⟨1,0,0⟩,[2048,-59392,686080,-3913728,9062400,21886976,-236591104,839079936,-1665478656,1901678592,-1082228736,169738240]),(⟨1,0,1⟩,[0,-20480,491520,-4493312,18915328,-23252992,-122306560,637177856,-1330798592,1377771520,-582844416]),(⟨1,0,2⟩,[-4096,106496,-991232,3518464,1892352,-51163136,149151744,-153563136,-35622912,130715648]),(⟨1,0,3⟩,[0,36864,-737280,4993024,-11165696,-18812928,135430144,-236695552,145825792]),(⟨1,0,4⟩,[2048,-47104,305152,-71680,-4384768,8050688,10762240,-25102336]),(⟨1,0,5⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨1,1,0⟩,[0,-20480,491520,-4493312,18915328,-23252992,-122306560,637177856,-1330798592,1377771520,-582844416]),(⟨1,1,1⟩,[0,-4096,204800,-2887680,16793600,-37670912,-28565504,310579200,-584941568,383115264]),(⟨1,1,2⟩,[0,20480,-409600,2797568,-6660096,-3297280,30998528,-21409792,-14622720]),(⟨1,1,3⟩,[0,4096,-155648,1667072,-6242304,3665920,22257664,-31682560]),(⟨1,2,0⟩,[-4096,106496,-991232,3518464,1892352,-51163136,149151744,-153563136,-35622912,130715648]),(⟨1,2,1⟩,[0,32768,-647168,4472832,-11837440,1310720,43442176,-55885824,10723328]),(⟨1,2,2⟩,[4096,-90112,651264,-1425408,-2035712,9150464,-847872,-11698176]),(⟨1,2,3⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨1,3,0⟩,[0,49152,-974848,6275072,-10313728,-50380800,255614976,-433831936,273408000]),(⟨1,3,1⟩,[0,12288,-335872,2904064,-7716864,-10760192,74506240,-81678336]),(⟨1,3,2⟩,[-4096,73728,-438272,835584,757760,-3661824,2437120]),(⟨1,4,0⟩,[2048,-43008,215040,481280,-3942400,-6502400,55629824,-66811904]),(⟨1,4,1⟩,[-4096,90112,-552960,-442368,14553088,-44867584,41709568]),(⟨1,5,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨2,0,0⟩,[-2048,34816,-88064,-1669120,14678016,-45385728,15874048,295229440,-902254592,1135255552,-545226752]),(⟨2,0,1⟩,[-2048,59392,-567296,1656832,5048320,-42362880,82216960,23517184,-266002432,253059072]),(⟨2,0,2⟩,[2048,-18432,-215040,3397632,-15390720,24422400,5957632,-43399168,18952192]),(⟨2,0,3⟩,[2048,-59392,493568,-698368,-6924288,26904576,-25028608,-5175296]),(⟨2,0,4⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨2,1,0⟩,[-2048,59392,-567296,1656832,5048320,-42362880,82216960,23517184,-266002432,253059072]),(⟨2,1,1⟩,[4096,-77824,462848,-323584,-7802880,45248512,-143544320,257404928,-189120512]),(⟨2,1,2⟩,[2048,-55296,550912,-2422784,3774464,4257792,-18876416,14866432]),(⟨2,1,3⟩,[-4096,73728,-438272,835584,757760,-3661824,2437120]),(⟨2,2,0⟩,[2048,-18432,-215040,3397632,-15390720,24422400,5957632,-43399168,18952192]),(⟨2,2,1⟩,[4096,-102400,921600,-3477504,3715072,8769536,-22990848,13160448]),(⟨2,3,0⟩,[4096,-106496,798720,-507904,-14979072,51732480,-44150784,-13762560]),(⟨2,3,1⟩,[-4096,73728,-438272,835584,757760,-3661824,2437120]),(⟨2,4,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨3,0,0⟩,[-4096,118784,-1187840,4096000,8896512,-117727232,398467072,-634978304,421941248,-22999040]),(⟨3,0,1⟩,[0,36864,-745472,4878336,-7716864,-41259008,192258048,-289894400,152928256]),(⟨3,0,2⟩,[4096,-90112,585728,-180224,-10031104,29466624,-15855616,-18579456]),(⟨3,0,3⟩,[0,-16384,245760,-557056,-4882432,24166400,-29442048]),(⟨3,1,0⟩,[0,36864,-745472,4878336,-7716864,-41259008,192258048,-289894400,152928256]),(⟨3,1,1⟩,[-4096,94208,-708608,1093632,10670080,-55881728,101453824,-65105920]),(⟨3,1,2⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨3,2,0⟩,[4096,-90112,585728,-180224,-10031104,29466624,-15855616,-18579456]),(⟨3,2,1⟩,[-4096,73728,-438272,835584,757760,-3661824,2437120]),(⟨3,3,0⟩,[0,-32768,491520,-1114112,-9764864,48332800,-58884096]),(⟨4,0,0⟩,[2048,-14336,-305152,3524608,-8689664,-31877120,205686784,-386869248,256290816]),(⟨4,0,1⟩,[2048,-43008,215040,481280,-3942400,-6502400,55629824,-66811904]),(⟨4,0,2⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨4,1,0⟩,[2048,-43008,215040,481280,-3942400,-6502400,55629824,-66811904]),(⟨4,1,1⟩,[-4096,90112,-552960,-442368,14553088,-44867584,41709568]),(⟨4,2,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨5,0,0⟩,[2048,-63488,518144,-137216,-13002752,47093760,-47417344,-3770368]),(⟨5,0,1⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨5,1,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨6,0,0⟩,[0,-16384,245760,-557056,-4882432,24166400,-29442048])]


theorem partial_checked8 :
    (Poly.add (Poly.add (Poly.mul chunk8 sourceRight) partial12)
      (Poly.scale (K.ofRat (-1)) partial8)).isZero := by decide +kernel

theorem partial_sound8 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 8)
      sourceRight).eval u v t=partial8.eval u v t := by
  change (Poly.mul (chunk8++(sourceLeft.drop 12))
    sourceRight).eval u v t=partial8.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound12 partial_checked8 u v t


noncomputable def chunk4 : Poly := [(⟨0,1,0⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨0,1,1⟩,[0,-512,6144,-15360,-18432,60928]),(⟨0,1,2⟩,[-128,1536,-3840,-4608,15232]),(⟨0,2,0⟩,[-128,1280,1280,-34816,69504,-12544])]

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[2048,-59392,686080,-3913728,9062400,21886976,-236591104,839079936,-1665478656,1901678592,-1082228736,169738240]),(⟨0,1,1⟩,[0,-20480,491520,-4493312,18915328,-23252992,-122306560,637177856,-1330798592,1377771520,-582844416]),(⟨0,1,2⟩,[-4096,106496,-991232,3518464,1892352,-51163136,149151744,-153563136,-35622912,130715648]),(⟨0,1,3⟩,[0,36864,-737280,4993024,-11165696,-18812928,135430144,-236695552,145825792]),(⟨0,1,4⟩,[2048,-47104,305152,-71680,-4384768,8050688,10762240,-25102336]),(⟨0,1,5⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨0,2,0⟩,[-2048,34816,-88064,-1669120,14678016,-45385728,15874048,295229440,-902254592,1135255552,-545226752]),(⟨0,2,1⟩,[-2048,59392,-567296,1656832,5048320,-42362880,82216960,23517184,-266002432,253059072]),(⟨0,2,2⟩,[2048,-18432,-215040,3397632,-15390720,24422400,5957632,-43399168,18952192]),(⟨0,2,3⟩,[2048,-59392,493568,-698368,-6924288,26904576,-25028608,-5175296]),(⟨0,2,4⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨0,3,0⟩,[-4096,118784,-1187840,4096000,8896512,-117727232,398467072,-634978304,421941248,-22999040]),(⟨0,3,1⟩,[0,36864,-745472,4878336,-7716864,-41259008,192258048,-289894400,152928256]),(⟨0,3,2⟩,[4096,-90112,585728,-180224,-10031104,29466624,-15855616,-18579456]),(⟨0,3,3⟩,[0,-16384,245760,-557056,-4882432,24166400,-29442048]),(⟨0,4,0⟩,[2048,-14336,-305152,3524608,-8689664,-31877120,205686784,-386869248,256290816]),(⟨0,4,1⟩,[2048,-43008,215040,481280,-3942400,-6502400,55629824,-66811904]),(⟨0,4,2⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨0,5,0⟩,[2048,-63488,518144,-137216,-13002752,47093760,-47417344,-3770368]),(⟨0,5,1⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨0,6,0⟩,[0,-16384,245760,-557056,-4882432,24166400,-29442048]),(⟨1,0,0⟩,[2048,-59392,686080,-3913728,9062400,21886976,-236591104,839079936,-1665478656,1901678592,-1082228736,169738240]),(⟨1,0,1⟩,[0,-20480,491520,-4493312,18915328,-23252992,-122306560,637177856,-1330798592,1377771520,-582844416]),(⟨1,0,2⟩,[-4096,106496,-991232,3518464,1892352,-51163136,149151744,-153563136,-35622912,130715648]),(⟨1,0,3⟩,[0,36864,-737280,4993024,-11165696,-18812928,135430144,-236695552,145825792]),(⟨1,0,4⟩,[2048,-47104,305152,-71680,-4384768,8050688,10762240,-25102336]),(⟨1,0,5⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨1,1,0⟩,[0,-32768,778240,-6946816,27467776,-19218432,-268230656,1211662336,-2468814848,2582331392,-1134493696]),(⟨1,1,1⟩,[0,-8192,360448,-4825088,26886144,-54632448,-75563008,571383808,-1031979008,664846336]),(⟨1,1,2⟩,[0,32768,-630784,4112384,-9101312,-6356992,43950080,-26361856,-22421504]),(⟨1,1,3⟩,[0,8192,-245760,2351104,-8159232,3792896,29638656,-39968768]),(⟨1,2,0⟩,[-4096,114688,-1097728,3534848,7061504,-78721024,197263360,-131624960,-207024128,290189312]),(⟨1,2,1⟩,[4096,-69632,274432,1159168,-12021760,45010944,-125497344,240947200,-195944448]),(⟨1,2,2⟩,[4096,-102400,921600,-3477504,3715072,8769536,-22990848,13160448]),(⟨1,2,3⟩,[-4096,73728,-438272,835584,757760,-3661824,2437120]),(⟨1,3,0⟩,[0,53248,-1056768,6713344,-9486336,-64442368,297197568,-475656192,280231936]),(⟨1,3,1⟩,[-4096,94208,-774144,2076672,6344704,-52342784,116330496,-88502272]),(⟨1,3,2⟩,[-4096,73728,-438272,835584,757760,-3661824,2437120]),(⟨1,4,0⟩,[2048,-43008,215040,481280,-3942400,-6502400,55629824,-66811904]),(⟨1,4,1⟩,[-4096,90112,-552960,-442368,14553088,-44867584,41709568]),(⟨1,5,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨2,0,0⟩,[-2048,34816,-88064,-1669120,14678016,-45385728,15874048,295229440,-902254592,1135255552,-545226752]),(⟨2,0,1⟩,[-2048,59392,-567296,1656832,5048320,-42362880,82216960,23517184,-266002432,253059072]),(⟨2,0,2⟩,[2048,-18432,-215040,3397632,-15390720,24422400,5957632,-43399168,18952192]),(⟨2,0,3⟩,[2048,-59392,493568,-698368,-6924288,26904576,-25028608,-5175296]),(⟨2,0,4⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨2,1,0⟩,[-4096,114688,-1097728,3534848,7061504,-78721024,197263360,-131624960,-207024128,290189312]),(⟨2,1,1⟩,[4096,-69632,274432,1159168,-12021760,45010944,-125497344,240947200,-195944448]),(⟨2,1,2⟩,[4096,-102400,921600,-3477504,3715072,8769536,-22990848,13160448]),(⟨2,1,3⟩,[-4096,73728,-438272,835584,757760,-3661824,2437120]),(⟨2,2,0⟩,[4096,-61440,28672,3805184,-23162880,47296512,-13479936,-47370240,20357120]),(⟨2,2,1⟩,[4096,-102400,921600,-3477504,3715072,8769536,-22990848,13160448]),(⟨2,3,0⟩,[4096,-106496,798720,-507904,-14979072,51732480,-44150784,-13762560]),(⟨2,3,1⟩,[-4096,73728,-438272,835584,757760,-3661824,2437120]),(⟨2,4,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨3,0,0⟩,[-4096,118784,-1187840,4096000,8896512,-117727232,398467072,-634978304,421941248,-22999040]),(⟨3,0,1⟩,[0,36864,-745472,4878336,-7716864,-41259008,192258048,-289894400,152928256]),(⟨3,0,2⟩,[4096,-90112,585728,-180224,-10031104,29466624,-15855616,-18579456]),(⟨3,0,3⟩,[0,-16384,245760,-557056,-4882432,24166400,-29442048]),(⟨3,1,0⟩,[0,53248,-1056768,6713344,-9486336,-64442368,297197568,-475656192,280231936]),(⟨3,1,1⟩,[-4096,94208,-774144,2076672,6344704,-52342784,116330496,-88502272]),(⟨3,1,2⟩,[-4096,73728,-438272,835584,757760,-3661824,2437120]),(⟨3,2,0⟩,[4096,-106496,798720,-507904,-14979072,51732480,-44150784,-13762560]),(⟨3,2,1⟩,[-4096,73728,-438272,835584,757760,-3661824,2437120]),(⟨3,3,0⟩,[0,-32768,491520,-1114112,-9764864,48332800,-58884096]),(⟨4,0,0⟩,[2048,-14336,-305152,3524608,-8689664,-31877120,205686784,-386869248,256290816]),(⟨4,0,1⟩,[2048,-43008,215040,481280,-3942400,-6502400,55629824,-66811904]),(⟨4,0,2⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨4,1,0⟩,[2048,-43008,215040,481280,-3942400,-6502400,55629824,-66811904]),(⟨4,1,1⟩,[-4096,90112,-552960,-442368,14553088,-44867584,41709568]),(⟨4,2,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨5,0,0⟩,[2048,-63488,518144,-137216,-13002752,47093760,-47417344,-3770368]),(⟨5,0,1⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨5,1,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨6,0,0⟩,[0,-16384,245760,-557056,-4882432,24166400,-29442048])]


theorem partial_checked4 :
    (Poly.add (Poly.add (Poly.mul chunk4 sourceRight) partial8)
      (Poly.scale (K.ofRat (-1)) partial4)).isZero := by decide +kernel

theorem partial_sound4 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 4)
      sourceRight).eval u v t=partial4.eval u v t := by
  change (Poly.mul (chunk4++(sourceLeft.drop 8))
    sourceRight).eval u v t=partial4.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound8 partial_checked4 u v t


noncomputable def chunk0 : Poly := [(⟨0,0,0⟩,[128,-1792,5120,30720,-231808,574208,-567040,116736]),(⟨0,0,1⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨0,0,2⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨0,0,3⟩,[-128,1536,256,-37376,76672])]

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[2048,-55296,583680,-2697216,-149504,70789120,-423675904,1353451520,-2658721792,3186085888,-2107703296,604110848,-59768832]),(⟨0,0,1⟩,[2048,-71680,948224,-5892096,13084672,53774336,-500455424,1756858368,-3472216064,3937333248,-2231238656,363986944]),(⟨0,0,2⟩,[-4096,86016,-524288,-729088,22437888,-105283584,193036288,44965888,-773640192,1163276288,-558301184]),(⟨0,0,3⟩,[-4096,135168,-1466368,5439488,10862592,-159195136,560979968,-928055296,654626816,-67825664]),(⟨0,0,4⟩,[2048,-14336,-305152,3524608,-8689664,-31877120,205686784,-386869248,256290816]),(⟨0,0,5⟩,[2048,-63488,518144,-137216,-13002752,47093760,-47417344,-3770368]),(⟨0,0,6⟩,[0,-16384,245760,-557056,-4882432,24166400,-29442048]),(⟨0,1,0⟩,[2048,-71680,948224,-5892096,13084672,53774336,-500455424,1756858368,-3472216064,3937333248,-2231238656,363986944]),(⟨0,1,1⟩,[0,-36864,876544,-7753728,29097984,-4755456,-377495552,1539657728,-2966372352,2928156672,-1197998080]),(⟨0,1,2⟩,[-4096,114688,-1097728,3534848,7061504,-78721024,197263360,-131624960,-207024128,290189312]),(⟨0,1,3⟩,[0,53248,-1056768,6713344,-9486336,-64442368,297197568,-475656192,280231936]),(⟨0,1,4⟩,[2048,-43008,215040,481280,-3942400,-6502400,55629824,-66811904]),(⟨0,1,5⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨0,2,0⟩,[-4096,86016,-524288,-729088,22437888,-105283584,193036288,44965888,-773640192,1163276288,-558301184]),(⟨0,2,1⟩,[-4096,114688,-1097728,3534848,7061504,-78721024,197263360,-131624960,-207024128,290189312]),(⟨0,2,2⟩,[4096,-61440,28672,3805184,-23162880,47296512,-13479936,-47370240,20357120]),(⟨0,2,3⟩,[4096,-106496,798720,-507904,-14979072,51732480,-44150784,-13762560]),(⟨0,2,4⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨0,3,0⟩,[-4096,135168,-1466368,5439488,10862592,-159195136,560979968,-928055296,654626816,-67825664]),(⟨0,3,1⟩,[0,53248,-1056768,6713344,-9486336,-64442368,297197568,-475656192,280231936]),(⟨0,3,2⟩,[4096,-106496,798720,-507904,-14979072,51732480,-44150784,-13762560]),(⟨0,3,3⟩,[0,-32768,491520,-1114112,-9764864,48332800,-58884096]),(⟨0,4,0⟩,[2048,-14336,-305152,3524608,-8689664,-31877120,205686784,-386869248,256290816]),(⟨0,4,1⟩,[2048,-43008,215040,481280,-3942400,-6502400,55629824,-66811904]),(⟨0,4,2⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨0,5,0⟩,[2048,-63488,518144,-137216,-13002752,47093760,-47417344,-3770368]),(⟨0,5,1⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨0,6,0⟩,[0,-16384,245760,-557056,-4882432,24166400,-29442048]),(⟨1,0,0⟩,[2048,-71680,948224,-5892096,13084672,53774336,-500455424,1756858368,-3472216064,3937333248,-2231238656,363986944]),(⟨1,0,1⟩,[0,-36864,876544,-7753728,29097984,-4755456,-377495552,1539657728,-2966372352,2928156672,-1197998080]),(⟨1,0,2⟩,[-4096,114688,-1097728,3534848,7061504,-78721024,197263360,-131624960,-207024128,290189312]),(⟨1,0,3⟩,[0,53248,-1056768,6713344,-9486336,-64442368,297197568,-475656192,280231936]),(⟨1,0,4⟩,[2048,-43008,215040,481280,-3942400,-6502400,55629824,-66811904]),(⟨1,0,5⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨1,1,0⟩,[0,-36864,876544,-7753728,29097984,-4755456,-377495552,1539657728,-2966372352,2928156672,-1197998080]),(⟨1,1,1⟩,[4096,-110592,1273856,-7442432,15814656,58380288,-468987904,1279971328,-1686937600,908697600]),(⟨1,1,2⟩,[4096,-69632,274432,1159168,-12021760,45010944,-125497344,240947200,-195944448]),(⟨1,1,3⟩,[-4096,94208,-774144,2076672,6344704,-52342784,116330496,-88502272]),(⟨1,1,4⟩,[-4096,90112,-552960,-442368,14553088,-44867584,41709568]),(⟨1,2,0⟩,[-4096,114688,-1097728,3534848,7061504,-78721024,197263360,-131624960,-207024128,290189312]),(⟨1,2,1⟩,[4096,-69632,274432,1159168,-12021760,45010944,-125497344,240947200,-195944448]),(⟨1,2,2⟩,[4096,-102400,921600,-3477504,3715072,8769536,-22990848,13160448]),(⟨1,2,3⟩,[-4096,73728,-438272,835584,757760,-3661824,2437120]),(⟨1,3,0⟩,[0,53248,-1056768,6713344,-9486336,-64442368,297197568,-475656192,280231936]),(⟨1,3,1⟩,[-4096,94208,-774144,2076672,6344704,-52342784,116330496,-88502272]),(⟨1,3,2⟩,[-4096,73728,-438272,835584,757760,-3661824,2437120]),(⟨1,4,0⟩,[2048,-43008,215040,481280,-3942400,-6502400,55629824,-66811904]),(⟨1,4,1⟩,[-4096,90112,-552960,-442368,14553088,-44867584,41709568]),(⟨1,5,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨2,0,0⟩,[-4096,86016,-524288,-729088,22437888,-105283584,193036288,44965888,-773640192,1163276288,-558301184]),(⟨2,0,1⟩,[-4096,114688,-1097728,3534848,7061504,-78721024,197263360,-131624960,-207024128,290189312]),(⟨2,0,2⟩,[4096,-61440,28672,3805184,-23162880,47296512,-13479936,-47370240,20357120]),(⟨2,0,3⟩,[4096,-106496,798720,-507904,-14979072,51732480,-44150784,-13762560]),(⟨2,0,4⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨2,1,0⟩,[-4096,114688,-1097728,3534848,7061504,-78721024,197263360,-131624960,-207024128,290189312]),(⟨2,1,1⟩,[4096,-69632,274432,1159168,-12021760,45010944,-125497344,240947200,-195944448]),(⟨2,1,2⟩,[4096,-102400,921600,-3477504,3715072,8769536,-22990848,13160448]),(⟨2,1,3⟩,[-4096,73728,-438272,835584,757760,-3661824,2437120]),(⟨2,2,0⟩,[4096,-61440,28672,3805184,-23162880,47296512,-13479936,-47370240,20357120]),(⟨2,2,1⟩,[4096,-102400,921600,-3477504,3715072,8769536,-22990848,13160448]),(⟨2,3,0⟩,[4096,-106496,798720,-507904,-14979072,51732480,-44150784,-13762560]),(⟨2,3,1⟩,[-4096,73728,-438272,835584,757760,-3661824,2437120]),(⟨2,4,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨3,0,0⟩,[-4096,135168,-1466368,5439488,10862592,-159195136,560979968,-928055296,654626816,-67825664]),(⟨3,0,1⟩,[0,53248,-1056768,6713344,-9486336,-64442368,297197568,-475656192,280231936]),(⟨3,0,2⟩,[4096,-106496,798720,-507904,-14979072,51732480,-44150784,-13762560]),(⟨3,0,3⟩,[0,-32768,491520,-1114112,-9764864,48332800,-58884096]),(⟨3,1,0⟩,[0,53248,-1056768,6713344,-9486336,-64442368,297197568,-475656192,280231936]),(⟨3,1,1⟩,[-4096,94208,-774144,2076672,6344704,-52342784,116330496,-88502272]),(⟨3,1,2⟩,[-4096,73728,-438272,835584,757760,-3661824,2437120]),(⟨3,2,0⟩,[4096,-106496,798720,-507904,-14979072,51732480,-44150784,-13762560]),(⟨3,2,1⟩,[-4096,73728,-438272,835584,757760,-3661824,2437120]),(⟨3,3,0⟩,[0,-32768,491520,-1114112,-9764864,48332800,-58884096]),(⟨4,0,0⟩,[2048,-14336,-305152,3524608,-8689664,-31877120,205686784,-386869248,256290816]),(⟨4,0,1⟩,[2048,-43008,215040,481280,-3942400,-6502400,55629824,-66811904]),(⟨4,0,2⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨4,1,0⟩,[2048,-43008,215040,481280,-3942400,-6502400,55629824,-66811904]),(⟨4,1,1⟩,[-4096,90112,-552960,-442368,14553088,-44867584,41709568]),(⟨4,2,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨5,0,0⟩,[2048,-63488,518144,-137216,-13002752,47093760,-47417344,-3770368]),(⟨5,0,1⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨5,1,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨6,0,0⟩,[0,-16384,245760,-557056,-4882432,24166400,-29442048])]


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
    (Poly.add (Poly.scale (K.ofRat r328) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 3 10).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r326*r327 : ℚ)=r328 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 3 10 r326 r327 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 3=10 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 3 10).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C091

#print axioms Coulomb8.Columns.C091.sound
