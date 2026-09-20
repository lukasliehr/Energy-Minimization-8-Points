import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C142

def r0 : ℚ := { num := 4096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -8192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 2162688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -20295680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 127721472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -80445440, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 250920960, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -3783991296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 5148250112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -2979848192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -410075136, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 987705344, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -4969365504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := 1232470016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := -94371840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -53248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 1474560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -18395136, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 136413184, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := -39002112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := 311459840, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := -4775043072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := 905936896, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := -3143438336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -253886464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 8422625280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -714735616, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 669122560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -8192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 266240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -3538944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 25669632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -110084096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 263888896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -193396736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -754688000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 2380685312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -2409869312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := -362938368, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := 2360930304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -168591360, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 126976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -3129344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 32780288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -191610880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 676077568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -1412448256, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 1428103168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 282509312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := -2190544896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := 1664417792, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := -135286784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -126976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 1081344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -1425408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -28811264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := 27795456, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -549502976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 689651712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -40235008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -764178432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 549306368, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -73728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 1622016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -13484032, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 54509568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -104071168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 43139072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := 136953856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := -147505152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -663552, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 327680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -4325376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 22216704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -52166656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 40566784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := 39714816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := -63111168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := 598016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := -10821632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := 97042432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := -519274496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := 1766129664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := -3791945728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := 4585439232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := -1349214208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -602071040, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 5808627712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -2455961600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 53248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := -1335296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 1929216, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -72351744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 12754944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -45301760, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -14639104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 758054912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -877359104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := -1384448, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 57815040, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := 8192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -720896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 11173888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -78577664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 301449216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -91291648, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 608731136, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 179765248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -897245184, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 564789248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := -81920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 1654784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -12795904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 48578560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -89243648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 45465600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := 79052800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := -5259264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -253952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 3112960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -19333120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 63717376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := -95797248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := -7143424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := 27262976, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := -20160512, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -5087232, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 1146880, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 655360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := -8650752, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := 44433408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := -104333312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := 81133568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := 79429632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -126222336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 3604480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -30842880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 24625152, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := -637845504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := 1519190016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := -2091270144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := 933142528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := 1662033920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -2735276032, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 73850880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -49152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 1138688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := -10878976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := 8192000, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := -26312704, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := 362004480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := -368967680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -21364736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 68599808, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := -3072000, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 245760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -3014656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := 19562496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := -71778304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := 141688832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := -103743488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := -103972864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := 13524992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := -376832, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := 81920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := -1654784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := 12795904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := -48578560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 89243648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := -45465600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := -79052800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := 5259264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -16384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 409600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -4079616, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := 20725760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := -54575104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 47235072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := 125386752, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := -385564672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := 346423296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -524288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 98304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -1900544, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 13402112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := -41418752, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := 36864000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := 14221312, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := -275808256, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := 1703936, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 16384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -376832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 2965504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := -8437760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -475136, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 36093952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -4702208, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := -114688, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -131072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := 1966080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := 7077888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := 29753344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := -393216, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := 32768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 5472256, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -15335424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := 1015808, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := 3473408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := 294912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -5701632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := 40206336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := -124256256, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := 110592000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 42663936, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -827424768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := 5111808, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := -311296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := 1523712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 147456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -31145984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := 38125568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 85180416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := -1228800, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -32768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 720896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -5472256, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 15335424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -1015808, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := -3473408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := 2048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := -4096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := -10147840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := 63860736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := -40222720, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := 125460480, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -1891995648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 2574125056, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -1489924096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -205037568, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 493852672, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := -2484682752, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := 616235008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := -47185920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -26624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := 737280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := -9197568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := 68206592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := -19501056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := 155729920, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := -2387521536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := 452968448, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -1571719168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := -126943232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := 4211312640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := -357367808, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := 334561280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := -4096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := 133120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := -1769472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := 12834816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := -55042048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := 131944448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := -96698368, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := -377344000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := 1190342656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -1204934656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -181469184, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := 1180465152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := -84295680, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := 63488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := -1564672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := 16390144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -95805440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 338038784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := -706224128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := 714051584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := 141254656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := -1095272448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := 832208896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := -67643392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := -63488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := 540672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := -712704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -14405632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := 13897728, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := -274751488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := 344825856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := -20117504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -382089216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := 274653184, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -36864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 811008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -6742016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 27254784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -52035584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := 21569536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := 68476928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -73752576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := -331776, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := 163840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := -2162688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := 11108352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -26083328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := 20283392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := 19857408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -31555584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 299008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -5410816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 48521216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -259637248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 883064832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -1895972864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 2292719616, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := -674607104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := -301035520, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := 2904313856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := -1227980800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := 26624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := -667648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := 964608, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := -36175872, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := 6377472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := -22650880, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := -7319552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := 379027456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := -438679552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -692224, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 28907520, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := -360448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := 5586944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -39288832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 150724608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -45645824, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 304365568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := 89882624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := -448622592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := 282394624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := -40960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := 827392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := -6397952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := 24289280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := -44621824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := 22732800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := 39526400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := -2629632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := 1556480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := -9666560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := 31858688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := -47898624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := -3571712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := 13631488, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := -10080256, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := -2543616, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := 573440, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := 1802240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := -15421440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := 12312576, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -318922752, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := 759595008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := -1045635072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := 466571264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := 831016960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := -1367638016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := 36925440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := -24576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := 569344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := -5439488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := 4096000, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := -13156352, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := 181002240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := -184483840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := -10682368, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := 34299904, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := -1536000, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := 122880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := -1507328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := 9781248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := -35889152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := 70844416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := -51871744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := -51986432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := 6762496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := -188416, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := 40960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := -827392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := 6397952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := -24289280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := 44621824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := -22732800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := -39526400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := 2629632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := 204800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := -2039808, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 10362880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := -27287552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := 23617536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := 62693376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := -192782336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := 173211648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := -262144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := 49152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := -950272, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := 6701056, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := -20709376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := 18432000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := 7110656, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := -137904128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := 851968, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := -188416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := 1482752, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := -4218880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := -237568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := 18046976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := -2351104, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := -57344, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := -65536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := 983040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := 3538944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := 14876672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := -196608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := 2736128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := -7667712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := 507904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := 1736704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := 147456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := -2850816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := 20103168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := -62128128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := 55296000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := 21331968, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := -413712384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := 2555904, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := -155648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := 761856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := 73728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := -15572992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := 19062784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := 42590208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := -614400, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := 360448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := -2736128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := 7667712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := -507904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := -1736704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := 1, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := 1, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14],[0,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27],[r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40],[0,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51],[r0,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61],[0,r62,r63,r64,r65,r66,r67,r68,r69,r70],[0,0,r71,r72,r73,r74,r75,r76,r77],[],[],[],[],[],[],[0,r28,r78,r79,r80,r81,r82,r83,r84,r85,r86,r87,r88],[0,r89,r90,r91,r92,r93,r94,r95,r96,r97,r98,r99],[0,r100,r101,r102,r103,r104,r105,r106,r107,r108,r109],[0,0,r110,r111,r112,r113,r114,r115,r116,r117],[],[],[],[],[],[],[],[r100,r118,r119,r120,r121,r122,r123,r124,r125,r126,r127],[0,r62,r63,r64,r65,r66,r67,r68,r69,r70],[],[],[],[],[],[],[],[0,0,r128,r129,r130,r131,r132,r133,r134],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[r100,r118,r135,r136,r137,r138,r139,r140,r141,r142,r143,r144],[0,r145,r146,r147,r148,r149,r150,r151,r152,r153,r154],[r28,r155,r156,r157,r158,r159,r160,r161,r162,r163],[0,r164,r165,r166,r167,r168,r169,r170,r171],[],[],[],[],[],[],[r172,r173,r174,r175,r176,r177,r178,r179,r180,r181],[0,r182,r183,r184,r185,r186,r187,r188,r189],[r190,r191,r192,r193,r194,r195,r196,r197],[0,r198,r199,r129,r200,r201,r202],[],[],[],[],[0,r203,r101,r204,r205,r206,r207,-32768],[],[],[],[],[],[],[],[],[],[],[],[0,r208,r209,r210,r211,r212,r213,r214,r215],[r190,r216,r217,r218,r219,r220,r221,r222],[0,r198,r199,r129,r200,r201,r202],[],[],[],[],[r223,r224,r225,r226,r227,r228,32768],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[r229,r230,r53,r231,r232,r233,r234,r235,r236,r237,r238,r239,r240,r241,r242]),(⟨0,0,1⟩,[0,r243,r244,r245,r246,r247,r248,r249,r250,r251,r252,r253,r254,r255]),(⟨0,0,2⟩,[r256,r257,r258,r259,r260,r261,r262,r263,r264,r265,r266,r267,r268]),(⟨0,0,3⟩,[0,r269,r270,r271,r272,r273,r274,r275,r276,r277,r278,r279]),(⟨0,0,4⟩,[r229,r280,r281,r282,r283,r284,r285,r286,r287,r288,r289]),(⟨0,0,5⟩,[0,r290,r291,r292,r293,r294,r295,r296,r297,r298]),(⟨0,0,6⟩,[0,0,r299,r300,r301,r302,r303,r304,r305]),(⟨0,1,0⟩,[0,r243,r244,r245,r246,r247,r248,r249,r250,r251,r252,r253,r254,r255]),(⟨0,1,1⟩,[0,r256,r306,r307,r308,r309,r310,r311,r312,r313,r314,r315,r316]),(⟨0,1,2⟩,[0,r317,r318,r319,r320,r321,r322,r323,r324,r325,r326,r327]),(⟨0,1,3⟩,[0,r0,r328,r329,r330,r331,r332,r333,r334,r335,r336]),(⟨0,1,4⟩,[0,0,r337,r338,r339,r340,r341,r342,r343,r344]),(⟨0,2,0⟩,[r256,r257,r258,r259,r260,r261,r262,r263,r264,r265,r266,r267,r268]),(⟨0,2,1⟩,[0,r317,r318,r319,r320,r321,r322,r323,r324,r325,r326,r327]),(⟨0,2,2⟩,[r0,r52,r345,r346,r347,r348,r349,r350,r351,r352,r353]),(⟨0,2,3⟩,[0,r290,r291,r292,r293,r294,r295,r296,r297,r298]),(⟨0,3,0⟩,[0,r269,r270,r271,r272,r273,r274,r275,r276,r277,r278,r279]),(⟨0,3,1⟩,[0,r0,r328,r329,r330,r331,r332,r333,r334,r335,r336]),(⟨0,3,2⟩,[0,r290,r291,r292,r293,r294,r295,r296,r297,r298]),(⟨0,3,3⟩,[0,0,r71,r72,r73,r74,r75,r76,r77]),(⟨0,4,0⟩,[r229,r280,r281,r282,r283,r284,r285,r286,r287,r288,r289]),(⟨0,4,1⟩,[0,0,r337,r338,r339,r340,r341,r342,r343,r344]),(⟨0,5,0⟩,[0,r290,r291,r292,r293,r294,r295,r296,r297,r298]),(⟨0,6,0⟩,[0,0,r299,r300,r301,r302,r303,r304,r305]),(⟨1,0,0⟩,[0,r243,r244,r245,r246,r247,r248,r249,r250,r251,r252,r253,r254,r255]),(⟨1,0,1⟩,[0,r256,r306,r307,r308,r309,r310,r311,r312,r313,r314,r315,r316]),(⟨1,0,2⟩,[0,r317,r318,r319,r320,r321,r322,r323,r324,r325,r326,r327]),(⟨1,0,3⟩,[0,r0,r328,r329,r330,r331,r332,r333,r334,r335,r336]),(⟨1,0,4⟩,[0,0,r337,r338,r339,r340,r341,r342,r343,r344]),(⟨1,1,0⟩,[0,r256,r306,r307,r308,r309,r310,r311,r312,r313,r314,r315,r316]),(⟨1,1,1⟩,[r0,r52,r354,r355,r356,r357,r358,r359,r360,r361,r362,r363]),(⟨1,1,2⟩,[0,r364,r365,r366,r367,r368,r369,r370,r371,r372,r373]),(⟨1,1,3⟩,[r256,r374,r375,r376,r377,r378,r379,r380,r381,r382]),(⟨1,1,4⟩,[0,r383,r384,r385,r386,r387,r388,r389,r390]),(⟨1,2,0⟩,[0,r317,r318,r319,r320,r321,r322,r323,r324,r325,r326,r327]),(⟨1,2,1⟩,[0,r364,r365,r366,r367,r368,r369,r370,r371,r372,r373]),(⟨1,2,2⟩,[r28,r391,r392,r393,r394,r395,r396,r397,r398,r399]),(⟨1,2,3⟩,[0,r400,r401,r402,r403,r404,r405,r406,r407]),(⟨1,2,4⟩,[r100,r408,r409,r410,r411,r412,r413,r414]),(⟨1,2,5⟩,[0,r415,r416,r72,r417,r418,r419]),(⟨1,3,0⟩,[0,r0,r328,r329,r330,r331,r332,r333,r334,r335,r336]),(⟨1,3,1⟩,[r256,r374,r375,r376,r377,r378,r379,r380,r381,r382]),(⟨1,3,2⟩,[0,r400,r401,r402,r403,r404,r405,r406,r407]),(⟨1,3,3⟩,[0,r190,r328,r420,r421,r422,r423,-16384]),(⟨1,4,0⟩,[0,0,r337,r338,r339,r340,r341,r342,r343,r344]),(⟨1,4,1⟩,[0,r383,r384,r385,r386,r387,r388,r389,r390]),(⟨1,4,2⟩,[r100,r408,r409,r410,r411,r412,r413,r414]),(⟨1,5,2⟩,[0,r415,r416,r72,r417,r418,r419]),(⟨2,0,0⟩,[r256,r257,r258,r259,r260,r261,r262,r263,r264,r265,r266,r267,r268]),(⟨2,0,1⟩,[0,r317,r318,r319,r320,r321,r322,r323,r324,r325,r326,r327]),(⟨2,0,2⟩,[r0,r52,r345,r346,r347,r348,r349,r350,r351,r352,r353]),(⟨2,0,3⟩,[0,r290,r291,r292,r293,r294,r295,r296,r297,r298]),(⟨2,1,0⟩,[0,r317,r318,r319,r320,r321,r322,r323,r324,r325,r326,r327]),(⟨2,1,1⟩,[0,r364,r365,r366,r367,r368,r369,r370,r371,r372,r373]),(⟨2,1,2⟩,[r28,r391,r392,r393,r394,r395,r396,r397,r398,r399]),(⟨2,1,3⟩,[0,r400,r401,r402,r403,r404,r405,r406,r407]),(⟨2,1,4⟩,[r100,r408,r409,r410,r411,r412,r413,r414]),(⟨2,1,5⟩,[0,r415,r416,r72,r417,r418,r419]),(⟨2,2,0⟩,[r0,r52,r345,r346,r347,r348,r349,r350,r351,r352,r353]),(⟨2,2,1⟩,[r28,r391,r392,r393,r394,r395,r396,r397,r398,r399]),(⟨2,2,2⟩,[0,r424,r425,r426,r427,r428,r429,r430,r431]),(⟨2,2,3⟩,[r100,r432,r433,r434,r435,r436,r437,r438]),(⟨2,2,4⟩,[0,r415,r416,r72,r417,r418,r419]),(⟨2,3,0⟩,[0,r290,r291,r292,r293,r294,r295,r296,r297,r298]),(⟨2,3,1⟩,[0,r400,r401,r402,r403,r404,r405,r406,r407]),(⟨2,3,2⟩,[r100,r432,r433,r434,r435,r436,r437,r438]),(⟨2,3,3⟩,[r172,r439,r440,r441,r442,r443,16384]),(⟨2,4,1⟩,[r100,r408,r409,r410,r411,r412,r413,r414]),(⟨2,4,2⟩,[0,r415,r416,r72,r417,r418,r419]),(⟨2,5,1⟩,[0,r415,r416,r72,r417,r418,r419]),(⟨3,0,0⟩,[0,r269,r270,r271,r272,r273,r274,r275,r276,r277,r278,r279]),(⟨3,0,1⟩,[0,r0,r328,r329,r330,r331,r332,r333,r334,r335,r336]),(⟨3,0,2⟩,[0,r290,r291,r292,r293,r294,r295,r296,r297,r298]),(⟨3,0,3⟩,[0,0,r71,r72,r73,r74,r75,r76,r77]),(⟨3,1,0⟩,[0,r0,r328,r329,r330,r331,r332,r333,r334,r335,r336]),(⟨3,1,1⟩,[r256,r374,r375,r376,r377,r378,r379,r380,r381,r382]),(⟨3,1,2⟩,[0,r400,r401,r402,r403,r404,r405,r406,r407]),(⟨3,1,3⟩,[0,r190,r328,r420,r421,r422,r423,-16384]),(⟨3,2,0⟩,[0,r290,r291,r292,r293,r294,r295,r296,r297,r298]),(⟨3,2,1⟩,[0,r400,r401,r402,r403,r404,r405,r406,r407]),(⟨3,2,2⟩,[r100,r432,r433,r434,r435,r436,r437,r438]),(⟨3,2,3⟩,[r172,r439,r440,r441,r442,r443,16384]),(⟨3,3,0⟩,[0,0,r71,r72,r73,r74,r75,r76,r77]),(⟨3,3,1⟩,[0,r190,r328,r420,r421,r422,r423,-16384]),(⟨3,3,2⟩,[r172,r439,r440,r441,r442,r443,16384]),(⟨4,0,0⟩,[r229,r280,r281,r282,r283,r284,r285,r286,r287,r288,r289]),(⟨4,0,1⟩,[0,0,r337,r338,r339,r340,r341,r342,r343,r344]),(⟨4,1,0⟩,[0,0,r337,r338,r339,r340,r341,r342,r343,r344]),(⟨4,1,1⟩,[0,r383,r384,r385,r386,r387,r388,r389,r390]),(⟨4,1,2⟩,[r100,r408,r409,r410,r411,r412,r413,r414]),(⟨4,2,1⟩,[r100,r408,r409,r410,r411,r412,r413,r414]),(⟨4,2,2⟩,[0,r415,r416,r72,r417,r418,r419]),(⟨5,0,0⟩,[0,r290,r291,r292,r293,r294,r295,r296,r297,r298]),(⟨5,1,2⟩,[0,r415,r416,r72,r417,r418,r419]),(⟨5,2,1⟩,[0,r415,r416,r72,r417,r418,r419]),(⟨6,0,0⟩,[0,0,r299,r300,r301,r302,r303,r304,r305])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[16,-208,1008,-2480,2688,-512]),(⟨0,0,1⟩,[0,-96,704,-1760,1664]),(⟨0,0,2⟩,[-16,176,-304,-112]),(⟨0,0,3⟩,[0,128,-384]),(⟨0,1,0⟩,[0,-96,704,-1760,1664]),(⟨0,1,1⟩,[0,-32,320,-544]),(⟨0,2,0⟩,[-16,176,-304,-112]),(⟨0,3,0⟩,[0,128,-384]),(⟨1,0,0⟩,[0,-96,704,-1760,1664]),(⟨1,0,1⟩,[0,-32,320,-544]),(⟨1,1,0⟩,[0,-32,320,-544]),(⟨1,1,1⟩,[32,-320,544]),(⟨2,0,0⟩,[-16,176,-304,-112]),(⟨3,0,0⟩,[0,128,-384])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[128,-2688,24576,-125568,372480,-579456,211968,627840,-719744,92160]),(⟨0,0,1⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920]),(⟨0,0,2⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨0,0,3⟩,[0,1280,-13056,47616,-60928,-24320,82176]),(⟨0,1,0⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920]),(⟨0,2,0⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨0,3,0⟩,[0,1280,-13056,47616,-60928,-24320,82176]),(⟨1,0,0⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920]),(⟨1,2,2⟩,[-512,6144,-15360,-18432,60928]),(⟨2,0,0⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨2,1,2⟩,[-512,6144,-15360,-18432,60928]),(⟨2,2,1⟩,[-512,6144,-15360,-18432,60928]),(⟨3,0,0⟩,[0,1280,-13056,47616,-60928,-24320,82176])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 10 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r444) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 12 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r445) sourceRight))).isZero := by decide +kernel

noncomputable def partial14 : Poly := []

theorem partial_sound14 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 14)
      sourceRight).eval u v t=partial14.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨2,0,0⟩,[-16,176,-304,-112]),(⟨3,0,0⟩,[0,128,-384])]

noncomputable def partial12 : Poly := [(⟨2,0,0⟩,[-2048,65536,-905216,7137280,-35229696,110247936,-204546048,161697792,122476544,-342753280,164704256,52594688,-10321920]),(⟨2,0,1⟩,[0,14336,-360448,3684352,-20299776,65286144,-117817344,82767872,82493440,-184576000,65945600,39639040]),(⟨2,0,2⟩,[2048,-63488,778240,-4833280,15929344,-23949312,-1785856,47710208,-35280896,-8902656,2007040]),(⟨2,0,3⟩,[0,-20480,434176,-3448832,13180928,-23347200,7593984,28680192,-22257664,-9203712]),(⟨2,1,0⟩,[0,14336,-360448,3684352,-20299776,65286144,-117817344,82767872,82493440,-184576000,65945600,39639040]),(⟨2,2,0⟩,[2048,-63488,778240,-4833280,15929344,-23949312,-1785856,47710208,-35280896,-8902656,2007040]),(⟨2,3,0⟩,[0,-20480,434176,-3448832,13180928,-23347200,7593984,28680192,-22257664,-9203712]),(⟨3,0,0⟩,[0,30720,-753664,7862272,-45809664,161181696,-335020032,332410880,81461248,-517793792,354123776,4249600]),(⟨3,0,1⟩,[0,0,-114688,1966080,-14319616,56754176,-126877696,135659520,15892480,-188088320,135905280]),(⟨3,0,2⟩,[0,-16384,376832,-3293184,14073856,-28688384,13975552,39796736,-51494912,6881280]),(⟨3,0,3⟩,[0,0,163840,-2162688,11108352,-26083328,20283392,19857408,-31555584]),(⟨3,1,0⟩,[0,0,-114688,1966080,-14319616,56754176,-126877696,135659520,15892480,-188088320,135905280]),(⟨3,2,0⟩,[0,-16384,376832,-3293184,14073856,-28688384,13975552,39796736,-51494912,6881280]),(⟨3,2,2⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨3,3,0⟩,[0,0,163840,-2162688,11108352,-26083328,20283392,19857408,-31555584]),(⟨4,0,0⟩,[2048,-63488,663552,-2867200,1609728,32804864,-128663552,183369728,-19388416,-196990976,137912320]),(⟨4,1,2⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨4,2,1⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨4,2,2⟩,[0,-65536,983040,-4325376,3538944,14876672,-23396352]),(⟨5,0,0⟩,[0,-36864,811008,-6742016,27254784,-52035584,21569536,68476928,-73752576,-2322432]),(⟨5,1,2⟩,[0,-65536,983040,-4325376,3538944,14876672,-23396352]),(⟨5,2,1⟩,[0,-65536,983040,-4325376,3538944,14876672,-23396352]),(⟨6,0,0⟩,[0,0,163840,-2162688,11108352,-26083328,20283392,19857408,-31555584])]


theorem partial_checked12 :
    (Poly.add (Poly.add (Poly.mul chunk12 sourceRight) partial14)
      (Poly.scale (K.ofRat (-1)) partial12)).isZero := by decide +kernel

theorem partial_sound12 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 12)
      sourceRight).eval u v t=partial12.eval u v t := by
  change (Poly.mul (chunk12++(sourceLeft.drop 14))
    sourceRight).eval u v t=partial12.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound14 partial_checked12 u v t


noncomputable def chunk8 : Poly := [(⟨1,0,0⟩,[0,-96,704,-1760,1664]),(⟨1,0,1⟩,[0,-32,320,-544]),(⟨1,1,0⟩,[0,-32,320,-544]),(⟨1,1,1⟩,[32,-320,544])]

noncomputable def partial8 : Poly := [(⟨1,0,0⟩,[0,-12288,348160,-4476928,34299904,-171884544,579747840,-1292795904,1728602112,-826183680,-1267830784,2376355840,-1359855616,153354240]),(⟨1,0,1⟩,[0,-4096,212992,-3563520,30932992,-162553856,544555008,-1145405440,1327841280,-282988544,-1341030400,1662672896,-639057920]),(⟨1,0,2⟩,[0,12288,-307200,3067904,-15876096,43130880,-40738816,-90087424,296534016,-254103552,-70791168,162713600]),(⟨1,0,3⟩,[0,4096,-245760,3620864,-24969216,93970432,-192643072,168706048,73990144,-260534272,146489344]),(⟨1,0,4⟩,[0,0,-40960,827392,-6397952,24289280,-44621824,22732800,39526400,-44703744]),(⟨1,1,0⟩,[0,-4096,212992,-3563520,30932992,-162553856,544555008,-1145405440,1327841280,-282988544,-1341030400,1662672896,-639057920]),(⟨1,1,1⟩,[4096,-126976,1773568,-14729216,79282176,-281296896,638009344,-818077696,274837504,745615360,-1052102656,435200000]),(⟨1,1,2⟩,[0,-24576,569344,-5439488,28672000,-92094464,181002240,-184483840,-10682368,240099328,-182784000]),(⟨1,1,3⟩,[-4096,122880,-1507328,9781248,-35889152,70844416,-51871744,-51986432,114962432,-54452224]),(⟨1,1,4⟩,[0,40960,-827392,6397952,-24289280,44621824,-22732800,-39526400,44703744]),(⟨1,2,0⟩,[0,12288,-307200,3067904,-15876096,43130880,-40738816,-90087424,296534016,-254103552,-70791168,162713600]),(⟨1,2,1⟩,[0,-24576,569344,-5439488,28672000,-92094464,181002240,-184483840,-10682368,240099328,-182784000]),(⟨1,3,0⟩,[0,4096,-245760,3620864,-24969216,93970432,-192643072,168706048,73990144,-260534272,146489344]),(⟨1,3,1⟩,[-4096,122880,-1507328,9781248,-35889152,70844416,-51871744,-51986432,114962432,-54452224]),(⟨1,4,0⟩,[0,0,-40960,827392,-6397952,24289280,-44621824,22732800,39526400,-44703744]),(⟨1,4,1⟩,[0,40960,-827392,6397952,-24289280,44621824,-22732800,-39526400,44703744]),(⟨2,0,0⟩,[-2048,65536,-819200,5289984,-17641472,13164544,133963776,-588869632,1087354880,-734371840,-601513984,1294235648,-599244800]),(⟨2,0,1⟩,[0,14336,-331776,2992128,-13393920,27660288,3768320,-144789504,274227200,-99174400,-249589760,232171520]),(⟨2,0,2⟩,[2048,-63488,778240,-4833280,15929344,-23949312,-1785856,47710208,-35280896,-8902656,2007040]),(⟨2,0,3⟩,[0,-20480,434176,-3448832,13180928,-23347200,7593984,28680192,-22257664,-9203712]),(⟨2,1,0⟩,[0,14336,-331776,2992128,-13393920,27660288,3768320,-144789504,274227200,-99174400,-249589760,232171520]),(⟨2,1,1⟩,[0,-28672,692224,-6905856,37625856,-121585664,227557376,-191733760,-85401600,315535360,-192532480]),(⟨2,2,0⟩,[2048,-63488,778240,-4833280,15929344,-23949312,-1785856,47710208,-35280896,-8902656,2007040]),(⟨2,2,2⟩,[0,49152,-950272,6701056,-20709376,18432000,49774592,-137904128,101384192]),(⟨2,2,3⟩,[0,16384,-360448,2736128,-7667712,507904,29523968,-33144832]),(⟨2,3,0⟩,[0,-20480,434176,-3448832,13180928,-23347200,7593984,28680192,-22257664,-9203712]),(⟨2,3,2⟩,[0,16384,-360448,2736128,-7667712,507904,29523968,-33144832]),(⟨2,3,3⟩,[-16384,360448,-2736128,7667712,-507904,-29523968,33144832]),(⟨3,0,0⟩,[0,43008,-1089536,11622400,-68591616,241938432,-497344512,469880832,186261504,-857298944,598867968,-25569280]),(⟨3,0,1⟩,[0,4096,-237568,3432448,-23273472,86245376,-173432832,142909440,90611712,-263524352,145653760]),(⟨3,0,2⟩,[0,-16384,376832,-3293184,14073856,-28688384,13975552,39796736,-51494912,6881280]),(⟨3,0,3⟩,[0,0,163840,-2162688,11108352,-26083328,20283392,19857408,-31555584]),(⟨3,1,0⟩,[0,4096,-237568,3432448,-23273472,86245376,-173432832,142909440,90611712,-263524352,145653760]),(⟨3,1,1⟩,[-4096,122880,-1466368,8953856,-29491200,46555136,-7249920,-74719232,75436032,-9748480]),(⟨3,1,2⟩,[0,49152,-950272,6701056,-20709376,18432000,49774592,-137904128,101384192]),(⟨3,1,3⟩,[0,16384,-360448,2736128,-7667712,507904,29523968,-33144832]),(⟨3,2,0⟩,[0,-16384,376832,-3293184,14073856,-28688384,13975552,39796736,-51494912,6881280]),(⟨3,2,1⟩,[0,49152,-950272,6701056,-20709376,18432000,49774592,-137904128,101384192]),(⟨3,2,2⟩,[8192,-155648,761856,1253376,-15572992,19062784,42590208,-73113600]),(⟨3,2,3⟩,[-16384,360448,-2736128,7667712,-507904,-29523968,33144832]),(⟨3,3,0⟩,[0,0,163840,-2162688,11108352,-26083328,20283392,19857408,-31555584]),(⟨3,3,1⟩,[0,16384,-360448,2736128,-7667712,507904,29523968,-33144832]),(⟨3,3,2⟩,[-16384,360448,-2736128,7667712,-507904,-29523968,33144832]),(⟨4,0,0⟩,[2048,-63488,540672,-712704,-14405632,97284096,-274751488,344825856,-20117504,-382089216,274653184]),(⟨4,0,1⟩,[0,0,-40960,827392,-6397952,24289280,-44621824,22732800,39526400,-44703744]),(⟨4,1,0⟩,[0,0,-40960,827392,-6397952,24289280,-44621824,22732800,39526400,-44703744]),(⟨4,1,1⟩,[0,40960,-827392,6397952,-24289280,44621824,-22732800,-39526400,44703744]),(⟨4,1,2⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨4,2,1⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨4,2,2⟩,[0,-65536,983040,-4325376,3538944,14876672,-23396352]),(⟨5,0,0⟩,[0,-36864,811008,-6742016,27254784,-52035584,21569536,68476928,-73752576,-2322432]),(⟨5,1,2⟩,[0,-65536,983040,-4325376,3538944,14876672,-23396352]),(⟨5,2,1⟩,[0,-65536,983040,-4325376,3538944,14876672,-23396352]),(⟨6,0,0⟩,[0,0,163840,-2162688,11108352,-26083328,20283392,19857408,-31555584])]


theorem partial_checked8 :
    (Poly.add (Poly.add (Poly.mul chunk8 sourceRight) partial12)
      (Poly.scale (K.ofRat (-1)) partial8)).isZero := by decide +kernel

theorem partial_sound8 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 8)
      sourceRight).eval u v t=partial8.eval u v t := by
  change (Poly.mul (chunk8++(sourceLeft.drop 12))
    sourceRight).eval u v t=partial8.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound12 partial_checked8 u v t


noncomputable def chunk4 : Poly := [(⟨0,1,0⟩,[0,-96,704,-1760,1664]),(⟨0,1,1⟩,[0,-32,320,-544]),(⟨0,2,0⟩,[-16,176,-304,-112]),(⟨0,3,0⟩,[0,128,-384])]

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[0,-12288,348160,-4476928,34299904,-171884544,579747840,-1292795904,1728602112,-826183680,-1267830784,2376355840,-1359855616,153354240]),(⟨0,1,1⟩,[0,-4096,212992,-3563520,30932992,-162553856,544555008,-1145405440,1327841280,-282988544,-1341030400,1662672896,-639057920]),(⟨0,1,2⟩,[0,12288,-307200,3067904,-15876096,43130880,-40738816,-90087424,296534016,-254103552,-70791168,162713600]),(⟨0,1,3⟩,[0,4096,-245760,3620864,-24969216,93970432,-192643072,168706048,73990144,-260534272,146489344]),(⟨0,1,4⟩,[0,0,-40960,827392,-6397952,24289280,-44621824,22732800,39526400,-44703744]),(⟨0,2,0⟩,[-2048,65536,-819200,5289984,-17641472,13164544,133963776,-588869632,1087354880,-734371840,-601513984,1294235648,-599244800]),(⟨0,2,1⟩,[0,14336,-331776,2992128,-13393920,27660288,3768320,-144789504,274227200,-99174400,-249589760,232171520]),(⟨0,2,2⟩,[2048,-63488,778240,-4833280,15929344,-23949312,-1785856,47710208,-35280896,-8902656,2007040]),(⟨0,2,3⟩,[0,-20480,434176,-3448832,13180928,-23347200,7593984,28680192,-22257664,-9203712]),(⟨0,3,0⟩,[0,43008,-1089536,11622400,-68591616,241938432,-497344512,469880832,186261504,-857298944,598867968,-25569280]),(⟨0,3,1⟩,[0,4096,-237568,3432448,-23273472,86245376,-173432832,142909440,90611712,-263524352,145653760]),(⟨0,3,2⟩,[0,-16384,376832,-3293184,14073856,-28688384,13975552,39796736,-51494912,6881280]),(⟨0,3,3⟩,[0,0,163840,-2162688,11108352,-26083328,20283392,19857408,-31555584]),(⟨0,4,0⟩,[2048,-63488,540672,-712704,-14405632,97284096,-274751488,344825856,-20117504,-382089216,274653184]),(⟨0,4,1⟩,[0,0,-40960,827392,-6397952,24289280,-44621824,22732800,39526400,-44703744]),(⟨0,5,0⟩,[0,-36864,811008,-6742016,27254784,-52035584,21569536,68476928,-73752576,-2322432]),(⟨0,6,0⟩,[0,0,163840,-2162688,11108352,-26083328,20283392,19857408,-31555584]),(⟨1,0,0⟩,[0,-12288,348160,-4476928,34299904,-171884544,579747840,-1292795904,1728602112,-826183680,-1267830784,2376355840,-1359855616,153354240]),(⟨1,0,1⟩,[0,-4096,212992,-3563520,30932992,-162553856,544555008,-1145405440,1327841280,-282988544,-1341030400,1662672896,-639057920]),(⟨1,0,2⟩,[0,12288,-307200,3067904,-15876096,43130880,-40738816,-90087424,296534016,-254103552,-70791168,162713600]),(⟨1,0,3⟩,[0,4096,-245760,3620864,-24969216,93970432,-192643072,168706048,73990144,-260534272,146489344]),(⟨1,0,4⟩,[0,0,-40960,827392,-6397952,24289280,-44621824,22732800,39526400,-44703744]),(⟨1,1,0⟩,[0,-4096,299008,-5410816,48521216,-259637248,883064832,-1895972864,2292719616,-674607104,-2107248640,2904313856,-1227980800]),(⟨1,1,1⟩,[4096,-126976,1802240,-15421440,86188032,-318922752,759595008,-1045635072,466571264,831016960,-1367638016,627732480]),(⟨1,1,2⟩,[0,-24576,569344,-5439488,28672000,-92094464,181002240,-184483840,-10682368,240099328,-182784000]),(⟨1,1,3⟩,[-4096,122880,-1507328,9781248,-35889152,70844416,-51871744,-51986432,114962432,-54452224]),(⟨1,1,4⟩,[0,40960,-827392,6397952,-24289280,44621824,-22732800,-39526400,44703744]),(⟨1,2,0⟩,[0,26624,-667648,6752256,-36175872,108417024,-158556160,-7319552,379027456,-438679552,-4845568,202352640]),(⟨1,2,1⟩,[0,-24576,569344,-5439488,28672000,-92094464,181002240,-184483840,-10682368,240099328,-182784000]),(⟨1,3,0⟩,[0,4096,-360448,5586944,-39288832,150724608,-319520768,304365568,89882624,-448622592,282394624]),(⟨1,3,1⟩,[-4096,122880,-1507328,9781248,-35889152,70844416,-51871744,-51986432,114962432,-54452224]),(⟨1,3,2⟩,[0,49152,-950272,6701056,-20709376,18432000,49774592,-137904128,101384192]),(⟨1,3,3⟩,[0,16384,-360448,2736128,-7667712,507904,29523968,-33144832]),(⟨1,4,0⟩,[0,0,-40960,827392,-6397952,24289280,-44621824,22732800,39526400,-44703744]),(⟨1,4,1⟩,[0,40960,-827392,6397952,-24289280,44621824,-22732800,-39526400,44703744]),(⟨1,4,2⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨1,5,2⟩,[0,-65536,983040,-4325376,3538944,14876672,-23396352]),(⟨2,0,0⟩,[-2048,65536,-819200,5289984,-17641472,13164544,133963776,-588869632,1087354880,-734371840,-601513984,1294235648,-599244800]),(⟨2,0,1⟩,[0,14336,-331776,2992128,-13393920,27660288,3768320,-144789504,274227200,-99174400,-249589760,232171520]),(⟨2,0,2⟩,[2048,-63488,778240,-4833280,15929344,-23949312,-1785856,47710208,-35280896,-8902656,2007040]),(⟨2,0,3⟩,[0,-20480,434176,-3448832,13180928,-23347200,7593984,28680192,-22257664,-9203712]),(⟨2,1,0⟩,[0,26624,-667648,6752256,-36175872,108417024,-158556160,-7319552,379027456,-438679552,-4845568,202352640]),(⟨2,1,1⟩,[0,-24576,569344,-5439488,28672000,-92094464,181002240,-184483840,-10682368,240099328,-182784000]),(⟨2,2,0⟩,[4096,-126976,1556480,-9666560,31858688,-47898624,-3571712,95420416,-70561792,-17805312,4014080]),(⟨2,2,2⟩,[0,98304,-1900544,13402112,-41418752,36864000,99549184,-275808256,202768384]),(⟨2,2,3⟩,[0,32768,-720896,5472256,-15335424,1015808,59047936,-66289664]),(⟨2,3,0⟩,[0,-36864,811008,-6742016,27254784,-52035584,21569536,68476928,-73752576,-2322432]),(⟨2,3,1⟩,[0,49152,-950272,6701056,-20709376,18432000,49774592,-137904128,101384192]),(⟨2,3,2⟩,[8192,-155648,761856,1253376,-15572992,19062784,42590208,-73113600]),(⟨2,3,3⟩,[-16384,360448,-2736128,7667712,-507904,-29523968,33144832]),(⟨2,4,1⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨2,4,2⟩,[0,-65536,983040,-4325376,3538944,14876672,-23396352]),(⟨2,5,1⟩,[0,-65536,983040,-4325376,3538944,14876672,-23396352]),(⟨3,0,0⟩,[0,43008,-1089536,11622400,-68591616,241938432,-497344512,469880832,186261504,-857298944,598867968,-25569280]),(⟨3,0,1⟩,[0,4096,-237568,3432448,-23273472,86245376,-173432832,142909440,90611712,-263524352,145653760]),(⟨3,0,2⟩,[0,-16384,376832,-3293184,14073856,-28688384,13975552,39796736,-51494912,6881280]),(⟨3,0,3⟩,[0,0,163840,-2162688,11108352,-26083328,20283392,19857408,-31555584]),(⟨3,1,0⟩,[0,4096,-360448,5586944,-39288832,150724608,-319520768,304365568,89882624,-448622592,282394624]),(⟨3,1,1⟩,[-4096,122880,-1507328,9781248,-35889152,70844416,-51871744,-51986432,114962432,-54452224]),(⟨3,1,2⟩,[0,49152,-950272,6701056,-20709376,18432000,49774592,-137904128,101384192]),(⟨3,1,3⟩,[0,16384,-360448,2736128,-7667712,507904,29523968,-33144832]),(⟨3,2,0⟩,[0,-36864,811008,-6742016,27254784,-52035584,21569536,68476928,-73752576,-2322432]),(⟨3,2,1⟩,[0,49152,-950272,6701056,-20709376,18432000,49774592,-137904128,101384192]),(⟨3,2,2⟩,[8192,-155648,761856,1253376,-15572992,19062784,42590208,-73113600]),(⟨3,2,3⟩,[-16384,360448,-2736128,7667712,-507904,-29523968,33144832]),(⟨3,3,0⟩,[0,0,327680,-4325376,22216704,-52166656,40566784,39714816,-63111168]),(⟨3,3,1⟩,[0,16384,-360448,2736128,-7667712,507904,29523968,-33144832]),(⟨3,3,2⟩,[-16384,360448,-2736128,7667712,-507904,-29523968,33144832]),(⟨4,0,0⟩,[2048,-63488,540672,-712704,-14405632,97284096,-274751488,344825856,-20117504,-382089216,274653184]),(⟨4,0,1⟩,[0,0,-40960,827392,-6397952,24289280,-44621824,22732800,39526400,-44703744]),(⟨4,1,0⟩,[0,0,-40960,827392,-6397952,24289280,-44621824,22732800,39526400,-44703744]),(⟨4,1,1⟩,[0,40960,-827392,6397952,-24289280,44621824,-22732800,-39526400,44703744]),(⟨4,1,2⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨4,2,1⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨4,2,2⟩,[0,-65536,983040,-4325376,3538944,14876672,-23396352]),(⟨5,0,0⟩,[0,-36864,811008,-6742016,27254784,-52035584,21569536,68476928,-73752576,-2322432]),(⟨5,1,2⟩,[0,-65536,983040,-4325376,3538944,14876672,-23396352]),(⟨5,2,1⟩,[0,-65536,983040,-4325376,3538944,14876672,-23396352]),(⟨6,0,0⟩,[0,0,163840,-2162688,11108352,-26083328,20283392,19857408,-31555584])]


theorem partial_checked4 :
    (Poly.add (Poly.add (Poly.mul chunk4 sourceRight) partial8)
      (Poly.scale (K.ofRat (-1)) partial4)).isZero := by decide +kernel

theorem partial_sound4 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 4)
      sourceRight).eval u v t=partial4.eval u v t := by
  change (Poly.mul (chunk4++(sourceLeft.drop 8))
    sourceRight).eval u v t=partial4.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound8 partial_checked4 u v t


noncomputable def chunk0 : Poly := [(⟨0,0,0⟩,[16,-208,1008,-2480,2688,-512]),(⟨0,0,1⟩,[0,-96,704,-1760,1664]),(⟨0,0,2⟩,[-16,176,-304,-112]),(⟨0,0,3⟩,[0,128,-384])]

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[2048,-69632,1081344,-10147840,63860736,-281559040,878223360,-1891995648,2574125056,-1489924096,-1435262976,3456968704,-2484682752,616235008,-47185920]),(⟨0,0,1⟩,[0,-26624,737280,-9197568,68206592,-331517952,1090109440,-2387521536,3170779136,-1571719168,-2158034944,4211312640,-2501574656,334561280]),(⟨0,0,2⟩,[-4096,133120,-1769472,12834816,-55042048,131944448,-96698368,-377344000,1190342656,-1204934656,-181469184,1180465152,-590069760]),(⟨0,0,3⟩,[0,63488,-1564672,16390144,-95805440,338038784,-706224128,714051584,141254656,-1095272448,832208896,-67643392]),(⟨0,0,4⟩,[2048,-63488,540672,-712704,-14405632,97284096,-274751488,344825856,-20117504,-382089216,274653184]),(⟨0,0,5⟩,[0,-36864,811008,-6742016,27254784,-52035584,21569536,68476928,-73752576,-2322432]),(⟨0,0,6⟩,[0,0,163840,-2162688,11108352,-26083328,20283392,19857408,-31555584]),(⟨0,1,0⟩,[0,-26624,737280,-9197568,68206592,-331517952,1090109440,-2387521536,3170779136,-1571719168,-2158034944,4211312640,-2501574656,334561280]),(⟨0,1,1⟩,[0,-4096,299008,-5410816,48521216,-259637248,883064832,-1895972864,2292719616,-674607104,-2107248640,2904313856,-1227980800]),(⟨0,1,2⟩,[0,26624,-667648,6752256,-36175872,108417024,-158556160,-7319552,379027456,-438679552,-4845568,202352640]),(⟨0,1,3⟩,[0,4096,-360448,5586944,-39288832,150724608,-319520768,304365568,89882624,-448622592,282394624]),(⟨0,1,4⟩,[0,0,-40960,827392,-6397952,24289280,-44621824,22732800,39526400,-44703744]),(⟨0,2,0⟩,[-4096,133120,-1769472,12834816,-55042048,131944448,-96698368,-377344000,1190342656,-1204934656,-181469184,1180465152,-590069760]),(⟨0,2,1⟩,[0,26624,-667648,6752256,-36175872,108417024,-158556160,-7319552,379027456,-438679552,-4845568,202352640]),(⟨0,2,2⟩,[4096,-126976,1556480,-9666560,31858688,-47898624,-3571712,95420416,-70561792,-17805312,4014080]),(⟨0,2,3⟩,[0,-36864,811008,-6742016,27254784,-52035584,21569536,68476928,-73752576,-2322432]),(⟨0,3,0⟩,[0,63488,-1564672,16390144,-95805440,338038784,-706224128,714051584,141254656,-1095272448,832208896,-67643392]),(⟨0,3,1⟩,[0,4096,-360448,5586944,-39288832,150724608,-319520768,304365568,89882624,-448622592,282394624]),(⟨0,3,2⟩,[0,-36864,811008,-6742016,27254784,-52035584,21569536,68476928,-73752576,-2322432]),(⟨0,3,3⟩,[0,0,327680,-4325376,22216704,-52166656,40566784,39714816,-63111168]),(⟨0,4,0⟩,[2048,-63488,540672,-712704,-14405632,97284096,-274751488,344825856,-20117504,-382089216,274653184]),(⟨0,4,1⟩,[0,0,-40960,827392,-6397952,24289280,-44621824,22732800,39526400,-44703744]),(⟨0,5,0⟩,[0,-36864,811008,-6742016,27254784,-52035584,21569536,68476928,-73752576,-2322432]),(⟨0,6,0⟩,[0,0,163840,-2162688,11108352,-26083328,20283392,19857408,-31555584]),(⟨1,0,0⟩,[0,-26624,737280,-9197568,68206592,-331517952,1090109440,-2387521536,3170779136,-1571719168,-2158034944,4211312640,-2501574656,334561280]),(⟨1,0,1⟩,[0,-4096,299008,-5410816,48521216,-259637248,883064832,-1895972864,2292719616,-674607104,-2107248640,2904313856,-1227980800]),(⟨1,0,2⟩,[0,26624,-667648,6752256,-36175872,108417024,-158556160,-7319552,379027456,-438679552,-4845568,202352640]),(⟨1,0,3⟩,[0,4096,-360448,5586944,-39288832,150724608,-319520768,304365568,89882624,-448622592,282394624]),(⟨1,0,4⟩,[0,0,-40960,827392,-6397952,24289280,-44621824,22732800,39526400,-44703744]),(⟨1,1,0⟩,[0,-4096,299008,-5410816,48521216,-259637248,883064832,-1895972864,2292719616,-674607104,-2107248640,2904313856,-1227980800]),(⟨1,1,1⟩,[4096,-126976,1802240,-15421440,86188032,-318922752,759595008,-1045635072,466571264,831016960,-1367638016,627732480]),(⟨1,1,2⟩,[0,-24576,569344,-5439488,28672000,-92094464,181002240,-184483840,-10682368,240099328,-182784000]),(⟨1,1,3⟩,[-4096,122880,-1507328,9781248,-35889152,70844416,-51871744,-51986432,114962432,-54452224]),(⟨1,1,4⟩,[0,40960,-827392,6397952,-24289280,44621824,-22732800,-39526400,44703744]),(⟨1,2,0⟩,[0,26624,-667648,6752256,-36175872,108417024,-158556160,-7319552,379027456,-438679552,-4845568,202352640]),(⟨1,2,1⟩,[0,-24576,569344,-5439488,28672000,-92094464,181002240,-184483840,-10682368,240099328,-182784000]),(⟨1,2,2⟩,[-8192,204800,-2039808,10362880,-27287552,23617536,62693376,-192782336,173211648,-31195136]),(⟨1,2,3⟩,[0,49152,-950272,6701056,-20709376,18432000,49774592,-137904128,101384192]),(⟨1,2,4⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨1,2,5⟩,[0,-65536,983040,-4325376,3538944,14876672,-23396352]),(⟨1,3,0⟩,[0,4096,-360448,5586944,-39288832,150724608,-319520768,304365568,89882624,-448622592,282394624]),(⟨1,3,1⟩,[-4096,122880,-1507328,9781248,-35889152,70844416,-51871744,-51986432,114962432,-54452224]),(⟨1,3,2⟩,[0,49152,-950272,6701056,-20709376,18432000,49774592,-137904128,101384192]),(⟨1,3,3⟩,[0,16384,-360448,2736128,-7667712,507904,29523968,-33144832]),(⟨1,4,0⟩,[0,0,-40960,827392,-6397952,24289280,-44621824,22732800,39526400,-44703744]),(⟨1,4,1⟩,[0,40960,-827392,6397952,-24289280,44621824,-22732800,-39526400,44703744]),(⟨1,4,2⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨1,5,2⟩,[0,-65536,983040,-4325376,3538944,14876672,-23396352]),(⟨2,0,0⟩,[-4096,133120,-1769472,12834816,-55042048,131944448,-96698368,-377344000,1190342656,-1204934656,-181469184,1180465152,-590069760]),(⟨2,0,1⟩,[0,26624,-667648,6752256,-36175872,108417024,-158556160,-7319552,379027456,-438679552,-4845568,202352640]),(⟨2,0,2⟩,[4096,-126976,1556480,-9666560,31858688,-47898624,-3571712,95420416,-70561792,-17805312,4014080]),(⟨2,0,3⟩,[0,-36864,811008,-6742016,27254784,-52035584,21569536,68476928,-73752576,-2322432]),(⟨2,1,0⟩,[0,26624,-667648,6752256,-36175872,108417024,-158556160,-7319552,379027456,-438679552,-4845568,202352640]),(⟨2,1,1⟩,[0,-24576,569344,-5439488,28672000,-92094464,181002240,-184483840,-10682368,240099328,-182784000]),(⟨2,1,2⟩,[-8192,204800,-2039808,10362880,-27287552,23617536,62693376,-192782336,173211648,-31195136]),(⟨2,1,3⟩,[0,49152,-950272,6701056,-20709376,18432000,49774592,-137904128,101384192]),(⟨2,1,4⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨2,1,5⟩,[0,-65536,983040,-4325376,3538944,14876672,-23396352]),(⟨2,2,0⟩,[4096,-126976,1556480,-9666560,31858688,-47898624,-3571712,95420416,-70561792,-17805312,4014080]),(⟨2,2,1⟩,[-8192,204800,-2039808,10362880,-27287552,23617536,62693376,-192782336,173211648,-31195136]),(⟨2,2,2⟩,[0,147456,-2850816,20103168,-62128128,55296000,149323776,-413712384,304152576]),(⟨2,2,3⟩,[8192,-155648,761856,1253376,-15572992,19062784,42590208,-73113600]),(⟨2,2,4⟩,[0,-65536,983040,-4325376,3538944,14876672,-23396352]),(⟨2,3,0⟩,[0,-36864,811008,-6742016,27254784,-52035584,21569536,68476928,-73752576,-2322432]),(⟨2,3,1⟩,[0,49152,-950272,6701056,-20709376,18432000,49774592,-137904128,101384192]),(⟨2,3,2⟩,[8192,-155648,761856,1253376,-15572992,19062784,42590208,-73113600]),(⟨2,3,3⟩,[-16384,360448,-2736128,7667712,-507904,-29523968,33144832]),(⟨2,4,1⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨2,4,2⟩,[0,-65536,983040,-4325376,3538944,14876672,-23396352]),(⟨2,5,1⟩,[0,-65536,983040,-4325376,3538944,14876672,-23396352]),(⟨3,0,0⟩,[0,63488,-1564672,16390144,-95805440,338038784,-706224128,714051584,141254656,-1095272448,832208896,-67643392]),(⟨3,0,1⟩,[0,4096,-360448,5586944,-39288832,150724608,-319520768,304365568,89882624,-448622592,282394624]),(⟨3,0,2⟩,[0,-36864,811008,-6742016,27254784,-52035584,21569536,68476928,-73752576,-2322432]),(⟨3,0,3⟩,[0,0,327680,-4325376,22216704,-52166656,40566784,39714816,-63111168]),(⟨3,1,0⟩,[0,4096,-360448,5586944,-39288832,150724608,-319520768,304365568,89882624,-448622592,282394624]),(⟨3,1,1⟩,[-4096,122880,-1507328,9781248,-35889152,70844416,-51871744,-51986432,114962432,-54452224]),(⟨3,1,2⟩,[0,49152,-950272,6701056,-20709376,18432000,49774592,-137904128,101384192]),(⟨3,1,3⟩,[0,16384,-360448,2736128,-7667712,507904,29523968,-33144832]),(⟨3,2,0⟩,[0,-36864,811008,-6742016,27254784,-52035584,21569536,68476928,-73752576,-2322432]),(⟨3,2,1⟩,[0,49152,-950272,6701056,-20709376,18432000,49774592,-137904128,101384192]),(⟨3,2,2⟩,[8192,-155648,761856,1253376,-15572992,19062784,42590208,-73113600]),(⟨3,2,3⟩,[-16384,360448,-2736128,7667712,-507904,-29523968,33144832]),(⟨3,3,0⟩,[0,0,327680,-4325376,22216704,-52166656,40566784,39714816,-63111168]),(⟨3,3,1⟩,[0,16384,-360448,2736128,-7667712,507904,29523968,-33144832]),(⟨3,3,2⟩,[-16384,360448,-2736128,7667712,-507904,-29523968,33144832]),(⟨4,0,0⟩,[2048,-63488,540672,-712704,-14405632,97284096,-274751488,344825856,-20117504,-382089216,274653184]),(⟨4,0,1⟩,[0,0,-40960,827392,-6397952,24289280,-44621824,22732800,39526400,-44703744]),(⟨4,1,0⟩,[0,0,-40960,827392,-6397952,24289280,-44621824,22732800,39526400,-44703744]),(⟨4,1,1⟩,[0,40960,-827392,6397952,-24289280,44621824,-22732800,-39526400,44703744]),(⟨4,1,2⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨4,2,1⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨4,2,2⟩,[0,-65536,983040,-4325376,3538944,14876672,-23396352]),(⟨5,0,0⟩,[0,-36864,811008,-6742016,27254784,-52035584,21569536,68476928,-73752576,-2322432]),(⟨5,1,2⟩,[0,-65536,983040,-4325376,3538944,14876672,-23396352]),(⟨5,2,1⟩,[0,-65536,983040,-4325376,3538944,14876672,-23396352]),(⟨6,0,0⟩,[0,0,163840,-2162688,11108352,-26083328,20283392,19857408,-31555584])]


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
    (Poly.add (Poly.scale (K.ofRat r446) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 10 12).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r444*r445 : ℚ)=r446 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 10 12 r444 r445 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 10=12 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 10 12).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C142

#print axioms Coulomb8.Columns.C142.sound
