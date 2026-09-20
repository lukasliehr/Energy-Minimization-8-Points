import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C131

def r0 : ℚ := { num := -12288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 428032, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -6776832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 65611776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -440092672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 128589824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -1192226816, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 24949837824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -3451666432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 107727079424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -151285663744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 156718467072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -112375023616, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := 49124151296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := -9664102400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := 627965952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := -2048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 180224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -618496, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 53526528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -419911680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 136323072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -9514246144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 29879566336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -72420734976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 134600228864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -187867697152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 189218701312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -127424915456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 48185712640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -5462720512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 26624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -843776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 11390976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -88133632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 442005504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -1511059456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 202448896, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := -605233152, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -1983866880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 20758495232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -45313159168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 54832640000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -37877348352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 1646407680, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 6144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -65536, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 9486336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -98099200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 627456000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -2765684736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 8843280384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -2966634496, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 35244705792, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -5914427392, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 30838521856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -11364425728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -241096704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -2048, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 22528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -206848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 11126784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := 34639872, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := -481611776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := 2348969984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := -7027208192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := 13834725376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := -17835526144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := 14140422144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := -5441820672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -4096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 16384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -290816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 40960000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -199925760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 652836864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -1452859392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 2045313024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -1587564544, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 360202240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := 56766464, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 32768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -1048576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 11534336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -9699328, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 261685248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -99090432, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 1197211648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -1250689024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 677019648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 49152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -1855488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := 28663808, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := -256225280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := 1542676480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -398008320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 3197845504, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -56234303488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 105941073920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := -145604972544, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := 139047854080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -11890888704, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 23657799680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := 2048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := -184320, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := 565248, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := -40783872, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 253593600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -151052288, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 3044769792, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := -5792112640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 6015883264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 410710016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -10768670720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := 14573694976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := -1097668608, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -4096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 2334720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -30167040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 218071040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -150364160, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 523714560, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := -9222660096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := 2326167552, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -19411128320, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 14314938368, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -5053157376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := -8192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 319488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := -4161536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := 229376, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := -123650048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := 468402176, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := -1335590912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := 2462875648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := -2747670528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := 89448448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := -4096, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 847872, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -10194944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 66523136, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -269869056, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := 729538560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -1293459456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 80388096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -783593472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 462303232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := -811651072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := 130297856, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 204800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -2039808, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 10362880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -27287552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 23617536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 62693376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := -192782336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := 173211648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -262144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := -950272, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := 6701056, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := -20709376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 18432000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := 7110656, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := -137904128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := 851968, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 8192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -188416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := 1482752, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := -4218880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := -237568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 18046976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -2351104, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -57344, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := -65536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := 983040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -4325376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 3538944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 14876672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -196608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := 65536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := -2097152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := 23068672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := -19398656, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := 523370496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := -198180864, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := 2394423296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := -2501378048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := 1354039296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := 16384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -360448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 2736128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -7667712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 507904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := 1736704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -376832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 2965504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -8437760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := -475136, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := 36093952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := -4702208, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := -114688, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -24576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 794624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := -11415552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 97533952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -561205248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := 2351153152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := -7602659328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := 19622395904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -2365489152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := 62998126592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := -70973288448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := 51857244160, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := -1110233088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := 24576, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -2936832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 28278784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := -25026560, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 741621760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -2269650944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := 5355274240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := -9872920576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := 13367910400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -12057645056, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 47677440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := 4096, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := -827392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := 9924608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := -66158592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := 281436160, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := -119750656, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := 1837424640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := -2988146688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := 3528142848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := -2850004992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := 72790016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := -319488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := 4685824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -2129920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 175554560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := -589512704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := 1377009664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := -2122612736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := 2016288768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := -56418304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := 131072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := -3145728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := 28049408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := -16252928, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := 192413696, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := 6291456, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -725352448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := 72876032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := -16384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 360448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -2736128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := 7667712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -507904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := -1736704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -6144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 214016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -3388416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := 32805888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := -220046336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := 64294912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -596113408, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := 12474918912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := -1725833216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := 53863539712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := -75642831872, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := 78359233536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := -56187511808, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := 24562075648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := -4832051200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := 313982976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := -1024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := 90112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := -309248, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := 26763264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := -209955840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := 68161536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := -4757123072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := 14939783168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -36210367488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := 67300114432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := -93933848576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := 94609350656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := -63712457728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := 24092856320, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := -2731360256, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := 13312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := -421888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := 5695488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := -44066816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := 221002752, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := -755529728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := 101224448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -302616576, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := -991933440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := 10379247616, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := -22656579584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := 27416320000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -18938674176, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := 823203840, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := 3072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -32768, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 4743168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -49049600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 313728000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -1382842368, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 4421640192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -1483317248, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 17622352896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := -2957213696, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 15419260928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -5682212864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := -120548352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := -1024, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := 11264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := -103424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := 5563392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := 17319936, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := -240805888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := 1174484992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -3513604096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 6917362688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -8917763072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 7070211072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := -2720910336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := 8192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -145408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 20480000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -99962880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 326418432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -726429696, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 1022656512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -793782272, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 180101120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := 28383232, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := -524288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := 5767168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := -4849664, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := 130842624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := -49545216, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := 598605824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := -625344512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := 338509824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := 24576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := -927744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := 14331904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := -128112640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := 771338240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := -199004160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := 1598922752, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := -28117151744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := 52970536960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := -72802486272, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := 69523927040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := -5945444352, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := 11828899840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := 1024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := -92160, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := 282624, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := -20391936, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := 126796800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := -75526144, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := 1522384896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := -2896056320, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := 3007941632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := 205355008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := -5384335360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := 7286847488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := -548834304, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := -2048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := 1167360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := -15083520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := 109035520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := -75182080, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := 261857280, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := -4611330048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := 1163083776, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := -9705564160, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := 7157469184, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := -2526578688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := 159744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := -2080768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := 114688, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := -61825024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := 234201088, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := -667795456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := 1231437824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := -1373835264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := 44724224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 423936, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := -5097472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := 33261568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := -134934528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := 364769280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := -646729728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := 40194048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := -391796736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := 231151616, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := -405825536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := 65148928, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := 102400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := -1019904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := 5181440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := -13643776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := 11808768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := 31346688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := -96391168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := 86605824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := -131072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := 3350528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := -10354688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := 9216000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := 3555328, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := -68952064, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := 425984, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := 4096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := -94208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := 741376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := -2109440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := -118784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := 9023488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := -1175552, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := -28672, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := -32768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := 491520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := -2162688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := 1769472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := 7438336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := -98304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := -180224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := 1368064, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := -3833856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := 253952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := 868352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := 397312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := -5707776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := 48766976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := -280602624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := 1175576576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := -3801329664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := 9811197952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := -1182744576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := 31499063296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := -35486644224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := 25928622080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := -555116544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r450 : ℚ := { num := 12288, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r451 : ℚ := { num := -1468416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r452 : ℚ := { num := 14139392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r453 : ℚ := { num := -12513280, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r454 : ℚ := { num := 370810880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r455 : ℚ := { num := -1134825472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r456 : ℚ := { num := 2677637120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r457 : ℚ := { num := -4936460288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r458 : ℚ := { num := 6683955200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r459 : ℚ := { num := -6028822528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r460 : ℚ := { num := 23838720, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r461 : ℚ := { num := 2048, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r462 : ℚ := { num := -413696, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r463 : ℚ := { num := 4962304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r464 : ℚ := { num := -33079296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r465 : ℚ := { num := 140718080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r466 : ℚ := { num := -59875328, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r467 : ℚ := { num := 918712320, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r468 : ℚ := { num := -1494073344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r469 : ℚ := { num := 1764071424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r470 : ℚ := { num := -1425002496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r471 : ℚ := { num := 36395008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r472 : ℚ := { num := -159744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r473 : ℚ := { num := 2342912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r474 : ℚ := { num := -1064960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r475 : ℚ := { num := 87777280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r476 : ℚ := { num := -294756352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r477 : ℚ := { num := 688504832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r478 : ℚ := { num := -1061306368, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r479 : ℚ := { num := 1008144384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r480 : ℚ := { num := -28209152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r481 : ℚ := { num := -1572864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r482 : ℚ := { num := 14024704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r483 : ℚ := { num := -8126464, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r484 : ℚ := { num := 96206848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r485 : ℚ := { num := 3145728, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r486 : ℚ := { num := -362676224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r487 : ℚ := { num := 36438016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r488 : ℚ := { num := -1368064, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r489 : ℚ := { num := 3833856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r490 : ℚ := { num := -253952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r491 : ℚ := { num := -868352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r492 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r493 : ℚ := { num := 1, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r494 : ℚ := { num := 1, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15],[r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30],[r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44],[r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57],[r58,r59,r60,r61,r62,r63,r64,r65,r66,r67,r68,r69],[r70,r71,r72,r73,r74,r75,r76,r77,r78,r79,r80],[0,r81,r82,r83,r84,r85,r86,r87,r88,r89],[],[],[],[],[],[],[0,r90,r91,r92,r93,r94,r95,r96,r97,r98,r99,r100,r101,r102],[r103,r104,r105,r106,r107,r108,r109,r110,r111,r112,r113,r114,r115],[0,r116,r117,r118,r119,r120,r121,r122,r123,r124,r125,r126],[0,r127,r128,r129,r130,r131,r132,r133,r134,r135,r136],[],[],[],[],[],[],[],[r137,r138,r139,r140,r141,r142,r143,r144,r145,r146,r147,r148],[r70,r71,r72,r73,r74,r75,r76,r77,r78,r79,r80],[r127,r149,r150,r151,r152,r153,r154,r155,r156,r157],[0,r90,r158,r159,r160,r161,r162,r163,r164],[r165,r166,r167,r168,r169,r170,r171,r172],[0,r173,r174,r175,r176,r177,r178],[],[],[],[0,r179,r180,r181,r182,r183,r184,r185,r186,r187],[0,r90,r158,r159,r160,r161,r162,r163,r164],[0,r188,r189,r190,r191,r192,r193,-16384],[],[],[],[],[r188,r194,r195,r196,r197,r198,r199,r200],[0,r173,r174,r175,r176,r177,r178],[],[],[],[],[],[],[],[r201,r202,r203,r204,r205,r206,r207,r208,r209,r210,r211,r212,r213],[r70,r214,r215,r216,r217,r218,r219,r220,r221,r222,r223,r224],[r225,r226,r227,r228,r229,r230,r231,r232,r233,r234,r235],[r165,r236,r237,r238,r239,r240,r241,r242,r243,r244],[],[],[],[],[],[],[0,0,r245,r246,r247,r248,r249,r250,r251,r252,-393216],[],[0,r90,r158,r159,r160,r161,r162,r163,r164],[0,r188,r189,r190,r191,r192,r193,-16384],[],[],[],[],[],[0,r188,r189,r190,r191,r192,r193,-16384],[r253,r254,r255,r256,r257,r258,16384],[],[],[],[],[],[],[],[],[],[],[],[r188,r194,r195,r196,r197,r198,r199,r200],[],[],[],[],[],[0,r173,r174,r175,r176,r177,r178],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[r259,r260,r261,r262,r263,r264,r265,r266,r267,r268,r269,r270,r271,r272,r273,r274]),(⟨0,0,1⟩,[r275,r276,r277,r278,r279,r280,r281,r282,r283,r284,r285,r286,r287,r288,r289]),(⟨0,0,2⟩,[r290,r291,r292,r293,r294,r295,r296,r297,r298,r299,r300,r301,r302,r303]),(⟨0,0,3⟩,[r304,r305,r306,r307,r308,r309,r310,r311,r312,r313,r314,r315,r316]),(⟨0,0,4⟩,[r317,r318,r319,r320,r321,r322,r323,r324,r325,r326,r327,r328]),(⟨0,0,5⟩,[r16,r329,r330,r331,r332,r333,r334,r335,r336,r337,r338]),(⟨0,0,6⟩,[0,r188,r339,r340,r341,r342,r343,r344,r345,r346]),(⟨0,1,0⟩,[r275,r276,r277,r278,r279,r280,r281,r282,r283,r284,r285,r286,r287,r288,r289]),(⟨0,1,1⟩,[0,r347,r348,r349,r350,r351,r352,r353,r354,r355,r356,r357,r358,r359]),(⟨0,1,2⟩,[r360,r361,r362,r363,r364,r365,r366,r367,r368,r369,r370,r371,r372]),(⟨0,1,3⟩,[0,r373,r374,r375,r376,r377,r378,r379,r380,r381,r382,r383]),(⟨0,1,4⟩,[0,r70,r384,r385,r386,r387,r388,r389,r390,r391,r392]),(⟨0,2,0⟩,[r290,r291,r292,r293,r294,r295,r296,r297,r298,r299,r300,r301,r302,r303]),(⟨0,2,1⟩,[r360,r361,r362,r363,r364,r365,r366,r367,r368,r369,r370,r371,r372]),(⟨0,2,2⟩,[r58,r393,r394,r395,r396,r397,r398,r399,r400,r401,r402,r403]),(⟨0,2,3⟩,[r16,r329,r330,r331,r332,r333,r334,r335,r336,r337,r338]),(⟨0,2,4⟩,[r70,r404,r405,r406,r407,r408,r409,r410,r411,r412]),(⟨0,2,5⟩,[0,r347,r197,r413,r414,r415,r416,r417,r418]),(⟨0,2,6⟩,[r419,r420,r421,r422,r423,r424,r425,r426]),(⟨0,2,7⟩,[0,r427,r428,r429,r430,r431,r432]),(⟨0,3,0⟩,[r304,r305,r306,r307,r308,r309,r310,r311,r312,r313,r314,r315,r316]),(⟨0,3,1⟩,[0,r373,r374,r375,r376,r377,r378,r379,r380,r381,r382,r383]),(⟨0,3,2⟩,[r16,r329,r330,r331,r332,r333,r334,r335,r336,r337,r338]),(⟨0,3,3⟩,[0,r81,r82,r83,r84,r85,r86,r87,r88,r89]),(⟨0,3,4⟩,[0,r347,r197,r413,r414,r415,r416,r417,r418]),(⟨0,3,5⟩,[0,r165,r433,r434,r435,r436,r437,-8192]),(⟨0,4,0⟩,[r317,r318,r319,r320,r321,r322,r323,r324,r325,r326,r327,r328]),(⟨0,4,1⟩,[0,r70,r384,r385,r386,r387,r388,r389,r390,r391,r392]),(⟨0,4,2⟩,[r70,r404,r405,r406,r407,r408,r409,r410,r411,r412]),(⟨0,4,3⟩,[0,r347,r197,r413,r414,r415,r416,r417,r418]),(⟨0,4,4⟩,[r165,r166,r167,r168,r169,r170,r171,r172]),(⟨0,4,5⟩,[0,r427,r428,r429,r430,r431,r432]),(⟨0,5,0⟩,[r16,r329,r330,r331,r332,r333,r334,r335,r336,r337,r338]),(⟨0,5,2⟩,[0,r347,r197,r413,r414,r415,r416,r417,r418]),(⟨0,5,3⟩,[0,r165,r433,r434,r435,r436,r437,-8192]),(⟨0,5,4⟩,[0,r427,r428,r429,r430,r431,r432]),(⟨0,6,0⟩,[0,r188,r339,r340,r341,r342,r343,r344,r345,r346]),(⟨0,6,2⟩,[r419,r420,r421,r422,r423,r424,r425,r426]),(⟨0,7,2⟩,[0,r427,r428,r429,r430,r431,r432]),(⟨1,0,0⟩,[r275,r276,r277,r278,r279,r280,r281,r282,r283,r284,r285,r286,r287,r288,r289]),(⟨1,0,1⟩,[0,r347,r348,r349,r350,r351,r352,r353,r354,r355,r356,r357,r358,r359]),(⟨1,0,2⟩,[r360,r361,r362,r363,r364,r365,r366,r367,r368,r369,r370,r371,r372]),(⟨1,0,3⟩,[0,r373,r374,r375,r376,r377,r378,r379,r380,r381,r382,r383]),(⟨1,0,4⟩,[0,r70,r384,r385,r386,r387,r388,r389,r390,r391,r392]),(⟨1,1,0⟩,[0,r347,r348,r349,r350,r351,r352,r353,r354,r355,r356,r357,r358,r359]),(⟨1,1,1⟩,[r0,r438,r439,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449]),(⟨1,1,2⟩,[r16,r450,r451,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨1,1,3⟩,[r461,r462,r463,r464,r465,r466,r467,r468,r469,r470,r471]),(⟨1,1,4⟩,[r419,r472,r473,r474,r475,r476,r477,r478,r479,r480]),(⟨1,2,0⟩,[r360,r361,r362,r363,r364,r365,r366,r367,r368,r369,r370,r371,r372]),(⟨1,2,1⟩,[r16,r450,r451,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨1,2,2⟩,[0,0,r179,r481,r482,r483,r484,r485,r486,r487,-196608]),(⟨1,2,4⟩,[0,r347,r197,r413,r414,r415,r416,r417,r418]),(⟨1,2,5⟩,[0,r165,r433,r434,r435,r436,r437,-8192]),(⟨1,3,0⟩,[0,r373,r374,r375,r376,r377,r378,r379,r380,r381,r382,r383]),(⟨1,3,1⟩,[r461,r462,r463,r464,r465,r466,r467,r468,r469,r470,r471]),(⟨1,3,4⟩,[0,r165,r433,r434,r435,r436,r437,-8192]),(⟨1,3,5⟩,[r127,r17,r488,r489,r490,r491,8192]),(⟨1,4,0⟩,[0,r70,r384,r385,r386,r387,r388,r389,r390,r391,r392]),(⟨1,4,1⟩,[r419,r472,r473,r474,r475,r476,r477,r478,r479,r480]),(⟨1,4,2⟩,[0,r347,r197,r413,r414,r415,r416,r417,r418]),(⟨1,4,3⟩,[0,r165,r433,r434,r435,r436,r437,-8192]),(⟨1,5,2⟩,[0,r165,r433,r434,r435,r436,r437,-8192]),(⟨1,5,3⟩,[r127,r17,r488,r489,r490,r491,8192]),(⟨2,0,0⟩,[r290,r291,r292,r293,r294,r295,r296,r297,r298,r299,r300,r301,r302,r303]),(⟨2,0,1⟩,[r360,r361,r362,r363,r364,r365,r366,r367,r368,r369,r370,r371,r372]),(⟨2,0,2⟩,[r58,r393,r394,r395,r396,r397,r398,r399,r400,r401,r402,r403]),(⟨2,0,3⟩,[r16,r329,r330,r331,r332,r333,r334,r335,r336,r337,r338]),(⟨2,0,4⟩,[r70,r404,r405,r406,r407,r408,r409,r410,r411,r412]),(⟨2,0,5⟩,[0,r347,r197,r413,r414,r415,r416,r417,r418]),(⟨2,0,6⟩,[r419,r420,r421,r422,r423,r424,r425,r426]),(⟨2,0,7⟩,[0,r427,r428,r429,r430,r431,r432]),(⟨2,1,0⟩,[r360,r361,r362,r363,r364,r365,r366,r367,r368,r369,r370,r371,r372]),(⟨2,1,1⟩,[r16,r450,r451,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨2,1,2⟩,[0,0,r179,r481,r482,r483,r484,r485,r486,r487,-196608]),(⟨2,1,4⟩,[0,r347,r197,r413,r414,r415,r416,r417,r418]),(⟨2,1,5⟩,[0,r165,r433,r434,r435,r436,r437,-8192]),(⟨2,2,0⟩,[r58,r393,r394,r395,r396,r397,r398,r399,r400,r401,r402,r403]),(⟨2,2,1⟩,[0,0,r179,r481,r482,r483,r484,r485,r486,r487,-196608]),(⟨2,2,4⟩,[r165,r166,r167,r168,r169,r170,r171,r172]),(⟨2,3,0⟩,[r16,r329,r330,r331,r332,r333,r334,r335,r336,r337,r338]),(⟨2,3,4⟩,[0,r427,r428,r429,r430,r431,r432]),(⟨2,4,0⟩,[r70,r404,r405,r406,r407,r408,r409,r410,r411,r412]),(⟨2,4,1⟩,[0,r347,r197,r413,r414,r415,r416,r417,r418]),(⟨2,4,2⟩,[r165,r166,r167,r168,r169,r170,r171,r172]),(⟨2,4,3⟩,[0,r427,r428,r429,r430,r431,r432]),(⟨2,5,0⟩,[0,r347,r197,r413,r414,r415,r416,r417,r418]),(⟨2,5,1⟩,[0,r165,r433,r434,r435,r436,r437,-8192]),(⟨2,6,0⟩,[r419,r420,r421,r422,r423,r424,r425,r426]),(⟨2,7,0⟩,[0,r427,r428,r429,r430,r431,r432]),(⟨3,0,0⟩,[r304,r305,r306,r307,r308,r309,r310,r311,r312,r313,r314,r315,r316]),(⟨3,0,1⟩,[0,r373,r374,r375,r376,r377,r378,r379,r380,r381,r382,r383]),(⟨3,0,2⟩,[r16,r329,r330,r331,r332,r333,r334,r335,r336,r337,r338]),(⟨3,0,3⟩,[0,r81,r82,r83,r84,r85,r86,r87,r88,r89]),(⟨3,0,4⟩,[0,r347,r197,r413,r414,r415,r416,r417,r418]),(⟨3,0,5⟩,[0,r165,r433,r434,r435,r436,r437,-8192]),(⟨3,1,0⟩,[0,r373,r374,r375,r376,r377,r378,r379,r380,r381,r382,r383]),(⟨3,1,1⟩,[r461,r462,r463,r464,r465,r466,r467,r468,r469,r470,r471]),(⟨3,1,4⟩,[0,r165,r433,r434,r435,r436,r437,-8192]),(⟨3,1,5⟩,[r127,r17,r488,r489,r490,r491,8192]),(⟨3,2,0⟩,[r16,r329,r330,r331,r332,r333,r334,r335,r336,r337,r338]),(⟨3,2,4⟩,[0,r427,r428,r429,r430,r431,r432]),(⟨3,3,0⟩,[0,r81,r82,r83,r84,r85,r86,r87,r88,r89]),(⟨3,4,0⟩,[0,r347,r197,r413,r414,r415,r416,r417,r418]),(⟨3,4,1⟩,[0,r165,r433,r434,r435,r436,r437,-8192]),(⟨3,4,2⟩,[0,r427,r428,r429,r430,r431,r432]),(⟨3,5,0⟩,[0,r165,r433,r434,r435,r436,r437,-8192]),(⟨3,5,1⟩,[r127,r17,r488,r489,r490,r491,8192]),(⟨4,0,0⟩,[r317,r318,r319,r320,r321,r322,r323,r324,r325,r326,r327,r328]),(⟨4,0,1⟩,[0,r70,r384,r385,r386,r387,r388,r389,r390,r391,r392]),(⟨4,0,2⟩,[r70,r404,r405,r406,r407,r408,r409,r410,r411,r412]),(⟨4,0,3⟩,[0,r347,r197,r413,r414,r415,r416,r417,r418]),(⟨4,0,4⟩,[r165,r166,r167,r168,r169,r170,r171,r172]),(⟨4,0,5⟩,[0,r427,r428,r429,r430,r431,r432]),(⟨4,1,0⟩,[0,r70,r384,r385,r386,r387,r388,r389,r390,r391,r392]),(⟨4,1,1⟩,[r419,r472,r473,r474,r475,r476,r477,r478,r479,r480]),(⟨4,1,2⟩,[0,r347,r197,r413,r414,r415,r416,r417,r418]),(⟨4,1,3⟩,[0,r165,r433,r434,r435,r436,r437,-8192]),(⟨4,2,0⟩,[r70,r404,r405,r406,r407,r408,r409,r410,r411,r412]),(⟨4,2,1⟩,[0,r347,r197,r413,r414,r415,r416,r417,r418]),(⟨4,2,2⟩,[r165,r166,r167,r168,r169,r170,r171,r172]),(⟨4,2,3⟩,[0,r427,r428,r429,r430,r431,r432]),(⟨4,3,0⟩,[0,r347,r197,r413,r414,r415,r416,r417,r418]),(⟨4,3,1⟩,[0,r165,r433,r434,r435,r436,r437,-8192]),(⟨4,3,2⟩,[0,r427,r428,r429,r430,r431,r432]),(⟨4,4,0⟩,[r165,r166,r167,r168,r169,r170,r171,r172]),(⟨4,5,0⟩,[0,r427,r428,r429,r430,r431,r432]),(⟨5,0,0⟩,[r16,r329,r330,r331,r332,r333,r334,r335,r336,r337,r338]),(⟨5,0,2⟩,[0,r347,r197,r413,r414,r415,r416,r417,r418]),(⟨5,0,3⟩,[0,r165,r433,r434,r435,r436,r437,-8192]),(⟨5,0,4⟩,[0,r427,r428,r429,r430,r431,r432]),(⟨5,1,2⟩,[0,r165,r433,r434,r435,r436,r437,-8192]),(⟨5,1,3⟩,[r127,r17,r488,r489,r490,r491,8192]),(⟨5,2,0⟩,[0,r347,r197,r413,r414,r415,r416,r417,r418]),(⟨5,2,1⟩,[0,r165,r433,r434,r435,r436,r437,-8192]),(⟨5,3,0⟩,[0,r165,r433,r434,r435,r436,r437,-8192]),(⟨5,3,1⟩,[r127,r17,r488,r489,r490,r491,8192]),(⟨5,4,0⟩,[0,r427,r428,r429,r430,r431,r432]),(⟨6,0,0⟩,[0,r188,r339,r340,r341,r342,r343,r344,r345,r346]),(⟨6,0,2⟩,[r419,r420,r421,r422,r423,r424,r425,r426]),(⟨6,2,0⟩,[r419,r420,r421,r422,r423,r424,r425,r426]),(⟨7,0,2⟩,[0,r427,r428,r429,r430,r431,r432]),(⟨7,2,0⟩,[0,r427,r428,r429,r430,r431,r432])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[-384,8384,-78592,440960,-1705088,4764160,-9624448,13537664,-12357632,6218048,-613248]),(⟨0,0,1⟩,[-64,2496,-31616,211840,-912896,2736384,-5720192,8092800,-7196096,3341632]),(⟨0,0,2⟩,[448,-8320,59264,-234624,617216,-1004928,849024,-247168,-260288]),(⟨0,0,3⟩,[128,-3712,33920,-163456,531840,-1113984,1334656,-881536]),(⟨0,1,0⟩,[-64,2496,-31616,211840,-912896,2736384,-5720192,8092800,-7196096,3341632]),(⟨0,1,1⟩,[0,0,2048,-28672,116736,-122880,-206848,708608,-731136]),(⟨0,2,0⟩,[448,-8320,59264,-234624,617216,-1004928,849024,-247168,-260288]),(⟨0,2,4⟩,[-256,3072,-7680,-9216,30464]),(⟨0,3,0⟩,[128,-3712,33920,-163456,531840,-1113984,1334656,-881536]),(⟨0,4,2⟩,[-256,3072,-7680,-9216,30464]),(⟨1,0,0⟩,[-64,2496,-31616,211840,-912896,2736384,-5720192,8092800,-7196096,3341632]),(⟨1,0,1⟩,[0,0,2048,-28672,116736,-122880,-206848,708608,-731136]),(⟨1,1,0⟩,[0,0,2048,-28672,116736,-122880,-206848,708608,-731136]),(⟨2,0,0⟩,[448,-8320,59264,-234624,617216,-1004928,849024,-247168,-260288]),(⟨2,0,4⟩,[-256,3072,-7680,-9216,30464]),(⟨2,4,0⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[128,-3712,33920,-163456,531840,-1113984,1334656,-881536]),(⟨4,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨4,2,0⟩,[-256,3072,-7680,-9216,30464])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[16,-208,1008,-2480,2688,-512]),(⟨0,0,1⟩,[0,-96,704,-1760,1664]),(⟨0,0,2⟩,[-16,176,-304,-112]),(⟨0,0,3⟩,[0,128,-384]),(⟨0,1,0⟩,[0,-96,704,-1760,1664]),(⟨0,1,1⟩,[0,-32,320,-544]),(⟨0,2,0⟩,[-16,176,-304,-112]),(⟨0,3,0⟩,[0,128,-384]),(⟨1,0,0⟩,[0,-96,704,-1760,1664]),(⟨1,0,1⟩,[0,-32,320,-544]),(⟨1,1,0⟩,[0,-32,320,-544]),(⟨1,1,1⟩,[32,-320,544]),(⟨2,0,0⟩,[-16,176,-304,-112]),(⟨3,0,0⟩,[0,128,-384])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 8 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r492) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 10 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r493) sourceRight))).isZero := by decide +kernel

noncomputable def partial19 : Poly := []

theorem partial_sound19 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 19)
      sourceRight).eval u v t=partial19.eval u v t := by rfl

noncomputable def chunk16 : Poly := [(⟨3,0,0⟩,[128,-3712,33920,-163456,531840,-1113984,1334656,-881536]),(⟨4,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨4,2,0⟩,[-256,3072,-7680,-9216,30464])]

noncomputable def partial16 : Poly := [(⟨3,0,0⟩,[2048,-86016,1443840,-13729792,86249472,-387375104,1287606272,-3190308864,5804648448,-7465226240,6344124416,-3052912640,451346432]),(⟨3,0,1⟩,[0,-12288,446464,-6094848,46317568,-232005632,825483264,-2120400896,3869818880,-4823265280,3772370944,-1466875904]),(⟨3,0,2⟩,[-2048,81920,-1234944,9699328,-47173632,157319168,-360787968,528089088,-436119552,118505472,98732032]),(⟨3,0,3⟩,[0,16384,-524288,5767168,-33947648,130842624,-346816512,598605824,-625344512,338509824]),(⟨3,1,0⟩,[0,-12288,446464,-6094848,46317568,-232005632,825483264,-2120400896,3869818880,-4823265280,3772370944,-1466875904]),(⟨3,1,1⟩,[0,-4096,159744,-2342912,18104320,-87777280,294756352,-688504832,1061306368,-1008144384,479555584]),(⟨3,2,0⟩,[-2048,81920,-1234944,9699328,-47173632,157319168,-360787968,528089088,-436119552,118505472,98732032]),(⟨3,3,0⟩,[0,16384,-524288,5767168,-33947648,130842624,-346816512,598605824,-625344512,338509824]),(⟨4,0,0⟩,[0,-12288,446464,-6094848,46317568,-232005632,825483264,-2120400896,3869818880,-4823265280,3772370944,-1466875904]),(⟨4,0,1⟩,[0,-4096,159744,-2342912,18104320,-87777280,294756352,-688504832,1061306368,-1008144384,479555584]),(⟨4,0,2⟩,[-4096,102400,-1019904,5181440,-13643776,11808768,31346688,-96391168,86605824,-15597568]),(⟨4,0,3⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨4,0,4⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨4,0,5⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨4,1,0⟩,[0,-4096,159744,-2342912,18104320,-87777280,294756352,-688504832,1061306368,-1008144384,479555584]),(⟨4,1,1⟩,[4096,-159744,2342912,-18104320,87777280,-294756352,688504832,-1061306368,1008144384,-479555584]),(⟨4,1,2⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨4,1,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨4,2,0⟩,[-4096,102400,-1019904,5181440,-13643776,11808768,31346688,-96391168,86605824,-15597568]),(⟨4,2,1⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨4,2,2⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨4,2,3⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨4,3,0⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨4,3,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨4,3,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨4,4,0⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨4,5,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨5,0,0⟩,[-2048,81920,-1234944,9699328,-47173632,157319168,-360787968,528089088,-436119552,118505472,98732032]),(⟨5,0,2⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨5,0,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨5,1,2⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨5,1,3⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨5,2,0⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨5,2,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨5,3,0⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨5,3,1⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨6,0,0⟩,[0,16384,-524288,5767168,-33947648,130842624,-346816512,598605824,-625344512,338509824]),(⟨6,0,2⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨6,2,0⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨7,0,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨7,2,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176])]


theorem partial_checked16 :
    (Poly.add (Poly.add (Poly.mul chunk16 sourceRight) partial19)
      (Poly.scale (K.ofRat (-1)) partial16)).isZero := by decide +kernel

theorem partial_sound16 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 16)
      sourceRight).eval u v t=partial16.eval u v t := by
  change (Poly.mul (chunk16++(sourceLeft.drop 19))
    sourceRight).eval u v t=partial16.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound19 partial_checked16 u v t


noncomputable def chunk12 : Poly := [(⟨1,1,0⟩,[0,0,2048,-28672,116736,-122880,-206848,708608,-731136]),(⟨2,0,0⟩,[448,-8320,59264,-234624,617216,-1004928,849024,-247168,-260288]),(⟨2,0,4⟩,[-256,3072,-7680,-9216,30464]),(⟨2,4,0⟩,[-256,3072,-7680,-9216,30464])]

noncomputable def partial12 : Poly := [(⟨1,1,0⟩,[0,0,32768,-884736,9895936,-60227584,216530944,-437125120,265617408,989265920,-2987425792,3823861760,-2328100864,374341632]),(⟨1,1,1⟩,[0,0,0,-196608,4194304,-34996224,147849216,-319815680,196870144,728629248,-2106064896,2465923072,-1216610304]),(⟨1,1,2⟩,[0,0,-32768,819200,-7536640,30998528,-50593792,-23461888,213057536,-320929792,142901248,81887232]),(⟨1,1,3⟩,[0,0,0,262144,-4456448,25952256,-60555264,20709376,170131456,-365690880,280756224]),(⟨1,2,0⟩,[0,0,0,-196608,4194304,-34996224,147849216,-319815680,196870144,728629248,-2106064896,2465923072,-1216610304]),(⟨1,2,1⟩,[0,0,0,-65536,1572864,-14024704,56885248,-96206848,-22020096,362676224,-619446272,397737984]),(⟨1,3,0⟩,[0,0,-32768,819200,-7536640,30998528,-50593792,-23461888,213057536,-320929792,142901248,81887232]),(⟨1,4,0⟩,[0,0,0,262144,-4456448,25952256,-60555264,20709376,170131456,-365690880,280756224]),(⟨2,0,0⟩,[7168,-226304,3130368,-25578496,140253184,-550529024,1590192128,-3385227264,5174488064,-5317846016,3147305984,-453573632,-573104128,133267456]),(⟨2,0,1⟩,[0,-43008,1114112,-12335104,79634432,-342577152,1042546688,-2265690112,3417161728,-3315501056,1664548864,46819328,-433119232]),(⟨2,0,2⟩,[-7168,211968,-2548736,16663552,-68253696,189396992,-351807488,389752832,-184888320,-65762304,106810368,29152256]),(⟨2,0,3⟩,[0,57344,-1236992,10780672,-52789248,169099264,-365641728,494567424,-357662720,61595648,99950592]),(⟨2,0,4⟩,[-4096,102400,-1019904,5181440,-13643776,11808768,31346688,-96391168,86605824,-15597568]),(⟨2,0,5⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨2,0,6⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨2,0,7⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨2,1,0⟩,[0,-43008,1114112,-12531712,83828736,-377573376,1190395904,-2585505792,3614031872,-2586871808,-441516032,2512742400,-1649729536]),(⟨2,1,1⟩,[0,-14336,409600,-4868096,32571392,-141094912,414187520,-780718080,804257792,-169957376,-568279040,539334656]),(⟨2,1,4⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨2,1,5⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨2,2,0⟩,[-7168,211968,-2548736,16598016,-66680832,175372288,-294922240,293545984,-206908416,296913920,-512635904,426890240]),(⟨2,2,1⟩,[0,0,65536,-1572864,14024704,-56885248,96206848,22020096,-362676224,619446272,-397737984]),(⟨2,2,4⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨2,3,0⟩,[0,57344,-1236992,10780672,-52789248,169099264,-365641728,494567424,-357662720,61595648,99950592]),(⟨2,3,4⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨2,4,0⟩,[-4096,102400,-1019904,5181440,-13643776,11808768,31346688,-96391168,86605824,-15597568]),(⟨2,4,1⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨2,4,2⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨2,4,3⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨2,5,0⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨2,5,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨2,6,0⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨2,7,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨3,0,0⟩,[2048,-129024,2557952,-26064896,165883904,-729952256,2330152960,-5455998976,9221810176,-10780727296,8008673280,-3006093312,18227200]),(⟨3,0,1⟩,[0,-26624,856064,-10897408,77316096,-359075840,1182785536,-2804912128,4696096768,-5355898880,3823538176,-1325279232]),(⟨3,0,2⟩,[-2048,81920,-1234944,9699328,-47173632,157319168,-360787968,528089088,-436119552,118505472,98732032]),(⟨3,0,3⟩,[0,16384,-524288,5767168,-33947648,130842624,-346816512,598605824,-625344512,338509824]),(⟨3,0,4⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨3,0,5⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,1,0⟩,[0,-26624,823296,-10078208,69779456,-328077312,1132191744,-2828374016,4909154304,-5676828672,3966439424,-1243392000]),(⟨3,1,1⟩,[14336,-413696,4962304,-33341440,145174528,-445079552,979267584,-1514782720,1593939968,-1059311616,337958912]),(⟨3,1,4⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,1,5⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨3,2,0⟩,[-2048,81920,-1234944,9699328,-47173632,157319168,-360787968,528089088,-436119552,118505472,98732032]),(⟨3,3,0⟩,[0,16384,-524288,5767168,-33947648,130842624,-346816512,598605824,-625344512,338509824]),(⟨3,4,0⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨3,4,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,5,0⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,5,1⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨4,0,0⟩,[-7168,199680,-2102272,10568704,-21936128,-42608640,473675776,-1730648064,3684930560,-4889027584,3879181312,-1437723648]),(⟨4,0,1⟩,[0,-4096,159744,-2342912,18104320,-87777280,294756352,-688504832,1061306368,-1008144384,479555584]),(⟨4,0,2⟩,[-4096,102400,-1019904,5181440,-13643776,11808768,31346688,-96391168,86605824,-15597568]),(⟨4,0,3⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨4,0,4⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨4,0,5⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨4,1,0⟩,[0,-4096,159744,-2080768,13647872,-61825024,234201088,-667795456,1231437824,-1373835264,760311808]),(⟨4,1,1⟩,[4096,-159744,2342912,-18104320,87777280,-294756352,688504832,-1061306368,1008144384,-479555584]),(⟨4,1,2⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨4,1,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨4,2,0⟩,[-4096,102400,-1019904,5181440,-13643776,11808768,31346688,-96391168,86605824,-15597568]),(⟨4,2,1⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨4,2,2⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨4,2,3⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨4,3,0⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨4,3,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨4,3,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨4,4,0⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨4,5,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨5,0,0⟩,[-2048,139264,-2471936,20480000,-99962880,326418432,-726429696,1022656512,-793782272,180101120,198682624]),(⟨5,0,2⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨5,0,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨5,0,4⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨5,1,2⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨5,1,3⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨5,2,0⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨5,2,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨5,3,0⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨5,3,1⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨5,4,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨6,0,0⟩,[0,16384,-524288,5767168,-33947648,130842624,-346816512,598605824,-625344512,338509824]),(⟨6,0,2⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨6,2,0⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨7,0,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨7,2,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176])]


theorem partial_checked12 :
    (Poly.add (Poly.add (Poly.mul chunk12 sourceRight) partial16)
      (Poly.scale (K.ofRat (-1)) partial12)).isZero := by decide +kernel

theorem partial_sound12 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 12)
      sourceRight).eval u v t=partial12.eval u v t := by
  change (Poly.mul (chunk12++(sourceLeft.drop 16))
    sourceRight).eval u v t=partial12.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound16 partial_checked12 u v t


noncomputable def chunk8 : Poly := [(⟨0,3,0⟩,[128,-3712,33920,-163456,531840,-1113984,1334656,-881536]),(⟨0,4,2⟩,[-256,3072,-7680,-9216,30464]),(⟨1,0,0⟩,[-64,2496,-31616,211840,-912896,2736384,-5720192,8092800,-7196096,3341632]),(⟨1,0,1⟩,[0,0,2048,-28672,116736,-122880,-206848,708608,-731136])]

noncomputable def partial8 : Poly := [(⟨0,3,0⟩,[2048,-86016,1443840,-13729792,86249472,-387375104,1287606272,-3190308864,5804648448,-7465226240,6344124416,-3052912640,451346432]),(⟨0,3,1⟩,[0,-12288,446464,-6094848,46317568,-232005632,825483264,-2120400896,3869818880,-4823265280,3772370944,-1466875904]),(⟨0,3,2⟩,[-2048,81920,-1234944,9699328,-47173632,157319168,-360787968,528089088,-436119552,118505472,98732032]),(⟨0,3,3⟩,[0,16384,-524288,5767168,-33947648,130842624,-346816512,598605824,-625344512,338509824]),(⟨0,4,0⟩,[0,-12288,446464,-6094848,46317568,-232005632,825483264,-2120400896,3869818880,-4823265280,3772370944,-1466875904]),(⟨0,4,1⟩,[0,-4096,159744,-2342912,18104320,-87777280,294756352,-688504832,1061306368,-1008144384,479555584]),(⟨0,4,2⟩,[-4096,102400,-1019904,5181440,-13643776,11808768,31346688,-96391168,86605824,-15597568]),(⟨0,4,3⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨0,4,4⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨0,4,5⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨0,5,0⟩,[-2048,81920,-1234944,9699328,-47173632,157319168,-360787968,528089088,-436119552,118505472,98732032]),(⟨0,5,2⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨0,5,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨0,6,0⟩,[0,16384,-524288,5767168,-33947648,130842624,-346816512,598605824,-625344512,338509824]),(⟨0,6,2⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨0,7,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨1,0,0⟩,[-1024,53248,-1089536,12640256,-96900096,532348928,-2192515072,6927155200,-16912952320,31716675584,-44795772928,45896867840,-31773867008,12666707968,-1710915584]),(⟨1,0,1⟩,[0,6144,-251904,4020224,-37197824,236343296,-1114288128,3997626368,-10873401344,21998303232,-32136001536,32307918848,-20183676928,5934817280]),(⟨1,0,2⟩,[1024,-51200,964608,-9902080,65416192,-300306432,974770176,-2185670656,3168803840,-2410899456,-236718080,2256029696,-1590873088]),(⟨1,0,3⟩,[0,-8192,311296,-4186112,31719424,-167198720,650215424,-1806417920,3445489664,-4349665280,3333931008,-1201299456]),(⟨1,0,4⟩,[0,0,0,262144,-4456448,25952256,-60555264,20709376,170131456,-365690880,280756224]),(⟨1,1,0⟩,[0,6144,-251904,4020224,-37197824,236343296,-1114288128,3997626368,-10873401344,21998303232,-32136001536,32307918848,-20183676928,5934817280]),(⟨1,1,1⟩,[0,2048,-100352,1452032,-9865216,44208128,-199233536,915673088,-3184283648,7389014016,-11024295936,9915844608,-4251068416]),(⟨1,1,2⟩,[0,0,-32768,753664,-5963776,16973824,6291456,-119668736,191037440,41746432,-476545024,479625216]),(⟨1,1,3⟩,[0,0,0,262144,-4456448,25952256,-60555264,20709376,170131456,-365690880,280756224]),(⟨1,2,0⟩,[1024,-51200,964608,-9902080,65416192,-300306432,974770176,-2185670656,3168803840,-2410899456,-236718080,2256029696,-1590873088]),(⟨1,2,1⟩,[0,0,-32768,753664,-5963776,16973824,6291456,-119668736,191037440,41746432,-476545024,479625216]),(⟨1,3,0⟩,[0,-20480,757760,-10280960,78036992,-399204352,1475698688,-3926818816,7315308544,-9172930560,7106301952,-2668175360]),(⟨1,3,1⟩,[0,-4096,159744,-2080768,13647872,-61825024,234201088,-667795456,1231437824,-1373835264,760311808]),(⟨1,4,0⟩,[0,-4096,159744,-2080768,13647872,-61825024,234201088,-667795456,1231437824,-1373835264,760311808]),(⟨1,4,1⟩,[4096,-159744,2342912,-18104320,87777280,-294756352,688504832,-1061306368,1008144384,-479555584]),(⟨1,4,2⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨1,4,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨1,5,2⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨1,5,3⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨2,0,0⟩,[7168,-220160,2845696,-20673536,93159424,-253958144,259373056,1049524224,-5964530688,15691191296,-26001269760,28030483456,-18428680192,5693743104]),(⟨2,0,1⟩,[0,-40960,1013760,-10686464,65574912,-263372800,695463936,-1030201344,36007936,3344883712,-7253682176,7496740864,-3467577344]),(⟨2,0,2⟩,[-7168,211968,-2548736,16598016,-66680832,175372288,-294922240,293545984,-206908416,296913920,-512635904,426890240]),(⟨2,0,3⟩,[0,57344,-1236992,10780672,-52789248,169099264,-365641728,494567424,-357662720,61595648,99950592]),(⟨2,0,4⟩,[-4096,102400,-1019904,5181440,-13643776,11808768,31346688,-96391168,86605824,-15597568]),(⟨2,0,5⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨2,0,6⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨2,0,7⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨2,1,0⟩,[0,-40960,1013760,-10686464,65574912,-263372800,695463936,-1030201344,36007936,3344883712,-7253682176,7496740864,-3467577344]),(⟨2,1,1⟩,[-2048,86016,-1435648,13320192,-80056320,339812352,-1084231680,2701099008,-5149517824,7004884992,-6171723776,2754920448]),(⟨2,1,2⟩,[0,0,65536,-1572864,14024704,-56885248,96206848,22020096,-362676224,619446272,-397737984]),(⟨2,1,4⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨2,1,5⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨2,2,0⟩,[-7168,211968,-2548736,16598016,-66680832,175372288,-294922240,293545984,-206908416,296913920,-512635904,426890240]),(⟨2,2,1⟩,[0,0,65536,-1572864,14024704,-56885248,96206848,22020096,-362676224,619446272,-397737984]),(⟨2,2,4⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨2,3,0⟩,[-2048,139264,-2471936,20480000,-99962880,326418432,-726429696,1022656512,-793782272,180101120,198682624]),(⟨2,3,4⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨2,4,0⟩,[-4096,102400,-1019904,5181440,-13643776,11808768,31346688,-96391168,86605824,-15597568]),(⟨2,4,1⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨2,4,2⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨2,4,3⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨2,5,0⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨2,5,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨2,6,0⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨2,7,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨3,0,0⟩,[3072,-180224,3522560,-35770368,227105792,-995262464,3157073920,-7321853952,12193743872,-13920256000,9878020096,-3215986688,-356035584]),(⟨3,0,1⟩,[0,-26624,823296,-10078208,69779456,-328077312,1132191744,-2828374016,4909154304,-5676828672,3966439424,-1243392000]),(⟨3,0,2⟩,[-2048,81920,-1234944,9699328,-47173632,157319168,-360787968,528089088,-436119552,118505472,98732032]),(⟨3,0,3⟩,[0,16384,-524288,5767168,-33947648,130842624,-346816512,598605824,-625344512,338509824]),(⟨3,0,4⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨3,0,5⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,1,0⟩,[0,-26624,823296,-10078208,69779456,-328077312,1132191744,-2828374016,4909154304,-5676828672,3966439424,-1243392000]),(⟨3,1,1⟩,[14336,-413696,4962304,-33341440,145174528,-445079552,979267584,-1514782720,1593939968,-1059311616,337958912]),(⟨3,1,4⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,1,5⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨3,2,0⟩,[-2048,81920,-1234944,9699328,-47173632,157319168,-360787968,528089088,-436119552,118505472,98732032]),(⟨3,3,0⟩,[0,32768,-1048576,11534336,-67895296,261685248,-693633024,1197211648,-1250689024,677019648]),(⟨3,4,0⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨3,4,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,4,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨3,5,0⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,5,1⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨4,0,0⟩,[-7168,191488,-1758208,5563392,17319936,-240805888,1174484992,-3513604096,6917362688,-8917763072,7070211072,-2720910336]),(⟨4,0,1⟩,[0,-4096,159744,-2080768,13647872,-61825024,234201088,-667795456,1231437824,-1373835264,760311808]),(⟨4,0,2⟩,[-4096,102400,-1019904,5181440,-13643776,11808768,31346688,-96391168,86605824,-15597568]),(⟨4,0,3⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨4,0,4⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨4,0,5⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨4,1,0⟩,[0,-4096,159744,-2080768,13647872,-61825024,234201088,-667795456,1231437824,-1373835264,760311808]),(⟨4,1,1⟩,[4096,-159744,2342912,-18104320,87777280,-294756352,688504832,-1061306368,1008144384,-479555584]),(⟨4,1,2⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨4,1,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨4,2,0⟩,[-4096,102400,-1019904,5181440,-13643776,11808768,31346688,-96391168,86605824,-15597568]),(⟨4,2,1⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨4,2,2⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨4,2,3⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨4,3,0⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨4,3,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨4,3,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨4,4,0⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨4,5,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨5,0,0⟩,[-2048,139264,-2471936,20480000,-99962880,326418432,-726429696,1022656512,-793782272,180101120,198682624]),(⟨5,0,2⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨5,0,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨5,0,4⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨5,1,2⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨5,1,3⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨5,2,0⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨5,2,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨5,3,0⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨5,3,1⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨5,4,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨6,0,0⟩,[0,16384,-524288,5767168,-33947648,130842624,-346816512,598605824,-625344512,338509824]),(⟨6,0,2⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨6,2,0⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨7,0,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨7,2,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176])]


theorem partial_checked8 :
    (Poly.add (Poly.add (Poly.mul chunk8 sourceRight) partial12)
      (Poly.scale (K.ofRat (-1)) partial8)).isZero := by decide +kernel

theorem partial_sound8 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 8)
      sourceRight).eval u v t=partial8.eval u v t := by
  change (Poly.mul (chunk8++(sourceLeft.drop 12))
    sourceRight).eval u v t=partial8.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound12 partial_checked8 u v t


noncomputable def chunk4 : Poly := [(⟨0,1,0⟩,[-64,2496,-31616,211840,-912896,2736384,-5720192,8092800,-7196096,3341632]),(⟨0,1,1⟩,[0,0,2048,-28672,116736,-122880,-206848,708608,-731136]),(⟨0,2,0⟩,[448,-8320,59264,-234624,617216,-1004928,849024,-247168,-260288]),(⟨0,2,4⟩,[-256,3072,-7680,-9216,30464])]

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[-1024,53248,-1089536,12640256,-96900096,532348928,-2192515072,6927155200,-16912952320,31716675584,-44795772928,45896867840,-31773867008,12666707968,-1710915584]),(⟨0,1,1⟩,[0,6144,-251904,4020224,-37197824,236343296,-1114288128,3997626368,-10873401344,21998303232,-32136001536,32307918848,-20183676928,5934817280]),(⟨0,1,2⟩,[1024,-51200,964608,-9902080,65416192,-300306432,974770176,-2185670656,3168803840,-2410899456,-236718080,2256029696,-1590873088]),(⟨0,1,3⟩,[0,-8192,311296,-4186112,31719424,-167198720,650215424,-1806417920,3445489664,-4349665280,3333931008,-1201299456]),(⟨0,1,4⟩,[0,0,0,262144,-4456448,25952256,-60555264,20709376,170131456,-365690880,280756224]),(⟨0,2,0⟩,[7168,-220160,2845696,-20673536,93159424,-253958144,259373056,1049524224,-5964530688,15691191296,-26001269760,28030483456,-18428680192,5693743104]),(⟨0,2,1⟩,[0,-40960,1013760,-10686464,65574912,-263372800,695463936,-1030201344,36007936,3344883712,-7253682176,7496740864,-3467577344]),(⟨0,2,2⟩,[-7168,211968,-2548736,16598016,-66680832,175372288,-294922240,293545984,-206908416,296913920,-512635904,426890240]),(⟨0,2,3⟩,[0,57344,-1236992,10780672,-52789248,169099264,-365641728,494567424,-357662720,61595648,99950592]),(⟨0,2,4⟩,[-4096,102400,-1019904,5181440,-13643776,11808768,31346688,-96391168,86605824,-15597568]),(⟨0,2,5⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨0,2,6⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨0,2,7⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨0,3,0⟩,[3072,-180224,3522560,-35770368,227105792,-995262464,3157073920,-7321853952,12193743872,-13920256000,9878020096,-3215986688,-356035584]),(⟨0,3,1⟩,[0,-26624,823296,-10078208,69779456,-328077312,1132191744,-2828374016,4909154304,-5676828672,3966439424,-1243392000]),(⟨0,3,2⟩,[-2048,81920,-1234944,9699328,-47173632,157319168,-360787968,528089088,-436119552,118505472,98732032]),(⟨0,3,3⟩,[0,16384,-524288,5767168,-33947648,130842624,-346816512,598605824,-625344512,338509824]),(⟨0,3,4⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨0,3,5⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨0,4,0⟩,[-7168,191488,-1758208,5563392,17319936,-240805888,1174484992,-3513604096,6917362688,-8917763072,7070211072,-2720910336]),(⟨0,4,1⟩,[0,-4096,159744,-2080768,13647872,-61825024,234201088,-667795456,1231437824,-1373835264,760311808]),(⟨0,4,2⟩,[-4096,102400,-1019904,5181440,-13643776,11808768,31346688,-96391168,86605824,-15597568]),(⟨0,4,3⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨0,4,4⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨0,4,5⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨0,5,0⟩,[-2048,139264,-2471936,20480000,-99962880,326418432,-726429696,1022656512,-793782272,180101120,198682624]),(⟨0,5,2⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨0,5,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨0,5,4⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨0,6,0⟩,[0,16384,-524288,5767168,-33947648,130842624,-346816512,598605824,-625344512,338509824]),(⟨0,6,2⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨0,7,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨1,0,0⟩,[-1024,53248,-1089536,12640256,-96900096,532348928,-2192515072,6927155200,-16912952320,31716675584,-44795772928,45896867840,-31773867008,12666707968,-1710915584]),(⟨1,0,1⟩,[0,6144,-251904,4020224,-37197824,236343296,-1114288128,3997626368,-10873401344,21998303232,-32136001536,32307918848,-20183676928,5934817280]),(⟨1,0,2⟩,[1024,-51200,964608,-9902080,65416192,-300306432,974770176,-2185670656,3168803840,-2410899456,-236718080,2256029696,-1590873088]),(⟨1,0,3⟩,[0,-8192,311296,-4186112,31719424,-167198720,650215424,-1806417920,3445489664,-4349665280,3333931008,-1201299456]),(⟨1,0,4⟩,[0,0,0,262144,-4456448,25952256,-60555264,20709376,170131456,-365690880,280756224]),(⟨1,1,0⟩,[0,12288,-536576,8925184,-84291584,532914176,-2445107200,8432377856,-22012420096,43007340544,-61284577280,60791975936,-38039252992,11495292928]),(⟨1,1,1⟩,[0,4096,-200704,3100672,-23924736,123412480,-546316288,2151161856,-6565437440,14049398784,-19942526976,17365766144,-7285526528]),(⟨1,1,2⟩,[0,0,-32768,688128,-4390912,2949120,63176704,-215875584,169017344,404422656,-1095991296,877363200]),(⟨1,1,3⟩,[0,0,0,262144,-4456448,25952256,-60555264,20709376,170131456,-365690880,280756224]),(⟨1,2,0⟩,[1024,-92160,1978368,-20391936,126796800,-528683008,1522384896,-2896056320,3007941632,205355008,-5384335360,7286847488,-3841840128]),(⟨1,2,1⟩,[-2048,86016,-1468416,14139392,-87592960,370810880,-1134825472,2677637120,-4936460288,6683955200,-6028822528,2836807680]),(⟨1,2,2⟩,[0,0,65536,-1572864,14024704,-56885248,96206848,22020096,-362676224,619446272,-397737984]),(⟨1,2,4⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨1,2,5⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨1,3,0⟩,[0,-34816,1167360,-15083520,109035520,-526274560,1833000960,-4611330048,8141586432,-9705564160,7157469184,-2526578688]),(⟨1,3,1⟩,[14336,-413696,4962304,-33079296,140718080,-419127296,918712320,-1494073344,1764071424,-1425002496,618715136]),(⟨1,3,4⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨1,3,5⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨1,4,0⟩,[0,-4096,159744,-2080768,13647872,-61825024,234201088,-667795456,1231437824,-1373835264,760311808]),(⟨1,4,1⟩,[4096,-159744,2342912,-18104320,87777280,-294756352,688504832,-1061306368,1008144384,-479555584]),(⟨1,4,2⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨1,4,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨1,5,2⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨1,5,3⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨2,0,0⟩,[7168,-220160,2845696,-20673536,93159424,-253958144,259373056,1049524224,-5964530688,15691191296,-26001269760,28030483456,-18428680192,5693743104]),(⟨2,0,1⟩,[0,-40960,1013760,-10686464,65574912,-263372800,695463936,-1030201344,36007936,3344883712,-7253682176,7496740864,-3467577344]),(⟨2,0,2⟩,[-7168,211968,-2548736,16598016,-66680832,175372288,-294922240,293545984,-206908416,296913920,-512635904,426890240]),(⟨2,0,3⟩,[0,57344,-1236992,10780672,-52789248,169099264,-365641728,494567424,-357662720,61595648,99950592]),(⟨2,0,4⟩,[-4096,102400,-1019904,5181440,-13643776,11808768,31346688,-96391168,86605824,-15597568]),(⟨2,0,5⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨2,0,6⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨2,0,7⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨2,1,0⟩,[1024,-92160,1978368,-20391936,126796800,-528683008,1522384896,-2896056320,3007941632,205355008,-5384335360,7286847488,-3841840128]),(⟨2,1,1⟩,[-2048,86016,-1468416,14139392,-87592960,370810880,-1134825472,2677637120,-4936460288,6683955200,-6028822528,2836807680]),(⟨2,1,2⟩,[0,0,65536,-1572864,14024704,-56885248,96206848,22020096,-362676224,619446272,-397737984]),(⟨2,1,4⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨2,1,5⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨2,2,0⟩,[-14336,423936,-5097472,33261568,-134934528,364769280,-646729728,683298816,-391796736,231151616,-405825536,456042496]),(⟨2,2,1⟩,[0,0,65536,-1572864,14024704,-56885248,96206848,22020096,-362676224,619446272,-397737984]),(⟨2,2,4⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨2,3,0⟩,[-2048,139264,-2471936,20480000,-99962880,326418432,-726429696,1022656512,-793782272,180101120,198682624]),(⟨2,3,4⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨2,4,0⟩,[-4096,102400,-1019904,5181440,-13643776,11808768,31346688,-96391168,86605824,-15597568]),(⟨2,4,1⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨2,4,2⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨2,4,3⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨2,5,0⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨2,5,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨2,6,0⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨2,7,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨3,0,0⟩,[3072,-180224,3522560,-35770368,227105792,-995262464,3157073920,-7321853952,12193743872,-13920256000,9878020096,-3215986688,-356035584]),(⟨3,0,1⟩,[0,-26624,823296,-10078208,69779456,-328077312,1132191744,-2828374016,4909154304,-5676828672,3966439424,-1243392000]),(⟨3,0,2⟩,[-2048,81920,-1234944,9699328,-47173632,157319168,-360787968,528089088,-436119552,118505472,98732032]),(⟨3,0,3⟩,[0,16384,-524288,5767168,-33947648,130842624,-346816512,598605824,-625344512,338509824]),(⟨3,0,4⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨3,0,5⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,1,0⟩,[0,-34816,1167360,-15083520,109035520,-526274560,1833000960,-4611330048,8141586432,-9705564160,7157469184,-2526578688]),(⟨3,1,1⟩,[14336,-413696,4962304,-33079296,140718080,-419127296,918712320,-1494073344,1764071424,-1425002496,618715136]),(⟨3,1,4⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,1,5⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨3,2,0⟩,[-2048,139264,-2471936,20480000,-99962880,326418432,-726429696,1022656512,-793782272,180101120,198682624]),(⟨3,2,4⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨3,3,0⟩,[0,32768,-1048576,11534336,-67895296,261685248,-693633024,1197211648,-1250689024,677019648]),(⟨3,4,0⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨3,4,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,4,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨3,5,0⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,5,1⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨4,0,0⟩,[-7168,191488,-1758208,5563392,17319936,-240805888,1174484992,-3513604096,6917362688,-8917763072,7070211072,-2720910336]),(⟨4,0,1⟩,[0,-4096,159744,-2080768,13647872,-61825024,234201088,-667795456,1231437824,-1373835264,760311808]),(⟨4,0,2⟩,[-4096,102400,-1019904,5181440,-13643776,11808768,31346688,-96391168,86605824,-15597568]),(⟨4,0,3⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨4,0,4⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨4,0,5⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨4,1,0⟩,[0,-4096,159744,-2080768,13647872,-61825024,234201088,-667795456,1231437824,-1373835264,760311808]),(⟨4,1,1⟩,[4096,-159744,2342912,-18104320,87777280,-294756352,688504832,-1061306368,1008144384,-479555584]),(⟨4,1,2⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨4,1,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨4,2,0⟩,[-4096,102400,-1019904,5181440,-13643776,11808768,31346688,-96391168,86605824,-15597568]),(⟨4,2,1⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨4,2,2⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨4,2,3⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨4,3,0⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨4,3,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨4,3,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨4,4,0⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨4,5,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨5,0,0⟩,[-2048,139264,-2471936,20480000,-99962880,326418432,-726429696,1022656512,-793782272,180101120,198682624]),(⟨5,0,2⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨5,0,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨5,0,4⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨5,1,2⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨5,1,3⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨5,2,0⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨5,2,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨5,3,0⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨5,3,1⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨5,4,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨6,0,0⟩,[0,16384,-524288,5767168,-33947648,130842624,-346816512,598605824,-625344512,338509824]),(⟨6,0,2⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨6,2,0⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨7,0,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨7,2,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176])]


theorem partial_checked4 :
    (Poly.add (Poly.add (Poly.mul chunk4 sourceRight) partial8)
      (Poly.scale (K.ofRat (-1)) partial4)).isZero := by decide +kernel

theorem partial_sound4 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 4)
      sourceRight).eval u v t=partial4.eval u v t := by
  change (Poly.mul (chunk4++(sourceLeft.drop 8))
    sourceRight).eval u v t=partial4.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound8 partial_checked4 u v t


noncomputable def chunk0 : Poly := [(⟨0,0,0⟩,[-384,8384,-78592,440960,-1705088,4764160,-9624448,13537664,-12357632,6218048,-613248]),(⟨0,0,1⟩,[-64,2496,-31616,211840,-912896,2736384,-5720192,8092800,-7196096,3341632]),(⟨0,0,2⟩,[448,-8320,59264,-234624,617216,-1004928,849024,-247168,-260288]),(⟨0,0,3⟩,[128,-3712,33920,-163456,531840,-1113984,1334656,-881536])]

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[-6144,214016,-3388416,32805888,-220046336,1093013504,-4172793856,12474918912,-29339164672,53863539712,-75642831872,78359233536,-56187511808,24562075648,-4832051200,313982976]),(⟨0,0,1⟩,[-1024,90112,-2164736,26763264,-209955840,1158746112,-4757123072,14939783168,-36210367488,67300114432,-93933848576,94609350656,-63712457728,24092856320,-2731360256]),(⟨0,0,2⟩,[13312,-421888,5695488,-44066816,221002752,-755529728,1720815616,-2118316032,-991933440,10379247616,-22656579584,27416320000,-18938674176,5762426880]),(⟨0,0,3⟩,[3072,-229376,4743168,-49049600,313728000,-1382842368,4421640192,-10383220736,17622352896,-20700495872,15419260928,-5682212864,-120548352]),(⟨0,0,4⟩,[-7168,191488,-1758208,5563392,17319936,-240805888,1174484992,-3513604096,6917362688,-8917763072,7070211072,-2720910336]),(⟨0,0,5⟩,[-2048,139264,-2471936,20480000,-99962880,326418432,-726429696,1022656512,-793782272,180101120,198682624]),(⟨0,0,6⟩,[0,16384,-524288,5767168,-33947648,130842624,-346816512,598605824,-625344512,338509824]),(⟨0,1,0⟩,[-1024,90112,-2164736,26763264,-209955840,1158746112,-4757123072,14939783168,-36210367488,67300114432,-93933848576,94609350656,-63712457728,24092856320,-2731360256]),(⟨0,1,1⟩,[0,24576,-927744,14331904,-128112640,771338240,-3383070720,11192459264,-28117151744,52970536960,-72802486272,69523927040,-41618110464,11828899840]),(⟨0,1,2⟩,[1024,-92160,1978368,-20391936,126796800,-528683008,1522384896,-2896056320,3007941632,205355008,-5384335360,7286847488,-3841840128]),(⟨0,1,3⟩,[0,-34816,1167360,-15083520,109035520,-526274560,1833000960,-4611330048,8141586432,-9705564160,7157469184,-2526578688]),(⟨0,1,4⟩,[0,-4096,159744,-2080768,13647872,-61825024,234201088,-667795456,1231437824,-1373835264,760311808]),(⟨0,2,0⟩,[13312,-421888,5695488,-44066816,221002752,-755529728,1720815616,-2118316032,-991933440,10379247616,-22656579584,27416320000,-18938674176,5762426880]),(⟨0,2,1⟩,[1024,-92160,1978368,-20391936,126796800,-528683008,1522384896,-2896056320,3007941632,205355008,-5384335360,7286847488,-3841840128]),(⟨0,2,2⟩,[-14336,423936,-5097472,33261568,-134934528,364769280,-646729728,683298816,-391796736,231151616,-405825536,456042496]),(⟨0,2,3⟩,[-2048,139264,-2471936,20480000,-99962880,326418432,-726429696,1022656512,-793782272,180101120,198682624]),(⟨0,2,4⟩,[-4096,102400,-1019904,5181440,-13643776,11808768,31346688,-96391168,86605824,-15597568]),(⟨0,2,5⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨0,2,6⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨0,2,7⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨0,3,0⟩,[3072,-229376,4743168,-49049600,313728000,-1382842368,4421640192,-10383220736,17622352896,-20700495872,15419260928,-5682212864,-120548352]),(⟨0,3,1⟩,[0,-34816,1167360,-15083520,109035520,-526274560,1833000960,-4611330048,8141586432,-9705564160,7157469184,-2526578688]),(⟨0,3,2⟩,[-2048,139264,-2471936,20480000,-99962880,326418432,-726429696,1022656512,-793782272,180101120,198682624]),(⟨0,3,3⟩,[0,32768,-1048576,11534336,-67895296,261685248,-693633024,1197211648,-1250689024,677019648]),(⟨0,3,4⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨0,3,5⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨0,4,0⟩,[-7168,191488,-1758208,5563392,17319936,-240805888,1174484992,-3513604096,6917362688,-8917763072,7070211072,-2720910336]),(⟨0,4,1⟩,[0,-4096,159744,-2080768,13647872,-61825024,234201088,-667795456,1231437824,-1373835264,760311808]),(⟨0,4,2⟩,[-4096,102400,-1019904,5181440,-13643776,11808768,31346688,-96391168,86605824,-15597568]),(⟨0,4,3⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨0,4,4⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨0,4,5⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨0,5,0⟩,[-2048,139264,-2471936,20480000,-99962880,326418432,-726429696,1022656512,-793782272,180101120,198682624]),(⟨0,5,2⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨0,5,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨0,5,4⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨0,6,0⟩,[0,16384,-524288,5767168,-33947648,130842624,-346816512,598605824,-625344512,338509824]),(⟨0,6,2⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨0,7,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨1,0,0⟩,[-1024,90112,-2164736,26763264,-209955840,1158746112,-4757123072,14939783168,-36210367488,67300114432,-93933848576,94609350656,-63712457728,24092856320,-2731360256]),(⟨1,0,1⟩,[0,24576,-927744,14331904,-128112640,771338240,-3383070720,11192459264,-28117151744,52970536960,-72802486272,69523927040,-41618110464,11828899840]),(⟨1,0,2⟩,[1024,-92160,1978368,-20391936,126796800,-528683008,1522384896,-2896056320,3007941632,205355008,-5384335360,7286847488,-3841840128]),(⟨1,0,3⟩,[0,-34816,1167360,-15083520,109035520,-526274560,1833000960,-4611330048,8141586432,-9705564160,7157469184,-2526578688]),(⟨1,0,4⟩,[0,-4096,159744,-2080768,13647872,-61825024,234201088,-667795456,1231437824,-1373835264,760311808]),(⟨1,1,0⟩,[0,24576,-927744,14331904,-128112640,771338240,-3383070720,11192459264,-28117151744,52970536960,-72802486272,69523927040,-41618110464,11828899840]),(⟨1,1,1⟩,[-12288,397312,-5707776,48766976,-280602624,1175576576,-3801329664,9811197952,-20106657792,31499063296,-35486644224,25928622080,-9436981248]),(⟨1,1,2⟩,[-2048,86016,-1468416,14139392,-87592960,370810880,-1134825472,2677637120,-4936460288,6683955200,-6028822528,2836807680]),(⟨1,1,3⟩,[14336,-413696,4962304,-33079296,140718080,-419127296,918712320,-1494073344,1764071424,-1425002496,618715136]),(⟨1,1,4⟩,[4096,-159744,2342912,-18104320,87777280,-294756352,688504832,-1061306368,1008144384,-479555584]),(⟨1,2,0⟩,[1024,-92160,1978368,-20391936,126796800,-528683008,1522384896,-2896056320,3007941632,205355008,-5384335360,7286847488,-3841840128]),(⟨1,2,1⟩,[-2048,86016,-1468416,14139392,-87592960,370810880,-1134825472,2677637120,-4936460288,6683955200,-6028822528,2836807680]),(⟨1,2,2⟩,[0,0,65536,-1572864,14024704,-56885248,96206848,22020096,-362676224,619446272,-397737984]),(⟨1,2,4⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨1,2,5⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨1,3,0⟩,[0,-34816,1167360,-15083520,109035520,-526274560,1833000960,-4611330048,8141586432,-9705564160,7157469184,-2526578688]),(⟨1,3,1⟩,[14336,-413696,4962304,-33079296,140718080,-419127296,918712320,-1494073344,1764071424,-1425002496,618715136]),(⟨1,3,4⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨1,3,5⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨1,4,0⟩,[0,-4096,159744,-2080768,13647872,-61825024,234201088,-667795456,1231437824,-1373835264,760311808]),(⟨1,4,1⟩,[4096,-159744,2342912,-18104320,87777280,-294756352,688504832,-1061306368,1008144384,-479555584]),(⟨1,4,2⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨1,4,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨1,5,2⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨1,5,3⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨2,0,0⟩,[13312,-421888,5695488,-44066816,221002752,-755529728,1720815616,-2118316032,-991933440,10379247616,-22656579584,27416320000,-18938674176,5762426880]),(⟨2,0,1⟩,[1024,-92160,1978368,-20391936,126796800,-528683008,1522384896,-2896056320,3007941632,205355008,-5384335360,7286847488,-3841840128]),(⟨2,0,2⟩,[-14336,423936,-5097472,33261568,-134934528,364769280,-646729728,683298816,-391796736,231151616,-405825536,456042496]),(⟨2,0,3⟩,[-2048,139264,-2471936,20480000,-99962880,326418432,-726429696,1022656512,-793782272,180101120,198682624]),(⟨2,0,4⟩,[-4096,102400,-1019904,5181440,-13643776,11808768,31346688,-96391168,86605824,-15597568]),(⟨2,0,5⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨2,0,6⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨2,0,7⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨2,1,0⟩,[1024,-92160,1978368,-20391936,126796800,-528683008,1522384896,-2896056320,3007941632,205355008,-5384335360,7286847488,-3841840128]),(⟨2,1,1⟩,[-2048,86016,-1468416,14139392,-87592960,370810880,-1134825472,2677637120,-4936460288,6683955200,-6028822528,2836807680]),(⟨2,1,2⟩,[0,0,65536,-1572864,14024704,-56885248,96206848,22020096,-362676224,619446272,-397737984]),(⟨2,1,4⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨2,1,5⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨2,2,0⟩,[-14336,423936,-5097472,33261568,-134934528,364769280,-646729728,683298816,-391796736,231151616,-405825536,456042496]),(⟨2,2,1⟩,[0,0,65536,-1572864,14024704,-56885248,96206848,22020096,-362676224,619446272,-397737984]),(⟨2,2,4⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨2,3,0⟩,[-2048,139264,-2471936,20480000,-99962880,326418432,-726429696,1022656512,-793782272,180101120,198682624]),(⟨2,3,4⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨2,4,0⟩,[-4096,102400,-1019904,5181440,-13643776,11808768,31346688,-96391168,86605824,-15597568]),(⟨2,4,1⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨2,4,2⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨2,4,3⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨2,5,0⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨2,5,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨2,6,0⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨2,7,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨3,0,0⟩,[3072,-229376,4743168,-49049600,313728000,-1382842368,4421640192,-10383220736,17622352896,-20700495872,15419260928,-5682212864,-120548352]),(⟨3,0,1⟩,[0,-34816,1167360,-15083520,109035520,-526274560,1833000960,-4611330048,8141586432,-9705564160,7157469184,-2526578688]),(⟨3,0,2⟩,[-2048,139264,-2471936,20480000,-99962880,326418432,-726429696,1022656512,-793782272,180101120,198682624]),(⟨3,0,3⟩,[0,32768,-1048576,11534336,-67895296,261685248,-693633024,1197211648,-1250689024,677019648]),(⟨3,0,4⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨3,0,5⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,1,0⟩,[0,-34816,1167360,-15083520,109035520,-526274560,1833000960,-4611330048,8141586432,-9705564160,7157469184,-2526578688]),(⟨3,1,1⟩,[14336,-413696,4962304,-33079296,140718080,-419127296,918712320,-1494073344,1764071424,-1425002496,618715136]),(⟨3,1,4⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,1,5⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨3,2,0⟩,[-2048,139264,-2471936,20480000,-99962880,326418432,-726429696,1022656512,-793782272,180101120,198682624]),(⟨3,2,4⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨3,3,0⟩,[0,32768,-1048576,11534336,-67895296,261685248,-693633024,1197211648,-1250689024,677019648]),(⟨3,4,0⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨3,4,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,4,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨3,5,0⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,5,1⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨4,0,0⟩,[-7168,191488,-1758208,5563392,17319936,-240805888,1174484992,-3513604096,6917362688,-8917763072,7070211072,-2720910336]),(⟨4,0,1⟩,[0,-4096,159744,-2080768,13647872,-61825024,234201088,-667795456,1231437824,-1373835264,760311808]),(⟨4,0,2⟩,[-4096,102400,-1019904,5181440,-13643776,11808768,31346688,-96391168,86605824,-15597568]),(⟨4,0,3⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨4,0,4⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨4,0,5⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨4,1,0⟩,[0,-4096,159744,-2080768,13647872,-61825024,234201088,-667795456,1231437824,-1373835264,760311808]),(⟨4,1,1⟩,[4096,-159744,2342912,-18104320,87777280,-294756352,688504832,-1061306368,1008144384,-479555584]),(⟨4,1,2⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨4,1,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨4,2,0⟩,[-4096,102400,-1019904,5181440,-13643776,11808768,31346688,-96391168,86605824,-15597568]),(⟨4,2,1⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨4,2,2⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨4,2,3⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨4,3,0⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨4,3,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨4,3,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨4,4,0⟩,[8192,-188416,1482752,-4218880,-237568,18046976,-16457728,-6823936]),(⟨4,5,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨5,0,0⟩,[-2048,139264,-2471936,20480000,-99962880,326418432,-726429696,1022656512,-793782272,180101120,198682624]),(⟨5,0,2⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨5,0,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨5,0,4⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨5,1,2⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨5,1,3⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨5,2,0⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨5,2,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨5,3,0⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨5,3,1⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨5,4,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨6,0,0⟩,[0,16384,-524288,5767168,-33947648,130842624,-346816512,598605824,-625344512,338509824]),(⟨6,0,2⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨6,2,0⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨7,0,2⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨7,2,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176])]


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
    (Poly.add (Poly.scale (K.ofRat r494) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 8 10).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r492*r493 : ℚ)=r494 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 8 10 r492 r493 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 8=10 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 8 10).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C131

#print axioms Coulomb8.Columns.C131.sound
