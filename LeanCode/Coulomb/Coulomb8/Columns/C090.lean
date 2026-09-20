import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C090

def r0 : ℚ := { num := -131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 4800512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -74039296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 605454336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -352370688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -456441856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 67632267264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -438896197632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 1636420780032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -4096481312768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 7081843703808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -8208731111424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 5695303303168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -1427907559424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := -836844126208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := 603381202944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := -13582467072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 7667712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := -18022400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := 1124909056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := -5553815552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := 594690048, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 54526410752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -70585286656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 1970605522944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -4953628246016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 8300527812608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -1282917318656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 5364644937728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -560663281664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -163930112000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 7706935296, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -5881856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 64946176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -244383744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -1222868992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 17928077312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -90672267264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 246441443328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -320591757312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -124025192448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 71734067200, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -2010947059712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 1367741464576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -7668318208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -5715591168, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 360448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := -13156352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := 191430656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := -1369571328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 4038754304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 9655631872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -137517203456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 598610935808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -213324824576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 325685886976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -1966184792064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 87103897600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 275235307520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := -18424774656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := -393216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := 29736960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := -420806656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := 2549792768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := -5199101952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -1230667776, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 167914110976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -505820151808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 831282872320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -713101361152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 25850609664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := 2063646720, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := -163840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := 114688, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := -1441792, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := 359907328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 37814272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -8987115520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 44863455232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -107916460032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 8030355456, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -67739140096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := -2577924096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := 230866944, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 32768, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -26542080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 181010432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := -274399232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -3160997888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := 20658782208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := -1148059648, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := 76484149248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -39584497664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -1059913728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := 16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := -622592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 11894784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -148078592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 1238777856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := -6625492992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := 19037650944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 3058106368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -277647409152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 1273349308416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := -3216624418816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := 5035564105728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -4605989830656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 1650752880640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 116415758336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -15266611200, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -4407296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := 109445120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := -927809536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := 3450568704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := -486817792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -2964979712, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 13660700672, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -549031116800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 768239484928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := -633926057984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := 345261424640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -40635826176, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 4815798272, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 589824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := -229376, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := 8224768, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -1090273280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 4740808704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := -6798114816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := -36420911104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := 233464479744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := -628085948416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := 55007936512, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := -703683526656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 14681030656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := 2738814976, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 327680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -737280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := -1507328, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := 229638144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := -97386496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := 196444160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 2337144832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := -644628480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -12101812224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 9325101056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := 6011420672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := -73367552, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -27590656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 228196352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := -986382336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 2053570560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -456392704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -7065174016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 822575104, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -1162379264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := -1769472, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 4521984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -24281088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := -224919552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := 74743808, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := -21059731456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := 64173572096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := -106458513408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 4125753344, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := 8777826304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := -175669248, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := 1814822912, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -422281216, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 163840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := 4489216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -90112000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 33800192, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := -856227840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -7322927104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := 44501827584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := -112335962112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := 145347477504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := -76705792000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -1136066560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 39796736, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := -65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := 1638400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -1769472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := -12189696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := 631635968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := -420347904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := 802553856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 35098460160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := -127790284800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := 196612259840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := -16552755200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -157679616, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 262144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -18743296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := 73924608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := 61997056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -1546649600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 5050466304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := -624427008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := -10857545728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := 4121690112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -24248320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := 65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := -1441792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := 1310720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := 8388608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := -300548096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := 1022623744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := -424935424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -3209691136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := 637992960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := -917504, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := -1572864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 11272192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -524288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := -308936704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 162004992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := -473169920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -3690463232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 39256064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := 262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := -6291456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := 3145728, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := -169869312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := -52953088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := 1314914304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := -1531969536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := -18874368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := 786432, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := -42467328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -13238272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 328728576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -382992384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -4718592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 49152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := 21233664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -167510016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := 937377792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -4147249152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := 13696008192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := -25485115392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := -9464758272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := 184213045248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := -427102371840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := 38246547456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := 12759121920, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -28738977792, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := 1093435392, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := 425984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := -5832704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := 66682880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := -592789504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := 3355443200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := -10877665280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := 16725245952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 4555096064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -1364033536, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := 2348089344, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := -1719173120, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := 55853056, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -49152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := 196608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := -15237120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := 88408064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := -318455808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := 837943296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := -199819264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -1184235520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 13954498560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := -30692278272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := 8046215168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := 10301669376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := -103071744, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := 655360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := -2260992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := -38928384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := 61341696, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := -1788084224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := 3328376832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := -723255296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := -180387840, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := 2523267072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := -21528576, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := 411959296, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := -22478848, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -4718592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 33816576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -926810112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 486014976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -1419509760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := -11071389696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := 117768192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := 2400256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := -37019648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := 302727168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := -176185344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := -228220928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := 33816133632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := -219448098816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := 818210390016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -2048240656384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 3540921851904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -4104365555712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 2847651651584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -713953779712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := -418422063104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := 301690601472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := -6791233536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := -98304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 3833856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -9011200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := 562454528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := -2776907776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := 297345024, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := 27263205376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := -35292643328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := 985302761472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := -2476814123008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := 4150263906304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -641458659328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 2682322468864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -280331640832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := -81965056000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := 3853467648, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := 98304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -2940928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 32473088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -122191872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := -611434496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := 8964038656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := -45336133632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := 123220721664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := -160295878656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := -62012596224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := 35867033600, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := -1005473529856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := 683870732288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := -3834159104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := -2857795584, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := 180224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := -6578176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := 95715328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := -684785664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := 2019377152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := 4827815936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := -68758601728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := 299305467904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := -106662412288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := 162842943488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := -983092396032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := 43551948800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := 137617653760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -9212387328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := 14868480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := -210403328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := 1274896384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := -2599550976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := -615333888, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := 83957055488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := -252910075904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := 415641436160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := -356550680576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := 12925304832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := 1031823360, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := -81920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := 57344, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := -720896, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := 179953664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := 18907136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := -4493557760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := 22431727616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := -53958230016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := 4015177728, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := -33869570048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := -1288962048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := 115433472, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := 16384, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := -13271040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := 90505216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := -137199616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := -1580498944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := 10329391104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := -574029824, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := 38242074624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := -19792248832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := -529956864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := 8192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := -311296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 5947392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := 619388928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := -3312746496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := 9518825472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := 1529053184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := -138823704576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := 636674654208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := -1608312209408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := 2517782052864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := -2302994915328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := 825376440320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := 58207879168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := -7633305600, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := -2203648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := 54722560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := -463904768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := 1725284352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := -243408896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := -1482489856, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := 6830350336, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := -274515558400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := 384119742464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := -316963028992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := 172630712320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := -20317913088, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := 2407899136, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := -8192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := 294912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := -114688, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := 4112384, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := -545136640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := 2370404352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := -3399057408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := -18210455552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := 116732239872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := -314042974208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := 27503968256, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := -351841763328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := 7340515328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := 1369407488, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := -368640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := -753664, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := 114819072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := -48693248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := 98222080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := 1168572416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := -322314240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := -6050906112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := 4662550528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := 3005710336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := -36683776, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := -13795328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := 114098176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := -493191168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := 1026785280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := -228196352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := -3532587008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r450 : ℚ := { num := 411287552, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r451 : ℚ := { num := -581189632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r452 : ℚ := { num := -884736, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r453 : ℚ := { num := 2260992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r454 : ℚ := { num := -12140544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r455 : ℚ := { num := -112459776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r456 : ℚ := { num := 37371904, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r457 : ℚ := { num := -10529865728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r458 : ℚ := { num := 32086786048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r459 : ℚ := { num := -53229256704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r460 : ℚ := { num := 2062876672, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r461 : ℚ := { num := 4388913152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r462 : ℚ := { num := -87834624, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r463 : ℚ := { num := 907411456, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r464 : ℚ := { num := -211140608, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r465 : ℚ := { num := 81920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r466 : ℚ := { num := 2244608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r467 : ℚ := { num := -45056000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r468 : ℚ := { num := 16900096, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r469 : ℚ := { num := -428113920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r470 : ℚ := { num := -3661463552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r471 : ℚ := { num := 22250913792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r472 : ℚ := { num := -56167981056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r473 : ℚ := { num := 72673738752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r474 : ℚ := { num := -38352896000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r475 : ℚ := { num := -568033280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r476 : ℚ := { num := 19898368, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r477 : ℚ := { num := 819200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r478 : ℚ := { num := -884736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r479 : ℚ := { num := -6094848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r480 : ℚ := { num := 315817984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r481 : ℚ := { num := -210173952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r482 : ℚ := { num := 401276928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r483 : ℚ := { num := 17549230080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r484 : ℚ := { num := -63895142400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r485 : ℚ := { num := 98306129920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r486 : ℚ := { num := -8276377600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r487 : ℚ := { num := -78839808, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r488 : ℚ := { num := 131072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r489 : ℚ := { num := -9371648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r490 : ℚ := { num := 36962304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r491 : ℚ := { num := 30998528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r492 : ℚ := { num := -773324800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r493 : ℚ := { num := 2525233152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r494 : ℚ := { num := -312213504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r495 : ℚ := { num := -5428772864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r496 : ℚ := { num := 2060845056, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r497 : ℚ := { num := -12124160, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r498 : ℚ := { num := 32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r499 : ℚ := { num := -720896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r500 : ℚ := { num := 655360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r501 : ℚ := { num := 4194304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r502 : ℚ := { num := -150274048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r503 : ℚ := { num := 511311872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r504 : ℚ := { num := -212467712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r505 : ℚ := { num := -1604845568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r506 : ℚ := { num := 318996480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r507 : ℚ := { num := -458752, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r508 : ℚ := { num := -786432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r509 : ℚ := { num := 5636096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r510 : ℚ := { num := -262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r511 : ℚ := { num := -154468352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r512 : ℚ := { num := 81002496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r513 : ℚ := { num := -236584960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r514 : ℚ := { num := -1845231616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r515 : ℚ := { num := 19628032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r516 : ℚ := { num := 131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r517 : ℚ := { num := -3145728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r518 : ℚ := { num := 1572864, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r519 : ℚ := { num := -84934656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r520 : ℚ := { num := -26476544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r521 : ℚ := { num := 657457152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r522 : ℚ := { num := -765984768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r523 : ℚ := { num := -9437184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r524 : ℚ := { num := 393216, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r525 : ℚ := { num := -21233664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r526 : ℚ := { num := -6619136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r527 : ℚ := { num := 164364288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r528 : ℚ := { num := -191496192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r529 : ℚ := { num := -2359296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r530 : ℚ := { num := 24576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r531 : ℚ := { num := 10616832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r532 : ℚ := { num := -83755008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r533 : ℚ := { num := 468688896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r534 : ℚ := { num := -2073624576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r535 : ℚ := { num := 6848004096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r536 : ℚ := { num := -12742557696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r537 : ℚ := { num := -4732379136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r538 : ℚ := { num := 92106522624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r539 : ℚ := { num := -213551185920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r540 : ℚ := { num := 19123273728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r541 : ℚ := { num := 6379560960, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r542 : ℚ := { num := -14369488896, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r543 : ℚ := { num := 546717696, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r544 : ℚ := { num := 212992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r545 : ℚ := { num := -2916352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r546 : ℚ := { num := 33341440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r547 : ℚ := { num := -296394752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r548 : ℚ := { num := 1677721600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r549 : ℚ := { num := -5438832640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r550 : ℚ := { num := 8362622976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r551 : ℚ := { num := 2277548032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r552 : ℚ := { num := -682016768, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r553 : ℚ := { num := 1174044672, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r554 : ℚ := { num := -859586560, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r555 : ℚ := { num := 27926528, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r556 : ℚ := { num := -24576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r557 : ℚ := { num := 98304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r558 : ℚ := { num := -7618560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r559 : ℚ := { num := 44204032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r560 : ℚ := { num := -159227904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r561 : ℚ := { num := 418971648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r562 : ℚ := { num := -99909632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r563 : ℚ := { num := -592117760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r564 : ℚ := { num := 6977249280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r565 : ℚ := { num := -15346139136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r566 : ℚ := { num := 4023107584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r567 : ℚ := { num := 5150834688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r568 : ℚ := { num := -51535872, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r569 : ℚ := { num := -1130496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r570 : ℚ := { num := -19464192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r571 : ℚ := { num := 30670848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r572 : ℚ := { num := -894042112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r573 : ℚ := { num := 1664188416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r574 : ℚ := { num := -361627648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r575 : ℚ := { num := -90193920, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r576 : ℚ := { num := 1261633536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r577 : ℚ := { num := -10764288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r578 : ℚ := { num := 205979648, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r579 : ℚ := { num := -11239424, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r580 : ℚ := { num := -2359296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r581 : ℚ := { num := 16908288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r582 : ℚ := { num := -463405056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r583 : ℚ := { num := 243007488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r584 : ℚ := { num := -709754880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r585 : ℚ := { num := -5535694848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r586 : ℚ := { num := 58884096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r587 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r588 : ℚ := { num := 1, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16],[0,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32],[0,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47],[0,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61],[0,r62,r63,r64,r65,r66,r67,r68,r69,r70,r71,r72,r73,r74],[0,r75,r76,r77,r78,r79,r80,r81,r82,r83,r84,r85,r86],[0,r62,r87,r88,r89,r90,r91,r92,r93,r94,r95,r96],[],[],[],[],[],[],[r97,r98,r99,r100,r101,r102,r103,r104,r105,r106,r107,r108,r109,r110,r111,r112],[r97,r17,r113,r114,r115,r116,r117,r118,r119,r120,r121,r122,r123,r124,r125],[r126,r127,r128,r129,r130,r131,r132,r133,r134,r135,r136,r137,r138,r139],[r126,r140,r141,r142,r143,r144,r145,r146,r147,r148,r149,r150,r151],[0,r62,r87,r152,r153,r154,r155,r156,r157,r158,r159,r160],[],[],[],[],[],[],[0,r17,r161,r162,r163,r164,r165,r166,r167,r168,r169,r170,r171,r172],[r126,r173,r174,r175,r176,r177,r178,r179,r180,r181,r182,r183,r184],[0,r62,r87,r152,r153,r154,r155,r156,r157,r158,r159,r160],[],[],[],[],[],[],[r185,r186,r187,r188,r189,r190,r191,r192,r193,r194,r195,r196],[r185,r197,r198,r199,r200,r201,r202,r203,r204,r205,r206],[r207,r208,r209,r210,r211,r212,r213,r214,r215,r216],[r207,r217,r218,r219,r220,r221,r222,r223,r224],[],[],[],[0,r225,r226,r227,r228,r229,r230,r231,r232,262144],[r207,r217,r233,r234,r235,r236,r237,r238,65536],[],[],[],[],[],[],[],[r239,r217,r240,r241,r242,r243,r244,r245,r246,r247,r248,r249,r250,r251,r252],[r126,r253,r254,r255,r256,r257,r258,r259,r260,r261,r262,r263,r264,-3211264],[r265,r266,r267,r268,r269,r270,r271,r272,r273,r274,r275,r276,r277],[],[],[],[],[],[],[],[r62,r278,r279,r280,r281,r282,r283,r284,r285,r286,r287,r288,r289],[0,r62,r87,r152,r153,r154,r155,r156,r157,r158,r159,r160],[],[],[],[],[],[],[r185,r197,r198,r199,r200,r201,r202,r203,r204,r205,r206],[0,r225,r226,r227,r228,r229,r230,r231,r232,262144],[r207,r217,r233,r234,r235,r236,r237,r238,65536],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[r207,r208,r209,r210,r211,r212,r213,r214,r215,r216],[r207,r217,r233,r234,r235,r236,r237,r238,65536],[],[],[],[],[],[],[],[r33,r290,r291,r217,r292,r293,r294,r295,r296],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,r185,r297,r298,r299,r300,r301,r302,r303,r304,r305,r306,r307,r308,r309,r310,r311,r312]),(⟨0,0,1⟩,[0,r313,r314,r315,r316,r317,r318,r319,r320,r321,r322,r323,r324,r325,r326,r327,r328]),(⟨0,0,2⟩,[0,r329,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340,r341,r342,r343]),(⟨0,0,3⟩,[0,r344,r345,r346,r347,r348,r349,r350,r351,r352,r353,r354,r355,r356,r357]),(⟨0,0,4⟩,[0,r126,r17,r358,r359,r360,r361,r362,r363,r364,r365,r366,r367,r368]),(⟨0,0,5⟩,[0,r369,r370,r371,r372,r373,r374,r375,r376,r377,r378,r379,r380]),(⟨0,0,6⟩,[0,r126,r381,r382,r383,r384,r385,r386,r387,r388,r389,r390]),(⟨0,1,0⟩,[0,r313,r314,r315,r316,r317,r318,r319,r320,r321,r322,r323,r324,r325,r326,r327,r328]),(⟨0,1,1⟩,[r391,r392,r393,r2,r394,r395,r396,r397,r398,r399,r400,r401,r402,r403,r404,r405]),(⟨0,1,2⟩,[r391,r313,r406,r407,r408,r409,r410,r411,r412,r413,r414,r415,r416,r417,r418]),(⟨0,1,3⟩,[r419,r420,r421,r422,r423,r424,r425,r426,r427,r428,r429,r430,r431,r432]),(⟨0,1,4⟩,[r419,r173,r433,r434,r435,r436,r437,r438,r439,r440,r441,r442,r443]),(⟨0,1,5⟩,[0,r126,r381,r444,r445,r446,r447,r448,r449,r450,r451,r452]),(⟨0,2,0⟩,[0,r329,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340,r341,r342,r343]),(⟨0,2,1⟩,[r391,r313,r406,r407,r408,r409,r410,r411,r412,r413,r414,r415,r416,r417,r418]),(⟨0,2,2⟩,[0,r313,r453,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464]),(⟨0,2,3⟩,[r419,r465,r466,r467,r468,r469,r470,r471,r472,r473,r474,r475,r476]),(⟨0,2,4⟩,[0,r126,r381,r444,r445,r446,r447,r448,r449,r450,r451,r452]),(⟨0,3,0⟩,[0,r344,r345,r346,r347,r348,r349,r350,r351,r352,r353,r354,r355,r356,r357]),(⟨0,3,1⟩,[r419,r420,r421,r422,r423,r424,r425,r426,r427,r428,r429,r430,r431,r432]),(⟨0,3,2⟩,[r419,r465,r466,r467,r468,r469,r470,r471,r472,r473,r474,r475,r476]),(⟨0,3,3⟩,[r62,r477,r478,r479,r480,r481,r482,r483,r484,r485,r486,r487]),(⟨0,3,4⟩,[r62,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497]),(⟨0,3,5⟩,[r498,r499,r500,r501,r502,r503,r504,r505,r506,r507]),(⟨0,3,6⟩,[r498,r508,r509,r510,r511,r512,r513,r514,r515]),(⟨0,4,0⟩,[0,r126,r17,r358,r359,r360,r361,r362,r363,r364,r365,r366,r367,r368]),(⟨0,4,1⟩,[r419,r173,r433,r434,r435,r436,r437,r438,r439,r440,r441,r442,r443]),(⟨0,4,2⟩,[0,r126,r381,r444,r445,r446,r447,r448,r449,r450,r451,r452]),(⟨0,4,3⟩,[r62,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497]),(⟨0,4,4⟩,[0,r516,r517,r518,r519,r520,r521,r522,r523,131072]),(⟨0,4,5⟩,[r498,r508,r524,r525,r526,r527,r528,r529,32768]),(⟨0,5,0⟩,[0,r369,r370,r371,r372,r373,r374,r375,r376,r377,r378,r379,r380]),(⟨0,5,1⟩,[0,r126,r381,r444,r445,r446,r447,r448,r449,r450,r451,r452]),(⟨0,5,3⟩,[r498,r499,r500,r501,r502,r503,r504,r505,r506,r507]),(⟨0,5,4⟩,[r498,r508,r524,r525,r526,r527,r528,r529,32768]),(⟨0,6,0⟩,[0,r126,r381,r382,r383,r384,r385,r386,r387,r388,r389,r390]),(⟨0,6,3⟩,[r498,r508,r509,r510,r511,r512,r513,r514,r515]),(⟨1,0,0⟩,[0,r313,r314,r315,r316,r317,r318,r319,r320,r321,r322,r323,r324,r325,r326,r327,r328]),(⟨1,0,1⟩,[r391,r392,r393,r2,r394,r395,r396,r397,r398,r399,r400,r401,r402,r403,r404,r405]),(⟨1,0,2⟩,[r391,r313,r406,r407,r408,r409,r410,r411,r412,r413,r414,r415,r416,r417,r418]),(⟨1,0,3⟩,[r419,r420,r421,r422,r423,r424,r425,r426,r427,r428,r429,r430,r431,r432]),(⟨1,0,4⟩,[r419,r173,r433,r434,r435,r436,r437,r438,r439,r440,r441,r442,r443]),(⟨1,0,5⟩,[0,r126,r381,r444,r445,r446,r447,r448,r449,r450,r451,r452]),(⟨1,1,0⟩,[r391,r392,r393,r2,r394,r395,r396,r397,r398,r399,r400,r401,r402,r403,r404,r405]),(⟨1,1,1⟩,[r530,r508,r531,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543]),(⟨1,1,2⟩,[r419,r544,r545,r546,r547,r548,r549,r550,r551,r552,r553,r554,r555,-1605632]),(⟨1,1,3⟩,[r556,r557,r558,r559,r560,r561,r562,r563,r564,r565,r566,r567,r568]),(⟨1,2,0⟩,[r391,r313,r406,r407,r408,r409,r410,r411,r412,r413,r414,r415,r416,r417,r418]),(⟨1,2,1⟩,[r419,r544,r545,r546,r547,r548,r549,r550,r551,r552,r553,r554,r555,-1605632]),(⟨1,2,2⟩,[r126,r140,r569,r570,r571,r572,r573,r574,r575,r576,r577,r578,r579]),(⟨1,2,3⟩,[0,r126,r381,r444,r445,r446,r447,r448,r449,r450,r451,r452]),(⟨1,3,0⟩,[r419,r420,r421,r422,r423,r424,r425,r426,r427,r428,r429,r430,r431,r432]),(⟨1,3,1⟩,[r556,r557,r558,r559,r560,r561,r562,r563,r564,r565,r566,r567,r568]),(⟨1,3,2⟩,[0,r126,r381,r444,r445,r446,r447,r448,r449,r450,r451,r452]),(⟨1,3,3⟩,[r62,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497]),(⟨1,3,4⟩,[0,r516,r517,r518,r519,r520,r521,r522,r523,131072]),(⟨1,3,5⟩,[r498,r508,r524,r525,r526,r527,r528,r529,32768]),(⟨1,4,0⟩,[r419,r173,r433,r434,r435,r436,r437,r438,r439,r440,r441,r442,r443]),(⟨1,4,3⟩,[0,r516,r517,r518,r519,r520,r521,r522,r523,131072]),(⟨1,5,0⟩,[0,r126,r381,r444,r445,r446,r447,r448,r449,r450,r451,r452]),(⟨1,5,3⟩,[r498,r508,r524,r525,r526,r527,r528,r529,32768]),(⟨2,0,0⟩,[0,r329,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340,r341,r342,r343]),(⟨2,0,1⟩,[r391,r313,r406,r407,r408,r409,r410,r411,r412,r413,r414,r415,r416,r417,r418]),(⟨2,0,2⟩,[0,r313,r453,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464]),(⟨2,0,3⟩,[r419,r465,r466,r467,r468,r469,r470,r471,r472,r473,r474,r475,r476]),(⟨2,0,4⟩,[0,r126,r381,r444,r445,r446,r447,r448,r449,r450,r451,r452]),(⟨2,1,0⟩,[r391,r313,r406,r407,r408,r409,r410,r411,r412,r413,r414,r415,r416,r417,r418]),(⟨2,1,1⟩,[r419,r544,r545,r546,r547,r548,r549,r550,r551,r552,r553,r554,r555,-1605632]),(⟨2,1,2⟩,[r126,r140,r569,r570,r571,r572,r573,r574,r575,r576,r577,r578,r579]),(⟨2,1,3⟩,[0,r126,r381,r444,r445,r446,r447,r448,r449,r450,r451,r452]),(⟨2,2,0⟩,[0,r313,r453,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464]),(⟨2,2,1⟩,[r126,r140,r569,r570,r571,r572,r573,r574,r575,r576,r577,r578,r579]),(⟨2,3,0⟩,[r419,r465,r466,r467,r468,r469,r470,r471,r472,r473,r474,r475,r476]),(⟨2,3,1⟩,[0,r126,r381,r444,r445,r446,r447,r448,r449,r450,r451,r452]),(⟨2,3,3⟩,[r498,r499,r500,r501,r502,r503,r504,r505,r506,r507]),(⟨2,3,4⟩,[r498,r508,r524,r525,r526,r527,r528,r529,32768]),(⟨2,4,0⟩,[0,r126,r381,r444,r445,r446,r447,r448,r449,r450,r451,r452]),(⟨2,4,3⟩,[r498,r508,r524,r525,r526,r527,r528,r529,32768]),(⟨3,0,0⟩,[0,r344,r345,r346,r347,r348,r349,r350,r351,r352,r353,r354,r355,r356,r357]),(⟨3,0,1⟩,[r419,r420,r421,r422,r423,r424,r425,r426,r427,r428,r429,r430,r431,r432]),(⟨3,0,2⟩,[r419,r465,r466,r467,r468,r469,r470,r471,r472,r473,r474,r475,r476]),(⟨3,0,3⟩,[r62,r477,r478,r479,r480,r481,r482,r483,r484,r485,r486,r487]),(⟨3,0,4⟩,[r62,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497]),(⟨3,0,5⟩,[r498,r499,r500,r501,r502,r503,r504,r505,r506,r507]),(⟨3,0,6⟩,[r498,r508,r509,r510,r511,r512,r513,r514,r515]),(⟨3,1,0⟩,[r419,r420,r421,r422,r423,r424,r425,r426,r427,r428,r429,r430,r431,r432]),(⟨3,1,1⟩,[r556,r557,r558,r559,r560,r561,r562,r563,r564,r565,r566,r567,r568]),(⟨3,1,2⟩,[0,r126,r381,r444,r445,r446,r447,r448,r449,r450,r451,r452]),(⟨3,1,3⟩,[r62,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497]),(⟨3,1,4⟩,[0,r516,r517,r518,r519,r520,r521,r522,r523,131072]),(⟨3,1,5⟩,[r498,r508,r524,r525,r526,r527,r528,r529,32768]),(⟨3,2,0⟩,[r419,r465,r466,r467,r468,r469,r470,r471,r472,r473,r474,r475,r476]),(⟨3,2,1⟩,[0,r126,r381,r444,r445,r446,r447,r448,r449,r450,r451,r452]),(⟨3,2,3⟩,[r498,r499,r500,r501,r502,r503,r504,r505,r506,r507]),(⟨3,2,4⟩,[r498,r508,r524,r525,r526,r527,r528,r529,32768]),(⟨3,3,0⟩,[r62,r477,r478,r479,r480,r481,r482,r483,r484,r485,r486,r487]),(⟨3,3,1⟩,[r62,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497]),(⟨3,3,2⟩,[r498,r499,r500,r501,r502,r503,r504,r505,r506,r507]),(⟨3,3,3⟩,[r329,r580,r581,r508,r582,r583,r584,r585,r586]),(⟨3,4,0⟩,[r62,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497]),(⟨3,4,1⟩,[0,r516,r517,r518,r519,r520,r521,r522,r523,131072]),(⟨3,4,2⟩,[r498,r508,r524,r525,r526,r527,r528,r529,32768]),(⟨3,5,0⟩,[r498,r499,r500,r501,r502,r503,r504,r505,r506,r507]),(⟨3,5,1⟩,[r498,r508,r524,r525,r526,r527,r528,r529,32768]),(⟨3,6,0⟩,[r498,r508,r509,r510,r511,r512,r513,r514,r515]),(⟨4,0,0⟩,[0,r126,r17,r358,r359,r360,r361,r362,r363,r364,r365,r366,r367,r368]),(⟨4,0,1⟩,[r419,r173,r433,r434,r435,r436,r437,r438,r439,r440,r441,r442,r443]),(⟨4,0,2⟩,[0,r126,r381,r444,r445,r446,r447,r448,r449,r450,r451,r452]),(⟨4,0,3⟩,[r62,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497]),(⟨4,0,4⟩,[0,r516,r517,r518,r519,r520,r521,r522,r523,131072]),(⟨4,0,5⟩,[r498,r508,r524,r525,r526,r527,r528,r529,32768]),(⟨4,1,0⟩,[r419,r173,r433,r434,r435,r436,r437,r438,r439,r440,r441,r442,r443]),(⟨4,1,3⟩,[0,r516,r517,r518,r519,r520,r521,r522,r523,131072]),(⟨4,2,0⟩,[0,r126,r381,r444,r445,r446,r447,r448,r449,r450,r451,r452]),(⟨4,2,3⟩,[r498,r508,r524,r525,r526,r527,r528,r529,32768]),(⟨4,3,0⟩,[r62,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497]),(⟨4,3,1⟩,[0,r516,r517,r518,r519,r520,r521,r522,r523,131072]),(⟨4,3,2⟩,[r498,r508,r524,r525,r526,r527,r528,r529,32768]),(⟨4,4,0⟩,[0,r516,r517,r518,r519,r520,r521,r522,r523,131072]),(⟨4,5,0⟩,[r498,r508,r524,r525,r526,r527,r528,r529,32768]),(⟨5,0,0⟩,[0,r369,r370,r371,r372,r373,r374,r375,r376,r377,r378,r379,r380]),(⟨5,0,1⟩,[0,r126,r381,r444,r445,r446,r447,r448,r449,r450,r451,r452]),(⟨5,0,3⟩,[r498,r499,r500,r501,r502,r503,r504,r505,r506,r507]),(⟨5,0,4⟩,[r498,r508,r524,r525,r526,r527,r528,r529,32768]),(⟨5,1,0⟩,[0,r126,r381,r444,r445,r446,r447,r448,r449,r450,r451,r452]),(⟨5,1,3⟩,[r498,r508,r524,r525,r526,r527,r528,r529,32768]),(⟨5,3,0⟩,[r498,r499,r500,r501,r502,r503,r504,r505,r506,r507]),(⟨5,3,1⟩,[r498,r508,r524,r525,r526,r527,r528,r529,32768]),(⟨5,4,0⟩,[r498,r508,r524,r525,r526,r527,r528,r529,32768]),(⟨6,0,0⟩,[0,r126,r381,r382,r383,r384,r385,r386,r387,r388,r389,r390]),(⟨6,0,3⟩,[r498,r508,r509,r510,r511,r512,r513,r514,r515]),(⟨6,3,0⟩,[r498,r508,r509,r510,r511,r512,r513,r514,r515])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[128,-1792,5120,30720,-231808,574208,-567040,116736]),(⟨0,0,1⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨0,0,2⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨0,0,3⟩,[-128,1536,256,-37376,76672]),(⟨0,1,0⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨0,1,1⟩,[0,-512,6144,-15360,-18432,60928]),(⟨0,1,2⟩,[-128,1536,-3840,-4608,15232]),(⟨0,2,0⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨0,2,1⟩,[-128,1536,-3840,-4608,15232]),(⟨0,3,0⟩,[-128,1536,256,-37376,76672]),(⟨1,0,0⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨1,0,1⟩,[0,-512,6144,-15360,-18432,60928]),(⟨1,0,2⟩,[-128,1536,-3840,-4608,15232]),(⟨1,1,0⟩,[0,-512,6144,-15360,-18432,60928]),(⟨1,2,0⟩,[-128,1536,-3840,-4608,15232]),(⟨2,0,0⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨2,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨2,1,0⟩,[-128,1536,-3840,-4608,15232]),(⟨3,0,0⟩,[-128,1536,256,-37376,76672])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[0,-512,11584,-106560,532736,-1621824,3051904,-3282624,1363712,606272,-407232]),(⟨0,0,1⟩,[0,-256,6592,-65600,337472,-994752,1716288,-1563072,348096,460992]),(⟨0,0,2⟩,[0,512,-9792,66304,-201792,309760,-192192,-87808,65856]),(⟨0,0,3⟩,[0,128,-4736,47104,-188672,361600,-281728,-48384]),(⟨0,1,0⟩,[0,-256,6592,-65600,337472,-994752,1716288,-1563072,348096,460992]),(⟨0,1,1⟩,[64,-1024,6144,-20992,42368,-19456,-107520,326144,-373184]),(⟨0,2,0⟩,[0,512,-9792,66304,-201792,309760,-192192,-87808,65856]),(⟨0,3,0⟩,[0,128,-4736,47104,-188672,361600,-281728,-48384]),(⟨0,3,3⟩,[-256,3072,-7680,-9216,30464]),(⟨1,0,0⟩,[0,-256,6592,-65600,337472,-994752,1716288,-1563072,348096,460992]),(⟨1,0,1⟩,[64,-1024,6144,-20992,42368,-19456,-107520,326144,-373184]),(⟨1,1,0⟩,[64,-1024,6144,-20992,42368,-19456,-107520,326144,-373184]),(⟨2,0,0⟩,[0,512,-9792,66304,-201792,309760,-192192,-87808,65856]),(⟨3,0,0⟩,[0,128,-4736,47104,-188672,361600,-281728,-48384]),(⟨3,0,3⟩,[-256,3072,-7680,-9216,30464]),(⟨3,3,0⟩,[-256,3072,-7680,-9216,30464])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 3 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r587) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 9 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r587) sourceRight))).isZero := by decide +kernel

noncomputable def partial19 : Poly := []

theorem partial_sound19 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 19)
      sourceRight).eval u v t=partial19.eval u v t := by rfl

noncomputable def chunk16 : Poly := [(⟨2,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨2,1,0⟩,[-128,1536,-3840,-4608,15232]),(⟨3,0,0⟩,[-128,1536,256,-37376,76672])]

noncomputable def partial16 : Poly := [(⟨2,0,1⟩,[0,65536,-2269184,33398784,-273989632,1373888512,-4259995648,7257735168,-1347977216,-24144461824,57359638528,-59238506496,19542130688,11111260160,-6202957824]),(⟨2,0,2⟩,[0,32768,-1236992,19505152,-168091648,863313920,-2640822272,4101849088,688209920,-16582852608,32716529664,-27182948352,3177947136,7021830144]),(⟨2,0,3⟩,[0,-65536,2039808,-25493504,162914304,-551288832,820592640,466354176,-3906355200,6042222592,-2775736320,-1640955904,1003118592]),(⟨2,0,4⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨2,1,0⟩,[0,65536,-2269184,33398784,-273989632,1373888512,-4259995648,7257735168,-1347977216,-24144461824,57359638528,-59238506496,19542130688,11111260160,-6202957824]),(⟨2,1,1⟩,[0,65536,-2473984,39010304,-336183296,1726627840,-5281644544,8203698176,1376419840,-33165705216,65433059328,-54365896704,6355894272,14043660288]),(⟨2,1,2⟩,[-8192,163840,-565248,-9732096,107347968,-447021056,832094208,-180813824,-2209751040,4415717376,-4483325952,5046501376,-4681220096]),(⟨2,1,3⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨2,2,0⟩,[0,32768,-1236992,19505152,-168091648,863313920,-2640822272,4101849088,688209920,-16582852608,32716529664,-27182948352,3177947136,7021830144]),(⟨2,2,1⟩,[-8192,163840,-565248,-9732096,107347968,-447021056,832094208,-180813824,-2209751040,4415717376,-4483325952,5046501376,-4681220096]),(⟨2,3,0⟩,[0,-65536,2039808,-25493504,162914304,-551288832,820592640,466354176,-3906355200,6042222592,-2775736320,-1640955904,1003118592]),(⟨2,3,1⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨2,3,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,4,0⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨2,4,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,0,0⟩,[0,65536,-2269184,31301632,-209764352,526376960,2125570048,-23388995584,97027850240,-237239746560,358019407872,-303125749760,81794252800,61704790016,-31223291904]),(⟨3,0,1⟩,[0,65536,-2473984,37961728,-300793856,1226194944,-1344765952,-10959552512,61736648704,-156924936192,223526338560,-159919226880,12637126656,42367008768]),(⟨3,0,2⟩,[-8192,163840,-565248,-7634944,50462720,176881664,-2768715776,11774001152,-25545285632,29385457664,-13144563712,-2506391552,-635027456]),(⟨3,0,3⟩,[0,-16384,802816,-13271040,90505216,-137199616,-1580498944,10329391104,-28127461376,38242074624,-19792248832,-3709698048]),(⟨3,1,0⟩,[0,65536,-2473984,37961728,-300793856,1226194944,-1344765952,-10959552512,61736648704,-156924936192,223526338560,-159919226880,12637126656,42367008768]),(⟨3,1,1⟩,[-24576,688128,-7553024,40992768,-104046592,-37421056,1273397248,-4699258880,7890034688,-1215791104,-23944445952,52329152512,-39981441024]),(⟨3,2,0⟩,[-8192,163840,-565248,-7634944,50462720,176881664,-2768715776,11774001152,-25545285632,29385457664,-13144563712,-2506391552,-635027456]),(⟨3,3,0⟩,[0,-16384,802816,-13271040,90505216,-137199616,-1580498944,10329391104,-28127461376,38242074624,-19792248832,-3709698048]),(⟨3,3,3⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨4,0,0⟩,[0,32768,-1236992,18456576,-132702208,362881024,1296056320,-15061401600,61048438784,-140342083584,190809808896,-132736278528,9459179520,35345178624]),(⟨4,0,1⟩,[-8192,163840,-303104,-16023552,170000384,-797245440,2070986752,-2938568704,590471168,8079441920,-23305003008,37313282048,-27609645056]),(⟨4,1,0⟩,[-8192,163840,-303104,-16023552,170000384,-797245440,2070986752,-2938568704,590471168,8079441920,-23305003008,37313282048,-27609645056]),(⟨5,0,0⟩,[0,-65536,2039808,-23396352,106029056,72613888,-2780217344,12421169152,-27241889792,31011962880,-11436974080,-9193848832,5049311232]),(⟨5,0,1⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨5,0,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,1,0⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨5,1,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,3,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,4,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,0,0⟩,[0,-16384,802816,-13271040,90505216,-137199616,-1580498944,10329391104,-28127461376,38242074624,-19792248832,-3709698048]),(⟨6,0,3⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨6,3,0⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808])]


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

noncomputable def partial12 : Poly := [(⟨1,0,2⟩,[0,65536,-2269184,33398784,-273989632,1373888512,-4259995648,7257735168,-1347977216,-24144461824,57359638528,-59238506496,19542130688,11111260160,-6202957824]),(⟨1,0,3⟩,[0,32768,-1236992,19505152,-168091648,863313920,-2640822272,4101849088,688209920,-16582852608,32716529664,-27182948352,3177947136,7021830144]),(⟨1,0,4⟩,[0,-65536,2039808,-25493504,162914304,-551288832,820592640,466354176,-3906355200,6042222592,-2775736320,-1640955904,1003118592]),(⟨1,0,5⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨1,1,0⟩,[0,0,262144,-9076736,133595136,-1095958528,5495554048,-17039982592,29030940672,-5391908864,-96577847296,229438554112,-236954025984,78168522752,44445040640,-24811831296]),(⟨1,1,1⟩,[0,0,131072,-4947968,78020608,-672366592,3453255680,-10563289088,16407396352,2752839680,-66331410432,130866118656,-108731793408,12711788544,28087320576]),(⟨1,1,2⟩,[0,32768,-1499136,27664384,-270065664,1514971136,-4845977600,7384219648,2553626624,-32208273408,56885420032,-38285893632,-3385876480,11034304512]),(⟨1,1,3⟩,[-8192,229376,-2670592,18972672,-110747648,560660480,-1961263104,3459973120,783818752,-15756853248,26259963904,-9585852416,-8632279040]),(⟨1,2,0⟩,[0,65536,-2138112,28450816,-195969024,701521920,-806739968,-3305553920,15059419136,-21391622144,-8971771904,71627612160,-89189662720,23823048704,21884362752]),(⟨1,2,1⟩,[0,0,-319488,9084928,-105046016,641048576,-2223751168,4147855360,-1900462080,-9796435968,26210508800,-34013306880,29927776256,-15715524608]),(⟨1,2,2⟩,[0,-131072,4079616,-50987008,325828608,-1102577664,1641185280,932708352,-7812710400,12084445184,-5551472640,-3281911808,2006237184]),(⟨1,2,3⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨1,3,0⟩,[0,32768,-1499136,27664384,-270065664,1514971136,-4845977600,7384219648,2553626624,-32208273408,56885420032,-38285893632,-3385876480,11034304512]),(⟨1,3,1⟩,[-8192,229376,-2605056,15761408,-55566336,104267776,11501568,-647168000,1696604160,-1626505216,-1707589632,6687457280,-5684338688]),(⟨1,3,2⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨1,3,5⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,4,0⟩,[0,-65536,1974272,-22282240,107732992,-94896128,-1152172032,4573495296,-4819140608,-8088125440,25191817216,-17914265600,-1944821760]),(⟨1,4,3⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨1,5,0⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨1,5,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,0,0⟩,[0,65536,-2138112,27811840,-171933696,314204160,2736873472,-23848714240,94359519232,-228194795520,349325238272,-313662808064,114331451392,39210115072,-35909328896,5108318208]),(⟨2,0,1⟩,[0,98304,-3440640,49905664,-383803392,1601912832,-2575687680,-8010203136,57715408896,-158885412864,244582236160,-200936620032,47293472768,38785531904,-11985641472]),(⟨2,0,2⟩,[0,0,-565248,18644992,-255844352,1890058240,-8114290688,20122238976,-24632082432,-2441609216,51330736128,-60350889984,12034613248,13217562624]),(⟨2,0,3⟩,[-8192,147456,204800,-21659648,181272576,-500727808,-881246208,9829744640,-28926091264,41661775872,-26915921920,5217615872,-4074291200]),(⟨2,0,4⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨2,1,0⟩,[0,98304,-3309568,44957696,-305782784,929546240,877568000,-18573492224,74122805248,-156132573184,178250825728,-70070501376,-61438320640,51497320448,16101679104]),(⟨2,1,1⟩,[-8192,245760,-3571712,35602432,-257466368,1248329728,-3650748416,5034246144,3000803328,-24579817472,39865319424,-24186437632,3076792320,-4012474368]),(⟨2,1,2⟩,[-16384,393216,-3170304,6029312,51781632,-342753280,843595776,-827981824,-513146880,2789212160,-6190915584,11733958656,-10365558784]),(⟨2,1,3⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨2,2,0⟩,[0,-32768,352256,8224768,-192798720,1667792896,-7697219584,20168245248,-27220754432,4344807424,44824715264,-67181248512,38784442368,-9519792128]),(⟨2,2,1⟩,[-16384,393216,-3170304,6029312,51781632,-342753280,843595776,-827981824,-513146880,2789212160,-6190915584,11733958656,-10365558784]),(⟨2,3,0⟩,[-8192,147456,204800,-21659648,181272576,-500727808,-881246208,9829744640,-28926091264,41661775872,-26915921920,5217615872,-4074291200]),(⟨2,3,1⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨2,3,3⟩,[32768,-720896,4587520,4194304,-150274048,511311872,-212467712,-1604845568,2232975360,-382140416]),(⟨2,3,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,4,0⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨2,4,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,0,0⟩,[0,98304,-3440640,47808512,-319578112,754401280,3809878016,-38656933888,156091236352,-371980697600,545242005504,-444823863296,109545594880,89379061760,-37005975552]),(⟨3,0,1⟩,[-8192,278528,-4489216,44974080,-285122560,970162176,-130940928,-14175010816,65949704192,-155125465088,204464619520,-122909409280,-17391804416,47048228864]),(⟨3,0,2⟩,[-8192,98304,1474560,-33128448,213377024,-374407168,-1948123136,12240355328,-29451640832,35427680256,-15920300032,-4147347456,368091136]),(⟨3,0,3⟩,[0,-16384,802816,-13271040,90505216,-137199616,-1580498944,10329391104,-28127461376,38242074624,-19792248832,-3709698048]),(⟨3,1,0⟩,[-8192,278528,-4751360,53133312,-387096576,1621819392,-2336096256,-10892640256,67815120896,-170750885888,228633509888,-134012354560,-23955628032,51060703232]),(⟨3,1,1⟩,[-24576,688128,-7553024,40992768,-104046592,-37421056,1273397248,-4699258880,7890034688,-1215791104,-23944445952,52329152512,-39981441024]),(⟨3,2,0⟩,[-8192,98304,1474560,-33128448,213377024,-374407168,-1948123136,12240355328,-29451640832,35427680256,-15920300032,-4147347456,368091136]),(⟨3,3,0⟩,[0,-16384,802816,-13271040,90505216,-137199616,-1580498944,10329391104,-28127461376,38242074624,-19792248832,-3709698048]),(⟨3,3,3⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨4,0,0⟩,[0,-32768,671744,-1908736,-52363264,526311424,-1536589824,-3142860800,35039936512,-109617987584,176707485696,-138721271808,15137898496,34519080960]),(⟨4,0,1⟩,[-8192,163840,-303104,-16023552,170000384,-797245440,2070986752,-2938568704,590471168,8079441920,-23305003008,37313282048,-27609645056]),(⟨4,0,2⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨4,0,5⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,1,0⟩,[-8192,163840,-368640,-12812288,114819072,-340852736,98222080,1168572416,-322314240,-6050906112,4662550528,21039972352,-30557585408]),(⟨4,1,3⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,2,0⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨4,2,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,3,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,4,0⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,5,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,0,0⟩,[0,-81920,2809856,-35323904,179953664,18907136,-4493557760,22431727616,-53958230016,68258021376,-33869570048,-9022734336,5656240128]),(⟨5,0,1⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨5,0,3⟩,[32768,-720896,4587520,4194304,-150274048,511311872,-212467712,-1604845568,2232975360,-382140416]),(⟨5,0,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,1,0⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨5,1,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,3,0⟩,[32768,-720896,4587520,4194304,-150274048,511311872,-212467712,-1604845568,2232975360,-382140416]),(⟨5,3,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,4,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,0,0⟩,[0,-16384,802816,-13271040,90505216,-137199616,-1580498944,10329391104,-28127461376,38242074624,-19792248832,-3709698048]),(⟨6,0,3⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨6,3,0⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808])]


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

noncomputable def partial8 : Poly := [(⟨0,2,1⟩,[0,65536,-2269184,33398784,-273989632,1373888512,-4259995648,7257735168,-1347977216,-24144461824,57359638528,-59238506496,19542130688,11111260160,-6202957824]),(⟨0,2,2⟩,[0,32768,-1236992,19505152,-168091648,863313920,-2640822272,4101849088,688209920,-16582852608,32716529664,-27182948352,3177947136,7021830144]),(⟨0,2,3⟩,[0,-65536,2039808,-25493504,162914304,-551288832,820592640,466354176,-3906355200,6042222592,-2775736320,-1640955904,1003118592]),(⟨0,2,4⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨0,3,0⟩,[0,65536,-2269184,31301632,-209764352,526376960,2125570048,-23388995584,97027850240,-237239746560,358019407872,-303125749760,81794252800,61704790016,-31223291904]),(⟨0,3,1⟩,[0,65536,-2473984,37961728,-300793856,1226194944,-1344765952,-10959552512,61736648704,-156924936192,223526338560,-159919226880,12637126656,42367008768]),(⟨0,3,2⟩,[-8192,163840,-565248,-7634944,50462720,176881664,-2768715776,11774001152,-25545285632,29385457664,-13144563712,-2506391552,-635027456]),(⟨0,3,3⟩,[0,-16384,802816,-13271040,90505216,-137199616,-1580498944,10329391104,-28127461376,38242074624,-19792248832,-3709698048]),(⟨0,4,0⟩,[0,32768,-1236992,18456576,-132702208,362881024,1296056320,-15061401600,61048438784,-140342083584,190809808896,-132736278528,9459179520,35345178624]),(⟨0,4,1⟩,[-8192,163840,-303104,-16023552,170000384,-797245440,2070986752,-2938568704,590471168,8079441920,-23305003008,37313282048,-27609645056]),(⟨0,5,0⟩,[0,-65536,2039808,-23396352,106029056,72613888,-2780217344,12421169152,-27241889792,31011962880,-11436974080,-9193848832,5049311232]),(⟨0,5,1⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨0,5,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨0,6,0⟩,[0,-16384,802816,-13271040,90505216,-137199616,-1580498944,10329391104,-28127461376,38242074624,-19792248832,-3709698048]),(⟨0,6,3⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨1,0,0⟩,[0,-65536,2531328,-41558016,375816192,-1970806784,5015035904,6127910912,-108458131456,478808162304,-1261690855424,2185911918592,-2436825088000,1502627651584,-165185806336,-352989822976,135005552640]),(⟨1,0,1⟩,[0,-32768,1630208,-33071104,362389504,-2342838272,8734867456,-12964724736,-41266954240,295394263040,-850137915392,1440024125440,-1436213698560,657659174912,101108596736,-177639899136]),(⟨1,0,2⟩,[0,131072,-4440064,61186048,-432300032,1516101632,-757129216,-16250159104,75037425664,-167723941888,201749463040,-89019768832,-68051918848,77513777152,51781632]),(⟨1,0,3⟩,[0,49152,-2367488,44441600,-428105728,2263556096,-5908938752,66404352,51470745600,-175500361728,295819370496,-256115302400,71953358848,27074568192]),(⟨1,0,4⟩,[0,-65536,1974272,-22282240,107732992,-94896128,-1152172032,4573495296,-4819140608,-8088125440,25191817216,-17914265600,-1944821760]),(⟨1,0,5⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨1,1,0⟩,[0,-32768,1630208,-33071104,362389504,-2342838272,8734867456,-12964724736,-41266954240,295394263040,-850137915392,1440024125440,-1436213698560,657659174912,101108596736,-177639899136]),(⟨1,1,1⟩,[8192,-262144,3670016,-32866304,234250240,-1363574784,5735923712,-14810808320,14829936640,33455013888,-137515139072,175487090688,-4532297728,-221989863424,179892600832]),(⟨1,1,2⟩,[0,0,-581632,17244160,-207020032,1292705792,-4428906496,7430225920,-35045376,-25421856768,50379399168,-45116252160,23363952640,-11703050240]),(⟨1,1,3⟩,[-8192,229376,-2670592,18972672,-110747648,560660480,-1961263104,3459973120,783818752,-15756853248,26259963904,-9585852416,-8632279040]),(⟨1,2,0⟩,[0,131072,-4440064,61186048,-432300032,1516101632,-757129216,-16250159104,75037425664,-167723941888,201749463040,-89019768832,-68051918848,77513777152,51781632]),(⟨1,2,1⟩,[0,32768,-1818624,36749312,-375111680,2156019712,-7069728768,11532075008,653164544,-42004709376,83095928832,-72299200512,26541899776,-4681220096]),(⟨1,2,2⟩,[-8192,98304,1474560,-35225600,270262272,-998309888,1652686848,285540352,-6116106240,10457939968,-7259062272,3405545472,-3678101504]),(⟨1,2,3⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨1,3,0⟩,[0,81920,-3604480,62898176,-560807936,2626437120,-4612882432,-14994997248,112519184384,-315842445312,486629179392,-388851580928,81412538368,62419746816]),(⟨1,3,1⟩,[-24576,688128,-7618560,44204032,-159227904,418971648,-699367424,-592117760,6977249280,-15346139136,4023107584,36055842816,-42929381376]),(⟨1,3,2⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨1,3,3⟩,[-32768,917504,-9371648,36962304,30998528,-773324800,2525233152,-2185494528,-5428772864,14425915392,-10099425280]),(⟨1,3,4⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨1,3,5⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,4,0⟩,[-8192,163840,-368640,-12812288,114819072,-340852736,98222080,1168572416,-322314240,-6050906112,4662550528,21039972352,-30557585408]),(⟨1,4,3⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨1,5,0⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨1,5,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,0,0⟩,[0,32768,-770048,3817472,56860672,-932675584,5976186880,-19773456384,24061624320,72591376384,-404234829824,896922763264,-1084928221184,618700767232,20754227200,-147719749632]),(⟨2,0,1⟩,[8192,-163840,98304,21987328,-227573760,910704640,-293019648,-12257722368,56137949184,-128183238656,173398507520,-156315648000,151492968448,-195916120064,139819638784]),(⟨2,0,2⟩,[0,-32768,352256,8224768,-192798720,1667792896,-7697219584,20168245248,-27220754432,4344807424,44824715264,-67181248512,38784442368,-9519792128]),(⟨2,0,3⟩,[-8192,147456,204800,-21659648,181272576,-500727808,-881246208,9829744640,-28926091264,41661775872,-26915921920,5217615872,-4074291200]),(⟨2,0,4⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨2,1,0⟩,[8192,-163840,98304,21987328,-227573760,910704640,-293019648,-12257722368,56137949184,-128183238656,173398507520,-156315648000,151492968448,-195916120064,139819638784]),(⟨2,1,1⟩,[-8192,212992,-2654208,25182208,-194420736,1026064384,-3233677312,5080252416,412131328,-17793400832,33359298560,-31016796160,29826621440,-26749829120]),(⟨2,1,2⟩,[-16384,393216,-3170304,6029312,51781632,-342753280,843595776,-827981824,-513146880,2789212160,-6190915584,11733958656,-10365558784]),(⟨2,1,3⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨2,2,0⟩,[0,-32768,352256,8224768,-192798720,1667792896,-7697219584,20168245248,-27220754432,4344807424,44824715264,-67181248512,38784442368,-9519792128]),(⟨2,2,1⟩,[-16384,327680,-1130496,-19464192,214695936,-894042112,1664188416,-361627648,-4419502080,8831434752,-8966651904,10093002752,-9362440192]),(⟨2,3,0⟩,[-8192,81920,2244608,-45056000,287301632,-428113920,-3661463552,22250913792,-56167981056,72673738752,-38352896000,-3976232960,975020032]),(⟨2,3,1⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨2,3,3⟩,[32768,-720896,4587520,4194304,-150274048,511311872,-212467712,-1604845568,2232975360,-382140416]),(⟨2,3,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,4,0⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨2,4,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,0,0⟩,[0,163840,-5742592,80543744,-555909120,1568980992,3859488768,-51601539072,216069242880,-518313017344,755963240448,-605471244288,130683338752,143069790208,-58838556672]),(⟨3,0,1⟩,[-8192,278528,-4751360,53133312,-387096576,1621819392,-2336096256,-10892640256,67815120896,-170750885888,228633509888,-134012354560,-23955628032,51060703232]),(⟨3,0,2⟩,[-8192,98304,1474560,-33128448,213377024,-374407168,-1948123136,12240355328,-29451640832,35427680256,-15920300032,-4147347456,368091136]),(⟨3,0,3⟩,[0,-16384,802816,-13271040,90505216,-137199616,-1580498944,10329391104,-28127461376,38242074624,-19792248832,-3709698048]),(⟨3,1,0⟩,[-8192,278528,-4751360,53133312,-387096576,1621819392,-2336096256,-10892640256,67815120896,-170750885888,228633509888,-134012354560,-23955628032,51060703232]),(⟨3,1,1⟩,[-24576,688128,-7553024,40992768,-104046592,-37421056,1273397248,-4699258880,7890034688,-1215791104,-23944445952,52329152512,-39981441024]),(⟨3,2,0⟩,[-8192,98304,1474560,-33128448,213377024,-374407168,-1948123136,12240355328,-29451640832,35427680256,-15920300032,-4147347456,368091136]),(⟨3,2,1⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨3,2,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,3,0⟩,[0,-32768,1605632,-26542080,181010432,-274399232,-3160997888,20658782208,-56254922752,76484149248,-39584497664,-7419396096]),(⟨3,3,3⟩,[65536,-1572864,11272192,-524288,-308936704,1134034944,-473169920,-3690463232,4671471616]),(⟨3,5,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,6,0⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨4,0,0⟩,[0,-16384,-196608,14868480,-210403328,1274896384,-2599550976,-10460676096,83957055488,-252910075904,415641436160,-356550680576,90477133824,50559344640]),(⟨4,0,1⟩,[-8192,163840,-368640,-12812288,114819072,-340852736,98222080,1168572416,-322314240,-6050906112,4662550528,21039972352,-30557585408]),(⟨4,0,2⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨4,0,3⟩,[-32768,917504,-9371648,36962304,30998528,-773324800,2525233152,-2185494528,-5428772864,14425915392,-10099425280]),(⟨4,0,4⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,0,5⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,1,0⟩,[-8192,163840,-368640,-12812288,114819072,-340852736,98222080,1168572416,-322314240,-6050906112,4662550528,21039972352,-30557585408]),(⟨4,1,3⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,2,0⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨4,2,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,3,0⟩,[-32768,917504,-9371648,36962304,30998528,-773324800,2525233152,-2185494528,-5428772864,14425915392,-10099425280]),(⟨4,3,1⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,3,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,4,0⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,5,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,0,0⟩,[0,-81920,2809856,-35323904,179953664,18907136,-4493557760,22431727616,-53958230016,68258021376,-33869570048,-9022734336,5656240128]),(⟨5,0,1⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨5,0,3⟩,[32768,-720896,4587520,4194304,-150274048,511311872,-212467712,-1604845568,2232975360,-382140416]),(⟨5,0,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,1,0⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨5,1,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,3,0⟩,[32768,-720896,4587520,4194304,-150274048,511311872,-212467712,-1604845568,2232975360,-382140416]),(⟨5,3,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,4,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,0,0⟩,[0,-16384,802816,-13271040,90505216,-137199616,-1580498944,10329391104,-28127461376,38242074624,-19792248832,-3709698048]),(⟨6,0,3⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨6,3,0⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808])]


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

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[0,-65536,2531328,-41558016,375816192,-1970806784,5015035904,6127910912,-108458131456,478808162304,-1261690855424,2185911918592,-2436825088000,1502627651584,-165185806336,-352989822976,135005552640]),(⟨0,1,1⟩,[0,-32768,1630208,-33071104,362389504,-2342838272,8734867456,-12964724736,-41266954240,295394263040,-850137915392,1440024125440,-1436213698560,657659174912,101108596736,-177639899136]),(⟨0,1,2⟩,[0,131072,-4440064,61186048,-432300032,1516101632,-757129216,-16250159104,75037425664,-167723941888,201749463040,-89019768832,-68051918848,77513777152,51781632]),(⟨0,1,3⟩,[0,49152,-2367488,44441600,-428105728,2263556096,-5908938752,66404352,51470745600,-175500361728,295819370496,-256115302400,71953358848,27074568192]),(⟨0,1,4⟩,[0,-65536,1974272,-22282240,107732992,-94896128,-1152172032,4573495296,-4819140608,-8088125440,25191817216,-17914265600,-1944821760]),(⟨0,1,5⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨0,2,0⟩,[0,32768,-770048,3817472,56860672,-932675584,5976186880,-19773456384,24061624320,72591376384,-404234829824,896922763264,-1084928221184,618700767232,20754227200,-147719749632]),(⟨0,2,1⟩,[8192,-163840,98304,21987328,-227573760,910704640,-293019648,-12257722368,56137949184,-128183238656,173398507520,-156315648000,151492968448,-195916120064,139819638784]),(⟨0,2,2⟩,[0,-32768,352256,8224768,-192798720,1667792896,-7697219584,20168245248,-27220754432,4344807424,44824715264,-67181248512,38784442368,-9519792128]),(⟨0,2,3⟩,[-8192,147456,204800,-21659648,181272576,-500727808,-881246208,9829744640,-28926091264,41661775872,-26915921920,5217615872,-4074291200]),(⟨0,2,4⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨0,3,0⟩,[0,163840,-5742592,80543744,-555909120,1568980992,3859488768,-51601539072,216069242880,-518313017344,755963240448,-605471244288,130683338752,143069790208,-58838556672]),(⟨0,3,1⟩,[-8192,278528,-4751360,53133312,-387096576,1621819392,-2336096256,-10892640256,67815120896,-170750885888,228633509888,-134012354560,-23955628032,51060703232]),(⟨0,3,2⟩,[-8192,98304,1474560,-33128448,213377024,-374407168,-1948123136,12240355328,-29451640832,35427680256,-15920300032,-4147347456,368091136]),(⟨0,3,3⟩,[0,-16384,802816,-13271040,90505216,-137199616,-1580498944,10329391104,-28127461376,38242074624,-19792248832,-3709698048]),(⟨0,4,0⟩,[0,-16384,-196608,14868480,-210403328,1274896384,-2599550976,-10460676096,83957055488,-252910075904,415641436160,-356550680576,90477133824,50559344640]),(⟨0,4,1⟩,[-8192,163840,-368640,-12812288,114819072,-340852736,98222080,1168572416,-322314240,-6050906112,4662550528,21039972352,-30557585408]),(⟨0,4,2⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨0,4,3⟩,[-32768,917504,-9371648,36962304,30998528,-773324800,2525233152,-2185494528,-5428772864,14425915392,-10099425280]),(⟨0,4,4⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨0,4,5⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨0,5,0⟩,[0,-81920,2809856,-35323904,179953664,18907136,-4493557760,22431727616,-53958230016,68258021376,-33869570048,-9022734336,5656240128]),(⟨0,5,1⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨0,5,3⟩,[32768,-720896,4587520,4194304,-150274048,511311872,-212467712,-1604845568,2232975360,-382140416]),(⟨0,5,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨0,6,0⟩,[0,-16384,802816,-13271040,90505216,-137199616,-1580498944,10329391104,-28127461376,38242074624,-19792248832,-3709698048]),(⟨0,6,3⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨1,0,0⟩,[0,-65536,2531328,-41558016,375816192,-1970806784,5015035904,6127910912,-108458131456,478808162304,-1261690855424,2185911918592,-2436825088000,1502627651584,-165185806336,-352989822976,135005552640]),(⟨1,0,1⟩,[0,-32768,1630208,-33071104,362389504,-2342838272,8734867456,-12964724736,-41266954240,295394263040,-850137915392,1440024125440,-1436213698560,657659174912,101108596736,-177639899136]),(⟨1,0,2⟩,[0,131072,-4440064,61186048,-432300032,1516101632,-757129216,-16250159104,75037425664,-167723941888,201749463040,-89019768832,-68051918848,77513777152,51781632]),(⟨1,0,3⟩,[0,49152,-2367488,44441600,-428105728,2263556096,-5908938752,66404352,51470745600,-175500361728,295819370496,-256115302400,71953358848,27074568192]),(⟨1,0,4⟩,[0,-65536,1974272,-22282240,107732992,-94896128,-1152172032,4573495296,-4819140608,-8088125440,25191817216,-17914265600,-1944821760]),(⟨1,0,5⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨1,1,0⟩,[0,-65536,2998272,-57065472,591183872,-3589718016,11974180864,-8889466880,-111564849152,596180434944,-1603697983488,2650609696768,-2635473371136,1237149827072,157772152832,-330467966976]),(⟨1,1,1⟩,[16384,-524288,7208960,-60784640,390479872,-2054782976,8018591744,-19058327552,13252476928,64157188096,-208698867712,220108062720,99667197952,-456691515392,331697881088]),(⟨1,1,2⟩,[0,0,-901120,26329088,-312066048,1933754368,-6652657664,11578081280,-1935507456,-35218292736,76589907968,-79129559040,53291728896,-27418574848]),(⟨1,1,3⟩,[-16384,458752,-5275648,34734080,-166313984,664928256,-1949761536,2812805120,2480422912,-17383358464,24552374272,-2898395136,-14316617728]),(⟨1,2,0⟩,[8192,-98304,-2203648,54722560,-463904768,1725284352,-243408896,-25202327552,116115955712,-274515558400,384119742464,-316963028992,172630712320,-142225391616,117987057664]),(⟨1,2,1⟩,[-8192,212992,-2916352,33341440,-296394752,1677721600,-5438832640,8362622976,2277548032,-33418821632,57528188928,-42119741440,23262797824,-22737354752]),(⟨1,2,2⟩,[-16384,327680,-1130496,-19464192,214695936,-894042112,1664188416,-361627648,-4419502080,8831434752,-8966651904,10093002752,-9362440192]),(⟨1,2,3⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨1,3,0⟩,[-8192,294912,-5619712,69910528,-545136640,2370404352,-3399057408,-18210455552,116732239872,-314042974208,467567460352,-351841763328,51383607296,67100966912]),(⟨1,3,1⟩,[-24576,688128,-7618560,44204032,-159227904,418971648,-699367424,-592117760,6977249280,-15346139136,4023107584,36055842816,-42929381376]),(⟨1,3,2⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨1,3,3⟩,[-32768,917504,-9371648,36962304,30998528,-773324800,2525233152,-2185494528,-5428772864,14425915392,-10099425280]),(⟨1,3,4⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨1,3,5⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,4,0⟩,[-8192,163840,-368640,-12812288,114819072,-340852736,98222080,1168572416,-322314240,-6050906112,4662550528,21039972352,-30557585408]),(⟨1,4,3⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨1,5,0⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨1,5,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,0,0⟩,[0,32768,-770048,3817472,56860672,-932675584,5976186880,-19773456384,24061624320,72591376384,-404234829824,896922763264,-1084928221184,618700767232,20754227200,-147719749632]),(⟨2,0,1⟩,[8192,-163840,98304,21987328,-227573760,910704640,-293019648,-12257722368,56137949184,-128183238656,173398507520,-156315648000,151492968448,-195916120064,139819638784]),(⟨2,0,2⟩,[0,-32768,352256,8224768,-192798720,1667792896,-7697219584,20168245248,-27220754432,4344807424,44824715264,-67181248512,38784442368,-9519792128]),(⟨2,0,3⟩,[-8192,147456,204800,-21659648,181272576,-500727808,-881246208,9829744640,-28926091264,41661775872,-26915921920,5217615872,-4074291200]),(⟨2,0,4⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨2,1,0⟩,[8192,-98304,-2203648,54722560,-463904768,1725284352,-243408896,-25202327552,116115955712,-274515558400,384119742464,-316963028992,172630712320,-142225391616,117987057664]),(⟨2,1,1⟩,[-8192,212992,-2916352,33341440,-296394752,1677721600,-5438832640,8362622976,2277548032,-33418821632,57528188928,-42119741440,23262797824,-22737354752]),(⟨2,1,2⟩,[-16384,327680,-1130496,-19464192,214695936,-894042112,1664188416,-361627648,-4419502080,8831434752,-8966651904,10093002752,-9362440192]),(⟨2,1,3⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨2,2,0⟩,[0,-98304,2260992,-12140544,-112459776,1831223296,-10529865728,32086786048,-53229256704,35068903424,30722392064,-73166241792,44463161344,-10345889792]),(⟨2,2,1⟩,[-16384,327680,-1130496,-19464192,214695936,-894042112,1664188416,-361627648,-4419502080,8831434752,-8966651904,10093002752,-9362440192]),(⟨2,3,0⟩,[-8192,81920,2244608,-45056000,287301632,-428113920,-3661463552,22250913792,-56167981056,72673738752,-38352896000,-3976232960,975020032]),(⟨2,3,1⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨2,3,3⟩,[32768,-720896,4587520,4194304,-150274048,511311872,-212467712,-1604845568,2232975360,-382140416]),(⟨2,3,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,4,0⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨2,4,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,0,0⟩,[0,163840,-5742592,80543744,-555909120,1568980992,3859488768,-51601539072,216069242880,-518313017344,755963240448,-605471244288,130683338752,143069790208,-58838556672]),(⟨3,0,1⟩,[-8192,278528,-4751360,53133312,-387096576,1621819392,-2336096256,-10892640256,67815120896,-170750885888,228633509888,-134012354560,-23955628032,51060703232]),(⟨3,0,2⟩,[-8192,98304,1474560,-33128448,213377024,-374407168,-1948123136,12240355328,-29451640832,35427680256,-15920300032,-4147347456,368091136]),(⟨3,0,3⟩,[0,-16384,802816,-13271040,90505216,-137199616,-1580498944,10329391104,-28127461376,38242074624,-19792248832,-3709698048]),(⟨3,1,0⟩,[-8192,294912,-5619712,69910528,-545136640,2370404352,-3399057408,-18210455552,116732239872,-314042974208,467567460352,-351841763328,51383607296,67100966912]),(⟨3,1,1⟩,[-24576,688128,-7618560,44204032,-159227904,418971648,-699367424,-592117760,6977249280,-15346139136,4023107584,36055842816,-42929381376]),(⟨3,1,2⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨3,1,3⟩,[-32768,917504,-9371648,36962304,30998528,-773324800,2525233152,-2185494528,-5428772864,14425915392,-10099425280]),(⟨3,1,4⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,1,5⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,2,0⟩,[-8192,81920,2244608,-45056000,287301632,-428113920,-3661463552,22250913792,-56167981056,72673738752,-38352896000,-3976232960,975020032]),(⟨3,2,1⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨3,2,3⟩,[32768,-720896,4587520,4194304,-150274048,511311872,-212467712,-1604845568,2232975360,-382140416]),(⟨3,2,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,3,0⟩,[0,-32768,1605632,-26542080,181010432,-274399232,-3160997888,20658782208,-56254922752,76484149248,-39584497664,-7419396096]),(⟨3,3,3⟩,[65536,-1572864,11272192,-524288,-308936704,1134034944,-473169920,-3690463232,4671471616]),(⟨3,4,0⟩,[-32768,917504,-9371648,36962304,30998528,-773324800,2525233152,-2185494528,-5428772864,14425915392,-10099425280]),(⟨3,4,1⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,4,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,5,0⟩,[32768,-720896,4587520,4194304,-150274048,511311872,-212467712,-1604845568,2232975360,-382140416]),(⟨3,5,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,6,0⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨4,0,0⟩,[0,-16384,-196608,14868480,-210403328,1274896384,-2599550976,-10460676096,83957055488,-252910075904,415641436160,-356550680576,90477133824,50559344640]),(⟨4,0,1⟩,[-8192,163840,-368640,-12812288,114819072,-340852736,98222080,1168572416,-322314240,-6050906112,4662550528,21039972352,-30557585408]),(⟨4,0,2⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨4,0,3⟩,[-32768,917504,-9371648,36962304,30998528,-773324800,2525233152,-2185494528,-5428772864,14425915392,-10099425280]),(⟨4,0,4⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,0,5⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,1,0⟩,[-8192,163840,-368640,-12812288,114819072,-340852736,98222080,1168572416,-322314240,-6050906112,4662550528,21039972352,-30557585408]),(⟨4,1,3⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,2,0⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨4,2,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,3,0⟩,[-32768,917504,-9371648,36962304,30998528,-773324800,2525233152,-2185494528,-5428772864,14425915392,-10099425280]),(⟨4,3,1⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,3,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,4,0⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,5,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,0,0⟩,[0,-81920,2809856,-35323904,179953664,18907136,-4493557760,22431727616,-53958230016,68258021376,-33869570048,-9022734336,5656240128]),(⟨5,0,1⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨5,0,3⟩,[32768,-720896,4587520,4194304,-150274048,511311872,-212467712,-1604845568,2232975360,-382140416]),(⟨5,0,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,1,0⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨5,1,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,3,0⟩,[32768,-720896,4587520,4194304,-150274048,511311872,-212467712,-1604845568,2232975360,-382140416]),(⟨5,3,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,4,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,0,0⟩,[0,-16384,802816,-13271040,90505216,-137199616,-1580498944,10329391104,-28127461376,38242074624,-19792248832,-3709698048]),(⟨6,0,3⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨6,3,0⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,-65536,2400256,-37019648,302727168,-1233297408,-228220928,33816133632,-219448098816,818210390016,-2048240656384,3540921851904,-4104365555712,2847651651584,-713953779712,-418422063104,301690601472,-47538634752]),(⟨0,0,1⟩,[0,-98304,3833856,-63078400,562454528,-2776907776,5054865408,27263205376,-247048503296,985302761472,-2476814123008,4150263906304,-4490210615296,2682322468864,-280331640832,-573755392000,188819914752]),(⟨0,0,2⟩,[0,98304,-2940928,32473088,-122191872,-611434496,8964038656,-45336133632,123220721664,-160295878656,-62012596224,609739571200,-1005473529856,683870732288,-26839113728,-140031983616]),(⟨0,0,3⟩,[0,180224,-6578176,95715328,-684785664,2019377152,4827815936,-68758601728,299305467904,-746636886016,1139900604416,-983092396032,304863641600,137617653760,-64486711296]),(⟨0,0,4⟩,[0,-16384,-196608,14868480,-210403328,1274896384,-2599550976,-10460676096,83957055488,-252910075904,415641436160,-356550680576,90477133824,50559344640]),(⟨0,0,5⟩,[0,-81920,2809856,-35323904,179953664,18907136,-4493557760,22431727616,-53958230016,68258021376,-33869570048,-9022734336,5656240128]),(⟨0,0,6⟩,[0,-16384,802816,-13271040,90505216,-137199616,-1580498944,10329391104,-28127461376,38242074624,-19792248832,-3709698048]),(⟨0,1,0⟩,[0,-98304,3833856,-63078400,562454528,-2776907776,5054865408,27263205376,-247048503296,985302761472,-2476814123008,4150263906304,-4490210615296,2682322468864,-280331640832,-573755392000,188819914752]),(⟨0,1,1⟩,[8192,-311296,5947392,-74039296,619388928,-3312746496,9518825472,1529053184,-138823704576,636674654208,-1608312209408,2517782052864,-2302994915328,825376440320,407455154176,-374031974400]),(⟨0,1,2⟩,[8192,-98304,-2203648,54722560,-463904768,1725284352,-243408896,-25202327552,116115955712,-274515558400,384119742464,-316963028992,172630712320,-142225391616,117987057664]),(⟨0,1,3⟩,[-8192,294912,-5619712,69910528,-545136640,2370404352,-3399057408,-18210455552,116732239872,-314042974208,467567460352,-351841763328,51383607296,67100966912]),(⟨0,1,4⟩,[-8192,163840,-368640,-12812288,114819072,-340852736,98222080,1168572416,-322314240,-6050906112,4662550528,21039972352,-30557585408]),(⟨0,1,5⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨0,2,0⟩,[0,98304,-2940928,32473088,-122191872,-611434496,8964038656,-45336133632,123220721664,-160295878656,-62012596224,609739571200,-1005473529856,683870732288,-26839113728,-140031983616]),(⟨0,2,1⟩,[8192,-98304,-2203648,54722560,-463904768,1725284352,-243408896,-25202327552,116115955712,-274515558400,384119742464,-316963028992,172630712320,-142225391616,117987057664]),(⟨0,2,2⟩,[0,-98304,2260992,-12140544,-112459776,1831223296,-10529865728,32086786048,-53229256704,35068903424,30722392064,-73166241792,44463161344,-10345889792]),(⟨0,2,3⟩,[-8192,81920,2244608,-45056000,287301632,-428113920,-3661463552,22250913792,-56167981056,72673738752,-38352896000,-3976232960,975020032]),(⟨0,2,4⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨0,3,0⟩,[0,180224,-6578176,95715328,-684785664,2019377152,4827815936,-68758601728,299305467904,-746636886016,1139900604416,-983092396032,304863641600,137617653760,-64486711296]),(⟨0,3,1⟩,[-8192,294912,-5619712,69910528,-545136640,2370404352,-3399057408,-18210455552,116732239872,-314042974208,467567460352,-351841763328,51383607296,67100966912]),(⟨0,3,2⟩,[-8192,81920,2244608,-45056000,287301632,-428113920,-3661463552,22250913792,-56167981056,72673738752,-38352896000,-3976232960,975020032]),(⟨0,3,3⟩,[-32768,819200,-6193152,-6094848,315817984,-1471217664,401276928,17549230080,-63895142400,98306129920,-57934643200,-3863150592]),(⟨0,3,4⟩,[-32768,917504,-9371648,36962304,30998528,-773324800,2525233152,-2185494528,-5428772864,14425915392,-10099425280]),(⟨0,3,5⟩,[32768,-720896,4587520,4194304,-150274048,511311872,-212467712,-1604845568,2232975360,-382140416]),(⟨0,3,6⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨0,4,0⟩,[0,-16384,-196608,14868480,-210403328,1274896384,-2599550976,-10460676096,83957055488,-252910075904,415641436160,-356550680576,90477133824,50559344640]),(⟨0,4,1⟩,[-8192,163840,-368640,-12812288,114819072,-340852736,98222080,1168572416,-322314240,-6050906112,4662550528,21039972352,-30557585408]),(⟨0,4,2⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨0,4,3⟩,[-32768,917504,-9371648,36962304,30998528,-773324800,2525233152,-2185494528,-5428772864,14425915392,-10099425280]),(⟨0,4,4⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨0,4,5⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨0,5,0⟩,[0,-81920,2809856,-35323904,179953664,18907136,-4493557760,22431727616,-53958230016,68258021376,-33869570048,-9022734336,5656240128]),(⟨0,5,1⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨0,5,3⟩,[32768,-720896,4587520,4194304,-150274048,511311872,-212467712,-1604845568,2232975360,-382140416]),(⟨0,5,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨0,6,0⟩,[0,-16384,802816,-13271040,90505216,-137199616,-1580498944,10329391104,-28127461376,38242074624,-19792248832,-3709698048]),(⟨0,6,3⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨1,0,0⟩,[0,-98304,3833856,-63078400,562454528,-2776907776,5054865408,27263205376,-247048503296,985302761472,-2476814123008,4150263906304,-4490210615296,2682322468864,-280331640832,-573755392000,188819914752]),(⟨1,0,1⟩,[8192,-311296,5947392,-74039296,619388928,-3312746496,9518825472,1529053184,-138823704576,636674654208,-1608312209408,2517782052864,-2302994915328,825376440320,407455154176,-374031974400]),(⟨1,0,2⟩,[8192,-98304,-2203648,54722560,-463904768,1725284352,-243408896,-25202327552,116115955712,-274515558400,384119742464,-316963028992,172630712320,-142225391616,117987057664]),(⟨1,0,3⟩,[-8192,294912,-5619712,69910528,-545136640,2370404352,-3399057408,-18210455552,116732239872,-314042974208,467567460352,-351841763328,51383607296,67100966912]),(⟨1,0,4⟩,[-8192,163840,-368640,-12812288,114819072,-340852736,98222080,1168572416,-322314240,-6050906112,4662550528,21039972352,-30557585408]),(⟨1,0,5⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨1,1,0⟩,[8192,-311296,5947392,-74039296,619388928,-3312746496,9518825472,1529053184,-138823704576,636674654208,-1608312209408,2517782052864,-2302994915328,825376440320,407455154176,-374031974400]),(⟨1,1,1⟩,[24576,-786432,10616832,-83755008,468688896,-2073624576,6848004096,-12742557696,-4732379136,92106522624,-213551185920,133862916096,312598487040,-704104955904,455415840768]),(⟨1,1,2⟩,[-8192,212992,-2916352,33341440,-296394752,1677721600,-5438832640,8362622976,2277548032,-33418821632,57528188928,-42119741440,23262797824,-22737354752]),(⟨1,1,3⟩,[-24576,688128,-7618560,44204032,-159227904,418971648,-699367424,-592117760,6977249280,-15346139136,4023107584,36055842816,-42929381376]),(⟨1,2,0⟩,[8192,-98304,-2203648,54722560,-463904768,1725284352,-243408896,-25202327552,116115955712,-274515558400,384119742464,-316963028992,172630712320,-142225391616,117987057664]),(⟨1,2,1⟩,[-8192,212992,-2916352,33341440,-296394752,1677721600,-5438832640,8362622976,2277548032,-33418821632,57528188928,-42119741440,23262797824,-22737354752]),(⟨1,2,2⟩,[-16384,327680,-1130496,-19464192,214695936,-894042112,1664188416,-361627648,-4419502080,8831434752,-8966651904,10093002752,-9362440192]),(⟨1,2,3⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨1,3,0⟩,[-8192,294912,-5619712,69910528,-545136640,2370404352,-3399057408,-18210455552,116732239872,-314042974208,467567460352,-351841763328,51383607296,67100966912]),(⟨1,3,1⟩,[-24576,688128,-7618560,44204032,-159227904,418971648,-699367424,-592117760,6977249280,-15346139136,4023107584,36055842816,-42929381376]),(⟨1,3,2⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨1,3,3⟩,[-32768,917504,-9371648,36962304,30998528,-773324800,2525233152,-2185494528,-5428772864,14425915392,-10099425280]),(⟨1,3,4⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨1,3,5⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,4,0⟩,[-8192,163840,-368640,-12812288,114819072,-340852736,98222080,1168572416,-322314240,-6050906112,4662550528,21039972352,-30557585408]),(⟨1,4,3⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨1,5,0⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨1,5,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,0,0⟩,[0,98304,-2940928,32473088,-122191872,-611434496,8964038656,-45336133632,123220721664,-160295878656,-62012596224,609739571200,-1005473529856,683870732288,-26839113728,-140031983616]),(⟨2,0,1⟩,[8192,-98304,-2203648,54722560,-463904768,1725284352,-243408896,-25202327552,116115955712,-274515558400,384119742464,-316963028992,172630712320,-142225391616,117987057664]),(⟨2,0,2⟩,[0,-98304,2260992,-12140544,-112459776,1831223296,-10529865728,32086786048,-53229256704,35068903424,30722392064,-73166241792,44463161344,-10345889792]),(⟨2,0,3⟩,[-8192,81920,2244608,-45056000,287301632,-428113920,-3661463552,22250913792,-56167981056,72673738752,-38352896000,-3976232960,975020032]),(⟨2,0,4⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨2,1,0⟩,[8192,-98304,-2203648,54722560,-463904768,1725284352,-243408896,-25202327552,116115955712,-274515558400,384119742464,-316963028992,172630712320,-142225391616,117987057664]),(⟨2,1,1⟩,[-8192,212992,-2916352,33341440,-296394752,1677721600,-5438832640,8362622976,2277548032,-33418821632,57528188928,-42119741440,23262797824,-22737354752]),(⟨2,1,2⟩,[-16384,327680,-1130496,-19464192,214695936,-894042112,1664188416,-361627648,-4419502080,8831434752,-8966651904,10093002752,-9362440192]),(⟨2,1,3⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨2,2,0⟩,[0,-98304,2260992,-12140544,-112459776,1831223296,-10529865728,32086786048,-53229256704,35068903424,30722392064,-73166241792,44463161344,-10345889792]),(⟨2,2,1⟩,[-16384,327680,-1130496,-19464192,214695936,-894042112,1664188416,-361627648,-4419502080,8831434752,-8966651904,10093002752,-9362440192]),(⟨2,3,0⟩,[-8192,81920,2244608,-45056000,287301632,-428113920,-3661463552,22250913792,-56167981056,72673738752,-38352896000,-3976232960,975020032]),(⟨2,3,1⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨2,3,3⟩,[32768,-720896,4587520,4194304,-150274048,511311872,-212467712,-1604845568,2232975360,-382140416]),(⟨2,3,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,4,0⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨2,4,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,0,0⟩,[0,180224,-6578176,95715328,-684785664,2019377152,4827815936,-68758601728,299305467904,-746636886016,1139900604416,-983092396032,304863641600,137617653760,-64486711296]),(⟨3,0,1⟩,[-8192,294912,-5619712,69910528,-545136640,2370404352,-3399057408,-18210455552,116732239872,-314042974208,467567460352,-351841763328,51383607296,67100966912]),(⟨3,0,2⟩,[-8192,81920,2244608,-45056000,287301632,-428113920,-3661463552,22250913792,-56167981056,72673738752,-38352896000,-3976232960,975020032]),(⟨3,0,3⟩,[-32768,819200,-6193152,-6094848,315817984,-1471217664,401276928,17549230080,-63895142400,98306129920,-57934643200,-3863150592]),(⟨3,0,4⟩,[-32768,917504,-9371648,36962304,30998528,-773324800,2525233152,-2185494528,-5428772864,14425915392,-10099425280]),(⟨3,0,5⟩,[32768,-720896,4587520,4194304,-150274048,511311872,-212467712,-1604845568,2232975360,-382140416]),(⟨3,0,6⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨3,1,0⟩,[-8192,294912,-5619712,69910528,-545136640,2370404352,-3399057408,-18210455552,116732239872,-314042974208,467567460352,-351841763328,51383607296,67100966912]),(⟨3,1,1⟩,[-24576,688128,-7618560,44204032,-159227904,418971648,-699367424,-592117760,6977249280,-15346139136,4023107584,36055842816,-42929381376]),(⟨3,1,2⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨3,1,3⟩,[-32768,917504,-9371648,36962304,30998528,-773324800,2525233152,-2185494528,-5428772864,14425915392,-10099425280]),(⟨3,1,4⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,1,5⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,2,0⟩,[-8192,81920,2244608,-45056000,287301632,-428113920,-3661463552,22250913792,-56167981056,72673738752,-38352896000,-3976232960,975020032]),(⟨3,2,1⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨3,2,3⟩,[32768,-720896,4587520,4194304,-150274048,511311872,-212467712,-1604845568,2232975360,-382140416]),(⟨3,2,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,3,0⟩,[-32768,819200,-6193152,-6094848,315817984,-1471217664,401276928,17549230080,-63895142400,98306129920,-57934643200,-3863150592]),(⟨3,3,1⟩,[-32768,917504,-9371648,36962304,30998528,-773324800,2525233152,-2185494528,-5428772864,14425915392,-10099425280]),(⟨3,3,2⟩,[32768,-720896,4587520,4194304,-150274048,511311872,-212467712,-1604845568,2232975360,-382140416]),(⟨3,3,3⟩,[98304,-2359296,16908288,-786432,-463405056,1701052416,-709754880,-5535694848,7007207424]),(⟨3,4,0⟩,[-32768,917504,-9371648,36962304,30998528,-773324800,2525233152,-2185494528,-5428772864,14425915392,-10099425280]),(⟨3,4,1⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,4,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,5,0⟩,[32768,-720896,4587520,4194304,-150274048,511311872,-212467712,-1604845568,2232975360,-382140416]),(⟨3,5,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,6,0⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨4,0,0⟩,[0,-16384,-196608,14868480,-210403328,1274896384,-2599550976,-10460676096,83957055488,-252910075904,415641436160,-356550680576,90477133824,50559344640]),(⟨4,0,1⟩,[-8192,163840,-368640,-12812288,114819072,-340852736,98222080,1168572416,-322314240,-6050906112,4662550528,21039972352,-30557585408]),(⟨4,0,2⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨4,0,3⟩,[-32768,917504,-9371648,36962304,30998528,-773324800,2525233152,-2185494528,-5428772864,14425915392,-10099425280]),(⟨4,0,4⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,0,5⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,1,0⟩,[-8192,163840,-368640,-12812288,114819072,-340852736,98222080,1168572416,-322314240,-6050906112,4662550528,21039972352,-30557585408]),(⟨4,1,3⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,2,0⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨4,2,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,3,0⟩,[-32768,917504,-9371648,36962304,30998528,-773324800,2525233152,-2185494528,-5428772864,14425915392,-10099425280]),(⟨4,3,1⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,3,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,4,0⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,5,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,0,0⟩,[0,-81920,2809856,-35323904,179953664,18907136,-4493557760,22431727616,-53958230016,68258021376,-33869570048,-9022734336,5656240128]),(⟨5,0,1⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨5,0,3⟩,[32768,-720896,4587520,4194304,-150274048,511311872,-212467712,-1604845568,2232975360,-382140416]),(⟨5,0,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,1,0⟩,[0,-16384,802816,-13795328,114098176,-493191168,1026785280,-228196352,-3532587008,6991888384,-4068327424,-736985088]),(⟨5,1,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,3,0⟩,[32768,-720896,4587520,4194304,-150274048,511311872,-212467712,-1604845568,2232975360,-382140416]),(⟨5,3,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,4,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,0,0⟩,[0,-16384,802816,-13271040,90505216,-137199616,-1580498944,10329391104,-28127461376,38242074624,-19792248832,-3709698048]),(⟨6,0,3⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808]),(⟨6,3,0⟩,[32768,-786432,5636096,-262144,-154468352,567017472,-236584960,-1845231616,2335735808])]


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
    (Poly.add (Poly.scale (K.ofRat r588) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 3 9).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r587*r587 : ℚ)=r588 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 3 9 r587 r587 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 3=9 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 3 9).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C090

#print axioms Coulomb8.Columns.C090.sound
