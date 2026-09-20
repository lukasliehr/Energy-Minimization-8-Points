import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C103

def r0 : ℚ := { num := -98304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 589824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -1605632, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 901382144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -6917554176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 37373509632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -8518402048, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 399709995008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -753440686080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 846063992832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -220456124416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -867942072320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 1309874552832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -668992634880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := -37248925696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := 115828621312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := -2099773440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 655360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -93978624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 1124827136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -8792113152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 6759120896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -179017842688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 473168248832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -832564854784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 820252639232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -27863875584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := -1051734016000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := 1236571652096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -437542191104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -122337984512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 9573662720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -7045120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 110755840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -1002897408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 5712904192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -20634763264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 42906812416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -25044582400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -2286485504, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 305853202432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -262160646144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -1816854528, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 271918432256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -12209061888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -722862080, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -9240576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 178192384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := -1898119168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := 1787691008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := -53456797696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 147733217280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -246008905728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 175431942144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 139782979584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -378084327424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 223824379904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 15802826752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -3505127424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 1933312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := -720896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -10452992, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 2276950016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -13346865152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 6408241152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -85848948736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 72028618752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := 34194292736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := -112788832256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 54372761600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 1553956864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := 4653056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := -83066880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := 758382592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := -3921346560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := 11568545792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := -17106141184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := 3268673536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 23936663552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -23949017088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 173899776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := 44040192, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 983040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -3866624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 297533440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -1696858112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 5324800000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -8421507072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 3045851136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 8339062784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -472449024, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -63111168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -163840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := 19300352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -210894848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := 1654292480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := -563970048, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 41056108544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -127803588608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 39667269632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := -378308165632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := 199347896320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 278952280064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -583226654720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 326048645120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 9979068416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -2057830400, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 1966080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 5832704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -322994176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 3105882112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -15688302592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 47858974720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -12696092672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 89298436096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -17659002880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := -9655877632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := 14857961472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := -15343812608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := 1317109760, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := -65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := 2195456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := -32997376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := 299630592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := -1842970624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 7998504960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := -24322441216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := 48947789824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := -54645227520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := 6285721600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := 62778933248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -60250128384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := -1027702784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := 2565177344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 32768, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := -819200, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := 143687680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := -46956544, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := 2510880768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := -3721461760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -135462912, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 20775108608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -710508544, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 12148113408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 252805120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -1048576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 13467648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -88211456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 297074688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -342884352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := -848625664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 3088842752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := -314998784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -414187520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := 581206016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := -655360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -327680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 7274496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := -62128128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := 250347520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := -387317760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -464388096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 2451308544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -2263089152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := -1498218496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 21037056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := -196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 7208960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -110166016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := 912654336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := -4436918272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := 12539658240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -17586847744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 34340864, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 4556521472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -674889728, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := 426049536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := 124649472, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -18350080, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -1343488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := -2621440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := 385646592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := -2733375488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := 9909764096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := -18740150272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := 13627359232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 9308864512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -22142681088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 2258108416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := -175996928, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := 65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := -2097152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := 589824, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := -230555648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := 1189216256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := -4079484928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := 8952348672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -10665328640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 1681719296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := 10879500288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := -7926382592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -282198016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -98304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := 19365888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := -234946560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := 1632436224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := -7159382016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := 2847375360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := -29998055424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := -6045696000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := 8255864832, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -310718201856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 39179059200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := 11707023360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := -7572848640, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := 271810560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := -32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 65536, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := -15794176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := 17498112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := -567771136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := 1554513920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := -273809408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -2385903616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 14323056640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := -3304652800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := 795410432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := 4139712512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := -603488256, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := 4587520, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := 786432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -19922944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 208404480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -1170997248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := 217579520, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := -768606208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := -3936878592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := 31133794304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := -49442717696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := 13954449408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := 6381895680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := -46923776, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := 393216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := -12976128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := 176685056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := -1275723776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := 5148770304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -1496580096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := 2443706368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := 35942825984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := -73420898304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := 49175199744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := 517996544, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -11665408, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := -655360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := 1409024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 61210624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -662372352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := 426508288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := -864223232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := 386138112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := 22372581376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -38730858496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := 2498527232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := 7733248, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := -393216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := 11272192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := -124256256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := 37748736, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := -196870144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := -350748672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := 5965873152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := -987758592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := 1703936, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := 1835008, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := 11534336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := -2621440, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := 38797312, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := -1361313792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -573571072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := 6062342144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := -850395136, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := -393216, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := 393216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -19398656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := 36175872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := 170131456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := -890503168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := 1337458688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := -108527616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -3266445312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := 8576958464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := -67108864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -3145728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := 1572864, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := -84934656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := -26476544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := 657457152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -765984768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := -9437184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := 1179648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -36175872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 448266240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -2878341120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 9985327104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -15602810880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := -8108113920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := 73732718592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := -107494637568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := 5751963648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 25165824, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := 131072, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := -56623104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := 196608000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := -1609826304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := 4181721088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := -4056416256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := -627834880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := 474087424, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -29360128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -6291456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 3145728, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := -169869312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := -52953088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := 1314914304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := -1531969536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -18874368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := -49152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := 294912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := -802816, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := 450691072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := -3458777088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := 18686754816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := -4259201024, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := 199854997504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := -376720343040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := 423031996416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := -110228062208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := -433971036160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := 654937276416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := -334496317440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := -18624462848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := 57914310656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := -1049886720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := 327680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := -46989312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := 562413568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := -4396056576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := 3379560448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := -89508921344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := 236584124416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -416282427392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := 410126319616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := -13931937792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := -525867008000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := 618285826048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := -218771095552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := -61168992256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := 4786831360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := 98304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := -3522560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := 55377920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := -501448704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := 2856452096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := -10317381632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := 21453406208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := -12522291200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := -1143242752, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := 152926601216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := -131080323072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := -908427264, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := 135959216128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := -6104530944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := -361431040, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := -4620288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := 89096192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := -949059584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := 893845504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := -26728398848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := 73866608640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := -123004452864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := 87715971072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := 69891489792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := -189042163712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := 111912189952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := 7901413376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := -1752563712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 966656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := -360448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := -5226496, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := 1138475008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := -6673432576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := 3204120576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := -42924474368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := 36014309376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := 17097146368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := -56394416128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := 27186380800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := 776978432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := 2326528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := -41533440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := 379191296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := -1960673280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := 5784272896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := -8553070592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := 1634336768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := 11968331776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := -11974508544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := 86949888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := 22020096, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := 491520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := -1933312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := 148766720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := -848429056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := 2662400000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := -4210753536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := 1522925568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := 4169531392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := -236224512, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := -31555584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := 16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := -81920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := 9650176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := -105447424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := 827146240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := -281985024, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := 20528054272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := -63901794304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := 19833634816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := -189154082816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := 99673948160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := 139476140032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := -291613327360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := 163024322560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := 4989534208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := -1028915200, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := 2916352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := -161497088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := 1552941056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := -7844151296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := 23929487360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := -6348046336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := 44649218048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := -8829501440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r450 : ℚ := { num := -4827938816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r451 : ℚ := { num := 7428980736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r452 : ℚ := { num := -7671906304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r453 : ℚ := { num := 658554880, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r454 : ℚ := { num := 1097728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r455 : ℚ := { num := -16498688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r456 : ℚ := { num := 149815296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r457 : ℚ := { num := -921485312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r458 : ℚ := { num := 3999252480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r459 : ℚ := { num := -12161220608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r460 : ℚ := { num := 24473894912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r461 : ℚ := { num := -27322613760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r462 : ℚ := { num := 3142860800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r463 : ℚ := { num := 31389466624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r464 : ℚ := { num := -30125064192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r465 : ℚ := { num := -513851392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r466 : ℚ := { num := 1282588672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r467 : ℚ := { num := 16384, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r468 : ℚ := { num := -409600, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r469 : ℚ := { num := 71843840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r470 : ℚ := { num := -23478272, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r471 : ℚ := { num := 1255440384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r472 : ℚ := { num := -1860730880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r473 : ℚ := { num := -67731456, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r474 : ℚ := { num := 10387554304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r475 : ℚ := { num := -355254272, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r476 : ℚ := { num := 6074056704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r477 : ℚ := { num := 126402560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r478 : ℚ := { num := -524288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r479 : ℚ := { num := 6733824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r480 : ℚ := { num := -44105728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r481 : ℚ := { num := 148537344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r482 : ℚ := { num := -171442176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r483 : ℚ := { num := -424312832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r484 : ℚ := { num := 1544421376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r485 : ℚ := { num := -157499392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r486 : ℚ := { num := -207093760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r487 : ℚ := { num := 290603008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r488 : ℚ := { num := -327680, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r489 : ℚ := { num := -163840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r490 : ℚ := { num := 3637248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r491 : ℚ := { num := -31064064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r492 : ℚ := { num := 125173760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r493 : ℚ := { num := -193658880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r494 : ℚ := { num := -232194048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r495 : ℚ := { num := 1225654272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r496 : ℚ := { num := -1131544576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r497 : ℚ := { num := -749109248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r498 : ℚ := { num := 10518528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r499 : ℚ := { num := 3604480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r500 : ℚ := { num := -55083008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r501 : ℚ := { num := 456327168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r502 : ℚ := { num := -2218459136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r503 : ℚ := { num := 6269829120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r504 : ℚ := { num := -8793423872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r505 : ℚ := { num := 17170432, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r506 : ℚ := { num := 2278260736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r507 : ℚ := { num := -337444864, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r508 : ℚ := { num := 213024768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r509 : ℚ := { num := 62324736, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r510 : ℚ := { num := -9175040, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r511 : ℚ := { num := -671744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r512 : ℚ := { num := -1310720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r513 : ℚ := { num := 192823296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r514 : ℚ := { num := -1366687744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r515 : ℚ := { num := 4954882048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r516 : ℚ := { num := -9370075136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r517 : ℚ := { num := 6813679616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r518 : ℚ := { num := 4654432256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r519 : ℚ := { num := -11071340544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r520 : ℚ := { num := 1129054208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r521 : ℚ := { num := -87998464, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r522 : ℚ := { num := 294912, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r523 : ℚ := { num := -115277824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r524 : ℚ := { num := 594608128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r525 : ℚ := { num := -2039742464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r526 : ℚ := { num := 4476174336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r527 : ℚ := { num := -5332664320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r528 : ℚ := { num := 840859648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r529 : ℚ := { num := 5439750144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r530 : ℚ := { num := -3963191296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r531 : ℚ := { num := -141099008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r532 : ℚ := { num := -49152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r533 : ℚ := { num := 9682944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r534 : ℚ := { num := -117473280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r535 : ℚ := { num := 816218112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r536 : ℚ := { num := -3579691008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r537 : ℚ := { num := 1423687680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r538 : ℚ := { num := -14999027712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r539 : ℚ := { num := -3022848000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r540 : ℚ := { num := 4127932416, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r541 : ℚ := { num := -155359100928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r542 : ℚ := { num := 19589529600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r543 : ℚ := { num := 5853511680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r544 : ℚ := { num := -3786424320, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r545 : ℚ := { num := 135905280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r546 : ℚ := { num := -16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r547 : ℚ := { num := -7897088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r548 : ℚ := { num := 8749056, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r549 : ℚ := { num := -283885568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r550 : ℚ := { num := 777256960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r551 : ℚ := { num := -136904704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r552 : ℚ := { num := -1192951808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r553 : ℚ := { num := 7161528320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r554 : ℚ := { num := -1652326400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r555 : ℚ := { num := 397705216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r556 : ℚ := { num := 2069856256, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r557 : ℚ := { num := -301744128, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r558 : ℚ := { num := 2293760, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r559 : ℚ := { num := -9961472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r560 : ℚ := { num := 104202240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r561 : ℚ := { num := -585498624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r562 : ℚ := { num := 108789760, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r563 : ℚ := { num := -384303104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r564 : ℚ := { num := -1968439296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r565 : ℚ := { num := 15566897152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r566 : ℚ := { num := -24721358848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r567 : ℚ := { num := 6977224704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r568 : ℚ := { num := 3190947840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r569 : ℚ := { num := -23461888, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r570 : ℚ := { num := -6488064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r571 : ℚ := { num := 88342528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r572 : ℚ := { num := -637861888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r573 : ℚ := { num := 2574385152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r574 : ℚ := { num := -748290048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r575 : ℚ := { num := 1221853184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r576 : ℚ := { num := 17971412992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r577 : ℚ := { num := -36710449152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r578 : ℚ := { num := 24587599872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r579 : ℚ := { num := 258998272, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r580 : ℚ := { num := -5832704, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r581 : ℚ := { num := 704512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r582 : ℚ := { num := 30605312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r583 : ℚ := { num := -331186176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r584 : ℚ := { num := 213254144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r585 : ℚ := { num := -432111616, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r586 : ℚ := { num := 193069056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r587 : ℚ := { num := 11186290688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r588 : ℚ := { num := -19365429248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r589 : ℚ := { num := 1249263616, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r590 : ℚ := { num := 3866624, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r591 : ℚ := { num := 5636096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r592 : ℚ := { num := 18874368, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r593 : ℚ := { num := -98435072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r594 : ℚ := { num := -175374336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r595 : ℚ := { num := 2982936576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r596 : ℚ := { num := -493879296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r597 : ℚ := { num := 851968, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r598 : ℚ := { num := 917504, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r599 : ℚ := { num := 5767168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r600 : ℚ := { num := -1310720, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r601 : ℚ := { num := 19398656, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r602 : ℚ := { num := -680656896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r603 : ℚ := { num := -286785536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r604 : ℚ := { num := 3031171072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r605 : ℚ := { num := -425197568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r606 : ℚ := { num := -196608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r607 : ℚ := { num := 196608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r608 : ℚ := { num := -9699328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r609 : ℚ := { num := 18087936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r610 : ℚ := { num := 85065728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r611 : ℚ := { num := -445251584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r612 : ℚ := { num := 668729344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r613 : ℚ := { num := -54263808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r614 : ℚ := { num := -1633222656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r615 : ℚ := { num := 4288479232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r616 : ℚ := { num := -33554432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r617 : ℚ := { num := -1572864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r618 : ℚ := { num := 786432, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r619 : ℚ := { num := -42467328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r620 : ℚ := { num := -13238272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r621 : ℚ := { num := 328728576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r622 : ℚ := { num := -382992384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r623 : ℚ := { num := -4718592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r624 : ℚ := { num := 589824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r625 : ℚ := { num := -18087936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r626 : ℚ := { num := 224133120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r627 : ℚ := { num := -1439170560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r628 : ℚ := { num := 4992663552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r629 : ℚ := { num := -7801405440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r630 : ℚ := { num := -4054056960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r631 : ℚ := { num := 36866359296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r632 : ℚ := { num := -53747318784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r633 : ℚ := { num := 2875981824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r634 : ℚ := { num := 12582912, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r635 : ℚ := { num := 65536, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r636 : ℚ := { num := -28311552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r637 : ℚ := { num := 98304000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r638 : ℚ := { num := -804913152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r639 : ℚ := { num := 2090860544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r640 : ℚ := { num := -2028208128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r641 : ℚ := { num := -313917440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r642 : ℚ := { num := 237043712, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r643 : ℚ := { num := -14680064, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r644 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r645 : ℚ := { num := 1, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16],[0,r0,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31],[0,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46],[0,r32,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59],[0,r0,r60,r61,r62,r63,r64,r65,r66,r67,r68,r69,r70,r71],[0,r0,r72,r73,r74,r75,r76,r77,r78,r79,r80,r81,r82],[0,0,r83,r84,r85,r86,r87,r88,r89,r90,r91,r92],[],[],[],[],[],[],[r93,r94,r95,r96,r97,r98,r99,r100,r101,r102,r103,r104,r105,r106,r107,r108],[0,r109,r110,r111,r112,r113,r114,r115,r116,r117,r118,r119,r120,r121,r122],[r123,r124,r125,r126,r127,r128,r129,r130,r131,r132,r133,r134,r135,r136],[0,r137,r138,r139,r140,r141,r142,r143,r144,r145,r146,r147,-1998848],[r93,r148,r149,r150,r151,r152,r153,r154,r155,r156,r157,r158],[0,r159,r160,r161,r162,r163,r164,r165,r166,r167,r168],[],[],[],[],[],[0,r169,r170,r171,r172,r173,r174,r175,r176,r177,r178,r179,r180,r181],[0,r182,r183,r184,r185,r186,r187,r188,r189,r190,r191,r192,r193],[],[],[],[],[],[],[],[r194,r195,r196,r197,r198,r199,r200,r201,r202,r203,r204,r205],[0,r159,r160,r161,r162,r163,r164,r165,r166,r167,r168],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,r206,r207,r208,r209,r210,r211,r212,r213,r214,r215,r216,r217,r218,r219],[r220,r221,r222,r223,r224,r225,r226,r227,r228,r229,r230,r231,r232,r233],[0,r234,r235,r236,r237,r238,r239,r240,r241,r242,r243,r244,r245],[],[],[],[],[],[],[],[0,r246,r247,r248,r249,r250,r251,r252,r253,r254,r255,r256,r257],[r93,r258,r259,r260,r261,r262,r263,r264,r265,r266,r267,r268],[0,r269,r270,r271,r272,r273,r274,r275,r276,r277,r278],[0,r269,r279,r280,r281,r282,r283,r284,r285,r286],[],[],[],[],[r109,r287,r288,r289,r290,r291,r292,r293,r294,r295,r296],[],[r182,r297,r298,r299,r300,r301,r302,r303,131072],[],[],[],[],[],[],[],[],[],[0,r304,r305,r306,r307,r308,r309,r310,r311,r312,r313,r314],[r315,r316,r317,r318,r288,r319,r320,r321,r322,r323,r324],[0,r269,r279,r280,r281,r282,r283,r284,r285,r286],[r325,r326,r327,r328,r329,r330,r331,r332,262144],[],[],[],[],[r182,r297,r298,r299,r300,r301,r302,r303,131072],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,r333,r334,r335,r336,r337,r338,r339,r340,r341,r342,r343,r344,r345,r346,r347,r348,r349]),(⟨0,0,1⟩,[0,r333,r350,r351,r352,r353,r354,r355,r356,r357,r358,r359,r360,r361,r362,r363,r364]),(⟨0,0,2⟩,[0,r365,r366,r367,r368,r369,r370,r371,r372,r373,r374,r375,r376,r377,r378,r379]),(⟨0,0,3⟩,[0,r365,r380,r381,r382,r383,r384,r385,r386,r387,r388,r389,r390,r391,r392]),(⟨0,0,4⟩,[0,r333,r393,r394,r395,r396,r397,r398,r399,r400,r401,r402,r403,r404]),(⟨0,0,5⟩,[0,r333,r405,r406,r407,r408,r409,r410,r411,r412,r413,r414,r415]),(⟨0,0,6⟩,[0,0,r416,r417,r418,r419,r420,r421,r422,r423,r424,r425]),(⟨0,1,0⟩,[0,r333,r350,r351,r352,r353,r354,r355,r356,r357,r358,r359,r360,r361,r362,r363,r364]),(⟨0,1,1⟩,[r426,r427,r428,r429,r430,r431,r432,r433,r434,r435,r436,r437,r438,r439,r440,r441]),(⟨0,1,2⟩,[0,r123,r83,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451,r452,r453]),(⟨0,1,3⟩,[r220,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466]),(⟨0,1,4⟩,[0,r467,r468,r469,r470,r471,r472,r473,r474,r475,r476,r477,-999424]),(⟨0,1,5⟩,[r426,r478,r479,r480,r481,r482,r483,r484,r485,r486,r487,r488]),(⟨0,1,6⟩,[0,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498]),(⟨0,2,0⟩,[0,r365,r366,r367,r368,r369,r370,r371,r372,r373,r374,r375,r376,r377,r378,r379]),(⟨0,2,1⟩,[0,r123,r83,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451,r452,r453]),(⟨0,2,2⟩,[0,r0,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508,r509,r510]),(⟨0,2,3⟩,[0,r194,r511,r512,r513,r514,r515,r516,r517,r518,r519,r520,r521]),(⟨0,3,0⟩,[0,r365,r380,r381,r382,r383,r384,r385,r386,r387,r388,r389,r390,r391,r392]),(⟨0,3,1⟩,[r220,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466]),(⟨0,3,2⟩,[0,r194,r511,r512,r513,r514,r515,r516,r517,r518,r519,r520,r521]),(⟨0,3,3⟩,[r93,r148,r522,r523,r524,r525,r526,r527,r528,r529,r530,r531]),(⟨0,3,4⟩,[0,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498]),(⟨0,4,0⟩,[0,r333,r393,r394,r395,r396,r397,r398,r399,r400,r401,r402,r403,r404]),(⟨0,4,1⟩,[0,r467,r468,r469,r470,r471,r472,r473,r474,r475,r476,r477,-999424]),(⟨0,4,3⟩,[0,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498]),(⟨0,5,0⟩,[0,r333,r405,r406,r407,r408,r409,r410,r411,r412,r413,r414,r415]),(⟨0,5,1⟩,[r426,r478,r479,r480,r481,r482,r483,r484,r485,r486,r487,r488]),(⟨0,6,0⟩,[0,0,r416,r417,r418,r419,r420,r421,r422,r423,r424,r425]),(⟨0,6,1⟩,[0,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498]),(⟨1,0,0⟩,[0,r333,r350,r351,r352,r353,r354,r355,r356,r357,r358,r359,r360,r361,r362,r363,r364]),(⟨1,0,1⟩,[r426,r427,r428,r429,r430,r431,r432,r433,r434,r435,r436,r437,r438,r439,r440,r441]),(⟨1,0,2⟩,[0,r123,r83,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451,r452,r453]),(⟨1,0,3⟩,[r220,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466]),(⟨1,0,4⟩,[0,r467,r468,r469,r470,r471,r472,r473,r474,r475,r476,r477,-999424]),(⟨1,0,5⟩,[r426,r478,r479,r480,r481,r482,r483,r484,r485,r486,r487,r488]),(⟨1,0,6⟩,[0,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498]),(⟨1,1,0⟩,[r426,r427,r428,r429,r430,r431,r432,r433,r434,r435,r436,r437,r438,r439,r440,r441]),(⟨1,1,1⟩,[0,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543,r544,r545]),(⟨1,1,2⟩,[r546,r137,r547,r548,r549,r550,r551,r552,r553,r554,r555,r556,r557,r558]),(⟨1,1,3⟩,[0,r246,r559,r560,r561,r562,r563,r564,r565,r566,r567,r568,r569]),(⟨1,2,0⟩,[0,r123,r83,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451,r452,r453]),(⟨1,2,1⟩,[r546,r137,r547,r548,r549,r550,r551,r552,r553,r554,r555,r556,r557,r558]),(⟨1,2,2⟩,[0,r32,r570,r571,r572,r573,r574,r575,r576,r577,r578,r579,r580]),(⟨1,2,3⟩,[r426,r159,r581,r582,r583,r584,r585,r586,r587,r588,r589,r590]),(⟨1,2,4⟩,[0,r169,r591,r161,r592,r593,r594,r595,r596,r597,r598]),(⟨1,2,5⟩,[0,r169,r599,r600,r601,r602,r603,r604,r605,r606]),(⟨1,3,0⟩,[r220,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466]),(⟨1,3,1⟩,[0,r246,r559,r560,r561,r562,r563,r564,r565,r566,r567,r568,r569]),(⟨1,3,2⟩,[r426,r159,r581,r582,r583,r584,r585,r586,r587,r588,r589,r590]),(⟨1,3,3⟩,[r123,r607,r608,r609,r610,r611,r612,r613,r614,r615,r616]),(⟨1,3,5⟩,[r194,r617,r618,r619,r620,r621,r622,r623,65536]),(⟨1,4,0⟩,[0,r467,r468,r469,r470,r471,r472,r473,r474,r475,r476,r477,-999424]),(⟨1,4,2⟩,[0,r169,r591,r161,r592,r593,r594,r595,r596,r597,r598]),(⟨1,5,0⟩,[r426,r478,r479,r480,r481,r482,r483,r484,r485,r486,r487,r488]),(⟨1,5,2⟩,[0,r169,r599,r600,r601,r602,r603,r604,r605,r606]),(⟨1,5,3⟩,[r194,r617,r618,r619,r620,r621,r622,r623,65536]),(⟨1,6,0⟩,[0,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498]),(⟨2,0,0⟩,[0,r365,r366,r367,r368,r369,r370,r371,r372,r373,r374,r375,r376,r377,r378,r379]),(⟨2,0,1⟩,[0,r123,r83,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451,r452,r453]),(⟨2,0,2⟩,[0,r0,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508,r509,r510]),(⟨2,0,3⟩,[0,r194,r511,r512,r513,r514,r515,r516,r517,r518,r519,r520,r521]),(⟨2,1,0⟩,[0,r123,r83,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451,r452,r453]),(⟨2,1,1⟩,[r546,r137,r547,r548,r549,r550,r551,r552,r553,r554,r555,r556,r557,r558]),(⟨2,1,2⟩,[0,r32,r570,r571,r572,r573,r574,r575,r576,r577,r578,r579,r580]),(⟨2,1,3⟩,[r426,r159,r581,r582,r583,r584,r585,r586,r587,r588,r589,r590]),(⟨2,1,4⟩,[0,r169,r591,r161,r592,r593,r594,r595,r596,r597,r598]),(⟨2,1,5⟩,[0,r169,r599,r600,r601,r602,r603,r604,r605,r606]),(⟨2,2,0⟩,[0,r0,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508,r509,r510]),(⟨2,2,1⟩,[0,r32,r570,r571,r572,r573,r574,r575,r576,r577,r578,r579,r580]),(⟨2,2,2⟩,[0,r624,r625,r626,r627,r628,r629,r630,r631,r632,r633,r634]),(⟨2,2,3⟩,[r109,r635,r636,r637,r608,r638,r639,r640,r641,r642,r643]),(⟨2,2,4⟩,[0,r169,r599,r600,r601,r602,r603,r604,r605,r606]),(⟨2,2,5⟩,[r182,r297,r298,r299,r300,r301,r302,r303,131072]),(⟨2,3,0⟩,[0,r194,r511,r512,r513,r514,r515,r516,r517,r518,r519,r520,r521]),(⟨2,3,1⟩,[r426,r159,r581,r582,r583,r584,r585,r586,r587,r588,r589,r590]),(⟨2,3,2⟩,[r109,r635,r636,r637,r608,r638,r639,r640,r641,r642,r643]),(⟨2,3,4⟩,[r194,r617,r618,r619,r620,r621,r622,r623,65536]),(⟨2,4,1⟩,[0,r169,r591,r161,r592,r593,r594,r595,r596,r597,r598]),(⟨2,4,2⟩,[0,r169,r599,r600,r601,r602,r603,r604,r605,r606]),(⟨2,4,3⟩,[r194,r617,r618,r619,r620,r621,r622,r623,65536]),(⟨2,5,1⟩,[0,r169,r599,r600,r601,r602,r603,r604,r605,r606]),(⟨2,5,2⟩,[r182,r297,r298,r299,r300,r301,r302,r303,131072]),(⟨3,0,0⟩,[0,r365,r380,r381,r382,r383,r384,r385,r386,r387,r388,r389,r390,r391,r392]),(⟨3,0,1⟩,[r220,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466]),(⟨3,0,2⟩,[0,r194,r511,r512,r513,r514,r515,r516,r517,r518,r519,r520,r521]),(⟨3,0,3⟩,[r93,r148,r522,r523,r524,r525,r526,r527,r528,r529,r530,r531]),(⟨3,0,4⟩,[0,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498]),(⟨3,1,0⟩,[r220,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466]),(⟨3,1,1⟩,[0,r246,r559,r560,r561,r562,r563,r564,r565,r566,r567,r568,r569]),(⟨3,1,2⟩,[r426,r159,r581,r582,r583,r584,r585,r586,r587,r588,r589,r590]),(⟨3,1,3⟩,[r123,r607,r608,r609,r610,r611,r612,r613,r614,r615,r616]),(⟨3,1,5⟩,[r194,r617,r618,r619,r620,r621,r622,r623,65536]),(⟨3,2,0⟩,[0,r194,r511,r512,r513,r514,r515,r516,r517,r518,r519,r520,r521]),(⟨3,2,1⟩,[r426,r159,r581,r582,r583,r584,r585,r586,r587,r588,r589,r590]),(⟨3,2,2⟩,[r109,r635,r636,r637,r608,r638,r639,r640,r641,r642,r643]),(⟨3,2,4⟩,[r194,r617,r618,r619,r620,r621,r622,r623,65536]),(⟨3,3,0⟩,[r93,r148,r522,r523,r524,r525,r526,r527,r528,r529,r530,r531]),(⟨3,3,1⟩,[r123,r607,r608,r609,r610,r611,r612,r613,r614,r615,r616]),(⟨3,4,0⟩,[0,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498]),(⟨3,4,2⟩,[r194,r617,r618,r619,r620,r621,r622,r623,65536]),(⟨3,5,1⟩,[r194,r617,r618,r619,r620,r621,r622,r623,65536]),(⟨4,0,0⟩,[0,r333,r393,r394,r395,r396,r397,r398,r399,r400,r401,r402,r403,r404]),(⟨4,0,1⟩,[0,r467,r468,r469,r470,r471,r472,r473,r474,r475,r476,r477,-999424]),(⟨4,0,3⟩,[0,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498]),(⟨4,1,0⟩,[0,r467,r468,r469,r470,r471,r472,r473,r474,r475,r476,r477,-999424]),(⟨4,1,2⟩,[0,r169,r591,r161,r592,r593,r594,r595,r596,r597,r598]),(⟨4,2,1⟩,[0,r169,r591,r161,r592,r593,r594,r595,r596,r597,r598]),(⟨4,2,2⟩,[0,r169,r599,r600,r601,r602,r603,r604,r605,r606]),(⟨4,2,3⟩,[r194,r617,r618,r619,r620,r621,r622,r623,65536]),(⟨4,3,0⟩,[0,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498]),(⟨4,3,2⟩,[r194,r617,r618,r619,r620,r621,r622,r623,65536]),(⟨5,0,0⟩,[0,r333,r405,r406,r407,r408,r409,r410,r411,r412,r413,r414,r415]),(⟨5,0,1⟩,[r426,r478,r479,r480,r481,r482,r483,r484,r485,r486,r487,r488]),(⟨5,1,0⟩,[r426,r478,r479,r480,r481,r482,r483,r484,r485,r486,r487,r488]),(⟨5,1,2⟩,[0,r169,r599,r600,r601,r602,r603,r604,r605,r606]),(⟨5,1,3⟩,[r194,r617,r618,r619,r620,r621,r622,r623,65536]),(⟨5,2,1⟩,[0,r169,r599,r600,r601,r602,r603,r604,r605,r606]),(⟨5,2,2⟩,[r182,r297,r298,r299,r300,r301,r302,r303,131072]),(⟨5,3,1⟩,[r194,r617,r618,r619,r620,r621,r622,r623,65536]),(⟨6,0,0⟩,[0,0,r416,r417,r418,r419,r420,r421,r422,r423,r424,r425]),(⟨6,0,1⟩,[0,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498]),(⟨6,1,0⟩,[0,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,-384,8064,-64256,246656,-476544,385152,5632,-79744]),(⟨0,0,1⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨0,0,2⟩,[0,384,-6400,33024,-52224,4480,12544]),(⟨0,0,3⟩,[0,384,-6656,34048,-49664,-2688]),(⟨0,1,0⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨0,1,1⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨0,1,3⟩,[-128,1536,-3840,-4608,15232]),(⟨0,2,0⟩,[0,384,-6400,33024,-52224,4480,12544]),(⟨0,3,0⟩,[0,384,-6656,34048,-49664,-2688]),(⟨0,3,1⟩,[-128,1536,-3840,-4608,15232]),(⟨1,0,0⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨1,0,1⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨1,0,3⟩,[-128,1536,-3840,-4608,15232]),(⟨1,1,0⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨1,3,0⟩,[-128,1536,-3840,-4608,15232]),(⟨2,0,0⟩,[0,384,-6400,33024,-52224,4480,12544]),(⟨3,0,0⟩,[0,384,-6656,34048,-49664,-2688]),(⟨3,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨3,1,0⟩,[-128,1536,-3840,-4608,15232])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[128,-2688,24576,-125568,372480,-579456,211968,627840,-719744,92160]),(⟨0,0,1⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920]),(⟨0,0,2⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨0,0,3⟩,[0,1280,-13056,47616,-60928,-24320,82176]),(⟨0,1,0⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920]),(⟨0,2,0⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨0,3,0⟩,[0,1280,-13056,47616,-60928,-24320,82176]),(⟨1,0,0⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920]),(⟨1,2,2⟩,[-512,6144,-15360,-18432,60928]),(⟨2,0,0⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨2,1,2⟩,[-512,6144,-15360,-18432,60928]),(⟨2,2,1⟩,[-512,6144,-15360,-18432,60928]),(⟨3,0,0⟩,[0,1280,-13056,47616,-60928,-24320,82176])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 4 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r644) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 12 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r644) sourceRight))).isZero := by decide +kernel

noncomputable def partial19 : Poly := []

theorem partial_sound19 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 19)
      sourceRight).eval u v t=partial19.eval u v t := by rfl

noncomputable def chunk16 : Poly := [(⟨3,0,0⟩,[0,384,-6656,34048,-49664,-2688]),(⟨3,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨3,1,0⟩,[-128,1536,-3840,-4608,15232])]

noncomputable def partial16 : Poly := [(⟨3,0,0⟩,[0,49152,-1884160,31686656,-309673984,1948729344,-8190394368,22790602752,-39060406272,30538678272,17233100800,-56870076416,37195595776,-2642362368,-247726080]),(⟨3,0,1⟩,[-16384,540672,-8110080,74383360,-463798272,2027012096,-6137675776,12227837952,-13730070528,2451161088,15032467456,-18213306368,5189763072,2355118080]),(⟨3,0,2⟩,[0,65536,-1163264,4030464,48709632,-540540928,2314240000,-5016059904,4911300608,346226688,-5906546688,7840301056,-5342740480]),(⟨3,0,3⟩,[16384,-524288,7225344,-57638912,297304064,-1019871232,2238087168,-2666332160,420429824,2719875072,-1981595648,-493846528]),(⟨3,0,4⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨3,1,0⟩,[-16384,540672,-8110080,74383360,-463798272,2027012096,-6137675776,12227837952,-13730070528,2451161088,15032467456,-18213306368,5189763072,2355118080]),(⟨3,1,1⟩,[0,229376,-5996544,64716800,-372736000,1187971072,-1658781696,-1634009088,10358685696,-14627799040,1806336000,14589460480,-10781818880]),(⟨3,1,2⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨3,1,3⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨3,2,0⟩,[0,65536,-1163264,4030464,48709632,-540540928,2314240000,-5016059904,4911300608,346226688,-5906546688,7840301056,-5342740480]),(⟨3,2,1⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨3,3,0⟩,[16384,-524288,7225344,-57638912,297304064,-1019871232,2238087168,-2666332160,420429824,2719875072,-1981595648,-493846528]),(⟨3,3,1⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨3,4,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨4,0,0⟩,[0,0,-344064,10829824,-143212544,1052721152,-4743135232,13386547200,-22316351488,15782412288,11791482880,-30739251200,16577576960,951336960]),(⟨4,0,1⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨4,1,0⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨4,2,2⟩,[0,-196608,5767168,-64225280,329777152,-680656896,-286785536,3031171072,-2976382976,-163774464]),(⟨4,2,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,3,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,0,0⟩,[0,-49152,1835008,-28327936,235077632,-1134526464,3143630848,-4199055360,-268042240,7660126208,-6809714688,545570816,48168960]),(⟨5,0,1⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨5,1,0⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨5,1,2⟩,[0,-196608,5767168,-64225280,329777152,-680656896,-286785536,3031171072,-2976382976,-163774464]),(⟨5,1,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,2,1⟩,[0,-196608,5767168,-64225280,329777152,-680656896,-286785536,3031171072,-2976382976,-163774464]),(⟨5,2,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨5,3,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨6,0,0⟩,[0,0,491520,-13533184,148766720,-848429056,2662400000,-4210753536,1522925568,4169531392,-4015816704,-220889088]),(⟨6,0,1⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨6,1,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832])]


theorem partial_checked16 :
    (Poly.add (Poly.add (Poly.mul chunk16 sourceRight) partial19)
      (Poly.scale (K.ofRat (-1)) partial16)).isZero := by decide +kernel

theorem partial_sound16 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 16)
      sourceRight).eval u v t=partial16.eval u v t := by
  change (Poly.mul (chunk16++(sourceLeft.drop 19))
    sourceRight).eval u v t=partial16.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound19 partial_checked16 u v t


noncomputable def chunk12 : Poly := [(⟨1,0,3⟩,[-128,1536,-3840,-4608,15232]),(⟨1,1,0⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨1,3,0⟩,[-128,1536,-3840,-4608,15232]),(⟨2,0,0⟩,[0,384,-6400,33024,-52224,4480,12544])]

noncomputable def partial12 : Poly := [(⟨1,0,3⟩,[-16384,540672,-7766016,63553536,-320585728,974290944,-1394540544,-1158709248,8586280960,-13331251200,3240984576,12525944832,-11387813888,1403781120]),(⟨1,0,4⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨1,0,5⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨1,0,6⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨1,1,0⟩,[16384,-573440,8962048,-82870272,502054912,-2060337152,5587222528,-8450408448,-1141915648,38614777856,-90007453696,87274782720,13752811520,-111861022720,82522259456,-9826467840]),(⟨1,1,1⟩,[0,-114688,3227648,-39157760,272072704,-1193230336,3321937920,-4999675904,-1007616000,23391617024,-51786366976,45708902400,13658193920,-61844930560,37736366080]),(⟨1,1,2⟩,[-16384,557056,-7897088,61243392,-283885568,777256960,-958332928,-1192951808,7161528320,-11566284800,2783936512,14488993792,-14785462272,1910702080]),(⟨1,1,3⟩,[0,278528,-6963200,71843840,-399130624,1255440384,-1860730880,-1151434752,10387554304,-17407459328,6074056704,15041904640,-14152843264]),(⟨1,2,0⟩,[0,-114688,3227648,-39157760,272072704,-1193230336,3321937920,-4999675904,-1007616000,23391617024,-51786366976,45708902400,13658193920,-61844930560,37736366080]),(⟨1,2,3⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨1,3,0⟩,[-32768,1097728,-15663104,124796928,-604471296,1751547904,-2352873472,-2351661056,15747809280,-24897536000,6024921088,27014938624,-26173276160,3314483200]),(⟨1,3,1⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨1,3,2⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨1,3,3⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨1,4,0⟩,[0,278528,-6963200,71843840,-399130624,1255440384,-1860730880,-1151434752,10387554304,-17407459328,6074056704,15041904640,-14152843264]),(⟨1,5,0⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨1,6,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨2,0,0⟩,[0,49152,-1851392,30867456,-300957696,1899216896,-8047034368,22724739072,-39958118400,33060569088,16382148608,-63466045440,46103052288,-161792000,-8615591936,1156055040]),(⟨2,0,1⟩,[0,0,-344064,10600448,-139051008,1023131648,-4649582592,13344669696,-22899949568,17290592256,11556274176,-34823290880,21184593920,3078799360,-4439572480]),(⟨2,0,2⟩,[0,-49152,1802240,-27541504,228163584,-1109229568,3134914560,-4396711936,145948672,7973912576,-8267399168,745586688,1526956032,-224788480]),(⟨2,0,3⟩,[0,114688,-2506752,19152896,-42254336,-232161280,1811251200,-5171019776,7081721856,-3005693952,-4261625856,7357808640,-4360093696]),(⟨2,1,0⟩,[0,-114688,2883584,-28557312,133021696,-170098688,-1327644672,8344993792,-23907565568,40682209280,-40230092800,10885611520,34842787840,-58766131200,33296793600]),(⟨2,2,0⟩,[0,-49152,1802240,-27541504,228163584,-1109229568,3134914560,-4396711936,145948672,7973912576,-8267399168,745586688,1526956032,-224788480]),(⟨2,2,5⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,3,0⟩,[0,114688,-2506752,19152896,-42254336,-232161280,1811251200,-5171019776,7081721856,-3005693952,-4261625856,7357808640,-4360093696]),(⟨2,3,2⟩,[-65536,1703936,-16973824,80216064,-165281792,-57933824,1133117440,-2505572352,629866496,5786697728,-6496387072]),(⟨2,5,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,0,0⟩,[0,49152,-2228224,42287104,-448724992,2971860992,-12839976960,36135272448,-61960355840,47829270528,28789374976,-91693367296,58380189696,436436992,-4687298560]),(⟨3,0,1⟩,[-16384,540672,-8110080,74383360,-463798272,2027012096,-6137675776,12227837952,-13730070528,2451161088,15032467456,-18213306368,5189763072,2355118080]),(⟨3,0,2⟩,[0,65536,-1163264,4030464,48709632,-540540928,2314240000,-5016059904,4911300608,346226688,-5906546688,7840301056,-5342740480]),(⟨3,0,3⟩,[32768,-1048576,13959168,-101744640,445841408,-1191313408,1813774336,-1121910784,-682065920,1270218752,52625408,-766803968]),(⟨3,0,4⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨3,1,0⟩,[-32768,1097728,-16007168,135626752,-747683840,2804269056,-7096008704,11034886144,-6568542208,-9115123712,17816403968,-3724312576,-9595699200,4265820160]),(⟨3,1,1⟩,[0,229376,-5996544,64716800,-372736000,1187971072,-1658781696,-1634009088,10358685696,-14627799040,1806336000,14589460480,-10781818880]),(⟨3,1,2⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨3,1,3⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨3,1,5⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,2,0⟩,[0,65536,-1163264,4030464,48709632,-540540928,2314240000,-5016059904,4911300608,346226688,-5906546688,7840301056,-5342740480]),(⟨3,2,1⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨3,2,2⟩,[-65536,1507328,-11337728,18087936,155582464,-746979328,957743104,477364224,-2827288576,5828444160,-5732106240]),(⟨3,2,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,3,0⟩,[32768,-1048576,13959168,-101744640,445841408,-1191313408,1813774336,-1121910784,-682065920,1270218752,52625408,-766803968]),(⟨3,3,1⟩,[-65536,1540096,-13336576,49152000,-40108032,-251592704,900923392,-1279918080,-501678080,5037588480,-5244682240]),(⟨3,4,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨3,4,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,5,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,0,0⟩,[0,-49152,1458176,-16711680,84951040,-56508416,-1608220672,8989835264,-22170402816,23756324864,3524083712,-29993664512,18104532992,726548480]),(⟨4,0,1⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨4,0,3⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨4,1,0⟩,[0,278528,-6963200,71843840,-399130624,1255440384,-1860730880,-1151434752,10387554304,-17407459328,6074056704,15041904640,-14152843264]),(⟨4,1,2⟩,[0,-196608,5636096,-62128128,320864256,-689045504,-175374336,2982936576,-3457155072,41746432,764280832]),(⟨4,2,1⟩,[0,-196608,5636096,-62128128,320864256,-689045504,-175374336,2982936576,-3457155072,41746432,764280832]),(⟨4,2,2⟩,[0,-196608,5767168,-64225280,329777152,-680656896,-286785536,3031171072,-2976382976,-163774464]),(⟨4,2,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,3,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨4,3,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,0,0⟩,[0,-49152,2326528,-41533440,379191296,-1960673280,5784272896,-8553070592,1634336768,11968331776,-11974508544,608649216,1078984704]),(⟨5,0,1⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨5,1,0⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨5,1,2⟩,[0,-196608,5767168,-64225280,329777152,-680656896,-286785536,3031171072,-2976382976,-163774464]),(⟨5,1,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,2,1⟩,[0,-196608,5767168,-64225280,329777152,-680656896,-286785536,3031171072,-2976382976,-163774464]),(⟨5,2,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨5,3,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨6,0,0⟩,[0,0,491520,-13533184,148766720,-848429056,2662400000,-4210753536,1522925568,4169531392,-4015816704,-220889088]),(⟨6,0,1⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨6,1,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832])]


theorem partial_checked12 :
    (Poly.add (Poly.add (Poly.mul chunk12 sourceRight) partial16)
      (Poly.scale (K.ofRat (-1)) partial12)).isZero := by decide +kernel

theorem partial_sound12 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 12)
      sourceRight).eval u v t=partial12.eval u v t := by
  change (Poly.mul (chunk12++(sourceLeft.drop 16))
    sourceRight).eval u v t=partial12.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound16 partial_checked12 u v t


noncomputable def chunk8 : Poly := [(⟨0,3,0⟩,[0,384,-6656,34048,-49664,-2688]),(⟨0,3,1⟩,[-128,1536,-3840,-4608,15232]),(⟨1,0,0⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨1,0,1⟩,[128,-1792,7808,-13824,2432,62720,-106624])]

noncomputable def partial8 : Poly := [(⟨0,3,0⟩,[0,49152,-1884160,31686656,-309673984,1948729344,-8190394368,22790602752,-39060406272,30538678272,17233100800,-56870076416,37195595776,-2642362368,-247726080]),(⟨0,3,1⟩,[-16384,540672,-8110080,74383360,-463798272,2027012096,-6137675776,12227837952,-13730070528,2451161088,15032467456,-18213306368,5189763072,2355118080]),(⟨0,3,2⟩,[0,65536,-1163264,4030464,48709632,-540540928,2314240000,-5016059904,4911300608,346226688,-5906546688,7840301056,-5342740480]),(⟨0,3,3⟩,[16384,-524288,7225344,-57638912,297304064,-1019871232,2238087168,-2666332160,420429824,2719875072,-1981595648,-493846528]),(⟨0,3,4⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨0,4,0⟩,[0,0,-344064,10829824,-143212544,1052721152,-4743135232,13386547200,-22316351488,15782412288,11791482880,-30739251200,16577576960,951336960]),(⟨0,4,1⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨0,5,0⟩,[0,-49152,1835008,-28327936,235077632,-1134526464,3143630848,-4199055360,-268042240,7660126208,-6809714688,545570816,48168960]),(⟨0,5,1⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨0,6,0⟩,[0,0,491520,-13533184,148766720,-848429056,2662400000,-4210753536,1522925568,4169531392,-4015816704,-220889088]),(⟨0,6,1⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨1,0,0⟩,[0,-49152,1949696,-34897920,374292480,-2680045568,13444743168,-47995879424,120343658496,-199749353472,177260904448,29281714176,-273646731264,279970070528,-77968637952,-29523705856,5284823040]),(⟨1,0,1⟩,[16384,-573440,9306112,-94158848,664600576,-3427041280,13057638400,-36176101376,68846764032,-75269652480,4833247232,113375461376,-138930257920,25581649920,58724499456,-30121656320]),(⟨1,0,2⟩,[0,-65536,1327104,-7684096,-22446080,529809408,-3194568704,10584817664,-21536374784,27358625792,-20385775616,1027719168,30818271232,-56782143488,36708761600]),(⟨1,0,3⟩,[-32768,1097728,-16154624,138985472,-778272768,2946531328,-7418085376,11087347712,-5006262272,-12639551488,19597983744,614187008,-17091428352,8026783744]),(⟨1,0,4⟩,[0,278528,-6963200,71843840,-399130624,1255440384,-1860730880,-1151434752,10387554304,-17407459328,6074056704,15041904640,-14152843264]),(⟨1,0,5⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨1,0,6⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨1,1,0⟩,[16384,-573440,9306112,-94158848,664600576,-3427041280,13057638400,-36176101376,68846764032,-75269652480,4833247232,113375461376,-138930257920,25581649920,58724499456,-30121656320]),(⟨1,1,1⟩,[0,-229376,6455296,-78315520,544145408,-2386460672,6643875840,-9999351808,-2015232000,46783234048,-103572733952,91417804800,27316387840,-123689861120,75472732160]),(⟨1,1,2⟩,[-16384,557056,-7897088,61243392,-283885568,777256960,-958332928,-1192951808,7161528320,-11566284800,2783936512,14488993792,-14785462272,1910702080]),(⟨1,1,3⟩,[0,278528,-6963200,71843840,-399130624,1255440384,-1860730880,-1151434752,10387554304,-17407459328,6074056704,15041904640,-14152843264]),(⟨1,2,0⟩,[0,-65536,1327104,-7684096,-22446080,529809408,-3194568704,10584817664,-21536374784,27358625792,-20385775616,1027719168,30818271232,-56782143488,36708761600]),(⟨1,2,1⟩,[-16384,557056,-7897088,61243392,-283885568,777256960,-958332928,-1192951808,7161528320,-11566284800,2783936512,14488993792,-14785462272,1910702080]),(⟨1,2,3⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨1,3,0⟩,[-32768,1097728,-16498688,149815296,-921485312,3999252480,-12161220608,24473894912,-27322613760,3142860800,31389466624,-30125064192,-513851392,8978120704]),(⟨1,3,1⟩,[0,393216,-9961472,104202240,-585498624,1849425920,-2690121728,-1968439296,15566897152,-24721358848,6977224704,22336634880,-19543752704]),(⟨1,3,2⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨1,3,3⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨1,4,0⟩,[0,278528,-6963200,71843840,-399130624,1255440384,-1860730880,-1151434752,10387554304,-17407459328,6074056704,15041904640,-14152843264]),(⟨1,5,0⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨1,5,2⟩,[0,-196608,5767168,-64225280,329777152,-680656896,-286785536,3031171072,-2976382976,-163774464]),(⟨1,5,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨1,6,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨2,0,0⟩,[0,49152,-1507328,19578880,-138412032,532512768,-576618496,-5000953856,30030561280,-80823861248,111222849536,-37365366784,-106580017152,137280880640,-32413351936,-19139133440]),(⟨2,0,1⟩,[0,-114688,2883584,-28557312,133021696,-170098688,-1327644672,8344993792,-23907565568,40682209280,-40230092800,10885611520,34842787840,-58766131200,33296793600]),(⟨2,0,2⟩,[0,-49152,1802240,-27541504,228163584,-1109229568,3134914560,-4396711936,145948672,7973912576,-8267399168,745586688,1526956032,-224788480]),(⟨2,0,3⟩,[0,114688,-2506752,19152896,-42254336,-232161280,1811251200,-5171019776,7081721856,-3005693952,-4261625856,7357808640,-4360093696]),(⟨2,1,0⟩,[0,-114688,2883584,-28557312,133021696,-170098688,-1327644672,8344993792,-23907565568,40682209280,-40230092800,10885611520,34842787840,-58766131200,33296793600]),(⟨2,2,0⟩,[0,-49152,1802240,-27541504,228163584,-1109229568,3134914560,-4396711936,145948672,7973912576,-8267399168,745586688,1526956032,-224788480]),(⟨2,2,2⟩,[0,196608,-6029312,74711040,-479723520,1664221184,-2600468480,-1351352320,12288786432,-17915772928,6710624256,3493855232]),(⟨2,2,3⟩,[-65536,1703936,-16973824,80216064,-165281792,-57933824,1133117440,-2505572352,629866496,5786697728,-6496387072]),(⟨2,2,5⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,3,0⟩,[0,65536,-671744,-9175040,192823296,-1366687744,4954882048,-9370075136,6813679616,4654432256,-11071340544,7903379456,-4311924736]),(⟨2,3,1⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨2,3,2⟩,[-65536,1703936,-16973824,80216064,-165281792,-57933824,1133117440,-2505572352,629866496,5786697728,-6496387072]),(⟨2,4,2⟩,[0,-196608,5767168,-64225280,329777152,-680656896,-286785536,3031171072,-2976382976,-163774464]),(⟨2,4,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,5,1⟩,[0,-196608,5767168,-64225280,329777152,-680656896,-286785536,3031171072,-2976382976,-163774464]),(⟨2,5,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,0,0⟩,[0,98304,-4128768,73760768,-743243776,4694900736,-19356483584,51719766016,-82489114624,51796279296,60189966336,-136374550528,75540267008,5499224064,-5714903040]),(⟨3,0,1⟩,[-32768,1097728,-16007168,135626752,-747683840,2804269056,-7096008704,11034886144,-6568542208,-9115123712,17816403968,-3724312576,-9595699200,4265820160]),(⟨3,0,2⟩,[0,65536,-1163264,4030464,48709632,-540540928,2314240000,-5016059904,4911300608,346226688,-5906546688,7840301056,-5342740480]),(⟨3,0,3⟩,[32768,-1048576,13959168,-101744640,445841408,-1191313408,1813774336,-1121910784,-682065920,1270218752,52625408,-766803968]),(⟨3,0,4⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨3,1,0⟩,[-32768,1097728,-16007168,135626752,-747683840,2804269056,-7096008704,11034886144,-6568542208,-9115123712,17816403968,-3724312576,-9595699200,4265820160]),(⟨3,1,1⟩,[0,229376,-5996544,64716800,-372736000,1187971072,-1658781696,-1634009088,10358685696,-14627799040,1806336000,14589460480,-10781818880]),(⟨3,1,2⟩,[16384,-327680,704512,30605312,-331186176,1492779008,-3024781312,193069056,11186290688,-19365429248,8744845312,3220897792]),(⟨3,1,3⟩,[-65536,1540096,-13336576,49152000,-40108032,-251592704,900923392,-1279918080,-501678080,5037588480,-5244682240]),(⟨3,1,5⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,2,0⟩,[0,65536,-1163264,4030464,48709632,-540540928,2314240000,-5016059904,4911300608,346226688,-5906546688,7840301056,-5342740480]),(⟨3,2,1⟩,[16384,-327680,704512,30605312,-331186176,1492779008,-3024781312,193069056,11186290688,-19365429248,8744845312,3220897792]),(⟨3,2,2⟩,[-131072,3211264,-28311552,98304000,-9699328,-804913152,2090860544,-2028208128,-2197422080,11615141888,-12228493312]),(⟨3,2,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,3,0⟩,[32768,-1048576,14450688,-115277824,594608128,-2039742464,4476174336,-5332664320,840859648,5439750144,-3963191296,-987693056]),(⟨3,3,1⟩,[-65536,1376256,-9699328,18087936,85065728,-445251584,668729344,-54263808,-1633222656,4288479232,-3992977408]),(⟨3,4,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨3,4,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,5,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,0,0⟩,[0,-49152,966656,-2523136,-88850432,1138475008,-6673432576,22428844032,-42924474368,36014309376,17097146368,-56394416128,27186380800,5438849024]),(⟨4,0,1⟩,[0,278528,-6963200,71843840,-399130624,1255440384,-1860730880,-1151434752,10387554304,-17407459328,6074056704,15041904640,-14152843264]),(⟨4,0,3⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨4,1,0⟩,[0,278528,-6963200,71843840,-399130624,1255440384,-1860730880,-1151434752,10387554304,-17407459328,6074056704,15041904640,-14152843264]),(⟨4,1,2⟩,[0,-196608,5636096,-62128128,320864256,-689045504,-175374336,2982936576,-3457155072,41746432,764280832]),(⟨4,2,1⟩,[0,-196608,5636096,-62128128,320864256,-689045504,-175374336,2982936576,-3457155072,41746432,764280832]),(⟨4,2,2⟩,[0,-196608,5767168,-64225280,329777152,-680656896,-286785536,3031171072,-2976382976,-163774464]),(⟨4,2,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,3,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨4,3,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,0,0⟩,[0,-49152,2326528,-41533440,379191296,-1960673280,5784272896,-8553070592,1634336768,11968331776,-11974508544,608649216,1078984704]),(⟨5,0,1⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨5,1,0⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨5,1,2⟩,[0,-196608,5767168,-64225280,329777152,-680656896,-286785536,3031171072,-2976382976,-163774464]),(⟨5,1,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,2,1⟩,[0,-196608,5767168,-64225280,329777152,-680656896,-286785536,3031171072,-2976382976,-163774464]),(⟨5,2,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨5,3,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨6,0,0⟩,[0,0,491520,-13533184,148766720,-848429056,2662400000,-4210753536,1522925568,4169531392,-4015816704,-220889088]),(⟨6,0,1⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨6,1,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832])]


theorem partial_checked8 :
    (Poly.add (Poly.add (Poly.mul chunk8 sourceRight) partial12)
      (Poly.scale (K.ofRat (-1)) partial8)).isZero := by decide +kernel

theorem partial_sound8 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 8)
      sourceRight).eval u v t=partial8.eval u v t := by
  change (Poly.mul (chunk8++(sourceLeft.drop 12))
    sourceRight).eval u v t=partial8.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound12 partial_checked8 u v t


noncomputable def chunk4 : Poly := [(⟨0,1,0⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨0,1,1⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨0,1,3⟩,[-128,1536,-3840,-4608,15232]),(⟨0,2,0⟩,[0,384,-6400,33024,-52224,4480,12544])]

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[0,-49152,1949696,-34897920,374292480,-2680045568,13444743168,-47995879424,120343658496,-199749353472,177260904448,29281714176,-273646731264,279970070528,-77968637952,-29523705856,5284823040]),(⟨0,1,1⟩,[16384,-573440,9306112,-94158848,664600576,-3427041280,13057638400,-36176101376,68846764032,-75269652480,4833247232,113375461376,-138930257920,25581649920,58724499456,-30121656320]),(⟨0,1,2⟩,[0,-65536,1327104,-7684096,-22446080,529809408,-3194568704,10584817664,-21536374784,27358625792,-20385775616,1027719168,30818271232,-56782143488,36708761600]),(⟨0,1,3⟩,[-32768,1097728,-16154624,138985472,-778272768,2946531328,-7418085376,11087347712,-5006262272,-12639551488,19597983744,614187008,-17091428352,8026783744]),(⟨0,1,4⟩,[0,278528,-6963200,71843840,-399130624,1255440384,-1860730880,-1151434752,10387554304,-17407459328,6074056704,15041904640,-14152843264]),(⟨0,1,5⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨0,1,6⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨0,2,0⟩,[0,49152,-1507328,19578880,-138412032,532512768,-576618496,-5000953856,30030561280,-80823861248,111222849536,-37365366784,-106580017152,137280880640,-32413351936,-19139133440]),(⟨0,2,1⟩,[0,-114688,2883584,-28557312,133021696,-170098688,-1327644672,8344993792,-23907565568,40682209280,-40230092800,10885611520,34842787840,-58766131200,33296793600]),(⟨0,2,2⟩,[0,-49152,1802240,-27541504,228163584,-1109229568,3134914560,-4396711936,145948672,7973912576,-8267399168,745586688,1526956032,-224788480]),(⟨0,2,3⟩,[0,114688,-2506752,19152896,-42254336,-232161280,1811251200,-5171019776,7081721856,-3005693952,-4261625856,7357808640,-4360093696]),(⟨0,3,0⟩,[0,98304,-4128768,73760768,-743243776,4694900736,-19356483584,51719766016,-82489114624,51796279296,60189966336,-136374550528,75540267008,5499224064,-5714903040]),(⟨0,3,1⟩,[-32768,1097728,-16007168,135626752,-747683840,2804269056,-7096008704,11034886144,-6568542208,-9115123712,17816403968,-3724312576,-9595699200,4265820160]),(⟨0,3,2⟩,[0,65536,-1163264,4030464,48709632,-540540928,2314240000,-5016059904,4911300608,346226688,-5906546688,7840301056,-5342740480]),(⟨0,3,3⟩,[32768,-1048576,13959168,-101744640,445841408,-1191313408,1813774336,-1121910784,-682065920,1270218752,52625408,-766803968]),(⟨0,3,4⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨0,4,0⟩,[0,-49152,966656,-2523136,-88850432,1138475008,-6673432576,22428844032,-42924474368,36014309376,17097146368,-56394416128,27186380800,5438849024]),(⟨0,4,1⟩,[0,278528,-6963200,71843840,-399130624,1255440384,-1860730880,-1151434752,10387554304,-17407459328,6074056704,15041904640,-14152843264]),(⟨0,4,3⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨0,5,0⟩,[0,-49152,2326528,-41533440,379191296,-1960673280,5784272896,-8553070592,1634336768,11968331776,-11974508544,608649216,1078984704]),(⟨0,5,1⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨0,6,0⟩,[0,0,491520,-13533184,148766720,-848429056,2662400000,-4210753536,1522925568,4169531392,-4015816704,-220889088]),(⟨0,6,1⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨1,0,0⟩,[0,-49152,1949696,-34897920,374292480,-2680045568,13444743168,-47995879424,120343658496,-199749353472,177260904448,29281714176,-273646731264,279970070528,-77968637952,-29523705856,5284823040]),(⟨1,0,1⟩,[16384,-573440,9306112,-94158848,664600576,-3427041280,13057638400,-36176101376,68846764032,-75269652480,4833247232,113375461376,-138930257920,25581649920,58724499456,-30121656320]),(⟨1,0,2⟩,[0,-65536,1327104,-7684096,-22446080,529809408,-3194568704,10584817664,-21536374784,27358625792,-20385775616,1027719168,30818271232,-56782143488,36708761600]),(⟨1,0,3⟩,[-32768,1097728,-16154624,138985472,-778272768,2946531328,-7418085376,11087347712,-5006262272,-12639551488,19597983744,614187008,-17091428352,8026783744]),(⟨1,0,4⟩,[0,278528,-6963200,71843840,-399130624,1255440384,-1860730880,-1151434752,10387554304,-17407459328,6074056704,15041904640,-14152843264]),(⟨1,0,5⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨1,0,6⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨1,1,0⟩,[16384,-573440,9650176,-105447424,827146240,-4793745408,20528054272,-63901794304,138835443712,-189154082816,99673948160,139476140032,-291613327360,163024322560,34926739456,-50416844800]),(⟨1,1,1⟩,[0,-344064,9682944,-117473280,816218112,-3579691008,9965813760,-14999027712,-3022848000,70174851072,-155359100928,137126707200,40974581760,-185534791680,113209098240]),(⟨1,1,2⟩,[-16384,557056,-7897088,61243392,-283885568,777256960,-958332928,-1192951808,7161528320,-11566284800,2783936512,14488993792,-14785462272,1910702080]),(⟨1,1,3⟩,[0,393216,-9961472,104202240,-585498624,1849425920,-2690121728,-1968439296,15566897152,-24721358848,6977224704,22336634880,-19543752704]),(⟨1,2,0⟩,[0,-65536,983040,2916352,-161497088,1552941056,-7844151296,23929487360,-44436324352,44649218048,-8829501440,-33795571712,52002865152,-53703344128,32269189120]),(⟨1,2,1⟩,[-16384,557056,-7897088,61243392,-283885568,777256960,-958332928,-1192951808,7161528320,-11566284800,2783936512,14488993792,-14785462272,1910702080]),(⟨1,2,3⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨1,3,0⟩,[-32768,1097728,-16498688,149815296,-921485312,3999252480,-12161220608,24473894912,-27322613760,3142860800,31389466624,-30125064192,-513851392,8978120704]),(⟨1,3,1⟩,[0,393216,-9961472,104202240,-585498624,1849425920,-2690121728,-1968439296,15566897152,-24721358848,6977224704,22336634880,-19543752704]),(⟨1,3,2⟩,[16384,-327680,704512,30605312,-331186176,1492779008,-3024781312,193069056,11186290688,-19365429248,8744845312,3220897792]),(⟨1,3,3⟩,[-65536,1376256,-9699328,18087936,85065728,-445251584,668729344,-54263808,-1633222656,4288479232,-3992977408]),(⟨1,3,5⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨1,4,0⟩,[0,278528,-6963200,71843840,-399130624,1255440384,-1860730880,-1151434752,10387554304,-17407459328,6074056704,15041904640,-14152843264]),(⟨1,4,2⟩,[0,-196608,5636096,-62128128,320864256,-689045504,-175374336,2982936576,-3457155072,41746432,764280832]),(⟨1,5,0⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨1,5,2⟩,[0,-196608,5767168,-64225280,329777152,-680656896,-286785536,3031171072,-2976382976,-163774464]),(⟨1,5,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨1,6,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨2,0,0⟩,[0,49152,-1507328,19578880,-138412032,532512768,-576618496,-5000953856,30030561280,-80823861248,111222849536,-37365366784,-106580017152,137280880640,-32413351936,-19139133440]),(⟨2,0,1⟩,[0,-114688,2883584,-28557312,133021696,-170098688,-1327644672,8344993792,-23907565568,40682209280,-40230092800,10885611520,34842787840,-58766131200,33296793600]),(⟨2,0,2⟩,[0,-49152,1802240,-27541504,228163584,-1109229568,3134914560,-4396711936,145948672,7973912576,-8267399168,745586688,1526956032,-224788480]),(⟨2,0,3⟩,[0,114688,-2506752,19152896,-42254336,-232161280,1811251200,-5171019776,7081721856,-3005693952,-4261625856,7357808640,-4360093696]),(⟨2,1,0⟩,[0,-65536,983040,2916352,-161497088,1552941056,-7844151296,23929487360,-44436324352,44649218048,-8829501440,-33795571712,52002865152,-53703344128,32269189120]),(⟨2,1,1⟩,[-16384,557056,-7897088,61243392,-283885568,777256960,-958332928,-1192951808,7161528320,-11566284800,2783936512,14488993792,-14785462272,1910702080]),(⟨2,1,3⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨2,2,0⟩,[0,-98304,3604480,-55083008,456327168,-2218459136,6269829120,-8793423872,291897344,15947825152,-16534798336,1491173376,3053912064,-449576960]),(⟨2,2,2⟩,[0,393216,-12058624,149422080,-959447040,3328442368,-5200936960,-2702704640,24577572864,-35831545856,13421248512,6987710464]),(⟨2,2,3⟩,[-131072,3407872,-33947648,160432128,-330563584,-115867648,2266234880,-5011144704,1259732992,11573395456,-12992774144]),(⟨2,2,5⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,3,0⟩,[0,65536,-671744,-9175040,192823296,-1366687744,4954882048,-9370075136,6813679616,4654432256,-11071340544,7903379456,-4311924736]),(⟨2,3,1⟩,[16384,-327680,704512,30605312,-331186176,1492779008,-3024781312,193069056,11186290688,-19365429248,8744845312,3220897792]),(⟨2,3,2⟩,[-131072,3211264,-28311552,98304000,-9699328,-804913152,2090860544,-2028208128,-2197422080,11615141888,-12228493312]),(⟨2,3,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,4,1⟩,[0,-196608,5636096,-62128128,320864256,-689045504,-175374336,2982936576,-3457155072,41746432,764280832]),(⟨2,4,2⟩,[0,-196608,5767168,-64225280,329777152,-680656896,-286785536,3031171072,-2976382976,-163774464]),(⟨2,4,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,5,1⟩,[0,-196608,5767168,-64225280,329777152,-680656896,-286785536,3031171072,-2976382976,-163774464]),(⟨2,5,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,0,0⟩,[0,98304,-4128768,73760768,-743243776,4694900736,-19356483584,51719766016,-82489114624,51796279296,60189966336,-136374550528,75540267008,5499224064,-5714903040]),(⟨3,0,1⟩,[-32768,1097728,-16007168,135626752,-747683840,2804269056,-7096008704,11034886144,-6568542208,-9115123712,17816403968,-3724312576,-9595699200,4265820160]),(⟨3,0,2⟩,[0,65536,-1163264,4030464,48709632,-540540928,2314240000,-5016059904,4911300608,346226688,-5906546688,7840301056,-5342740480]),(⟨3,0,3⟩,[32768,-1048576,13959168,-101744640,445841408,-1191313408,1813774336,-1121910784,-682065920,1270218752,52625408,-766803968]),(⟨3,0,4⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨3,1,0⟩,[-32768,1097728,-16498688,149815296,-921485312,3999252480,-12161220608,24473894912,-27322613760,3142860800,31389466624,-30125064192,-513851392,8978120704]),(⟨3,1,1⟩,[0,393216,-9961472,104202240,-585498624,1849425920,-2690121728,-1968439296,15566897152,-24721358848,6977224704,22336634880,-19543752704]),(⟨3,1,2⟩,[16384,-327680,704512,30605312,-331186176,1492779008,-3024781312,193069056,11186290688,-19365429248,8744845312,3220897792]),(⟨3,1,3⟩,[-65536,1376256,-9699328,18087936,85065728,-445251584,668729344,-54263808,-1633222656,4288479232,-3992977408]),(⟨3,1,5⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,2,0⟩,[0,65536,-671744,-9175040,192823296,-1366687744,4954882048,-9370075136,6813679616,4654432256,-11071340544,7903379456,-4311924736]),(⟨3,2,1⟩,[16384,-327680,704512,30605312,-331186176,1492779008,-3024781312,193069056,11186290688,-19365429248,8744845312,3220897792]),(⟨3,2,2⟩,[-131072,3211264,-28311552,98304000,-9699328,-804913152,2090860544,-2028208128,-2197422080,11615141888,-12228493312]),(⟨3,2,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,3,0⟩,[32768,-1048576,14450688,-115277824,594608128,-2039742464,4476174336,-5332664320,840859648,5439750144,-3963191296,-987693056]),(⟨3,3,1⟩,[-65536,1376256,-9699328,18087936,85065728,-445251584,668729344,-54263808,-1633222656,4288479232,-3992977408]),(⟨3,4,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨3,4,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,5,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,0,0⟩,[0,-49152,966656,-2523136,-88850432,1138475008,-6673432576,22428844032,-42924474368,36014309376,17097146368,-56394416128,27186380800,5438849024]),(⟨4,0,1⟩,[0,278528,-6963200,71843840,-399130624,1255440384,-1860730880,-1151434752,10387554304,-17407459328,6074056704,15041904640,-14152843264]),(⟨4,0,3⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨4,1,0⟩,[0,278528,-6963200,71843840,-399130624,1255440384,-1860730880,-1151434752,10387554304,-17407459328,6074056704,15041904640,-14152843264]),(⟨4,1,2⟩,[0,-196608,5636096,-62128128,320864256,-689045504,-175374336,2982936576,-3457155072,41746432,764280832]),(⟨4,2,1⟩,[0,-196608,5636096,-62128128,320864256,-689045504,-175374336,2982936576,-3457155072,41746432,764280832]),(⟨4,2,2⟩,[0,-196608,5767168,-64225280,329777152,-680656896,-286785536,3031171072,-2976382976,-163774464]),(⟨4,2,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,3,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨4,3,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,0,0⟩,[0,-49152,2326528,-41533440,379191296,-1960673280,5784272896,-8553070592,1634336768,11968331776,-11974508544,608649216,1078984704]),(⟨5,0,1⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨5,1,0⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨5,1,2⟩,[0,-196608,5767168,-64225280,329777152,-680656896,-286785536,3031171072,-2976382976,-163774464]),(⟨5,1,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,2,1⟩,[0,-196608,5767168,-64225280,329777152,-680656896,-286785536,3031171072,-2976382976,-163774464]),(⟨5,2,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨5,3,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨6,0,0⟩,[0,0,491520,-13533184,148766720,-848429056,2662400000,-4210753536,1522925568,4169531392,-4015816704,-220889088]),(⟨6,0,1⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨6,1,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832])]


theorem partial_checked4 :
    (Poly.add (Poly.add (Poly.mul chunk4 sourceRight) partial8)
      (Poly.scale (K.ofRat (-1)) partial4)).isZero := by decide +kernel

theorem partial_sound4 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 4)
      sourceRight).eval u v t=partial4.eval u v t := by
  change (Poly.mul (chunk4++(sourceLeft.drop 8))
    sourceRight).eval u v t=partial4.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound8 partial_checked4 u v t


noncomputable def chunk0 : Poly := [(⟨0,0,0⟩,[0,-384,8064,-64256,246656,-476544,385152,5632,-79744]),(⟨0,0,1⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨0,0,2⟩,[0,384,-6400,33024,-52224,4480,12544]),(⟨0,0,3⟩,[0,384,-6656,34048,-49664,-2688])]

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,-49152,2064384,-39337984,450691072,-3458777088,18686754816,-72406417408,199854997504,-376720343040,423031996416,-110228062208,-433971036160,654937276416,-334496317440,-18624462848,57914310656,-7349207040]),(⟨0,0,1⟩,[0,-49152,2293760,-46989312,562413568,-4396056576,23656923136,-89508921344,236584124416,-416282427392,410126319616,-13931937792,-525867008000,618285826048,-218771095552,-61168992256,33507819520]),(⟨0,0,2⟩,[0,98304,-3522560,55377920,-501448704,2856452096,-10317381632,21453406208,-12522291200,-56018894848,152926601216,-131080323072,-44512935936,135959216128,-42731716608,-17710120960]),(⟨0,0,3⟩,[0,98304,-4620288,89096192,-949059584,6256918528,-26728398848,73866608640,-123004452864,87715971072,69891489792,-189042163712,111912189952,7901413376,-12267945984]),(⟨0,0,4⟩,[0,-49152,966656,-2523136,-88850432,1138475008,-6673432576,22428844032,-42924474368,36014309376,17097146368,-56394416128,27186380800,5438849024]),(⟨0,0,5⟩,[0,-49152,2326528,-41533440,379191296,-1960673280,5784272896,-8553070592,1634336768,11968331776,-11974508544,608649216,1078984704]),(⟨0,0,6⟩,[0,0,491520,-13533184,148766720,-848429056,2662400000,-4210753536,1522925568,4169531392,-4015816704,-220889088]),(⟨0,1,0⟩,[0,-49152,2293760,-46989312,562413568,-4396056576,23656923136,-89508921344,236584124416,-416282427392,410126319616,-13931937792,-525867008000,618285826048,-218771095552,-61168992256,33507819520]),(⟨0,1,1⟩,[16384,-573440,9650176,-105447424,827146240,-4793745408,20528054272,-63901794304,138835443712,-189154082816,99673948160,139476140032,-291613327360,163024322560,34926739456,-50416844800]),(⟨0,1,2⟩,[0,-65536,983040,2916352,-161497088,1552941056,-7844151296,23929487360,-44436324352,44649218048,-8829501440,-33795571712,52002865152,-53703344128,32269189120]),(⟨0,1,3⟩,[-32768,1097728,-16498688,149815296,-921485312,3999252480,-12161220608,24473894912,-27322613760,3142860800,31389466624,-30125064192,-513851392,8978120704]),(⟨0,1,4⟩,[0,278528,-6963200,71843840,-399130624,1255440384,-1860730880,-1151434752,10387554304,-17407459328,6074056704,15041904640,-14152843264]),(⟨0,1,5⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨0,1,6⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨0,2,0⟩,[0,98304,-3522560,55377920,-501448704,2856452096,-10317381632,21453406208,-12522291200,-56018894848,152926601216,-131080323072,-44512935936,135959216128,-42731716608,-17710120960]),(⟨0,2,1⟩,[0,-65536,983040,2916352,-161497088,1552941056,-7844151296,23929487360,-44436324352,44649218048,-8829501440,-33795571712,52002865152,-53703344128,32269189120]),(⟨0,2,2⟩,[0,-98304,3604480,-55083008,456327168,-2218459136,6269829120,-8793423872,291897344,15947825152,-16534798336,1491173376,3053912064,-449576960]),(⟨0,2,3⟩,[0,65536,-671744,-9175040,192823296,-1366687744,4954882048,-9370075136,6813679616,4654432256,-11071340544,7903379456,-4311924736]),(⟨0,3,0⟩,[0,98304,-4620288,89096192,-949059584,6256918528,-26728398848,73866608640,-123004452864,87715971072,69891489792,-189042163712,111912189952,7901413376,-12267945984]),(⟨0,3,1⟩,[-32768,1097728,-16498688,149815296,-921485312,3999252480,-12161220608,24473894912,-27322613760,3142860800,31389466624,-30125064192,-513851392,8978120704]),(⟨0,3,2⟩,[0,65536,-671744,-9175040,192823296,-1366687744,4954882048,-9370075136,6813679616,4654432256,-11071340544,7903379456,-4311924736]),(⟨0,3,3⟩,[32768,-1048576,14450688,-115277824,594608128,-2039742464,4476174336,-5332664320,840859648,5439750144,-3963191296,-987693056]),(⟨0,3,4⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨0,4,0⟩,[0,-49152,966656,-2523136,-88850432,1138475008,-6673432576,22428844032,-42924474368,36014309376,17097146368,-56394416128,27186380800,5438849024]),(⟨0,4,1⟩,[0,278528,-6963200,71843840,-399130624,1255440384,-1860730880,-1151434752,10387554304,-17407459328,6074056704,15041904640,-14152843264]),(⟨0,4,3⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨0,5,0⟩,[0,-49152,2326528,-41533440,379191296,-1960673280,5784272896,-8553070592,1634336768,11968331776,-11974508544,608649216,1078984704]),(⟨0,5,1⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨0,6,0⟩,[0,0,491520,-13533184,148766720,-848429056,2662400000,-4210753536,1522925568,4169531392,-4015816704,-220889088]),(⟨0,6,1⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨1,0,0⟩,[0,-49152,2293760,-46989312,562413568,-4396056576,23656923136,-89508921344,236584124416,-416282427392,410126319616,-13931937792,-525867008000,618285826048,-218771095552,-61168992256,33507819520]),(⟨1,0,1⟩,[16384,-573440,9650176,-105447424,827146240,-4793745408,20528054272,-63901794304,138835443712,-189154082816,99673948160,139476140032,-291613327360,163024322560,34926739456,-50416844800]),(⟨1,0,2⟩,[0,-65536,983040,2916352,-161497088,1552941056,-7844151296,23929487360,-44436324352,44649218048,-8829501440,-33795571712,52002865152,-53703344128,32269189120]),(⟨1,0,3⟩,[-32768,1097728,-16498688,149815296,-921485312,3999252480,-12161220608,24473894912,-27322613760,3142860800,31389466624,-30125064192,-513851392,8978120704]),(⟨1,0,4⟩,[0,278528,-6963200,71843840,-399130624,1255440384,-1860730880,-1151434752,10387554304,-17407459328,6074056704,15041904640,-14152843264]),(⟨1,0,5⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨1,0,6⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨1,1,0⟩,[16384,-573440,9650176,-105447424,827146240,-4793745408,20528054272,-63901794304,138835443712,-189154082816,99673948160,139476140032,-291613327360,163024322560,34926739456,-50416844800]),(⟨1,1,1⟩,[0,-344064,9682944,-117473280,816218112,-3579691008,9965813760,-14999027712,-3022848000,70174851072,-155359100928,137126707200,40974581760,-185534791680,113209098240]),(⟨1,1,2⟩,[-16384,557056,-7897088,61243392,-283885568,777256960,-958332928,-1192951808,7161528320,-11566284800,2783936512,14488993792,-14785462272,1910702080]),(⟨1,1,3⟩,[0,393216,-9961472,104202240,-585498624,1849425920,-2690121728,-1968439296,15566897152,-24721358848,6977224704,22336634880,-19543752704]),(⟨1,2,0⟩,[0,-65536,983040,2916352,-161497088,1552941056,-7844151296,23929487360,-44436324352,44649218048,-8829501440,-33795571712,52002865152,-53703344128,32269189120]),(⟨1,2,1⟩,[-16384,557056,-7897088,61243392,-283885568,777256960,-958332928,-1192951808,7161528320,-11566284800,2783936512,14488993792,-14785462272,1910702080]),(⟨1,2,2⟩,[0,196608,-6488064,88342528,-637861888,2574385152,-5238030336,1221853184,17971412992,-36710449152,24587599872,1812987904,-4858642432]),(⟨1,2,3⟩,[16384,-327680,704512,30605312,-331186176,1492779008,-3024781312,193069056,11186290688,-19365429248,8744845312,3220897792]),(⟨1,2,4⟩,[0,-196608,5636096,-62128128,320864256,-689045504,-175374336,2982936576,-3457155072,41746432,764280832]),(⟨1,2,5⟩,[0,-196608,5767168,-64225280,329777152,-680656896,-286785536,3031171072,-2976382976,-163774464]),(⟨1,3,0⟩,[-32768,1097728,-16498688,149815296,-921485312,3999252480,-12161220608,24473894912,-27322613760,3142860800,31389466624,-30125064192,-513851392,8978120704]),(⟨1,3,1⟩,[0,393216,-9961472,104202240,-585498624,1849425920,-2690121728,-1968439296,15566897152,-24721358848,6977224704,22336634880,-19543752704]),(⟨1,3,2⟩,[16384,-327680,704512,30605312,-331186176,1492779008,-3024781312,193069056,11186290688,-19365429248,8744845312,3220897792]),(⟨1,3,3⟩,[-65536,1376256,-9699328,18087936,85065728,-445251584,668729344,-54263808,-1633222656,4288479232,-3992977408]),(⟨1,3,5⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨1,4,0⟩,[0,278528,-6963200,71843840,-399130624,1255440384,-1860730880,-1151434752,10387554304,-17407459328,6074056704,15041904640,-14152843264]),(⟨1,4,2⟩,[0,-196608,5636096,-62128128,320864256,-689045504,-175374336,2982936576,-3457155072,41746432,764280832]),(⟨1,5,0⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨1,5,2⟩,[0,-196608,5767168,-64225280,329777152,-680656896,-286785536,3031171072,-2976382976,-163774464]),(⟨1,5,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨1,6,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨2,0,0⟩,[0,98304,-3522560,55377920,-501448704,2856452096,-10317381632,21453406208,-12522291200,-56018894848,152926601216,-131080323072,-44512935936,135959216128,-42731716608,-17710120960]),(⟨2,0,1⟩,[0,-65536,983040,2916352,-161497088,1552941056,-7844151296,23929487360,-44436324352,44649218048,-8829501440,-33795571712,52002865152,-53703344128,32269189120]),(⟨2,0,2⟩,[0,-98304,3604480,-55083008,456327168,-2218459136,6269829120,-8793423872,291897344,15947825152,-16534798336,1491173376,3053912064,-449576960]),(⟨2,0,3⟩,[0,65536,-671744,-9175040,192823296,-1366687744,4954882048,-9370075136,6813679616,4654432256,-11071340544,7903379456,-4311924736]),(⟨2,1,0⟩,[0,-65536,983040,2916352,-161497088,1552941056,-7844151296,23929487360,-44436324352,44649218048,-8829501440,-33795571712,52002865152,-53703344128,32269189120]),(⟨2,1,1⟩,[-16384,557056,-7897088,61243392,-283885568,777256960,-958332928,-1192951808,7161528320,-11566284800,2783936512,14488993792,-14785462272,1910702080]),(⟨2,1,2⟩,[0,196608,-6488064,88342528,-637861888,2574385152,-5238030336,1221853184,17971412992,-36710449152,24587599872,1812987904,-4858642432]),(⟨2,1,3⟩,[16384,-327680,704512,30605312,-331186176,1492779008,-3024781312,193069056,11186290688,-19365429248,8744845312,3220897792]),(⟨2,1,4⟩,[0,-196608,5636096,-62128128,320864256,-689045504,-175374336,2982936576,-3457155072,41746432,764280832]),(⟨2,1,5⟩,[0,-196608,5767168,-64225280,329777152,-680656896,-286785536,3031171072,-2976382976,-163774464]),(⟨2,2,0⟩,[0,-98304,3604480,-55083008,456327168,-2218459136,6269829120,-8793423872,291897344,15947825152,-16534798336,1491173376,3053912064,-449576960]),(⟨2,2,1⟩,[0,196608,-6488064,88342528,-637861888,2574385152,-5238030336,1221853184,17971412992,-36710449152,24587599872,1812987904,-4858642432]),(⟨2,2,2⟩,[0,589824,-18087936,224133120,-1439170560,4992663552,-7801405440,-4054056960,36866359296,-53747318784,20131872768,10481565696]),(⟨2,2,3⟩,[-131072,3211264,-28311552,98304000,-9699328,-804913152,2090860544,-2028208128,-2197422080,11615141888,-12228493312]),(⟨2,2,4⟩,[0,-196608,5767168,-64225280,329777152,-680656896,-286785536,3031171072,-2976382976,-163774464]),(⟨2,2,5⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,3,0⟩,[0,65536,-671744,-9175040,192823296,-1366687744,4954882048,-9370075136,6813679616,4654432256,-11071340544,7903379456,-4311924736]),(⟨2,3,1⟩,[16384,-327680,704512,30605312,-331186176,1492779008,-3024781312,193069056,11186290688,-19365429248,8744845312,3220897792]),(⟨2,3,2⟩,[-131072,3211264,-28311552,98304000,-9699328,-804913152,2090860544,-2028208128,-2197422080,11615141888,-12228493312]),(⟨2,3,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,4,1⟩,[0,-196608,5636096,-62128128,320864256,-689045504,-175374336,2982936576,-3457155072,41746432,764280832]),(⟨2,4,2⟩,[0,-196608,5767168,-64225280,329777152,-680656896,-286785536,3031171072,-2976382976,-163774464]),(⟨2,4,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,5,1⟩,[0,-196608,5767168,-64225280,329777152,-680656896,-286785536,3031171072,-2976382976,-163774464]),(⟨2,5,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,0,0⟩,[0,98304,-4620288,89096192,-949059584,6256918528,-26728398848,73866608640,-123004452864,87715971072,69891489792,-189042163712,111912189952,7901413376,-12267945984]),(⟨3,0,1⟩,[-32768,1097728,-16498688,149815296,-921485312,3999252480,-12161220608,24473894912,-27322613760,3142860800,31389466624,-30125064192,-513851392,8978120704]),(⟨3,0,2⟩,[0,65536,-671744,-9175040,192823296,-1366687744,4954882048,-9370075136,6813679616,4654432256,-11071340544,7903379456,-4311924736]),(⟨3,0,3⟩,[32768,-1048576,14450688,-115277824,594608128,-2039742464,4476174336,-5332664320,840859648,5439750144,-3963191296,-987693056]),(⟨3,0,4⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨3,1,0⟩,[-32768,1097728,-16498688,149815296,-921485312,3999252480,-12161220608,24473894912,-27322613760,3142860800,31389466624,-30125064192,-513851392,8978120704]),(⟨3,1,1⟩,[0,393216,-9961472,104202240,-585498624,1849425920,-2690121728,-1968439296,15566897152,-24721358848,6977224704,22336634880,-19543752704]),(⟨3,1,2⟩,[16384,-327680,704512,30605312,-331186176,1492779008,-3024781312,193069056,11186290688,-19365429248,8744845312,3220897792]),(⟨3,1,3⟩,[-65536,1376256,-9699328,18087936,85065728,-445251584,668729344,-54263808,-1633222656,4288479232,-3992977408]),(⟨3,1,5⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,2,0⟩,[0,65536,-671744,-9175040,192823296,-1366687744,4954882048,-9370075136,6813679616,4654432256,-11071340544,7903379456,-4311924736]),(⟨3,2,1⟩,[16384,-327680,704512,30605312,-331186176,1492779008,-3024781312,193069056,11186290688,-19365429248,8744845312,3220897792]),(⟨3,2,2⟩,[-131072,3211264,-28311552,98304000,-9699328,-804913152,2090860544,-2028208128,-2197422080,11615141888,-12228493312]),(⟨3,2,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,3,0⟩,[32768,-1048576,14450688,-115277824,594608128,-2039742464,4476174336,-5332664320,840859648,5439750144,-3963191296,-987693056]),(⟨3,3,1⟩,[-65536,1376256,-9699328,18087936,85065728,-445251584,668729344,-54263808,-1633222656,4288479232,-3992977408]),(⟨3,4,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨3,4,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,5,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,0,0⟩,[0,-49152,966656,-2523136,-88850432,1138475008,-6673432576,22428844032,-42924474368,36014309376,17097146368,-56394416128,27186380800,5438849024]),(⟨4,0,1⟩,[0,278528,-6963200,71843840,-399130624,1255440384,-1860730880,-1151434752,10387554304,-17407459328,6074056704,15041904640,-14152843264]),(⟨4,0,3⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨4,1,0⟩,[0,278528,-6963200,71843840,-399130624,1255440384,-1860730880,-1151434752,10387554304,-17407459328,6074056704,15041904640,-14152843264]),(⟨4,1,2⟩,[0,-196608,5636096,-62128128,320864256,-689045504,-175374336,2982936576,-3457155072,41746432,764280832]),(⟨4,2,1⟩,[0,-196608,5636096,-62128128,320864256,-689045504,-175374336,2982936576,-3457155072,41746432,764280832]),(⟨4,2,2⟩,[0,-196608,5767168,-64225280,329777152,-680656896,-286785536,3031171072,-2976382976,-163774464]),(⟨4,2,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,3,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨4,3,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,0,0⟩,[0,-49152,2326528,-41533440,379191296,-1960673280,5784272896,-8553070592,1634336768,11968331776,-11974508544,608649216,1078984704]),(⟨5,0,1⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨5,1,0⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨5,1,2⟩,[0,-196608,5767168,-64225280,329777152,-680656896,-286785536,3031171072,-2976382976,-163774464]),(⟨5,1,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,2,1⟩,[0,-196608,5767168,-64225280,329777152,-680656896,-286785536,3031171072,-2976382976,-163774464]),(⟨5,2,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨5,3,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨6,0,0⟩,[0,0,491520,-13533184,148766720,-848429056,2662400000,-4210753536,1522925568,4169531392,-4015816704,-220889088]),(⟨6,0,1⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨6,1,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832])]


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
    (Poly.add (Poly.scale (K.ofRat r645) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 4 12).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r644*r644 : ℚ)=r645 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 4 12 r644 r644 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 4=12 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 4 12).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C103

#print axioms Coulomb8.Columns.C103.sound
