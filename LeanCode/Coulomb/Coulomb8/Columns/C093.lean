import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C093

def r0 : ℚ := { num := 32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -163840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 17235968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -139886592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 572555264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 134021120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -16395599872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 105869672448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -22426845184, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 866604580864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -1184593018880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 653186531328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 684693225472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -1531824570368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 1068668354560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -272556883968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 21516779520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -1441792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 25853952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := -247595008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := 1312620544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := -2747727872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -11559698432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 16460546048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -455503609856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 1054287593472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -1403280130048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 663447797760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := 965831032832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -1789875912704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 1034203955200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -2933391360, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 1900544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -21037056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 91095040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 216006656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -4654104576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 25154879488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -67981803520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 69844271104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 412680192, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -467098861568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 502925492224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 25877676032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -429639729152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 32595312640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 2818048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -45154304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 345243648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -1085931520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := -139788288, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 36006395904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -150993895424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 328034615296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -332591464448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -53893988352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 473494716416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -53283913728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 54078799872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -425984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := -3735552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := 98992128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := -692092928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := 1633091584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 678821888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -42396745728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 118049177600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -141082263552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 179240960, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 155239350272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -2210365440, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -196608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 2719744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -101187584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := -19333120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := 381550592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := -12590186496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := 24500764672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := -11890425856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -26504134656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 33020477440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -687079424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := -327680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := 7274496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := -51642368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := 59506688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 145096704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -5688393728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 12096110592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := -7482900480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -580714496, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := 12601196544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := -589824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := 18153472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -233111552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 1603731456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -5890244608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 816316416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 51308789760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -282958888960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 710420922368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := -133132779520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := 344537366528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 756624326656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -1112591826944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 68650926080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 2490368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -37355520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 279576576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := -139853824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -201916416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 16525033472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -4131389440, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := 138633740288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := -100509679616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -105596190720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 14583463936, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -121275416576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := -2794127360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := 131072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := -3538944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := 262602752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := -1332805632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := 2380267520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 1216348160, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -59760836608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 145520984064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := -21216493568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := -27331002368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := 191808077824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := -2484142080, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := -1048576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := 1736704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -59113472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 48562176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := 658505728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := -342556672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 175898624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := 7600242688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := -11951669248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := -1924431872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := 79560704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -62128128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 250347520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -387317760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := -464388096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 2451308544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -2263089152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := -1498218496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := 21037056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -1507328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 9699328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 39387136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := -18677760, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := 5634129920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -16903569408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 21403140096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := 11201871872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := -61284745216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 6398148608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := 362610688, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := -421724160, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -2424832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 32505856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -655360, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := 277741568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 2327969792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := -13438812160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 27589607424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -14095417344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -29403447296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 37088919552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -765067264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -655360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 14548992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := -103284736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := 119013376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := 290193408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := -11376787456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := 24192221184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := -14965800960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -1161428992, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 25202393088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := 393216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := -71958528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := 776601600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := -638976000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := 14255652864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := -19905380352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -19608109056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 124304228352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := -175533588480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := 442368000, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 25010503680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -155320320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 589824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -16187392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := 183304192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := -1098317824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := 3564240896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := -4689100800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := -6662520832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 33072742400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -38075564032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -1140654080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := 6493241344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := -28508160, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -1310720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := 29097984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := -248512512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := 1001390080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := -1549271040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -1857552384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := 9805234176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := -9052356608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := -5992873984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 84148224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := 1310720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := -4259840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := -94633984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := 1133379584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -5473042432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 12551847936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -6260523008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := -2057109504, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := 81489297408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := -65263697920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := 110362624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := -131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := 196608, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := -30212096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := 85721088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := 3145728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -3480616960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 1376649216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -6290669568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -23978180608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 56205443072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := -318439424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := 131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := -2883584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := 2621440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := 16777216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := -601096192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := 2045247488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := -849870848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := -6419382272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := 1275985920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := -1835008, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -3145728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := 22544384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := -617873408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 324009984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -946339840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := -7380926464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := 78512128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := 524288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -12582912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 6291456, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -339738624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := -105906176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := 2629828608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := -3063939072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -37748736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := 1572864, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := -84934656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := -26476544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := 657457152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := -765984768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := -9437184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -393216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 1572864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := -112459776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := 443547648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := 371982336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := -9279897600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := 30302797824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := -3746562048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := -65145274368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := 24730140672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := -145489920, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -262144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := -6815744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := 230686720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := -1280573440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := 1833435136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := 4409786368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := -12547260416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -7471104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 15990784, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := 393216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := -9437184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := 76021760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := -170917888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := -670826496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := 210763776, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := -2478309376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := -9626976256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := 109707264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := 262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -6291456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := 3145728, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := -169869312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -52953088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 1314914304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -1531969536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := -18874368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := 16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := -81920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := 8617984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := -69943296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := 286277632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 67010560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -8197799936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := 52934836224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := -11213422592, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := 433302290432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := -592296509440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := 326593265664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := 342346612736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := -765912285184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := 534334177280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -136278441984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 10758389760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -720896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 12926976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := -123797504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := 656310272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -1373863936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := -5779849216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := 8230273024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := -227751804928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := 527143796736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := -701640065024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := 331723898880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 482915516416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := -894937956352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := 517101977600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := -1466695680, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := -32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := 950272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := -10518528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := 45547520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := 108003328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := -2327052288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := 12577439744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := -33990901760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := 34922135552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := 206340096, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := -233549430784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := 251462746112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := 12938838016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := -214819864576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := 16297656320, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := 1409024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -22577152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := 172621824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := -542965760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := -69894144, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := 18003197952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := -75496947712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := 164017307648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := -166295732224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := -26946994176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := 236747358208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := -26641956864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := 27039399936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := -212992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := -1867776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := 49496064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := -346046464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := 816545792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := 339410944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := -21198372864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := 59024588800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := -70541131776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := 89620480, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := 77619675136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := -1105182720, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := -98304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := 1359872, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := -50593792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := -9666560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := 190775296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := -6295093248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := 12250382336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := -5945212928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := -13252067328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := 16510238720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := -343539712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := -163840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 3637248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := -25821184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := 29753344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := 72548352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := -2844196864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := 6048055296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := -3741450240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := -290357248, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := 6300598272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := -294912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := 9076736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := -116555776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := 801865728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := -2945122304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := 408158208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := 25654394880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := -141479444480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := 355210461184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := -66566389760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := 172268683264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := 378312163328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := -556295913472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := 34325463040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := 1245184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := -18677760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := 139788288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := -69926912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := -100958208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := 8262516736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := -2065694720, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := 69316870144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := -50254839808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := -52798095360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := 7291731968, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := -60637708288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := -1397063680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := 65536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := -1769472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := 131301376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := -666402816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := 1190133760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := 608174080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := -29880418304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := 72760492032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := -10608246784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := -13665501184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := 95904038912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := -1242071040, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := -524288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := 868352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := -29556736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := 24281088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := 329252864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := -171278336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := 87949312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := 3800121344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := -5975834624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r450 : ℚ := { num := -962215936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r451 : ℚ := { num := 39780352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r452 : ℚ := { num := -31064064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r453 : ℚ := { num := 125173760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r454 : ℚ := { num := -193658880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r455 : ℚ := { num := -232194048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r456 : ℚ := { num := 1225654272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r457 : ℚ := { num := -1131544576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r458 : ℚ := { num := -749109248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r459 : ℚ := { num := 10518528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r460 : ℚ := { num := -753664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r461 : ℚ := { num := 4849664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r462 : ℚ := { num := 19693568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r463 : ℚ := { num := -9338880, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r464 : ℚ := { num := 2817064960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r465 : ℚ := { num := -8451784704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r466 : ℚ := { num := 10701570048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r467 : ℚ := { num := 5600935936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r468 : ℚ := { num := -30642372608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r469 : ℚ := { num := 3199074304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r470 : ℚ := { num := 181305344, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r471 : ℚ := { num := -210862080, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r472 : ℚ := { num := -1212416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r473 : ℚ := { num := 16252928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r474 : ℚ := { num := -327680, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r475 : ℚ := { num := 138870784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r476 : ℚ := { num := 1163984896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r477 : ℚ := { num := -6719406080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r478 : ℚ := { num := 13794803712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r479 : ℚ := { num := -7047708672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r480 : ℚ := { num := -14701723648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r481 : ℚ := { num := 18544459776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r482 : ℚ := { num := -382533632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r483 : ℚ := { num := 196608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r484 : ℚ := { num := -35979264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r485 : ℚ := { num := 388300800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r486 : ℚ := { num := -319488000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r487 : ℚ := { num := 7127826432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r488 : ℚ := { num := -9952690176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r489 : ℚ := { num := -9804054528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r490 : ℚ := { num := 62152114176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r491 : ℚ := { num := -87766794240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r492 : ℚ := { num := 221184000, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r493 : ℚ := { num := 12505251840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r494 : ℚ := { num := -77660160, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r495 : ℚ := { num := 294912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r496 : ℚ := { num := -8093696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r497 : ℚ := { num := 91652096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r498 : ℚ := { num := -549158912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r499 : ℚ := { num := 1782120448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r500 : ℚ := { num := -2344550400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r501 : ℚ := { num := -3331260416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r502 : ℚ := { num := 16536371200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r503 : ℚ := { num := -19037782016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r504 : ℚ := { num := -570327040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r505 : ℚ := { num := 3246620672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r506 : ℚ := { num := -14254080, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r507 : ℚ := { num := -124256256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r508 : ℚ := { num := 500695040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r509 : ℚ := { num := -774635520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r510 : ℚ := { num := -928776192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r511 : ℚ := { num := 4902617088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r512 : ℚ := { num := -4526178304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r513 : ℚ := { num := -2996436992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r514 : ℚ := { num := 42074112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r515 : ℚ := { num := 655360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r516 : ℚ := { num := -2129920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r517 : ℚ := { num := -47316992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r518 : ℚ := { num := 566689792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r519 : ℚ := { num := -2736521216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r520 : ℚ := { num := 6275923968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r521 : ℚ := { num := -3130261504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r522 : ℚ := { num := -1028554752, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r523 : ℚ := { num := 40744648704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r524 : ℚ := { num := -32631848960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r525 : ℚ := { num := 55181312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r526 : ℚ := { num := 98304, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r527 : ℚ := { num := -15106048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r528 : ℚ := { num := 42860544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r529 : ℚ := { num := 1572864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r530 : ℚ := { num := -1740308480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r531 : ℚ := { num := 688324608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r532 : ℚ := { num := -3145334784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r533 : ℚ := { num := -11989090304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r534 : ℚ := { num := 28102721536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r535 : ℚ := { num := -159219712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r536 : ℚ := { num := 1310720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r537 : ℚ := { num := 8388608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r538 : ℚ := { num := -300548096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r539 : ℚ := { num := 1022623744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r540 : ℚ := { num := -424935424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r541 : ℚ := { num := -3209691136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r542 : ℚ := { num := 637992960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r543 : ℚ := { num := -917504, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r544 : ℚ := { num := -1572864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r545 : ℚ := { num := 11272192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r546 : ℚ := { num := -308936704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r547 : ℚ := { num := 162004992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r548 : ℚ := { num := -473169920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r549 : ℚ := { num := -3690463232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r550 : ℚ := { num := 39256064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r551 : ℚ := { num := 786432, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r552 : ℚ := { num := -42467328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r553 : ℚ := { num := -13238272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r554 : ℚ := { num := 328728576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r555 : ℚ := { num := -382992384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r556 : ℚ := { num := -4718592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r557 : ℚ := { num := -196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r558 : ℚ := { num := 786432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r559 : ℚ := { num := -56229888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r560 : ℚ := { num := 221773824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r561 : ℚ := { num := 185991168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r562 : ℚ := { num := -4639948800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r563 : ℚ := { num := 15151398912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r564 : ℚ := { num := -1873281024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r565 : ℚ := { num := -32572637184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r566 : ℚ := { num := 12365070336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r567 : ℚ := { num := -72744960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r568 : ℚ := { num := -131072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r569 : ℚ := { num := -3407872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r570 : ℚ := { num := 115343360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r571 : ℚ := { num := -640286720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r572 : ℚ := { num := 916717568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r573 : ℚ := { num := 2204893184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r574 : ℚ := { num := -6273630208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r575 : ℚ := { num := -3735552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r576 : ℚ := { num := 7995392, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r577 : ℚ := { num := 196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r578 : ℚ := { num := -4718592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r579 : ℚ := { num := 38010880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r580 : ℚ := { num := -85458944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r581 : ℚ := { num := -335413248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r582 : ℚ := { num := 105381888, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r583 : ℚ := { num := -1239154688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r584 : ℚ := { num := -4813488128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r585 : ℚ := { num := 54853632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r586 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r587 : ℚ := { num := 1, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16],[r0,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31],[r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46],[r32,r47,r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59],[r0,r60,r61,r62,r63,r64,r65,r66,r67,r68,r69,r70,r71],[r0,r72,r73,r74,r75,r76,r77,r78,r79,r80,r81,r82],[0,r83,r84,r85,r86,r87,r88,r89,r90,r91,r92],[],[],[],[],[],[],[0,r93,r94,r95,r96,r97,r98,r99,r100,r101,r102,r103,r104,r105,r106],[r32,r107,r108,r109,r110,r111,r112,r113,r114,r115,r116,r117,r118,r119],[0,r120,r121,r122,r123,r124,r125,r126,r127,r128,r129,r130,r131],[r0,r132,r133,r134,r135,r136,r137,r138,r139,r140,r141,r142],[0,r83,r84,r143,r144,r145,r146,r147,r148,r149,r150],[],[],[],[],[],[],[r151,r152,r153,r154,r155,r156,r157,r158,r159,r160,r161,r162,r163],[r151,r164,r165,r166,r167,r168,r169,r170,r171,r172,r173,r174],[0,r83,r84,r143,r144,r145,r146,r147,r148,r149,r150],[],[],[],[],[],[],[0,r175,r176,r177,r178,r179,r180,r181,r182,r183,r184],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,0,r185,r186,r187,r188,r189,r190,r191,r192,r193,r194,r195,r196],[0,r197,r198,r199,r200,r201,r202,r203,r204,r205,r206,r207,r208],[0,0,r209,r210,r211,r212,r213,r214,r215,r216,r217,r218],[],[],[],[],[],[],[],[r32,r219,r220,r221,r222,r223,r224,r225,r226,r227,r228,r229],[r230,r231,r232,r233,r234,r235,r236,r237,r238,r239,r240],[r241,r242,r243,r244,r245,r246,r247,r248,r249,r250],[r241,r251,r252,r132,r253,r254,r255,r256,r257],[],[],[],[],[0,r258,r259,r260,r261,r262,r263,r264,r265,524288],[r241,r251,r266,r267,r268,r269,r270,r271,131072],[],[],[],[],[],[],[],[],[],[],[r272,r273,r274,r275,r276,r277,r278,r279,r280,r281,r282],[r241,r283,r284,r285,r286,r287,r288,r289,r290,r291],[r292,r293,r294,r295,r296,r297,r298,r299,r300],[],[],[],[],[r301,r302,r303,r304,r305,r306,r307,r308,262144],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[r309,r310,r311,r312,r313,r314,r315,r316,r317,r318,r319,r320,r321,r322,r323,r324,r325]),(⟨0,0,1⟩,[r309,r326,r327,r328,r329,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340]),(⟨0,0,2⟩,[r341,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351,r352,r353,r354,r355]),(⟨0,0,3⟩,[r341,r356,r357,r358,r359,r360,r361,r362,r363,r364,r365,r366,r367,r368]),(⟨0,0,4⟩,[r309,r369,r370,r371,r372,r373,r374,r375,r376,r377,r378,r379,r380]),(⟨0,0,5⟩,[r309,r381,r382,r383,r384,r385,r386,r387,r388,r389,r390,r391]),(⟨0,0,6⟩,[0,r392,r393,r394,r395,r396,r397,r398,r399,r400,r401]),(⟨0,1,0⟩,[r309,r326,r327,r328,r329,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340]),(⟨0,1,1⟩,[0,r402,r403,r404,r405,r406,r407,r408,r409,r410,r411,r412,r413,r414,r415]),(⟨0,1,2⟩,[r341,r416,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427,r428]),(⟨0,1,3⟩,[0,r429,r430,r431,r432,r433,r434,r435,r436,r437,r438,r439,r440]),(⟨0,1,4⟩,[r309,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451]),(⟨0,1,5⟩,[0,r392,r393,r452,r453,r454,r455,r456,r457,r458,r459]),(⟨0,2,0⟩,[r341,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351,r352,r353,r354,r355]),(⟨0,2,1⟩,[r341,r416,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427,r428]),(⟨0,2,2⟩,[r0,r460,r461,r462,r463,r464,r465,r466,r467,r468,r469,r470,r471]),(⟨0,2,3⟩,[r0,r472,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482]),(⟨0,2,4⟩,[0,r392,r393,r452,r453,r454,r455,r456,r457,r458,r459]),(⟨0,3,0⟩,[r341,r356,r357,r358,r359,r360,r361,r362,r363,r364,r365,r366,r367,r368]),(⟨0,3,1⟩,[0,r429,r430,r431,r432,r433,r434,r435,r436,r437,r438,r439,r440]),(⟨0,3,2⟩,[r0,r472,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482]),(⟨0,3,3⟩,[0,r83,r84,r85,r86,r87,r88,r89,r90,r91,r92]),(⟨0,4,0⟩,[r309,r369,r370,r371,r372,r373,r374,r375,r376,r377,r378,r379,r380]),(⟨0,4,1⟩,[r309,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451]),(⟨0,4,2⟩,[0,r392,r393,r452,r453,r454,r455,r456,r457,r458,r459]),(⟨0,5,0⟩,[r309,r381,r382,r383,r384,r385,r386,r387,r388,r389,r390,r391]),(⟨0,5,1⟩,[0,r392,r393,r452,r453,r454,r455,r456,r457,r458,r459]),(⟨0,6,0⟩,[0,r392,r393,r394,r395,r396,r397,r398,r399,r400,r401]),(⟨1,0,0⟩,[r309,r326,r327,r328,r329,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340]),(⟨1,0,1⟩,[0,r402,r403,r404,r405,r406,r407,r408,r409,r410,r411,r412,r413,r414,r415]),(⟨1,0,2⟩,[r341,r416,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427,r428]),(⟨1,0,3⟩,[0,r429,r430,r431,r432,r433,r434,r435,r436,r437,r438,r439,r440]),(⟨1,0,4⟩,[r309,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451]),(⟨1,0,5⟩,[0,r392,r393,r452,r453,r454,r455,r456,r457,r458,r459]),(⟨1,1,0⟩,[0,r402,r403,r404,r405,r406,r407,r408,r409,r410,r411,r412,r413,r414,r415]),(⟨1,1,1⟩,[0,0,r483,r484,r485,r486,r487,r488,r489,r490,r491,r492,r493,r494]),(⟨1,1,2⟩,[0,r495,r496,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506]),(⟨1,1,3⟩,[0,0,r175,r176,r507,r508,r509,r510,r511,r512,r513,r514]),(⟨1,2,0⟩,[r341,r416,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427,r428]),(⟨1,2,1⟩,[0,r495,r496,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506]),(⟨1,2,2⟩,[r341,r515,r516,r517,r518,r519,r520,r521,r522,r523,r524,r525]),(⟨1,2,3⟩,[r32,r526,r527,r528,r529,r530,r531,r532,r533,r534,r535]),(⟨1,2,4⟩,[r151,r17,r536,r537,r538,r539,r540,r541,r542,r543]),(⟨1,2,5⟩,[r151,r544,r545,r441,r546,r547,r548,r549,r550]),(⟨1,3,0⟩,[0,r429,r430,r431,r432,r433,r434,r435,r436,r437,r438,r439,r440]),(⟨1,3,1⟩,[0,0,r175,r176,r507,r508,r509,r510,r511,r512,r513,r514]),(⟨1,3,2⟩,[r32,r526,r527,r528,r529,r530,r531,r532,r533,r534,r535]),(⟨1,3,3⟩,[0,r301,r302,r303,r304,r305,r306,r307,r308,262144]),(⟨1,3,4⟩,[r151,r544,r551,r552,r553,r554,r555,r556,65536]),(⟨1,4,0⟩,[r309,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451]),(⟨1,4,2⟩,[r151,r17,r536,r537,r538,r539,r540,r541,r542,r543]),(⟨1,4,3⟩,[r151,r544,r551,r552,r553,r554,r555,r556,65536]),(⟨1,5,0⟩,[0,r392,r393,r452,r453,r454,r455,r456,r457,r458,r459]),(⟨1,5,2⟩,[r151,r544,r545,r441,r546,r547,r548,r549,r550]),(⟨2,0,0⟩,[r341,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351,r352,r353,r354,r355]),(⟨2,0,1⟩,[r341,r416,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427,r428]),(⟨2,0,2⟩,[r0,r460,r461,r462,r463,r464,r465,r466,r467,r468,r469,r470,r471]),(⟨2,0,3⟩,[r0,r472,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482]),(⟨2,0,4⟩,[0,r392,r393,r452,r453,r454,r455,r456,r457,r458,r459]),(⟨2,1,0⟩,[r341,r416,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427,r428]),(⟨2,1,1⟩,[0,r495,r496,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506]),(⟨2,1,2⟩,[r341,r515,r516,r517,r518,r519,r520,r521,r522,r523,r524,r525]),(⟨2,1,3⟩,[r32,r526,r527,r528,r529,r530,r531,r532,r533,r534,r535]),(⟨2,1,4⟩,[r151,r17,r536,r537,r538,r539,r540,r541,r542,r543]),(⟨2,1,5⟩,[r151,r544,r545,r441,r546,r547,r548,r549,r550]),(⟨2,2,0⟩,[r0,r460,r461,r462,r463,r464,r465,r466,r467,r468,r469,r470,r471]),(⟨2,2,1⟩,[r341,r515,r516,r517,r518,r519,r520,r521,r522,r523,r524,r525]),(⟨2,2,2⟩,[r557,r558,r559,r560,r561,r562,r563,r564,r565,r566,r567]),(⟨2,2,3⟩,[r151,r568,r569,r570,r571,r572,r573,r574,r575,r576]),(⟨2,2,4⟩,[r577,r578,r579,r580,r581,r582,r583,r584,r585]),(⟨2,3,0⟩,[r0,r472,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482]),(⟨2,3,1⟩,[r32,r526,r527,r528,r529,r530,r531,r532,r533,r534,r535]),(⟨2,3,2⟩,[r151,r568,r569,r570,r571,r572,r573,r574,r575,r576]),(⟨2,3,3⟩,[r241,r251,r266,r267,r268,r269,r270,r271,131072]),(⟨2,4,0⟩,[0,r392,r393,r452,r453,r454,r455,r456,r457,r458,r459]),(⟨2,4,1⟩,[r151,r17,r536,r537,r538,r539,r540,r541,r542,r543]),(⟨2,4,2⟩,[r577,r578,r579,r580,r581,r582,r583,r584,r585]),(⟨2,5,1⟩,[r151,r544,r545,r441,r546,r547,r548,r549,r550]),(⟨3,0,0⟩,[r341,r356,r357,r358,r359,r360,r361,r362,r363,r364,r365,r366,r367,r368]),(⟨3,0,1⟩,[0,r429,r430,r431,r432,r433,r434,r435,r436,r437,r438,r439,r440]),(⟨3,0,2⟩,[r0,r472,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482]),(⟨3,0,3⟩,[0,r83,r84,r85,r86,r87,r88,r89,r90,r91,r92]),(⟨3,1,0⟩,[0,r429,r430,r431,r432,r433,r434,r435,r436,r437,r438,r439,r440]),(⟨3,1,1⟩,[0,0,r175,r176,r507,r508,r509,r510,r511,r512,r513,r514]),(⟨3,1,2⟩,[r32,r526,r527,r528,r529,r530,r531,r532,r533,r534,r535]),(⟨3,1,3⟩,[0,r301,r302,r303,r304,r305,r306,r307,r308,262144]),(⟨3,1,4⟩,[r151,r544,r551,r552,r553,r554,r555,r556,65536]),(⟨3,2,0⟩,[r0,r472,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482]),(⟨3,2,1⟩,[r32,r526,r527,r528,r529,r530,r531,r532,r533,r534,r535]),(⟨3,2,2⟩,[r151,r568,r569,r570,r571,r572,r573,r574,r575,r576]),(⟨3,2,3⟩,[r241,r251,r266,r267,r268,r269,r270,r271,131072]),(⟨3,3,0⟩,[0,r83,r84,r85,r86,r87,r88,r89,r90,r91,r92]),(⟨3,3,1⟩,[0,r301,r302,r303,r304,r305,r306,r307,r308,262144]),(⟨3,3,2⟩,[r241,r251,r266,r267,r268,r269,r270,r271,131072]),(⟨3,4,1⟩,[r151,r544,r551,r552,r553,r554,r555,r556,65536]),(⟨4,0,0⟩,[r309,r369,r370,r371,r372,r373,r374,r375,r376,r377,r378,r379,r380]),(⟨4,0,1⟩,[r309,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451]),(⟨4,0,2⟩,[0,r392,r393,r452,r453,r454,r455,r456,r457,r458,r459]),(⟨4,1,0⟩,[r309,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451]),(⟨4,1,2⟩,[r151,r17,r536,r537,r538,r539,r540,r541,r542,r543]),(⟨4,1,3⟩,[r151,r544,r551,r552,r553,r554,r555,r556,65536]),(⟨4,2,0⟩,[0,r392,r393,r452,r453,r454,r455,r456,r457,r458,r459]),(⟨4,2,1⟩,[r151,r17,r536,r537,r538,r539,r540,r541,r542,r543]),(⟨4,2,2⟩,[r577,r578,r579,r580,r581,r582,r583,r584,r585]),(⟨4,3,1⟩,[r151,r544,r551,r552,r553,r554,r555,r556,65536]),(⟨5,0,0⟩,[r309,r381,r382,r383,r384,r385,r386,r387,r388,r389,r390,r391]),(⟨5,0,1⟩,[0,r392,r393,r452,r453,r454,r455,r456,r457,r458,r459]),(⟨5,1,0⟩,[0,r392,r393,r452,r453,r454,r455,r456,r457,r458,r459]),(⟨5,1,2⟩,[r151,r544,r545,r441,r546,r547,r548,r549,r550]),(⟨5,2,1⟩,[r151,r544,r545,r441,r546,r547,r548,r549,r550]),(⟨6,0,0⟩,[0,r392,r393,r394,r395,r396,r397,r398,r399,r400,r401])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[128,-1792,5120,30720,-231808,574208,-567040,116736]),(⟨0,0,1⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨0,0,2⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨0,0,3⟩,[-128,1536,256,-37376,76672]),(⟨0,1,0⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨0,1,1⟩,[0,-512,6144,-15360,-18432,60928]),(⟨0,1,2⟩,[-128,1536,-3840,-4608,15232]),(⟨0,2,0⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨0,2,1⟩,[-128,1536,-3840,-4608,15232]),(⟨0,3,0⟩,[-128,1536,256,-37376,76672]),(⟨1,0,0⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨1,0,1⟩,[0,-512,6144,-15360,-18432,60928]),(⟨1,0,2⟩,[-128,1536,-3840,-4608,15232]),(⟨1,1,0⟩,[0,-512,6144,-15360,-18432,60928]),(⟨1,2,0⟩,[-128,1536,-3840,-4608,15232]),(⟨2,0,0⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨2,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨2,1,0⟩,[-128,1536,-3840,-4608,15232]),(⟨3,0,0⟩,[-128,1536,256,-37376,76672])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[128,-2688,24576,-125568,372480,-579456,211968,627840,-719744,92160]),(⟨0,0,1⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920]),(⟨0,0,2⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨0,0,3⟩,[0,1280,-13056,47616,-60928,-24320,82176]),(⟨0,1,0⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920]),(⟨0,2,0⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨0,3,0⟩,[0,1280,-13056,47616,-60928,-24320,82176]),(⟨1,0,0⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920]),(⟨1,2,2⟩,[-512,6144,-15360,-18432,60928]),(⟨2,0,0⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨2,1,2⟩,[-512,6144,-15360,-18432,60928]),(⟨2,2,1⟩,[-512,6144,-15360,-18432,60928]),(⟨3,0,0⟩,[0,1280,-13056,47616,-60928,-24320,82176])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 3 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r586) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 12 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r586) sourceRight))).isZero := by decide +kernel

noncomputable def partial19 : Poly := []

theorem partial_sound19 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 19)
      sourceRight).eval u v t=partial19.eval u v t := by rfl

noncomputable def chunk16 : Poly := [(⟨2,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨2,1,0⟩,[-128,1536,-3840,-4608,15232]),(⟨3,0,0⟩,[-128,1536,256,-37376,76672])]

noncomputable def partial16 : Poly := [(⟨2,0,1⟩,[-16384,540672,-7766016,63553536,-320585728,974290944,-1394540544,-1158709248,8586280960,-13331251200,3240984576,12525944832,-11387813888,1403781120]),(⟨2,0,2⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨2,0,3⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨2,0,4⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨2,1,0⟩,[-16384,540672,-7766016,63553536,-320585728,974290944,-1394540544,-1158709248,8586280960,-13331251200,3240984576,12525944832,-11387813888,1403781120]),(⟨2,1,1⟩,[0,229376,-5996544,64716800,-372736000,1187971072,-1658781696,-1634009088,10358685696,-14627799040,1806336000,14589460480,-10781818880]),(⟨2,1,2⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨2,1,3⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨2,2,0⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨2,2,1⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨2,3,0⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨2,3,1⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨2,4,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨3,0,0⟩,[-16384,540672,-7241728,48349184,-123977728,-510492672,5755699200,-23452483584,51327287296,-53307162624,-7256834048,75062493184,-58628784128,7066091520]),(⟨3,0,1⟩,[0,229376,-5996544,61046784,-291471360,415170560,2448490496,-14774763520,35000221696,-35824762880,-6755287040,49032560640,-32526663680]),(⟨3,0,2⟩,[16384,-524288,6209536,-29425664,-17137664,805830656,-3594158080,6581780480,-2065088512,-9464971264,10493607936,-1373962240]),(⟨3,0,3⟩,[0,-163840,3637248,-25821184,29753344,507838464,-2844196864,6048055296,-3741450240,-4936073216,6300598272]),(⟨3,1,0⟩,[0,229376,-5996544,61046784,-291471360,415170560,2448490496,-14774763520,35000221696,-35824762880,-6755287040,49032560640,-32526663680]),(⟨3,2,0⟩,[16384,-524288,6209536,-29425664,-17137664,805830656,-3594158080,6581780480,-2065088512,-9464971264,10493607936,-1373962240]),(⟨3,2,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,3,0⟩,[0,-163840,3637248,-25821184,29753344,507838464,-2844196864,6048055296,-3741450240,-4936073216,6300598272]),(⟨3,3,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,0,0⟩,[0,114688,-2998272,28688384,-105103360,-178814976,3277881344,-13957758976,29820878848,-28510863360,-7658455040,41737830400,-27135754240]),(⟨4,0,1⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨4,1,0⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨4,1,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,2,2⟩,[196608,-4718592,38010880,-85458944,-335413248,1791492096,-1239154688,-4813488128,6527582208]),(⟨4,3,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,0,0⟩,[16384,-524288,6209536,-29425664,-17137664,805830656,-3594158080,6581780480,-2065088512,-9464971264,10493607936,-1373962240]),(⟨5,0,1⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨5,1,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨5,1,2⟩,[65536,-1572864,11272192,-524288,-308936704,1134034944,-473169920,-3690463232,4671471616]),(⟨5,2,1⟩,[65536,-1572864,11272192,-524288,-308936704,1134034944,-473169920,-3690463232,4671471616]),(⟨6,0,0⟩,[0,-163840,3637248,-25821184,29753344,507838464,-2844196864,6048055296,-3741450240,-4936073216,6300598272])]


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

noncomputable def partial12 : Poly := [(⟨1,0,2⟩,[-16384,540672,-7766016,63553536,-320585728,974290944,-1394540544,-1158709248,8586280960,-13331251200,3240984576,12525944832,-11387813888,1403781120]),(⟨1,0,3⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨1,0,4⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨1,0,5⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨1,1,0⟩,[0,-65536,2162688,-31064064,254214144,-1282342912,3897163776,-5578162176,-4634836992,34345123840,-53325004800,12963938304,50103779328,-45551255552,5615124480]),(⟨1,1,1⟩,[0,0,458752,-11993088,129433600,-745472000,2375942144,-3317563392,-3268018176,20717371392,-29255598080,3612672000,29178920960,-21563637760]),(⟨1,1,2⟩,[0,180224,-5095424,59293696,-362790912,1188134912,-1515159552,-2514255872,11357028352,-11723882496,-4895457280,15431614464,-6482739200]),(⟨1,1,3⟩,[0,0,-655360,14548992,-124256256,500695040,-774635520,-928776192,4902617088,-4526178304,-2996436992,5006819328]),(⟨1,2,0⟩,[-16384,540672,-7307264,51560448,-191152128,228818944,981401600,-4476272640,5318262784,7386120192,-26014613504,16138616832,17791107072,-20159856640]),(⟨1,2,1⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨1,2,2⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨1,2,3⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨1,3,0⟩,[0,180224,-5095424,59293696,-362790912,1188134912,-1515159552,-2514255872,11357028352,-11723882496,-4895457280,15431614464,-6482739200]),(⟨1,3,2⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨1,4,0⟩,[16384,-524288,6078464,-29556736,24281088,329252864,-1198948352,615645184,3800121344,-5975834624,-962215936,4733861888]),(⟨1,5,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨2,0,0⟩,[-16384,507904,-6422528,39632896,-74465280,-653852672,5821562880,-22554771456,48805396480,-52456210432,-660865024,66155036672,-61109354496,15433957376,-1156055040]),(⟨2,0,1⟩,[-16384,655360,-10534912,88080384,-396099584,701923328,1925218304,-14532870144,36898979840,-41606905856,-333430784,49656758272,-40651030528,5843353600]),(⟨2,0,2⟩,[16384,-262144,-573440,42205184,-415170560,2002518016,-5055283200,4533780480,7979810816,-22635085824,12099928064,11736711168,-10557030400]),(⟨2,0,3⟩,[16384,-688128,10043392,-65273856,156008448,358154240,-3125248000,7213023232,-4982620160,-5236752384,8050851840,-1303773184]),(⟨2,0,4⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨2,1,0⟩,[-16384,655360,-10076160,76087296,-266665984,-43548672,4301160448,-17850433536,33630961664,-20889534464,-29589028864,53269430272,-11472109568,-15720284160]),(⟨2,1,1⟩,[0,229376,-5996544,64716800,-372736000,1187971072,-1658781696,-1634009088,10358685696,-14627799040,1806336000,14589460480,-10781818880]),(⟨2,1,2⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨2,1,3⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨2,2,0⟩,[16384,-262144,-573440,42205184,-415170560,2002518016,-5055283200,4533780480,7979810816,-22635085824,12099928064,11736711168,-10557030400]),(⟨2,2,1⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨2,2,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,3,0⟩,[16384,-688128,10043392,-65273856,156008448,358154240,-3125248000,7213023232,-4982620160,-5236752384,8050851840,-1303773184]),(⟨2,3,1⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨2,3,2⟩,[0,262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨2,4,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨2,4,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,0,0⟩,[-16384,655360,-10010624,72876032,-199491584,-782860288,9075458048,-36826644480,79639986176,-81582817280,-10831249408,112193306624,-87892000768,11505664000]),(⟨3,0,1⟩,[0,229376,-5996544,61046784,-291471360,415170560,2448490496,-14774763520,35000221696,-35824762880,-6755287040,49032560640,-32526663680]),(⟨3,0,2⟩,[32768,-1048576,12943360,-73531392,131399680,634388480,-4018470912,8126201856,-3167584256,-10914627584,12527828992,-1646919680]),(⟨3,0,3⟩,[0,-163840,3637248,-25821184,29753344,507838464,-2844196864,6048055296,-3741450240,-4936073216,6300598272]),(⟨3,1,0⟩,[0,294912,-8093696,87982080,-467894272,1009319936,1762721792,-16472014848,41177907200,-40234745856,-12553912320,57169444864,-33618493440]),(⟨3,1,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,2,0⟩,[32768,-1048576,12943360,-73531392,131399680,634388480,-4018470912,8126201856,-3167584256,-10914627584,12527828992,-1646919680]),(⟨3,2,2⟩,[65536,-1179648,2883584,61865984,-470417408,969670656,889978880,-4741660672,2219900928,2947940352]),(⟨3,2,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,3,0⟩,[0,-163840,3637248,-25821184,29753344,507838464,-2844196864,6048055296,-3741450240,-4936073216,6300598272]),(⟨3,3,1⟩,[0,262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨3,3,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,4,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,0,0⟩,[16384,-376832,2424832,6176768,-147537920,635731968,-118620160,-7789969408,27442003968,-36518150144,2635137024,38885081088,-26910965760]),(⟨4,0,1⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨4,0,2⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨4,1,0⟩,[16384,-524288,6078464,-29556736,24281088,329252864,-1198948352,615645184,3800121344,-5975834624,-962215936,4733861888]),(⟨4,1,2⟩,[65536,-1441792,9175040,8388608,-300548096,1022623744,-424935424,-3209691136,4465950720,-764280832]),(⟨4,1,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,2,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨4,2,1⟩,[65536,-1441792,9175040,8388608,-300548096,1022623744,-424935424,-3209691136,4465950720,-764280832]),(⟨4,2,2⟩,[196608,-4718592,38010880,-85458944,-335413248,1791492096,-1239154688,-4813488128,6527582208]),(⟨4,3,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,0,0⟩,[16384,-688128,9519104,-50593792,-9666560,1335427072,-6295093248,12250382336,-5945212928,-13252067328,16510238720,-2404777984]),(⟨5,0,1⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨5,1,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨5,1,2⟩,[65536,-1572864,11272192,-524288,-308936704,1134034944,-473169920,-3690463232,4671471616]),(⟨5,2,1⟩,[65536,-1572864,11272192,-524288,-308936704,1134034944,-473169920,-3690463232,4671471616]),(⟨6,0,0⟩,[0,-163840,3637248,-25821184,29753344,507838464,-2844196864,6048055296,-3741450240,-4936073216,6300598272])]


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

noncomputable def partial8 : Poly := [(⟨0,2,1⟩,[-16384,540672,-7766016,63553536,-320585728,974290944,-1394540544,-1158709248,8586280960,-13331251200,3240984576,12525944832,-11387813888,1403781120]),(⟨0,2,2⟩,[0,114688,-2998272,32358400,-186368000,593985536,-829390848,-817004544,5179342848,-7313899520,903168000,7294730240,-5390909440]),(⟨0,2,3⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨0,2,4⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨0,3,0⟩,[-16384,540672,-7241728,48349184,-123977728,-510492672,5755699200,-23452483584,51327287296,-53307162624,-7256834048,75062493184,-58628784128,7066091520]),(⟨0,3,1⟩,[0,229376,-5996544,61046784,-291471360,415170560,2448490496,-14774763520,35000221696,-35824762880,-6755287040,49032560640,-32526663680]),(⟨0,3,2⟩,[16384,-524288,6209536,-29425664,-17137664,805830656,-3594158080,6581780480,-2065088512,-9464971264,10493607936,-1373962240]),(⟨0,3,3⟩,[0,-163840,3637248,-25821184,29753344,507838464,-2844196864,6048055296,-3741450240,-4936073216,6300598272]),(⟨0,4,0⟩,[0,114688,-2998272,28688384,-105103360,-178814976,3277881344,-13957758976,29820878848,-28510863360,-7658455040,41737830400,-27135754240]),(⟨0,4,1⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨0,5,0⟩,[16384,-524288,6209536,-29425664,-17137664,805830656,-3594158080,6581780480,-2065088512,-9464971264,10493607936,-1373962240]),(⟨0,5,1⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨0,6,0⟩,[0,-163840,3637248,-25821184,29753344,507838464,-2844196864,6048055296,-3741450240,-4936073216,6300598272]),(⟨1,0,0⟩,[16384,-606208,9699328,-87048192,458211328,-1153499136,-1789100032,27660877824,-116336115712,275824033792,-370654117888,170771398656,272203268096,-490503831552,273008066560,-30552883200]),(⟨1,0,1⟩,[0,-180224,5619712,-73809920,528039936,-2113732608,3377135616,10038116352,-73057140736,194777792512,-259644866560,92616310784,214207971328,-300923584512,122946682880]),(⟨1,0,2⟩,[-32768,1130496,-15908864,115261440,-413974528,171409408,4942757888,-21742649344,41004171264,-21979185152,-49223680000,86828630016,-31374491648,-14219018240]),(⟨1,0,3⟩,[0,344064,-9388032,102612992,-561299456,1368948736,979337216,-15922659328,42939613184,-45746864128,-6007046144,54166208512,-33725726720]),(⟨1,0,4⟩,[16384,-524288,6078464,-29556736,24281088,329252864,-1198948352,615645184,3800121344,-5975834624,-962215936,4733861888]),(⟨1,0,5⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨1,1,0⟩,[0,-180224,5619712,-73809920,528039936,-2113732608,3377135616,10038116352,-73057140736,194777792512,-259644866560,92616310784,214207971328,-300923584512,122946682880]),(⟨1,1,1⟩,[0,0,917504,-23986176,258867200,-1490944000,4751884288,-6635126784,-6536036352,41434742784,-58511196160,7225344000,58357841920,-43127275520]),(⟨1,1,2⟩,[0,180224,-5095424,59293696,-362790912,1188134912,-1515159552,-2514255872,11357028352,-11723882496,-4895457280,15431614464,-6482739200]),(⟨1,1,3⟩,[0,0,-655360,14548992,-124256256,500695040,-774635520,-928776192,4902617088,-4526178304,-2996436992,5006819328]),(⟨1,2,0⟩,[-32768,1130496,-15908864,115261440,-413974528,171409408,4942757888,-21742649344,41004171264,-21979185152,-49223680000,86828630016,-31374491648,-14219018240]),(⟨1,2,1⟩,[0,294912,-8093696,91652096,-549158912,1782120448,-2344550400,-3331260416,16536371200,-19037782016,-3992289280,22726344704,-11873648640]),(⟨1,2,2⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨1,2,3⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨1,3,0⟩,[0,458752,-12386304,131301376,-666402816,1190133760,4257218560,-29880418304,72760492032,-74257727488,-13665501184,95904038912,-60861480960]),(⟨1,3,1⟩,[0,0,-655360,14548992,-124256256,500695040,-774635520,-928776192,4902617088,-4526178304,-2996436992,5006819328]),(⟨1,3,2⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨1,4,0⟩,[16384,-524288,6078464,-29556736,24281088,329252864,-1198948352,615645184,3800121344,-5975834624,-962215936,4733861888]),(⟨1,4,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨1,5,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨1,5,2⟩,[65536,-1572864,11272192,-524288,-308936704,1134034944,-473169920,-3690463232,4671471616]),(⟨2,0,0⟩,[-16384,393216,-2965504,-3112960,199360512,-1485242368,5301534720,-6938492928,-19616907264,107976458240,-206980726784,145807409152,102994837504,-239938371584,116175503360]),(⟨2,0,1⟩,[-16384,655360,-10076160,76087296,-266665984,-43548672,4301160448,-17850433536,33630961664,-20889534464,-29589028864,53269430272,-11472109568,-15720284160]),(⟨2,0,2⟩,[16384,-262144,-573440,42205184,-415170560,2002518016,-5055283200,4533780480,7979810816,-22635085824,12099928064,11736711168,-10557030400]),(⟨2,0,3⟩,[16384,-688128,10043392,-65273856,156008448,358154240,-3125248000,7213023232,-4982620160,-5236752384,8050851840,-1303773184]),(⟨2,0,4⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨2,1,0⟩,[-16384,655360,-10076160,76087296,-266665984,-43548672,4301160448,-17850433536,33630961664,-20889534464,-29589028864,53269430272,-11472109568,-15720284160]),(⟨2,1,1⟩,[0,229376,-5996544,64716800,-372736000,1187971072,-1658781696,-1634009088,10358685696,-14627799040,1806336000,14589460480,-10781818880]),(⟨2,1,2⟩,[16384,-524288,6733824,-44105728,148537344,-171442176,-424312832,1544421376,-1102495744,-1449656320,2034221056,-272957440]),(⟨2,1,3⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨2,2,0⟩,[16384,-262144,-573440,42205184,-415170560,2002518016,-5055283200,4533780480,7979810816,-22635085824,12099928064,11736711168,-10557030400]),(⟨2,2,1⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨2,2,2⟩,[-65536,1835008,-18743296,73924608,61997056,-1546649600,5050466304,-4370989056,-10857545728,28851830784,-20198850560]),(⟨2,2,3⟩,[0,262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨2,2,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,3,0⟩,[32768,-1212416,16252928,-94699520,138870784,1163984896,-6719406080,13794803712,-7047708672,-14701723648,18544459776,-2677735424]),(⟨2,3,1⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨2,3,2⟩,[0,262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨2,3,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,4,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨2,4,2⟩,[196608,-4718592,38010880,-85458944,-335413248,1791492096,-1239154688,-4813488128,6527582208]),(⟨2,5,1⟩,[65536,-1572864,11272192,-524288,-308936704,1134034944,-473169920,-3690463232,4671471616]),(⟨3,0,0⟩,[-32768,1245184,-18612224,136577024,-422313984,-840269824,13036814336,-54093021184,115325894656,-110948122624,-34040315904,182883319808,-137057599488,17446502400]),(⟨3,0,1⟩,[0,294912,-8093696,87982080,-467894272,1009319936,1762721792,-16472014848,41177907200,-40234745856,-12553912320,57169444864,-33618493440]),(⟨3,0,2⟩,[32768,-1048576,12943360,-73531392,131399680,634388480,-4018470912,8126201856,-3167584256,-10914627584,12527828992,-1646919680]),(⟨3,0,3⟩,[0,-163840,3637248,-25821184,29753344,507838464,-2844196864,6048055296,-3741450240,-4936073216,6300598272]),(⟨3,1,0⟩,[0,294912,-8093696,87982080,-467894272,1009319936,1762721792,-16472014848,41177907200,-40234745856,-12553912320,57169444864,-33618493440]),(⟨3,1,2⟩,[-65536,1835008,-18743296,73924608,61997056,-1546649600,5050466304,-4370989056,-10857545728,28851830784,-20198850560]),(⟨3,1,3⟩,[0,262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨3,1,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,2,0⟩,[32768,-1048576,12943360,-73531392,131399680,634388480,-4018470912,8126201856,-3167584256,-10914627584,12527828992,-1646919680]),(⟨3,2,1⟩,[-65536,1671168,-15106048,42860544,187170816,-1740308480,4818272256,-3145334784,-11989090304,28102721536,-18947145728]),(⟨3,2,2⟩,[65536,-917504,-3407872,115343360,-640286720,916717568,2204893184,-6273630208,-26148864,6660161536]),(⟨3,2,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,3,0⟩,[0,-327680,7274496,-51642368,59506688,1015676928,-5688393728,12096110592,-7482900480,-9872146432,12601196544]),(⟨3,3,1⟩,[0,262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨3,3,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,4,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,0,0⟩,[16384,-212992,-1867776,49496064,-346046464,816545792,2375876608,-21198372864,59024588800,-70541131776,1523548160,77619675136,-54153953280]),(⟨4,0,1⟩,[16384,-524288,6078464,-29556736,24281088,329252864,-1198948352,615645184,3800121344,-5975834624,-962215936,4733861888]),(⟨4,0,2⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨4,1,0⟩,[16384,-524288,6078464,-29556736,24281088,329252864,-1198948352,615645184,3800121344,-5975834624,-962215936,4733861888]),(⟨4,1,2⟩,[65536,-1441792,9175040,8388608,-300548096,1022623744,-424935424,-3209691136,4465950720,-764280832]),(⟨4,1,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,2,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨4,2,1⟩,[65536,-1441792,9175040,8388608,-300548096,1022623744,-424935424,-3209691136,4465950720,-764280832]),(⟨4,2,2⟩,[196608,-4718592,38010880,-85458944,-335413248,1791492096,-1239154688,-4813488128,6527582208]),(⟨4,3,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,0,0⟩,[16384,-688128,9519104,-50593792,-9666560,1335427072,-6295093248,12250382336,-5945212928,-13252067328,16510238720,-2404777984]),(⟨5,0,1⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨5,1,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨5,1,2⟩,[65536,-1572864,11272192,-524288,-308936704,1134034944,-473169920,-3690463232,4671471616]),(⟨5,2,1⟩,[65536,-1572864,11272192,-524288,-308936704,1134034944,-473169920,-3690463232,4671471616]),(⟨6,0,0⟩,[0,-163840,3637248,-25821184,29753344,507838464,-2844196864,6048055296,-3741450240,-4936073216,6300598272])]


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

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[16384,-606208,9699328,-87048192,458211328,-1153499136,-1789100032,27660877824,-116336115712,275824033792,-370654117888,170771398656,272203268096,-490503831552,273008066560,-30552883200]),(⟨0,1,1⟩,[0,-180224,5619712,-73809920,528039936,-2113732608,3377135616,10038116352,-73057140736,194777792512,-259644866560,92616310784,214207971328,-300923584512,122946682880]),(⟨0,1,2⟩,[-32768,1130496,-15908864,115261440,-413974528,171409408,4942757888,-21742649344,41004171264,-21979185152,-49223680000,86828630016,-31374491648,-14219018240]),(⟨0,1,3⟩,[0,344064,-9388032,102612992,-561299456,1368948736,979337216,-15922659328,42939613184,-45746864128,-6007046144,54166208512,-33725726720]),(⟨0,1,4⟩,[16384,-524288,6078464,-29556736,24281088,329252864,-1198948352,615645184,3800121344,-5975834624,-962215936,4733861888]),(⟨0,1,5⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨0,2,0⟩,[-16384,393216,-2965504,-3112960,199360512,-1485242368,5301534720,-6938492928,-19616907264,107976458240,-206980726784,145807409152,102994837504,-239938371584,116175503360]),(⟨0,2,1⟩,[-16384,655360,-10076160,76087296,-266665984,-43548672,4301160448,-17850433536,33630961664,-20889534464,-29589028864,53269430272,-11472109568,-15720284160]),(⟨0,2,2⟩,[16384,-262144,-573440,42205184,-415170560,2002518016,-5055283200,4533780480,7979810816,-22635085824,12099928064,11736711168,-10557030400]),(⟨0,2,3⟩,[16384,-688128,10043392,-65273856,156008448,358154240,-3125248000,7213023232,-4982620160,-5236752384,8050851840,-1303773184]),(⟨0,2,4⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨0,3,0⟩,[-32768,1245184,-18612224,136577024,-422313984,-840269824,13036814336,-54093021184,115325894656,-110948122624,-34040315904,182883319808,-137057599488,17446502400]),(⟨0,3,1⟩,[0,294912,-8093696,87982080,-467894272,1009319936,1762721792,-16472014848,41177907200,-40234745856,-12553912320,57169444864,-33618493440]),(⟨0,3,2⟩,[32768,-1048576,12943360,-73531392,131399680,634388480,-4018470912,8126201856,-3167584256,-10914627584,12527828992,-1646919680]),(⟨0,3,3⟩,[0,-163840,3637248,-25821184,29753344,507838464,-2844196864,6048055296,-3741450240,-4936073216,6300598272]),(⟨0,4,0⟩,[16384,-212992,-1867776,49496064,-346046464,816545792,2375876608,-21198372864,59024588800,-70541131776,1523548160,77619675136,-54153953280]),(⟨0,4,1⟩,[16384,-524288,6078464,-29556736,24281088,329252864,-1198948352,615645184,3800121344,-5975834624,-962215936,4733861888]),(⟨0,4,2⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨0,5,0⟩,[16384,-688128,9519104,-50593792,-9666560,1335427072,-6295093248,12250382336,-5945212928,-13252067328,16510238720,-2404777984]),(⟨0,5,1⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨0,6,0⟩,[0,-163840,3637248,-25821184,29753344,507838464,-2844196864,6048055296,-3741450240,-4936073216,6300598272]),(⟨1,0,0⟩,[16384,-606208,9699328,-87048192,458211328,-1153499136,-1789100032,27660877824,-116336115712,275824033792,-370654117888,170771398656,272203268096,-490503831552,273008066560,-30552883200]),(⟨1,0,1⟩,[0,-180224,5619712,-73809920,528039936,-2113732608,3377135616,10038116352,-73057140736,194777792512,-259644866560,92616310784,214207971328,-300923584512,122946682880]),(⟨1,0,2⟩,[-32768,1130496,-15908864,115261440,-413974528,171409408,4942757888,-21742649344,41004171264,-21979185152,-49223680000,86828630016,-31374491648,-14219018240]),(⟨1,0,3⟩,[0,344064,-9388032,102612992,-561299456,1368948736,979337216,-15922659328,42939613184,-45746864128,-6007046144,54166208512,-33725726720]),(⟨1,0,4⟩,[16384,-524288,6078464,-29556736,24281088,329252864,-1198948352,615645184,3800121344,-5975834624,-962215936,4733861888]),(⟨1,0,5⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨1,1,0⟩,[0,-294912,9076736,-116555776,801865728,-2945122304,2857107456,25654394880,-141479444480,355210461184,-465964728320,172268683264,378312163328,-556295913472,240278241280]),(⟨1,1,1⟩,[0,0,1376256,-35979264,388300800,-2236416000,7127826432,-9952690176,-9804054528,62152114176,-87766794240,10838016000,87536762880,-64690913280]),(⟨1,1,2⟩,[0,294912,-8093696,91652096,-549158912,1782120448,-2344550400,-3331260416,16536371200,-19037782016,-3992289280,22726344704,-11873648640]),(⟨1,1,3⟩,[0,0,-655360,14548992,-124256256,500695040,-774635520,-928776192,4902617088,-4526178304,-2996436992,5006819328]),(⟨1,2,0⟩,[-32768,1245184,-18677760,139788288,-489488384,-100958208,8262516736,-35116810240,69316870144,-50254839808,-52798095360,123959443456,-60637708288,-9779445760]),(⟨1,2,1⟩,[0,294912,-8093696,91652096,-549158912,1782120448,-2344550400,-3331260416,16536371200,-19037782016,-3992289280,22726344704,-11873648640]),(⟨1,2,2⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨1,2,3⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨1,3,0⟩,[0,458752,-12386304,131301376,-666402816,1190133760,4257218560,-29880418304,72760492032,-74257727488,-13665501184,95904038912,-60861480960]),(⟨1,3,1⟩,[0,0,-655360,14548992,-124256256,500695040,-774635520,-928776192,4902617088,-4526178304,-2996436992,5006819328]),(⟨1,3,2⟩,[-65536,1671168,-15106048,42860544,187170816,-1740308480,4818272256,-3145334784,-11989090304,28102721536,-18947145728]),(⟨1,3,3⟩,[0,262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨1,3,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨1,4,0⟩,[16384,-524288,6078464,-29556736,24281088,329252864,-1198948352,615645184,3800121344,-5975834624,-962215936,4733861888]),(⟨1,4,2⟩,[65536,-1441792,9175040,8388608,-300548096,1022623744,-424935424,-3209691136,4465950720,-764280832]),(⟨1,4,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨1,5,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨1,5,2⟩,[65536,-1572864,11272192,-524288,-308936704,1134034944,-473169920,-3690463232,4671471616]),(⟨2,0,0⟩,[-16384,393216,-2965504,-3112960,199360512,-1485242368,5301534720,-6938492928,-19616907264,107976458240,-206980726784,145807409152,102994837504,-239938371584,116175503360]),(⟨2,0,1⟩,[-16384,655360,-10076160,76087296,-266665984,-43548672,4301160448,-17850433536,33630961664,-20889534464,-29589028864,53269430272,-11472109568,-15720284160]),(⟨2,0,2⟩,[16384,-262144,-573440,42205184,-415170560,2002518016,-5055283200,4533780480,7979810816,-22635085824,12099928064,11736711168,-10557030400]),(⟨2,0,3⟩,[16384,-688128,10043392,-65273856,156008448,358154240,-3125248000,7213023232,-4982620160,-5236752384,8050851840,-1303773184]),(⟨2,0,4⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨2,1,0⟩,[-32768,1245184,-18677760,139788288,-489488384,-100958208,8262516736,-35116810240,69316870144,-50254839808,-52798095360,123959443456,-60637708288,-9779445760]),(⟨2,1,1⟩,[0,294912,-8093696,91652096,-549158912,1782120448,-2344550400,-3331260416,16536371200,-19037782016,-3992289280,22726344704,-11873648640]),(⟨2,1,2⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨2,1,3⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨2,2,0⟩,[32768,-753664,4849664,19693568,-457605120,2817064960,-8451784704,10701570048,5600935936,-30642372608,22393520128,8883961856,-10332241920]),(⟨2,2,1⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨2,2,2⟩,[-131072,3670016,-37486592,147849216,123994112,-3093299200,10100932608,-8741978112,-21715091456,57703661568,-40397701120]),(⟨2,2,3⟩,[0,524288,-12582912,106954752,-339738624,-105906176,2629828608,-3063939072,-4492099584,7424442368]),(⟨2,2,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,3,0⟩,[32768,-1212416,16252928,-94699520,138870784,1163984896,-6719406080,13794803712,-7047708672,-14701723648,18544459776,-2677735424]),(⟨2,3,1⟩,[-65536,1671168,-15106048,42860544,187170816,-1740308480,4818272256,-3145334784,-11989090304,28102721536,-18947145728]),(⟨2,3,2⟩,[65536,-917504,-3407872,115343360,-640286720,916717568,2204893184,-6273630208,-26148864,6660161536]),(⟨2,3,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,4,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨2,4,1⟩,[65536,-1441792,9175040,8388608,-300548096,1022623744,-424935424,-3209691136,4465950720,-764280832]),(⟨2,4,2⟩,[196608,-4718592,38010880,-85458944,-335413248,1791492096,-1239154688,-4813488128,6527582208]),(⟨2,5,1⟩,[65536,-1572864,11272192,-524288,-308936704,1134034944,-473169920,-3690463232,4671471616]),(⟨3,0,0⟩,[-32768,1245184,-18612224,136577024,-422313984,-840269824,13036814336,-54093021184,115325894656,-110948122624,-34040315904,182883319808,-137057599488,17446502400]),(⟨3,0,1⟩,[0,294912,-8093696,87982080,-467894272,1009319936,1762721792,-16472014848,41177907200,-40234745856,-12553912320,57169444864,-33618493440]),(⟨3,0,2⟩,[32768,-1048576,12943360,-73531392,131399680,634388480,-4018470912,8126201856,-3167584256,-10914627584,12527828992,-1646919680]),(⟨3,0,3⟩,[0,-163840,3637248,-25821184,29753344,507838464,-2844196864,6048055296,-3741450240,-4936073216,6300598272]),(⟨3,1,0⟩,[0,458752,-12386304,131301376,-666402816,1190133760,4257218560,-29880418304,72760492032,-74257727488,-13665501184,95904038912,-60861480960]),(⟨3,1,1⟩,[0,0,-655360,14548992,-124256256,500695040,-774635520,-928776192,4902617088,-4526178304,-2996436992,5006819328]),(⟨3,1,2⟩,[-65536,1671168,-15106048,42860544,187170816,-1740308480,4818272256,-3145334784,-11989090304,28102721536,-18947145728]),(⟨3,1,3⟩,[0,262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨3,1,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,2,0⟩,[32768,-1212416,16252928,-94699520,138870784,1163984896,-6719406080,13794803712,-7047708672,-14701723648,18544459776,-2677735424]),(⟨3,2,1⟩,[-65536,1671168,-15106048,42860544,187170816,-1740308480,4818272256,-3145334784,-11989090304,28102721536,-18947145728]),(⟨3,2,2⟩,[65536,-917504,-3407872,115343360,-640286720,916717568,2204893184,-6273630208,-26148864,6660161536]),(⟨3,2,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,3,0⟩,[0,-327680,7274496,-51642368,59506688,1015676928,-5688393728,12096110592,-7482900480,-9872146432,12601196544]),(⟨3,3,1⟩,[0,262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨3,3,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,4,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,0,0⟩,[16384,-212992,-1867776,49496064,-346046464,816545792,2375876608,-21198372864,59024588800,-70541131776,1523548160,77619675136,-54153953280]),(⟨4,0,1⟩,[16384,-524288,6078464,-29556736,24281088,329252864,-1198948352,615645184,3800121344,-5975834624,-962215936,4733861888]),(⟨4,0,2⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨4,1,0⟩,[16384,-524288,6078464,-29556736,24281088,329252864,-1198948352,615645184,3800121344,-5975834624,-962215936,4733861888]),(⟨4,1,2⟩,[65536,-1441792,9175040,8388608,-300548096,1022623744,-424935424,-3209691136,4465950720,-764280832]),(⟨4,1,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,2,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨4,2,1⟩,[65536,-1441792,9175040,8388608,-300548096,1022623744,-424935424,-3209691136,4465950720,-764280832]),(⟨4,2,2⟩,[196608,-4718592,38010880,-85458944,-335413248,1791492096,-1239154688,-4813488128,6527582208]),(⟨4,3,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,0,0⟩,[16384,-688128,9519104,-50593792,-9666560,1335427072,-6295093248,12250382336,-5945212928,-13252067328,16510238720,-2404777984]),(⟨5,0,1⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨5,1,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨5,1,2⟩,[65536,-1572864,11272192,-524288,-308936704,1134034944,-473169920,-3690463232,4671471616]),(⟨5,2,1⟩,[65536,-1572864,11272192,-524288,-308936704,1134034944,-473169920,-3690463232,4671471616]),(⟨6,0,0⟩,[0,-163840,3637248,-25821184,29753344,507838464,-2844196864,6048055296,-3741450240,-4936073216,6300598272])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[16384,-573440,8617984,-69943296,286277632,67010560,-8197799936,52934836224,-190628184064,433302290432,-592296509440,326593265664,342346612736,-765912285184,534334177280,-136278441984,10758389760]),(⟨0,0,1⟩,[16384,-720896,12926976,-123797504,656310272,-1373863936,-5779849216,57611911168,-227751804928,527143796736,-701640065024,331723898880,482915516416,-894937956352,517101977600,-71868088320]),(⟨0,0,2⟩,[-32768,950272,-10518528,45547520,108003328,-2327052288,12577439744,-33990901760,34922135552,59632287744,-233549430784,251462746112,12938838016,-214819864576,114083594240]),(⟨0,0,3⟩,[-32768,1409024,-22577152,172621824,-542965760,-1188200448,18003197952,-75496947712,164017307648,-166295732224,-26946994176,236747358208,-186493698048,27039399936]),(⟨0,0,4⟩,[16384,-212992,-1867776,49496064,-346046464,816545792,2375876608,-21198372864,59024588800,-70541131776,1523548160,77619675136,-54153953280]),(⟨0,0,5⟩,[16384,-688128,9519104,-50593792,-9666560,1335427072,-6295093248,12250382336,-5945212928,-13252067328,16510238720,-2404777984]),(⟨0,0,6⟩,[0,-163840,3637248,-25821184,29753344,507838464,-2844196864,6048055296,-3741450240,-4936073216,6300598272]),(⟨0,1,0⟩,[16384,-720896,12926976,-123797504,656310272,-1373863936,-5779849216,57611911168,-227751804928,527143796736,-701640065024,331723898880,482915516416,-894937956352,517101977600,-71868088320]),(⟨0,1,1⟩,[0,-294912,9076736,-116555776,801865728,-2945122304,2857107456,25654394880,-141479444480,355210461184,-465964728320,172268683264,378312163328,-556295913472,240278241280]),(⟨0,1,2⟩,[-32768,1245184,-18677760,139788288,-489488384,-100958208,8262516736,-35116810240,69316870144,-50254839808,-52798095360,123959443456,-60637708288,-9779445760]),(⟨0,1,3⟩,[0,458752,-12386304,131301376,-666402816,1190133760,4257218560,-29880418304,72760492032,-74257727488,-13665501184,95904038912,-60861480960]),(⟨0,1,4⟩,[16384,-524288,6078464,-29556736,24281088,329252864,-1198948352,615645184,3800121344,-5975834624,-962215936,4733861888]),(⟨0,1,5⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨0,2,0⟩,[-32768,950272,-10518528,45547520,108003328,-2327052288,12577439744,-33990901760,34922135552,59632287744,-233549430784,251462746112,12938838016,-214819864576,114083594240]),(⟨0,2,1⟩,[-32768,1245184,-18677760,139788288,-489488384,-100958208,8262516736,-35116810240,69316870144,-50254839808,-52798095360,123959443456,-60637708288,-9779445760]),(⟨0,2,2⟩,[32768,-753664,4849664,19693568,-457605120,2817064960,-8451784704,10701570048,5600935936,-30642372608,22393520128,8883961856,-10332241920]),(⟨0,2,3⟩,[32768,-1212416,16252928,-94699520,138870784,1163984896,-6719406080,13794803712,-7047708672,-14701723648,18544459776,-2677735424]),(⟨0,2,4⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨0,3,0⟩,[-32768,1409024,-22577152,172621824,-542965760,-1188200448,18003197952,-75496947712,164017307648,-166295732224,-26946994176,236747358208,-186493698048,27039399936]),(⟨0,3,1⟩,[0,458752,-12386304,131301376,-666402816,1190133760,4257218560,-29880418304,72760492032,-74257727488,-13665501184,95904038912,-60861480960]),(⟨0,3,2⟩,[32768,-1212416,16252928,-94699520,138870784,1163984896,-6719406080,13794803712,-7047708672,-14701723648,18544459776,-2677735424]),(⟨0,3,3⟩,[0,-327680,7274496,-51642368,59506688,1015676928,-5688393728,12096110592,-7482900480,-9872146432,12601196544]),(⟨0,4,0⟩,[16384,-212992,-1867776,49496064,-346046464,816545792,2375876608,-21198372864,59024588800,-70541131776,1523548160,77619675136,-54153953280]),(⟨0,4,1⟩,[16384,-524288,6078464,-29556736,24281088,329252864,-1198948352,615645184,3800121344,-5975834624,-962215936,4733861888]),(⟨0,4,2⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨0,5,0⟩,[16384,-688128,9519104,-50593792,-9666560,1335427072,-6295093248,12250382336,-5945212928,-13252067328,16510238720,-2404777984]),(⟨0,5,1⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨0,6,0⟩,[0,-163840,3637248,-25821184,29753344,507838464,-2844196864,6048055296,-3741450240,-4936073216,6300598272]),(⟨1,0,0⟩,[16384,-720896,12926976,-123797504,656310272,-1373863936,-5779849216,57611911168,-227751804928,527143796736,-701640065024,331723898880,482915516416,-894937956352,517101977600,-71868088320]),(⟨1,0,1⟩,[0,-294912,9076736,-116555776,801865728,-2945122304,2857107456,25654394880,-141479444480,355210461184,-465964728320,172268683264,378312163328,-556295913472,240278241280]),(⟨1,0,2⟩,[-32768,1245184,-18677760,139788288,-489488384,-100958208,8262516736,-35116810240,69316870144,-50254839808,-52798095360,123959443456,-60637708288,-9779445760]),(⟨1,0,3⟩,[0,458752,-12386304,131301376,-666402816,1190133760,4257218560,-29880418304,72760492032,-74257727488,-13665501184,95904038912,-60861480960]),(⟨1,0,4⟩,[16384,-524288,6078464,-29556736,24281088,329252864,-1198948352,615645184,3800121344,-5975834624,-962215936,4733861888]),(⟨1,0,5⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨1,1,0⟩,[0,-294912,9076736,-116555776,801865728,-2945122304,2857107456,25654394880,-141479444480,355210461184,-465964728320,172268683264,378312163328,-556295913472,240278241280]),(⟨1,1,1⟩,[0,0,1376256,-35979264,388300800,-2236416000,7127826432,-9952690176,-9804054528,62152114176,-87766794240,10838016000,87536762880,-64690913280]),(⟨1,1,2⟩,[0,294912,-8093696,91652096,-549158912,1782120448,-2344550400,-3331260416,16536371200,-19037782016,-3992289280,22726344704,-11873648640]),(⟨1,1,3⟩,[0,0,-655360,14548992,-124256256,500695040,-774635520,-928776192,4902617088,-4526178304,-2996436992,5006819328]),(⟨1,2,0⟩,[-32768,1245184,-18677760,139788288,-489488384,-100958208,8262516736,-35116810240,69316870144,-50254839808,-52798095360,123959443456,-60637708288,-9779445760]),(⟨1,2,1⟩,[0,294912,-8093696,91652096,-549158912,1782120448,-2344550400,-3331260416,16536371200,-19037782016,-3992289280,22726344704,-11873648640]),(⟨1,2,2⟩,[-32768,655360,-2129920,-47316992,566689792,-2736521216,6275923968,-3130261504,-17485430784,40744648704,-32631848960,6566576128]),(⟨1,2,3⟩,[-65536,1671168,-15106048,42860544,187170816,-1740308480,4818272256,-3145334784,-11989090304,28102721536,-18947145728]),(⟨1,2,4⟩,[65536,-1441792,9175040,8388608,-300548096,1022623744,-424935424,-3209691136,4465950720,-764280832]),(⟨1,2,5⟩,[65536,-1572864,11272192,-524288,-308936704,1134034944,-473169920,-3690463232,4671471616]),(⟨1,3,0⟩,[0,458752,-12386304,131301376,-666402816,1190133760,4257218560,-29880418304,72760492032,-74257727488,-13665501184,95904038912,-60861480960]),(⟨1,3,1⟩,[0,0,-655360,14548992,-124256256,500695040,-774635520,-928776192,4902617088,-4526178304,-2996436992,5006819328]),(⟨1,3,2⟩,[-65536,1671168,-15106048,42860544,187170816,-1740308480,4818272256,-3145334784,-11989090304,28102721536,-18947145728]),(⟨1,3,3⟩,[0,262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨1,3,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨1,4,0⟩,[16384,-524288,6078464,-29556736,24281088,329252864,-1198948352,615645184,3800121344,-5975834624,-962215936,4733861888]),(⟨1,4,2⟩,[65536,-1441792,9175040,8388608,-300548096,1022623744,-424935424,-3209691136,4465950720,-764280832]),(⟨1,4,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨1,5,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨1,5,2⟩,[65536,-1572864,11272192,-524288,-308936704,1134034944,-473169920,-3690463232,4671471616]),(⟨2,0,0⟩,[-32768,950272,-10518528,45547520,108003328,-2327052288,12577439744,-33990901760,34922135552,59632287744,-233549430784,251462746112,12938838016,-214819864576,114083594240]),(⟨2,0,1⟩,[-32768,1245184,-18677760,139788288,-489488384,-100958208,8262516736,-35116810240,69316870144,-50254839808,-52798095360,123959443456,-60637708288,-9779445760]),(⟨2,0,2⟩,[32768,-753664,4849664,19693568,-457605120,2817064960,-8451784704,10701570048,5600935936,-30642372608,22393520128,8883961856,-10332241920]),(⟨2,0,3⟩,[32768,-1212416,16252928,-94699520,138870784,1163984896,-6719406080,13794803712,-7047708672,-14701723648,18544459776,-2677735424]),(⟨2,0,4⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨2,1,0⟩,[-32768,1245184,-18677760,139788288,-489488384,-100958208,8262516736,-35116810240,69316870144,-50254839808,-52798095360,123959443456,-60637708288,-9779445760]),(⟨2,1,1⟩,[0,294912,-8093696,91652096,-549158912,1782120448,-2344550400,-3331260416,16536371200,-19037782016,-3992289280,22726344704,-11873648640]),(⟨2,1,2⟩,[-32768,655360,-2129920,-47316992,566689792,-2736521216,6275923968,-3130261504,-17485430784,40744648704,-32631848960,6566576128]),(⟨2,1,3⟩,[-65536,1671168,-15106048,42860544,187170816,-1740308480,4818272256,-3145334784,-11989090304,28102721536,-18947145728]),(⟨2,1,4⟩,[65536,-1441792,9175040,8388608,-300548096,1022623744,-424935424,-3209691136,4465950720,-764280832]),(⟨2,1,5⟩,[65536,-1572864,11272192,-524288,-308936704,1134034944,-473169920,-3690463232,4671471616]),(⟨2,2,0⟩,[32768,-753664,4849664,19693568,-457605120,2817064960,-8451784704,10701570048,5600935936,-30642372608,22393520128,8883961856,-10332241920]),(⟨2,2,1⟩,[-32768,655360,-2129920,-47316992,566689792,-2736521216,6275923968,-3130261504,-17485430784,40744648704,-32631848960,6566576128]),(⟨2,2,2⟩,[-196608,5505024,-56229888,221773824,185991168,-4639948800,15151398912,-13112967168,-32572637184,86555492352,-60596551680]),(⟨2,2,3⟩,[65536,-917504,-3407872,115343360,-640286720,916717568,2204893184,-6273630208,-26148864,6660161536]),(⟨2,2,4⟩,[196608,-4718592,38010880,-85458944,-335413248,1791492096,-1239154688,-4813488128,6527582208]),(⟨2,3,0⟩,[32768,-1212416,16252928,-94699520,138870784,1163984896,-6719406080,13794803712,-7047708672,-14701723648,18544459776,-2677735424]),(⟨2,3,1⟩,[-65536,1671168,-15106048,42860544,187170816,-1740308480,4818272256,-3145334784,-11989090304,28102721536,-18947145728]),(⟨2,3,2⟩,[65536,-917504,-3407872,115343360,-640286720,916717568,2204893184,-6273630208,-26148864,6660161536]),(⟨2,3,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,4,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨2,4,1⟩,[65536,-1441792,9175040,8388608,-300548096,1022623744,-424935424,-3209691136,4465950720,-764280832]),(⟨2,4,2⟩,[196608,-4718592,38010880,-85458944,-335413248,1791492096,-1239154688,-4813488128,6527582208]),(⟨2,5,1⟩,[65536,-1572864,11272192,-524288,-308936704,1134034944,-473169920,-3690463232,4671471616]),(⟨3,0,0⟩,[-32768,1409024,-22577152,172621824,-542965760,-1188200448,18003197952,-75496947712,164017307648,-166295732224,-26946994176,236747358208,-186493698048,27039399936]),(⟨3,0,1⟩,[0,458752,-12386304,131301376,-666402816,1190133760,4257218560,-29880418304,72760492032,-74257727488,-13665501184,95904038912,-60861480960]),(⟨3,0,2⟩,[32768,-1212416,16252928,-94699520,138870784,1163984896,-6719406080,13794803712,-7047708672,-14701723648,18544459776,-2677735424]),(⟨3,0,3⟩,[0,-327680,7274496,-51642368,59506688,1015676928,-5688393728,12096110592,-7482900480,-9872146432,12601196544]),(⟨3,1,0⟩,[0,458752,-12386304,131301376,-666402816,1190133760,4257218560,-29880418304,72760492032,-74257727488,-13665501184,95904038912,-60861480960]),(⟨3,1,1⟩,[0,0,-655360,14548992,-124256256,500695040,-774635520,-928776192,4902617088,-4526178304,-2996436992,5006819328]),(⟨3,1,2⟩,[-65536,1671168,-15106048,42860544,187170816,-1740308480,4818272256,-3145334784,-11989090304,28102721536,-18947145728]),(⟨3,1,3⟩,[0,262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨3,1,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,2,0⟩,[32768,-1212416,16252928,-94699520,138870784,1163984896,-6719406080,13794803712,-7047708672,-14701723648,18544459776,-2677735424]),(⟨3,2,1⟩,[-65536,1671168,-15106048,42860544,187170816,-1740308480,4818272256,-3145334784,-11989090304,28102721536,-18947145728]),(⟨3,2,2⟩,[65536,-917504,-3407872,115343360,-640286720,916717568,2204893184,-6273630208,-26148864,6660161536]),(⟨3,2,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,3,0⟩,[0,-327680,7274496,-51642368,59506688,1015676928,-5688393728,12096110592,-7482900480,-9872146432,12601196544]),(⟨3,3,1⟩,[0,262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨3,3,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,4,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,0,0⟩,[16384,-212992,-1867776,49496064,-346046464,816545792,2375876608,-21198372864,59024588800,-70541131776,1523548160,77619675136,-54153953280]),(⟨4,0,1⟩,[16384,-524288,6078464,-29556736,24281088,329252864,-1198948352,615645184,3800121344,-5975834624,-962215936,4733861888]),(⟨4,0,2⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨4,1,0⟩,[16384,-524288,6078464,-29556736,24281088,329252864,-1198948352,615645184,3800121344,-5975834624,-962215936,4733861888]),(⟨4,1,2⟩,[65536,-1441792,9175040,8388608,-300548096,1022623744,-424935424,-3209691136,4465950720,-764280832]),(⟨4,1,3⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,2,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨4,2,1⟩,[65536,-1441792,9175040,8388608,-300548096,1022623744,-424935424,-3209691136,4465950720,-764280832]),(⟨4,2,2⟩,[196608,-4718592,38010880,-85458944,-335413248,1791492096,-1239154688,-4813488128,6527582208]),(⟨4,3,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,0,0⟩,[16384,-688128,9519104,-50593792,-9666560,1335427072,-6295093248,12250382336,-5945212928,-13252067328,16510238720,-2404777984]),(⟨5,0,1⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨5,1,0⟩,[0,-163840,3637248,-31064064,125173760,-193658880,-232194048,1225654272,-1131544576,-749109248,1251704832]),(⟨5,1,2⟩,[65536,-1572864,11272192,-524288,-308936704,1134034944,-473169920,-3690463232,4671471616]),(⟨5,2,1⟩,[65536,-1572864,11272192,-524288,-308936704,1134034944,-473169920,-3690463232,4671471616]),(⟨6,0,0⟩,[0,-163840,3637248,-25821184,29753344,507838464,-2844196864,6048055296,-3741450240,-4936073216,6300598272])]


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
    (Poly.add (Poly.scale (K.ofRat r587) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 3 12).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r586*r586 : ℚ)=r587 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 3 12 r586 r586 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 3=12 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 3 12).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C093

#print axioms Coulomb8.Columns.C093.sound
