import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C147

def r0 : ℚ := { num := 16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -98304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 13516800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -164265984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 1374388224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -8322711552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 37244878848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -123003371520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 291122741248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -450151809024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 300131401728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 407346905088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -1242006061056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := 1168939450368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := -17747656704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -123528314880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 633754894336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -132663214080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 8493465600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := -32768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := 8060928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := -131072000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := 185958400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := -1250852864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := 5957419008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := -142153744384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := 338868076544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := -514415558656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := 311146119168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 519297302528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -692813824, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 1181281648640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 137984409600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -964452024320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 82571591680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -9319219200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 1343488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := -23871488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := 35225600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -1646968832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 7350943744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -3035414528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 32797523968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 9274736640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -162104246272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 321902821376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -179077152768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -301969981440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 522528456704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -19763576832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := -30541578240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 17422336000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 32768, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -18055168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 261423104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -131006464, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 12295176192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -2663415808, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 108256821248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -20653670400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 18318852096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := 286495309824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := -436161413120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := 18348441600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 262419415040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -226794897408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 27831173120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -655360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 8880128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -50855936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 20692992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := 1523187712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := -10343677952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := 34609299456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := -61884088320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := 35872440320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 74075701248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -21450194944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 57210322944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := 10533601280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := -8263761920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -327680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 9895936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -2555904, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 873529344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -518127616, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 8693088256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -8983019520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -1137836032, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 32024494080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -23675600896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -286982144, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 447545344, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -420741120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := 1638400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -1966080, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := 292356096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := -82313216, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 3795976192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -4956880896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -107085824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 10789322752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -9422176256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := -3997040640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := 6752894976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 32768, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := -6488064, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := 585859072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -4538630144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 23320756224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -82340151296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 28214460416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -293319475200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := 157704355840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 326909624320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -784921886720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 11917721600, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := 22807347200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := -10742988800, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := 5112627200, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 32768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := -7831552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := 116129792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -992346112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 5401051136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -19267420160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 43447353344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := -50223120384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := -15485992960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := 144101965824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := -26165903360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := 3951165440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := 19350650880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -2122874880, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 258867200, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -327680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 55836672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := -605290496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := 3812360192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := -15160246272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := 38078513152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := -7654604800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := 14014742528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 86894379008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -19510067200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 38609879040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 11189616640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -8309637120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -1310720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 22347776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -213385216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 1251966976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := -654049280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 9633136640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -6938427392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -16603709440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 6245056512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -3662479360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := -3880255488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 759201792, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -187432960, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 13107200, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := 3276800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := -3932160, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := 584712192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := -164626432, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 7591952384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := -9913761792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := -214171648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := 21578645504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -18844352512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := -7994081280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := 13505789952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 4325376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := -62128128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := 508428288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := -150863872, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := 458489856, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -11156324352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := -9269673984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := 68690247680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := -106650009600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := 25927876608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := 100207558656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -91102511104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := 94371840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := 131072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := -23986176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := 258867200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := -212992000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := 4751884288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -6635126784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := -6536036352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := 41434742784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := -58511196160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := 147456000, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := 8336834560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := -51773440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := 131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := -4194304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := 53870592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := -352845824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := 1188298752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -1371537408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := -3394502656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := 12355371008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -1259995136, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := -1656750080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := 2324824064, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := -2621440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 29097984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -248512512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := 1001390080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := -1549271040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := -1857552384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 9805234176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -9052356608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := -5992873984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 84148224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := 393216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -71958528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 776601600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -638976000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 14255652864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -19905380352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := -19608109056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := 124304228352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := -175533588480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := 442368000, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := 25010503680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := -155320320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := 262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -6291456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 3145728, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -169869312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -52953088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 1314914304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := -1531969536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -18874368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := 524288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -12582912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := 6291456, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := -339738624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := -105906176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := 2629828608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := -3063939072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := -37748736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := 1, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18],[0,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35],[r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52],[0,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63,r64,r65,r66,r67],[r0,r68,r69,r70,r71,r72,r73,r74,r75,r76,r77,r78,r79,r80,r81],[0,r82,r83,r84,r85,r86,r87,r88,r89,r90,r91,r92,r93,r94],[0,0,r95,r96,r97,r98,r99,r100,r101,r102,r103,r104,r105],[],[],[],[],[],[],[0,0,r106,r107,r108,r109,r110,r111,r112,r113,r114,r115,r116,r117,r118,r119,r120],[0,r121,r122,r123,r124,r125,r126,r127,r128,r129,r130,r131,r132,r133,r134,r135],[0,0,r136,r137,r138,r139,r140,r141,r142,r143,r144,r145,r146,r147,r148],[],[],[],[],[],[],[],[],[r149,r150,r151,r152,r153,r154,r155,r156,r157,r158,r159,r160,r161,r162,r163],[0,r82,r83,r84,r85,r86,r87,r88,r89,r90,r91,r92,r93,r94],[],[],[],[],[],[],[],[0,0,r164,r165,r166,r167,r168,r169,r170,r171,r172,r173,r174],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[r175,r176,r177,r178,r179,r180,r181,r182,r183,r184,r185,r186,r187,r188],[0,r189,r190,r191,r192,r193,r194,r195,r196,r197,r198,r199,r200],[r201,r202,r203,r204,r205,r206,r207,r208,r209,r210,r211,r212],[0,r150,r213,r214,r215,r216,r217,r218,r219,r220,r221],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,r222,r223,r224,r225,r226,r227,r228,r229,r230,r231,r232,r233],[r201,r202,r203,r204,r205,r206,r207,r208,r209,r210,r211,r212],[0,r150,r213,r214,r215,r216,r217,r218,r219,r220,r221],[],[],[],[],[],[],[],[],[],[r234,r235,r236,r237,r238,r239,r240,r241,262144],[],[],[],[],[r242,r243,r244,r245,r246,r247,r248,r249,524288],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17,r18]),(⟨0,0,1⟩,[0,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35]),(⟨0,0,2⟩,[r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52]),(⟨0,0,3⟩,[0,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63,r64,r65,r66,r67]),(⟨0,0,4⟩,[r0,r68,r69,r70,r71,r72,r73,r74,r75,r76,r77,r78,r79,r80,r81]),(⟨0,0,5⟩,[0,r82,r83,r84,r85,r86,r87,r88,r89,r90,r91,r92,r93,r94]),(⟨0,0,6⟩,[0,0,r95,r96,r97,r98,r99,r100,r101,r102,r103,r104,r105]),(⟨0,1,0⟩,[0,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35]),(⟨0,1,1⟩,[0,0,r106,r107,r108,r109,r110,r111,r112,r113,r114,r115,r116,r117,r118,r119,r120]),(⟨0,1,2⟩,[0,r121,r122,r123,r124,r125,r126,r127,r128,r129,r130,r131,r132,r133,r134,r135]),(⟨0,1,3⟩,[0,0,r136,r137,r138,r139,r140,r141,r142,r143,r144,r145,r146,r147,r148]),(⟨0,2,0⟩,[r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52]),(⟨0,2,1⟩,[0,r121,r122,r123,r124,r125,r126,r127,r128,r129,r130,r131,r132,r133,r134,r135]),(⟨0,2,2⟩,[r149,r150,r151,r152,r153,r154,r155,r156,r157,r158,r159,r160,r161,r162,r163]),(⟨0,2,3⟩,[0,r82,r83,r84,r85,r86,r87,r88,r89,r90,r91,r92,r93,r94]),(⟨0,3,0⟩,[0,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63,r64,r65,r66,r67]),(⟨0,3,1⟩,[0,0,r136,r137,r138,r139,r140,r141,r142,r143,r144,r145,r146,r147,r148]),(⟨0,3,2⟩,[0,r82,r83,r84,r85,r86,r87,r88,r89,r90,r91,r92,r93,r94]),(⟨0,3,3⟩,[0,0,r164,r165,r166,r167,r168,r169,r170,r171,r172,r173,r174]),(⟨0,4,0⟩,[r0,r68,r69,r70,r71,r72,r73,r74,r75,r76,r77,r78,r79,r80,r81]),(⟨0,5,0⟩,[0,r82,r83,r84,r85,r86,r87,r88,r89,r90,r91,r92,r93,r94]),(⟨0,6,0⟩,[0,0,r95,r96,r97,r98,r99,r100,r101,r102,r103,r104,r105]),(⟨1,0,0⟩,[0,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34,r35]),(⟨1,0,1⟩,[0,0,r106,r107,r108,r109,r110,r111,r112,r113,r114,r115,r116,r117,r118,r119,r120]),(⟨1,0,2⟩,[0,r121,r122,r123,r124,r125,r126,r127,r128,r129,r130,r131,r132,r133,r134,r135]),(⟨1,0,3⟩,[0,0,r136,r137,r138,r139,r140,r141,r142,r143,r144,r145,r146,r147,r148]),(⟨1,1,0⟩,[0,0,r106,r107,r108,r109,r110,r111,r112,r113,r114,r115,r116,r117,r118,r119,r120]),(⟨1,2,0⟩,[0,r121,r122,r123,r124,r125,r126,r127,r128,r129,r130,r131,r132,r133,r134,r135]),(⟨1,2,2⟩,[r175,r176,r177,r178,r179,r180,r181,r182,r183,r184,r185,r186,r187,r188]),(⟨1,2,3⟩,[0,r189,r190,r191,r192,r193,r194,r195,r196,r197,r198,r199,r200]),(⟨1,2,4⟩,[r201,r202,r203,r204,r205,r206,r207,r208,r209,r210,r211,r212]),(⟨1,2,5⟩,[0,r150,r213,r214,r215,r216,r217,r218,r219,r220,r221]),(⟨1,3,0⟩,[0,0,r136,r137,r138,r139,r140,r141,r142,r143,r144,r145,r146,r147,r148]),(⟨1,3,2⟩,[0,r189,r190,r191,r192,r193,r194,r195,r196,r197,r198,r199,r200]),(⟨1,4,2⟩,[r201,r202,r203,r204,r205,r206,r207,r208,r209,r210,r211,r212]),(⟨1,5,2⟩,[0,r150,r213,r214,r215,r216,r217,r218,r219,r220,r221]),(⟨2,0,0⟩,[r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52]),(⟨2,0,1⟩,[0,r121,r122,r123,r124,r125,r126,r127,r128,r129,r130,r131,r132,r133,r134,r135]),(⟨2,0,2⟩,[r149,r150,r151,r152,r153,r154,r155,r156,r157,r158,r159,r160,r161,r162,r163]),(⟨2,0,3⟩,[0,r82,r83,r84,r85,r86,r87,r88,r89,r90,r91,r92,r93,r94]),(⟨2,1,0⟩,[0,r121,r122,r123,r124,r125,r126,r127,r128,r129,r130,r131,r132,r133,r134,r135]),(⟨2,1,2⟩,[r175,r176,r177,r178,r179,r180,r181,r182,r183,r184,r185,r186,r187,r188]),(⟨2,1,3⟩,[0,r189,r190,r191,r192,r193,r194,r195,r196,r197,r198,r199,r200]),(⟨2,1,4⟩,[r201,r202,r203,r204,r205,r206,r207,r208,r209,r210,r211,r212]),(⟨2,1,5⟩,[0,r150,r213,r214,r215,r216,r217,r218,r219,r220,r221]),(⟨2,2,0⟩,[r149,r150,r151,r152,r153,r154,r155,r156,r157,r158,r159,r160,r161,r162,r163]),(⟨2,2,1⟩,[r175,r176,r177,r178,r179,r180,r181,r182,r183,r184,r185,r186,r187,r188]),(⟨2,2,2⟩,[0,r222,r223,r224,r225,r226,r227,r228,r229,r230,r231,r232,r233]),(⟨2,2,3⟩,[r201,r202,r203,r204,r205,r206,r207,r208,r209,r210,r211,r212]),(⟨2,2,4⟩,[0,r150,r213,r214,r215,r216,r217,r218,r219,r220,r221]),(⟨2,3,0⟩,[0,r82,r83,r84,r85,r86,r87,r88,r89,r90,r91,r92,r93,r94]),(⟨2,3,1⟩,[0,r189,r190,r191,r192,r193,r194,r195,r196,r197,r198,r199,r200]),(⟨2,3,2⟩,[r201,r202,r203,r204,r205,r206,r207,r208,r209,r210,r211,r212]),(⟨2,4,1⟩,[r201,r202,r203,r204,r205,r206,r207,r208,r209,r210,r211,r212]),(⟨2,4,2⟩,[0,r150,r213,r214,r215,r216,r217,r218,r219,r220,r221]),(⟨2,4,4⟩,[r234,r235,r236,r237,r238,r239,r240,r241,262144]),(⟨2,5,1⟩,[0,r150,r213,r214,r215,r216,r217,r218,r219,r220,r221]),(⟨3,0,0⟩,[0,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63,r64,r65,r66,r67]),(⟨3,0,1⟩,[0,0,r136,r137,r138,r139,r140,r141,r142,r143,r144,r145,r146,r147,r148]),(⟨3,0,2⟩,[0,r82,r83,r84,r85,r86,r87,r88,r89,r90,r91,r92,r93,r94]),(⟨3,0,3⟩,[0,0,r164,r165,r166,r167,r168,r169,r170,r171,r172,r173,r174]),(⟨3,1,0⟩,[0,0,r136,r137,r138,r139,r140,r141,r142,r143,r144,r145,r146,r147,r148]),(⟨3,1,2⟩,[0,r189,r190,r191,r192,r193,r194,r195,r196,r197,r198,r199,r200]),(⟨3,2,0⟩,[0,r82,r83,r84,r85,r86,r87,r88,r89,r90,r91,r92,r93,r94]),(⟨3,2,1⟩,[0,r189,r190,r191,r192,r193,r194,r195,r196,r197,r198,r199,r200]),(⟨3,2,2⟩,[r201,r202,r203,r204,r205,r206,r207,r208,r209,r210,r211,r212]),(⟨3,3,0⟩,[0,0,r164,r165,r166,r167,r168,r169,r170,r171,r172,r173,r174]),(⟨3,3,4⟩,[r242,r243,r244,r245,r246,r247,r248,r249,524288]),(⟨3,4,3⟩,[r242,r243,r244,r245,r246,r247,r248,r249,524288]),(⟨4,0,0⟩,[r0,r68,r69,r70,r71,r72,r73,r74,r75,r76,r77,r78,r79,r80,r81]),(⟨4,1,2⟩,[r201,r202,r203,r204,r205,r206,r207,r208,r209,r210,r211,r212]),(⟨4,2,1⟩,[r201,r202,r203,r204,r205,r206,r207,r208,r209,r210,r211,r212]),(⟨4,2,2⟩,[0,r150,r213,r214,r215,r216,r217,r218,r219,r220,r221]),(⟨4,2,4⟩,[r234,r235,r236,r237,r238,r239,r240,r241,262144]),(⟨4,3,3⟩,[r242,r243,r244,r245,r246,r247,r248,r249,524288]),(⟨4,4,2⟩,[r234,r235,r236,r237,r238,r239,r240,r241,262144]),(⟨5,0,0⟩,[0,r82,r83,r84,r85,r86,r87,r88,r89,r90,r91,r92,r93,r94]),(⟨5,1,2⟩,[0,r150,r213,r214,r215,r216,r217,r218,r219,r220,r221]),(⟨5,2,1⟩,[0,r150,r213,r214,r215,r216,r217,r218,r219,r220,r221]),(⟨6,0,0⟩,[0,0,r95,r96,r97,r98,r99,r100,r101,r102,r103,r104,r105])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[128,-2688,24576,-125568,372480,-579456,211968,627840,-719744,92160]),(⟨0,0,1⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920]),(⟨0,0,2⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨0,0,3⟩,[0,1280,-13056,47616,-60928,-24320,82176]),(⟨0,1,0⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920]),(⟨0,2,0⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨0,3,0⟩,[0,1280,-13056,47616,-60928,-24320,82176]),(⟨1,0,0⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920]),(⟨1,2,2⟩,[-512,6144,-15360,-18432,60928]),(⟨2,0,0⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨2,1,2⟩,[-512,6144,-15360,-18432,60928]),(⟨2,2,1⟩,[-512,6144,-15360,-18432,60928]),(⟨3,0,0⟩,[0,1280,-13056,47616,-60928,-24320,82176])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[128,-2688,24576,-125568,372480,-579456,211968,627840,-719744,92160]),(⟨0,0,1⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920]),(⟨0,0,2⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨0,0,3⟩,[0,1280,-13056,47616,-60928,-24320,82176]),(⟨0,1,0⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920]),(⟨0,2,0⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨0,3,0⟩,[0,1280,-13056,47616,-60928,-24320,82176]),(⟨1,0,0⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920]),(⟨1,2,2⟩,[-512,6144,-15360,-18432,60928]),(⟨2,0,0⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨2,1,2⟩,[-512,6144,-15360,-18432,60928]),(⟨2,2,1⟩,[-512,6144,-15360,-18432,60928]),(⟨3,0,0⟩,[0,1280,-13056,47616,-60928,-24320,82176])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 12 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r250) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 12 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r250) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨3,0,0⟩,[0,1280,-13056,47616,-60928,-24320,82176])]

noncomputable def partial12 : Poly := [(⟨3,0,0⟩,[0,163840,-5111808,72646656,-617381888,3447062528,-13005324288,32404733952,-47176286208,16902422528,71196672000,-126500044800,50390466560,63482429440,-61387014144,7573340160]),(⟨3,0,1⟩,[0,0,-1146880,27918336,-302645248,1906180096,-7580123136,19039256576,-26791116800,7007371264,43447189504,-68285235200,19304939520,39163658240,-29083729920]),(⟨3,0,2⟩,[0,-163840,4947968,-62619648,436764672,-1813446656,4346544128,-4491509760,-3982426112,16012247040,-11837800448,-7031062528,10964860928,-1472593920]),(⟨3,0,3⟩,[0,0,1638400,-33423360,292356096,-1399324672,3795976192,-4956880896,-749600768,10789322752,-9422176256,-3997040640,6752894976]),(⟨3,1,0⟩,[0,0,-1146880,27918336,-302645248,1906180096,-7580123136,19039256576,-26791116800,7007371264,43447189504,-68285235200,19304939520,39163658240,-29083729920]),(⟨3,2,0⟩,[0,-163840,4947968,-62619648,436764672,-1813446656,4346544128,-4491509760,-3982426112,16012247040,-11837800448,-7031062528,10964860928,-1472593920]),(⟨3,3,0⟩,[0,0,1638400,-33423360,292356096,-1399324672,3795976192,-4956880896,-749600768,10789322752,-9422176256,-3997040640,6752894976]),(⟨4,0,0⟩,[0,0,-1146880,27918336,-302645248,1906180096,-7580123136,19039256576,-26791116800,7007371264,43447189504,-68285235200,19304939520,39163658240,-29083729920]),(⟨4,2,2⟩,[0,-655360,14548992,-124256256,500695040,-774635520,-928776192,4902617088,-4526178304,-2996436992,5006819328]),(⟨5,0,0⟩,[0,-163840,4947968,-62619648,436764672,-1813446656,4346544128,-4491509760,-3982426112,16012247040,-11837800448,-7031062528,10964860928,-1472593920]),(⟨5,1,2⟩,[0,-655360,14548992,-124256256,500695040,-774635520,-928776192,4902617088,-4526178304,-2996436992,5006819328]),(⟨5,2,1⟩,[0,-655360,14548992,-124256256,500695040,-774635520,-928776192,4902617088,-4526178304,-2996436992,5006819328]),(⟨6,0,0⟩,[0,0,1638400,-33423360,292356096,-1399324672,3795976192,-4956880896,-749600768,10789322752,-9422176256,-3997040640,6752894976])]


theorem partial_checked12 :
    (Poly.add (Poly.add (Poly.mul chunk12 sourceRight) partial13)
      (Poly.scale (K.ofRat (-1)) partial12)).isZero := by decide +kernel

theorem partial_sound12 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 12)
      sourceRight).eval u v t=partial12.eval u v t := by
  change (Poly.mul (chunk12++(sourceLeft.drop 13))
    sourceRight).eval u v t=partial12.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound13 partial_checked12 u v t


noncomputable def chunk8 : Poly := [(⟨1,2,2⟩,[-512,6144,-15360,-18432,60928]),(⟨2,0,0⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨2,1,2⟩,[-512,6144,-15360,-18432,60928]),(⟨2,2,1⟩,[-512,6144,-15360,-18432,60928])]

noncomputable def partial8 : Poly := [(⟨1,2,2⟩,[-65536,2162688,-31064064,254214144,-1282342912,3897163776,-5578162176,-4634836992,34345123840,-53325004800,12963938304,50103779328,-45551255552,5615124480]),(⟨1,2,3⟩,[0,458752,-11993088,129433600,-745472000,2375942144,-3317563392,-3268018176,20717371392,-29255598080,3612672000,29178920960,-21563637760]),(⟨1,2,4⟩,[65536,-2097152,26935296,-176422912,594149376,-685768704,-1697251328,6177685504,-4409982976,-5798625280,8136884224,-1091829760]),(⟨1,2,5⟩,[0,-655360,14548992,-124256256,500695040,-774635520,-928776192,4902617088,-4526178304,-2996436992,5006819328]),(⟨1,3,2⟩,[0,458752,-11993088,129433600,-745472000,2375942144,-3317563392,-3268018176,20717371392,-29255598080,3612672000,29178920960,-21563637760]),(⟨1,4,2⟩,[65536,-2097152,26935296,-176422912,594149376,-685768704,-1697251328,6177685504,-4409982976,-5798625280,8136884224,-1091829760]),(⟨1,5,2⟩,[0,-655360,14548992,-124256256,500695040,-774635520,-928776192,4902617088,-4526178304,-2996436992,5006819328]),(⟨2,0,0⟩,[-16384,671744,-12337152,134643712,-969949184,4810129408,-16454139904,36983799808,-44737937408,-7722254336,121525321728,-171265982464,45245480960,115272138752,-109085376512,24706088960,-1651507200]),(⟨2,0,1⟩,[0,114688,-3915776,58064896,-496173056,2700525568,-9633710080,21723676672,-25111560192,-7742996480,72050982912,-91580661760,13829079040,67727278080,-52010434560,6342246400]),(⟨2,0,2⟩,[16384,-655360,11173888,-106692608,625983488,-2289172480,4816568320,-3469213696,-8301854720,21857697792,-12818677760,-13580894208,18600443904,-4592107520,321126400]),(⟨2,0,3⟩,[0,-163840,4947968,-62619648,436764672,-1813446656,4346544128,-4491509760,-3982426112,16012247040,-11837800448,-7031062528,10964860928,-1472593920]),(⟨2,1,0⟩,[0,114688,-3915776,58064896,-496173056,2700525568,-9633710080,21723676672,-25111560192,-7742996480,72050982912,-91580661760,13829079040,67727278080,-52010434560,6342246400]),(⟨2,1,2⟩,[-65536,2162688,-31064064,254214144,-1282342912,3897163776,-5578162176,-4634836992,34345123840,-53325004800,12963938304,50103779328,-45551255552,5615124480]),(⟨2,1,3⟩,[0,458752,-11993088,129433600,-745472000,2375942144,-3317563392,-3268018176,20717371392,-29255598080,3612672000,29178920960,-21563637760]),(⟨2,1,4⟩,[65536,-2097152,26935296,-176422912,594149376,-685768704,-1697251328,6177685504,-4409982976,-5798625280,8136884224,-1091829760]),(⟨2,1,5⟩,[0,-655360,14548992,-124256256,500695040,-774635520,-928776192,4902617088,-4526178304,-2996436992,5006819328]),(⟨2,2,0⟩,[16384,-655360,11173888,-106692608,625983488,-2289172480,4816568320,-3469213696,-8301854720,21857697792,-12818677760,-13580894208,18600443904,-4592107520,321126400]),(⟨2,2,1⟩,[-65536,2162688,-31064064,254214144,-1282342912,3897163776,-5578162176,-4634836992,34345123840,-53325004800,12963938304,50103779328,-45551255552,5615124480]),(⟨2,2,2⟩,[0,1376256,-35979264,388300800,-2236416000,7127826432,-9952690176,-9804054528,62152114176,-87766794240,10838016000,87536762880,-64690913280]),(⟨2,2,3⟩,[65536,-2097152,26935296,-176422912,594149376,-685768704,-1697251328,6177685504,-4409982976,-5798625280,8136884224,-1091829760]),(⟨2,2,4⟩,[0,-655360,14548992,-124256256,500695040,-774635520,-928776192,4902617088,-4526178304,-2996436992,5006819328]),(⟨2,3,0⟩,[0,-163840,4947968,-62619648,436764672,-1813446656,4346544128,-4491509760,-3982426112,16012247040,-11837800448,-7031062528,10964860928,-1472593920]),(⟨2,3,1⟩,[0,458752,-11993088,129433600,-745472000,2375942144,-3317563392,-3268018176,20717371392,-29255598080,3612672000,29178920960,-21563637760]),(⟨2,3,2⟩,[65536,-2097152,26935296,-176422912,594149376,-685768704,-1697251328,6177685504,-4409982976,-5798625280,8136884224,-1091829760]),(⟨2,4,1⟩,[65536,-2097152,26935296,-176422912,594149376,-685768704,-1697251328,6177685504,-4409982976,-5798625280,8136884224,-1091829760]),(⟨2,4,2⟩,[0,-655360,14548992,-124256256,500695040,-774635520,-928776192,4902617088,-4526178304,-2996436992,5006819328]),(⟨2,4,4⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨2,5,1⟩,[0,-655360,14548992,-124256256,500695040,-774635520,-928776192,4902617088,-4526178304,-2996436992,5006819328]),(⟨3,0,0⟩,[0,278528,-9027584,130711552,-1113554944,6147588096,-22639034368,54128410624,-72287846400,9159426048,143247654912,-218080706560,64219545600,131209707520,-113397448704,13915586560]),(⟨3,0,1⟩,[0,0,-1146880,27918336,-302645248,1906180096,-7580123136,19039256576,-26791116800,7007371264,43447189504,-68285235200,19304939520,39163658240,-29083729920]),(⟨3,0,2⟩,[0,-163840,4947968,-62619648,436764672,-1813446656,4346544128,-4491509760,-3982426112,16012247040,-11837800448,-7031062528,10964860928,-1472593920]),(⟨3,0,3⟩,[0,0,1638400,-33423360,292356096,-1399324672,3795976192,-4956880896,-749600768,10789322752,-9422176256,-3997040640,6752894976]),(⟨3,1,0⟩,[0,0,-1146880,27918336,-302645248,1906180096,-7580123136,19039256576,-26791116800,7007371264,43447189504,-68285235200,19304939520,39163658240,-29083729920]),(⟨3,1,2⟩,[0,458752,-11993088,129433600,-745472000,2375942144,-3317563392,-3268018176,20717371392,-29255598080,3612672000,29178920960,-21563637760]),(⟨3,2,0⟩,[0,-163840,4947968,-62619648,436764672,-1813446656,4346544128,-4491509760,-3982426112,16012247040,-11837800448,-7031062528,10964860928,-1472593920]),(⟨3,2,1⟩,[0,458752,-11993088,129433600,-745472000,2375942144,-3317563392,-3268018176,20717371392,-29255598080,3612672000,29178920960,-21563637760]),(⟨3,2,2⟩,[131072,-4194304,53870592,-352845824,1188298752,-1371537408,-3394502656,12355371008,-8819965952,-11597250560,16273768448,-2183659520]),(⟨3,3,0⟩,[0,0,1638400,-33423360,292356096,-1399324672,3795976192,-4956880896,-749600768,10789322752,-9422176256,-3997040640,6752894976]),(⟨3,3,4⟩,[524288,-12582912,106954752,-339738624,-105906176,2629828608,-3063939072,-4492099584,7424442368]),(⟨3,4,3⟩,[524288,-12582912,106954752,-339738624,-105906176,2629828608,-3063939072,-4492099584,7424442368]),(⟨4,0,0⟩,[16384,-655360,10027008,-78774272,323338240,-382992384,-2763554816,15570042880,-35092971520,28865069056,30628511744,-81866129408,37905383424,34571550720,-28762603520]),(⟨4,1,2⟩,[131072,-4194304,53870592,-352845824,1188298752,-1371537408,-3394502656,12355371008,-8819965952,-11597250560,16273768448,-2183659520]),(⟨4,2,1⟩,[131072,-4194304,53870592,-352845824,1188298752,-1371537408,-3394502656,12355371008,-8819965952,-11597250560,16273768448,-2183659520]),(⟨4,2,2⟩,[0,-1310720,29097984,-248512512,1001390080,-1549271040,-1857552384,9805234176,-9052356608,-5992873984,10013638656]),(⟨4,2,4⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨4,3,3⟩,[524288,-12582912,106954752,-339738624,-105906176,2629828608,-3063939072,-4492099584,7424442368]),(⟨4,4,2⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨5,0,0⟩,[0,-327680,9895936,-125239296,873529344,-3626893312,8693088256,-8983019520,-7964852224,32024494080,-23675600896,-14062125056,21929721856,-2945187840]),(⟨5,1,2⟩,[0,-1310720,29097984,-248512512,1001390080,-1549271040,-1857552384,9805234176,-9052356608,-5992873984,10013638656]),(⟨5,2,1⟩,[0,-1310720,29097984,-248512512,1001390080,-1549271040,-1857552384,9805234176,-9052356608,-5992873984,10013638656]),(⟨6,0,0⟩,[0,0,1638400,-33423360,292356096,-1399324672,3795976192,-4956880896,-749600768,10789322752,-9422176256,-3997040640,6752894976])]


theorem partial_checked8 :
    (Poly.add (Poly.add (Poly.mul chunk8 sourceRight) partial12)
      (Poly.scale (K.ofRat (-1)) partial8)).isZero := by decide +kernel

theorem partial_sound8 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 8)
      sourceRight).eval u v t=partial8.eval u v t := by
  change (Poly.mul (chunk8++(sourceLeft.drop 12))
    sourceRight).eval u v t=partial8.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound12 partial_checked8 u v t


noncomputable def chunk4 : Poly := [(⟨0,1,0⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920]),(⟨0,2,0⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨0,3,0⟩,[0,1280,-13056,47616,-60928,-24320,82176]),(⟨1,0,0⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920])]

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[0,-114688,4030464,-65536000,650854400,-4377985024,20850966528,-71076872192,169434038272,-257207779328,155573059584,259648651264,-700781182976,590640824320,68992204800,-482226012160,289000570880,-32617267200]),(⟨0,1,1⟩,[0,0,802816,-22708224,292929536,-2269315072,11660378112,-41170075648,98750611456,-146659737600,78852177920,163454812160,-392460943360,291984179200,79825715200,-263203225600,125259366400]),(⟨0,1,2⟩,[0,114688,-3915776,58064896,-496173056,2700525568,-9633710080,21723676672,-25111560192,-7742996480,72050982912,-91580661760,13829079040,67727278080,-52010434560,6342246400]),(⟨0,1,3⟩,[0,0,-1146880,27918336,-302645248,1906180096,-7580123136,19039256576,-26791116800,7007371264,43447189504,-68285235200,19304939520,39163658240,-29083729920]),(⟨0,2,0⟩,[-16384,671744,-11534336,111935488,-677019648,2540814336,-4793761792,-4186275840,54012674048,-154381991936,200377499648,-7811170304,-347215462400,407256317952,-29259661312,-238497136640,123607859200]),(⟨0,2,1⟩,[0,114688,-3915776,58064896,-496173056,2700525568,-9633710080,21723676672,-25111560192,-7742996480,72050982912,-91580661760,13829079040,67727278080,-52010434560,6342246400]),(⟨0,2,2⟩,[16384,-655360,11173888,-106692608,625983488,-2289172480,4816568320,-3469213696,-8301854720,21857697792,-12818677760,-13580894208,18600443904,-4592107520,321126400]),(⟨0,2,3⟩,[0,-163840,4947968,-62619648,436764672,-1813446656,4346544128,-4491509760,-3982426112,16012247040,-11837800448,-7031062528,10964860928,-1472593920]),(⟨0,3,0⟩,[0,393216,-12943360,188776448,-1609728000,8848113664,-32272744448,75852087296,-97399406592,1416429568,215298637824,-309661368320,78048624640,198936985600,-165407883264,20257832960]),(⟨0,3,1⟩,[0,0,-1146880,27918336,-302645248,1906180096,-7580123136,19039256576,-26791116800,7007371264,43447189504,-68285235200,19304939520,39163658240,-29083729920]),(⟨0,3,2⟩,[0,-163840,4947968,-62619648,436764672,-1813446656,4346544128,-4491509760,-3982426112,16012247040,-11837800448,-7031062528,10964860928,-1472593920]),(⟨0,3,3⟩,[0,0,1638400,-33423360,292356096,-1399324672,3795976192,-4956880896,-749600768,10789322752,-9422176256,-3997040640,6752894976]),(⟨0,4,0⟩,[16384,-655360,8880128,-50855936,20692992,1523187712,-10343677952,34609299456,-61884088320,35872440320,74075701248,-150151364608,57210322944,73735208960,-57846333440]),(⟨0,5,0⟩,[0,-327680,9895936,-125239296,873529344,-3626893312,8693088256,-8983019520,-7964852224,32024494080,-23675600896,-14062125056,21929721856,-2945187840]),(⟨0,6,0⟩,[0,0,1638400,-33423360,292356096,-1399324672,3795976192,-4956880896,-749600768,10789322752,-9422176256,-3997040640,6752894976]),(⟨1,0,0⟩,[0,-114688,4030464,-65536000,650854400,-4377985024,20850966528,-71076872192,169434038272,-257207779328,155573059584,259648651264,-700781182976,590640824320,68992204800,-482226012160,289000570880,-32617267200]),(⟨1,0,1⟩,[0,0,802816,-22708224,292929536,-2269315072,11660378112,-41170075648,98750611456,-146659737600,78852177920,163454812160,-392460943360,291984179200,79825715200,-263203225600,125259366400]),(⟨1,0,2⟩,[0,114688,-3915776,58064896,-496173056,2700525568,-9633710080,21723676672,-25111560192,-7742996480,72050982912,-91580661760,13829079040,67727278080,-52010434560,6342246400]),(⟨1,0,3⟩,[0,0,-1146880,27918336,-302645248,1906180096,-7580123136,19039256576,-26791116800,7007371264,43447189504,-68285235200,19304939520,39163658240,-29083729920]),(⟨1,1,0⟩,[0,0,1605632,-45416448,585859072,-4538630144,23320756224,-82340151296,197501222912,-293319475200,157704355840,326909624320,-784921886720,583968358400,159651430400,-526406451200,250518732800]),(⟨1,2,0⟩,[0,229376,-7831552,116129792,-992346112,5401051136,-19267420160,43447353344,-50223120384,-15485992960,144101965824,-183161323520,27658158080,135454556160,-104020869120,12684492800]),(⟨1,2,2⟩,[-65536,2162688,-31064064,254214144,-1282342912,3897163776,-5578162176,-4634836992,34345123840,-53325004800,12963938304,50103779328,-45551255552,5615124480]),(⟨1,2,3⟩,[0,458752,-11993088,129433600,-745472000,2375942144,-3317563392,-3268018176,20717371392,-29255598080,3612672000,29178920960,-21563637760]),(⟨1,2,4⟩,[65536,-2097152,26935296,-176422912,594149376,-685768704,-1697251328,6177685504,-4409982976,-5798625280,8136884224,-1091829760]),(⟨1,2,5⟩,[0,-655360,14548992,-124256256,500695040,-774635520,-928776192,4902617088,-4526178304,-2996436992,5006819328]),(⟨1,3,0⟩,[0,0,-2293760,55836672,-605290496,3812360192,-15160246272,38078513152,-53582233600,14014742528,86894379008,-136570470400,38609879040,78327316480,-58167459840]),(⟨1,3,2⟩,[0,917504,-23986176,258867200,-1490944000,4751884288,-6635126784,-6536036352,41434742784,-58511196160,7225344000,58357841920,-43127275520]),(⟨1,4,2⟩,[131072,-4194304,53870592,-352845824,1188298752,-1371537408,-3394502656,12355371008,-8819965952,-11597250560,16273768448,-2183659520]),(⟨1,5,2⟩,[0,-1310720,29097984,-248512512,1001390080,-1549271040,-1857552384,9805234176,-9052356608,-5992873984,10013638656]),(⟨2,0,0⟩,[-16384,671744,-11534336,111935488,-677019648,2540814336,-4793761792,-4186275840,54012674048,-154381991936,200377499648,-7811170304,-347215462400,407256317952,-29259661312,-238497136640,123607859200]),(⟨2,0,1⟩,[0,114688,-3915776,58064896,-496173056,2700525568,-9633710080,21723676672,-25111560192,-7742996480,72050982912,-91580661760,13829079040,67727278080,-52010434560,6342246400]),(⟨2,0,2⟩,[16384,-655360,11173888,-106692608,625983488,-2289172480,4816568320,-3469213696,-8301854720,21857697792,-12818677760,-13580894208,18600443904,-4592107520,321126400]),(⟨2,0,3⟩,[0,-163840,4947968,-62619648,436764672,-1813446656,4346544128,-4491509760,-3982426112,16012247040,-11837800448,-7031062528,10964860928,-1472593920]),(⟨2,1,0⟩,[0,229376,-7831552,116129792,-992346112,5401051136,-19267420160,43447353344,-50223120384,-15485992960,144101965824,-183161323520,27658158080,135454556160,-104020869120,12684492800]),(⟨2,1,2⟩,[-65536,2162688,-31064064,254214144,-1282342912,3897163776,-5578162176,-4634836992,34345123840,-53325004800,12963938304,50103779328,-45551255552,5615124480]),(⟨2,1,3⟩,[0,458752,-11993088,129433600,-745472000,2375942144,-3317563392,-3268018176,20717371392,-29255598080,3612672000,29178920960,-21563637760]),(⟨2,1,4⟩,[65536,-2097152,26935296,-176422912,594149376,-685768704,-1697251328,6177685504,-4409982976,-5798625280,8136884224,-1091829760]),(⟨2,1,5⟩,[0,-655360,14548992,-124256256,500695040,-774635520,-928776192,4902617088,-4526178304,-2996436992,5006819328]),(⟨2,2,0⟩,[32768,-1310720,22347776,-213385216,1251966976,-4578344960,9633136640,-6938427392,-16603709440,43715395584,-25637355520,-27161788416,37200887808,-9184215040,642252800]),(⟨2,2,1⟩,[-65536,2162688,-31064064,254214144,-1282342912,3897163776,-5578162176,-4634836992,34345123840,-53325004800,12963938304,50103779328,-45551255552,5615124480]),(⟨2,2,2⟩,[0,2293760,-59965440,647168000,-3727360000,11879710720,-16587816960,-16340090880,103586856960,-146277990400,18063360000,145894604800,-107818188800]),(⟨2,2,3⟩,[65536,-2097152,26935296,-176422912,594149376,-685768704,-1697251328,6177685504,-4409982976,-5798625280,8136884224,-1091829760]),(⟨2,2,4⟩,[0,-655360,14548992,-124256256,500695040,-774635520,-928776192,4902617088,-4526178304,-2996436992,5006819328]),(⟨2,3,0⟩,[0,-327680,9895936,-125239296,873529344,-3626893312,8693088256,-8983019520,-7964852224,32024494080,-23675600896,-14062125056,21929721856,-2945187840]),(⟨2,3,1⟩,[0,917504,-23986176,258867200,-1490944000,4751884288,-6635126784,-6536036352,41434742784,-58511196160,7225344000,58357841920,-43127275520]),(⟨2,3,2⟩,[131072,-4194304,53870592,-352845824,1188298752,-1371537408,-3394502656,12355371008,-8819965952,-11597250560,16273768448,-2183659520]),(⟨2,4,1⟩,[131072,-4194304,53870592,-352845824,1188298752,-1371537408,-3394502656,12355371008,-8819965952,-11597250560,16273768448,-2183659520]),(⟨2,4,2⟩,[0,-1310720,29097984,-248512512,1001390080,-1549271040,-1857552384,9805234176,-9052356608,-5992873984,10013638656]),(⟨2,4,4⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨2,5,1⟩,[0,-1310720,29097984,-248512512,1001390080,-1549271040,-1857552384,9805234176,-9052356608,-5992873984,10013638656]),(⟨3,0,0⟩,[0,393216,-12943360,188776448,-1609728000,8848113664,-32272744448,75852087296,-97399406592,1416429568,215298637824,-309661368320,78048624640,198936985600,-165407883264,20257832960]),(⟨3,0,1⟩,[0,0,-1146880,27918336,-302645248,1906180096,-7580123136,19039256576,-26791116800,7007371264,43447189504,-68285235200,19304939520,39163658240,-29083729920]),(⟨3,0,2⟩,[0,-163840,4947968,-62619648,436764672,-1813446656,4346544128,-4491509760,-3982426112,16012247040,-11837800448,-7031062528,10964860928,-1472593920]),(⟨3,0,3⟩,[0,0,1638400,-33423360,292356096,-1399324672,3795976192,-4956880896,-749600768,10789322752,-9422176256,-3997040640,6752894976]),(⟨3,1,0⟩,[0,0,-2293760,55836672,-605290496,3812360192,-15160246272,38078513152,-53582233600,14014742528,86894379008,-136570470400,38609879040,78327316480,-58167459840]),(⟨3,1,2⟩,[0,917504,-23986176,258867200,-1490944000,4751884288,-6635126784,-6536036352,41434742784,-58511196160,7225344000,58357841920,-43127275520]),(⟨3,2,0⟩,[0,-327680,9895936,-125239296,873529344,-3626893312,8693088256,-8983019520,-7964852224,32024494080,-23675600896,-14062125056,21929721856,-2945187840]),(⟨3,2,1⟩,[0,917504,-23986176,258867200,-1490944000,4751884288,-6635126784,-6536036352,41434742784,-58511196160,7225344000,58357841920,-43127275520]),(⟨3,2,2⟩,[131072,-4194304,53870592,-352845824,1188298752,-1371537408,-3394502656,12355371008,-8819965952,-11597250560,16273768448,-2183659520]),(⟨3,3,0⟩,[0,0,3276800,-66846720,584712192,-2798649344,7591952384,-9913761792,-1499201536,21578645504,-18844352512,-7994081280,13505789952]),(⟨3,3,4⟩,[524288,-12582912,106954752,-339738624,-105906176,2629828608,-3063939072,-4492099584,7424442368]),(⟨3,4,3⟩,[524288,-12582912,106954752,-339738624,-105906176,2629828608,-3063939072,-4492099584,7424442368]),(⟨4,0,0⟩,[16384,-655360,8880128,-50855936,20692992,1523187712,-10343677952,34609299456,-61884088320,35872440320,74075701248,-150151364608,57210322944,73735208960,-57846333440]),(⟨4,1,2⟩,[131072,-4194304,53870592,-352845824,1188298752,-1371537408,-3394502656,12355371008,-8819965952,-11597250560,16273768448,-2183659520]),(⟨4,2,1⟩,[131072,-4194304,53870592,-352845824,1188298752,-1371537408,-3394502656,12355371008,-8819965952,-11597250560,16273768448,-2183659520]),(⟨4,2,2⟩,[0,-1310720,29097984,-248512512,1001390080,-1549271040,-1857552384,9805234176,-9052356608,-5992873984,10013638656]),(⟨4,2,4⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨4,3,3⟩,[524288,-12582912,106954752,-339738624,-105906176,2629828608,-3063939072,-4492099584,7424442368]),(⟨4,4,2⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨5,0,0⟩,[0,-327680,9895936,-125239296,873529344,-3626893312,8693088256,-8983019520,-7964852224,32024494080,-23675600896,-14062125056,21929721856,-2945187840]),(⟨5,1,2⟩,[0,-1310720,29097984,-248512512,1001390080,-1549271040,-1857552384,9805234176,-9052356608,-5992873984,10013638656]),(⟨5,2,1⟩,[0,-1310720,29097984,-248512512,1001390080,-1549271040,-1857552384,9805234176,-9052356608,-5992873984,10013638656]),(⟨6,0,0⟩,[0,0,1638400,-33423360,292356096,-1399324672,3795976192,-4956880896,-749600768,10789322752,-9422176256,-3997040640,6752894976])]


theorem partial_checked4 :
    (Poly.add (Poly.add (Poly.mul chunk4 sourceRight) partial8)
      (Poly.scale (K.ofRat (-1)) partial4)).isZero := by decide +kernel

theorem partial_sound4 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 4)
      sourceRight).eval u v t=partial4.eval u v t := by
  change (Poly.mul (chunk4++(sourceLeft.drop 8))
    sourceRight).eval u v t=partial4.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound8 partial_checked4 u v t


noncomputable def chunk0 : Poly := [(⟨0,0,0⟩,[128,-2688,24576,-125568,372480,-579456,211968,627840,-719744,92160]),(⟨0,0,1⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920]),(⟨0,0,2⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨0,0,3⟩,[0,1280,-13056,47616,-60928,-24320,82176])]

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[16384,-688128,13516800,-164265984,1374388224,-8322711552,37244878848,-123003371520,291122741248,-450151809024,300131401728,407346905088,-1242006061056,1168939450368,-17747656704,-864698204160,633754894336,-132663214080,8493465600]),(⟨0,0,1⟩,[0,-229376,8060928,-131072000,1301708800,-8755970048,41701933056,-142153744384,338868076544,-514415558656,311146119168,519297302528,-1401562365952,1181281648640,137984409600,-964452024320,578001141760,-65234534400]),(⟨0,0,2⟩,[-32768,1343488,-23871488,246579200,-1646968832,7350943744,-21247901696,32797523968,9274736640,-162104246272,321902821376,-179077152768,-301969981440,522528456704,-138345037824,-213791047680,121956352000]),(⟨0,0,3⟩,[0,557056,-18055168,261423104,-2227109888,12295176192,-45278068736,108256821248,-144575692800,18318852096,286495309824,-436161413120,128439091200,262419415040,-226794897408,27831173120]),(⟨0,0,4⟩,[16384,-655360,8880128,-50855936,20692992,1523187712,-10343677952,34609299456,-61884088320,35872440320,74075701248,-150151364608,57210322944,73735208960,-57846333440]),(⟨0,0,5⟩,[0,-327680,9895936,-125239296,873529344,-3626893312,8693088256,-8983019520,-7964852224,32024494080,-23675600896,-14062125056,21929721856,-2945187840]),(⟨0,0,6⟩,[0,0,1638400,-33423360,292356096,-1399324672,3795976192,-4956880896,-749600768,10789322752,-9422176256,-3997040640,6752894976]),(⟨0,1,0⟩,[0,-229376,8060928,-131072000,1301708800,-8755970048,41701933056,-142153744384,338868076544,-514415558656,311146119168,519297302528,-1401562365952,1181281648640,137984409600,-964452024320,578001141760,-65234534400]),(⟨0,1,1⟩,[0,0,1605632,-45416448,585859072,-4538630144,23320756224,-82340151296,197501222912,-293319475200,157704355840,326909624320,-784921886720,583968358400,159651430400,-526406451200,250518732800]),(⟨0,1,2⟩,[0,229376,-7831552,116129792,-992346112,5401051136,-19267420160,43447353344,-50223120384,-15485992960,144101965824,-183161323520,27658158080,135454556160,-104020869120,12684492800]),(⟨0,1,3⟩,[0,0,-2293760,55836672,-605290496,3812360192,-15160246272,38078513152,-53582233600,14014742528,86894379008,-136570470400,38609879040,78327316480,-58167459840]),(⟨0,2,0⟩,[-32768,1343488,-23871488,246579200,-1646968832,7350943744,-21247901696,32797523968,9274736640,-162104246272,321902821376,-179077152768,-301969981440,522528456704,-138345037824,-213791047680,121956352000]),(⟨0,2,1⟩,[0,229376,-7831552,116129792,-992346112,5401051136,-19267420160,43447353344,-50223120384,-15485992960,144101965824,-183161323520,27658158080,135454556160,-104020869120,12684492800]),(⟨0,2,2⟩,[32768,-1310720,22347776,-213385216,1251966976,-4578344960,9633136640,-6938427392,-16603709440,43715395584,-25637355520,-27161788416,37200887808,-9184215040,642252800]),(⟨0,2,3⟩,[0,-327680,9895936,-125239296,873529344,-3626893312,8693088256,-8983019520,-7964852224,32024494080,-23675600896,-14062125056,21929721856,-2945187840]),(⟨0,3,0⟩,[0,557056,-18055168,261423104,-2227109888,12295176192,-45278068736,108256821248,-144575692800,18318852096,286495309824,-436161413120,128439091200,262419415040,-226794897408,27831173120]),(⟨0,3,1⟩,[0,0,-2293760,55836672,-605290496,3812360192,-15160246272,38078513152,-53582233600,14014742528,86894379008,-136570470400,38609879040,78327316480,-58167459840]),(⟨0,3,2⟩,[0,-327680,9895936,-125239296,873529344,-3626893312,8693088256,-8983019520,-7964852224,32024494080,-23675600896,-14062125056,21929721856,-2945187840]),(⟨0,3,3⟩,[0,0,3276800,-66846720,584712192,-2798649344,7591952384,-9913761792,-1499201536,21578645504,-18844352512,-7994081280,13505789952]),(⟨0,4,0⟩,[16384,-655360,8880128,-50855936,20692992,1523187712,-10343677952,34609299456,-61884088320,35872440320,74075701248,-150151364608,57210322944,73735208960,-57846333440]),(⟨0,5,0⟩,[0,-327680,9895936,-125239296,873529344,-3626893312,8693088256,-8983019520,-7964852224,32024494080,-23675600896,-14062125056,21929721856,-2945187840]),(⟨0,6,0⟩,[0,0,1638400,-33423360,292356096,-1399324672,3795976192,-4956880896,-749600768,10789322752,-9422176256,-3997040640,6752894976]),(⟨1,0,0⟩,[0,-229376,8060928,-131072000,1301708800,-8755970048,41701933056,-142153744384,338868076544,-514415558656,311146119168,519297302528,-1401562365952,1181281648640,137984409600,-964452024320,578001141760,-65234534400]),(⟨1,0,1⟩,[0,0,1605632,-45416448,585859072,-4538630144,23320756224,-82340151296,197501222912,-293319475200,157704355840,326909624320,-784921886720,583968358400,159651430400,-526406451200,250518732800]),(⟨1,0,2⟩,[0,229376,-7831552,116129792,-992346112,5401051136,-19267420160,43447353344,-50223120384,-15485992960,144101965824,-183161323520,27658158080,135454556160,-104020869120,12684492800]),(⟨1,0,3⟩,[0,0,-2293760,55836672,-605290496,3812360192,-15160246272,38078513152,-53582233600,14014742528,86894379008,-136570470400,38609879040,78327316480,-58167459840]),(⟨1,1,0⟩,[0,0,1605632,-45416448,585859072,-4538630144,23320756224,-82340151296,197501222912,-293319475200,157704355840,326909624320,-784921886720,583968358400,159651430400,-526406451200,250518732800]),(⟨1,2,0⟩,[0,229376,-7831552,116129792,-992346112,5401051136,-19267420160,43447353344,-50223120384,-15485992960,144101965824,-183161323520,27658158080,135454556160,-104020869120,12684492800]),(⟨1,2,2⟩,[-131072,4325376,-62128128,508428288,-2564685824,7794327552,-11156324352,-9269673984,68690247680,-106650009600,25927876608,100207558656,-91102511104,11230248960]),(⟨1,2,3⟩,[0,917504,-23986176,258867200,-1490944000,4751884288,-6635126784,-6536036352,41434742784,-58511196160,7225344000,58357841920,-43127275520]),(⟨1,2,4⟩,[131072,-4194304,53870592,-352845824,1188298752,-1371537408,-3394502656,12355371008,-8819965952,-11597250560,16273768448,-2183659520]),(⟨1,2,5⟩,[0,-1310720,29097984,-248512512,1001390080,-1549271040,-1857552384,9805234176,-9052356608,-5992873984,10013638656]),(⟨1,3,0⟩,[0,0,-2293760,55836672,-605290496,3812360192,-15160246272,38078513152,-53582233600,14014742528,86894379008,-136570470400,38609879040,78327316480,-58167459840]),(⟨1,3,2⟩,[0,917504,-23986176,258867200,-1490944000,4751884288,-6635126784,-6536036352,41434742784,-58511196160,7225344000,58357841920,-43127275520]),(⟨1,4,2⟩,[131072,-4194304,53870592,-352845824,1188298752,-1371537408,-3394502656,12355371008,-8819965952,-11597250560,16273768448,-2183659520]),(⟨1,5,2⟩,[0,-1310720,29097984,-248512512,1001390080,-1549271040,-1857552384,9805234176,-9052356608,-5992873984,10013638656]),(⟨2,0,0⟩,[-32768,1343488,-23871488,246579200,-1646968832,7350943744,-21247901696,32797523968,9274736640,-162104246272,321902821376,-179077152768,-301969981440,522528456704,-138345037824,-213791047680,121956352000]),(⟨2,0,1⟩,[0,229376,-7831552,116129792,-992346112,5401051136,-19267420160,43447353344,-50223120384,-15485992960,144101965824,-183161323520,27658158080,135454556160,-104020869120,12684492800]),(⟨2,0,2⟩,[32768,-1310720,22347776,-213385216,1251966976,-4578344960,9633136640,-6938427392,-16603709440,43715395584,-25637355520,-27161788416,37200887808,-9184215040,642252800]),(⟨2,0,3⟩,[0,-327680,9895936,-125239296,873529344,-3626893312,8693088256,-8983019520,-7964852224,32024494080,-23675600896,-14062125056,21929721856,-2945187840]),(⟨2,1,0⟩,[0,229376,-7831552,116129792,-992346112,5401051136,-19267420160,43447353344,-50223120384,-15485992960,144101965824,-183161323520,27658158080,135454556160,-104020869120,12684492800]),(⟨2,1,2⟩,[-131072,4325376,-62128128,508428288,-2564685824,7794327552,-11156324352,-9269673984,68690247680,-106650009600,25927876608,100207558656,-91102511104,11230248960]),(⟨2,1,3⟩,[0,917504,-23986176,258867200,-1490944000,4751884288,-6635126784,-6536036352,41434742784,-58511196160,7225344000,58357841920,-43127275520]),(⟨2,1,4⟩,[131072,-4194304,53870592,-352845824,1188298752,-1371537408,-3394502656,12355371008,-8819965952,-11597250560,16273768448,-2183659520]),(⟨2,1,5⟩,[0,-1310720,29097984,-248512512,1001390080,-1549271040,-1857552384,9805234176,-9052356608,-5992873984,10013638656]),(⟨2,2,0⟩,[32768,-1310720,22347776,-213385216,1251966976,-4578344960,9633136640,-6938427392,-16603709440,43715395584,-25637355520,-27161788416,37200887808,-9184215040,642252800]),(⟨2,2,1⟩,[-131072,4325376,-62128128,508428288,-2564685824,7794327552,-11156324352,-9269673984,68690247680,-106650009600,25927876608,100207558656,-91102511104,11230248960]),(⟨2,2,2⟩,[0,2752512,-71958528,776601600,-4472832000,14255652864,-19905380352,-19608109056,124304228352,-175533588480,21676032000,175073525760,-129381826560]),(⟨2,2,3⟩,[131072,-4194304,53870592,-352845824,1188298752,-1371537408,-3394502656,12355371008,-8819965952,-11597250560,16273768448,-2183659520]),(⟨2,2,4⟩,[0,-1310720,29097984,-248512512,1001390080,-1549271040,-1857552384,9805234176,-9052356608,-5992873984,10013638656]),(⟨2,3,0⟩,[0,-327680,9895936,-125239296,873529344,-3626893312,8693088256,-8983019520,-7964852224,32024494080,-23675600896,-14062125056,21929721856,-2945187840]),(⟨2,3,1⟩,[0,917504,-23986176,258867200,-1490944000,4751884288,-6635126784,-6536036352,41434742784,-58511196160,7225344000,58357841920,-43127275520]),(⟨2,3,2⟩,[131072,-4194304,53870592,-352845824,1188298752,-1371537408,-3394502656,12355371008,-8819965952,-11597250560,16273768448,-2183659520]),(⟨2,4,1⟩,[131072,-4194304,53870592,-352845824,1188298752,-1371537408,-3394502656,12355371008,-8819965952,-11597250560,16273768448,-2183659520]),(⟨2,4,2⟩,[0,-1310720,29097984,-248512512,1001390080,-1549271040,-1857552384,9805234176,-9052356608,-5992873984,10013638656]),(⟨2,4,4⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨2,5,1⟩,[0,-1310720,29097984,-248512512,1001390080,-1549271040,-1857552384,9805234176,-9052356608,-5992873984,10013638656]),(⟨3,0,0⟩,[0,557056,-18055168,261423104,-2227109888,12295176192,-45278068736,108256821248,-144575692800,18318852096,286495309824,-436161413120,128439091200,262419415040,-226794897408,27831173120]),(⟨3,0,1⟩,[0,0,-2293760,55836672,-605290496,3812360192,-15160246272,38078513152,-53582233600,14014742528,86894379008,-136570470400,38609879040,78327316480,-58167459840]),(⟨3,0,2⟩,[0,-327680,9895936,-125239296,873529344,-3626893312,8693088256,-8983019520,-7964852224,32024494080,-23675600896,-14062125056,21929721856,-2945187840]),(⟨3,0,3⟩,[0,0,3276800,-66846720,584712192,-2798649344,7591952384,-9913761792,-1499201536,21578645504,-18844352512,-7994081280,13505789952]),(⟨3,1,0⟩,[0,0,-2293760,55836672,-605290496,3812360192,-15160246272,38078513152,-53582233600,14014742528,86894379008,-136570470400,38609879040,78327316480,-58167459840]),(⟨3,1,2⟩,[0,917504,-23986176,258867200,-1490944000,4751884288,-6635126784,-6536036352,41434742784,-58511196160,7225344000,58357841920,-43127275520]),(⟨3,2,0⟩,[0,-327680,9895936,-125239296,873529344,-3626893312,8693088256,-8983019520,-7964852224,32024494080,-23675600896,-14062125056,21929721856,-2945187840]),(⟨3,2,1⟩,[0,917504,-23986176,258867200,-1490944000,4751884288,-6635126784,-6536036352,41434742784,-58511196160,7225344000,58357841920,-43127275520]),(⟨3,2,2⟩,[131072,-4194304,53870592,-352845824,1188298752,-1371537408,-3394502656,12355371008,-8819965952,-11597250560,16273768448,-2183659520]),(⟨3,3,0⟩,[0,0,3276800,-66846720,584712192,-2798649344,7591952384,-9913761792,-1499201536,21578645504,-18844352512,-7994081280,13505789952]),(⟨3,3,4⟩,[524288,-12582912,106954752,-339738624,-105906176,2629828608,-3063939072,-4492099584,7424442368]),(⟨3,4,3⟩,[524288,-12582912,106954752,-339738624,-105906176,2629828608,-3063939072,-4492099584,7424442368]),(⟨4,0,0⟩,[16384,-655360,8880128,-50855936,20692992,1523187712,-10343677952,34609299456,-61884088320,35872440320,74075701248,-150151364608,57210322944,73735208960,-57846333440]),(⟨4,1,2⟩,[131072,-4194304,53870592,-352845824,1188298752,-1371537408,-3394502656,12355371008,-8819965952,-11597250560,16273768448,-2183659520]),(⟨4,2,1⟩,[131072,-4194304,53870592,-352845824,1188298752,-1371537408,-3394502656,12355371008,-8819965952,-11597250560,16273768448,-2183659520]),(⟨4,2,2⟩,[0,-1310720,29097984,-248512512,1001390080,-1549271040,-1857552384,9805234176,-9052356608,-5992873984,10013638656]),(⟨4,2,4⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨4,3,3⟩,[524288,-12582912,106954752,-339738624,-105906176,2629828608,-3063939072,-4492099584,7424442368]),(⟨4,4,2⟩,[262144,-6291456,53477376,-169869312,-52953088,1314914304,-1531969536,-2246049792,3712221184]),(⟨5,0,0⟩,[0,-327680,9895936,-125239296,873529344,-3626893312,8693088256,-8983019520,-7964852224,32024494080,-23675600896,-14062125056,21929721856,-2945187840]),(⟨5,1,2⟩,[0,-1310720,29097984,-248512512,1001390080,-1549271040,-1857552384,9805234176,-9052356608,-5992873984,10013638656]),(⟨5,2,1⟩,[0,-1310720,29097984,-248512512,1001390080,-1549271040,-1857552384,9805234176,-9052356608,-5992873984,10013638656]),(⟨6,0,0⟩,[0,0,1638400,-33423360,292356096,-1399324672,3795976192,-4956880896,-749600768,10789322752,-9422176256,-3997040640,6752894976])]


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
    (Poly.add (Poly.scale (K.ofRat r251) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 12 12).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r250*r250 : ℚ)=r251 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 12 12 r250 r250 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 12=12 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 12 12).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C147

#print axioms Coulomb8.Columns.C147.sound
