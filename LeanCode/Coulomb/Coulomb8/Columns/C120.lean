import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C120

def r0 : ℚ := { num := -65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 2605056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -47529984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 529547264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -4034920448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 22286352384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -92240265216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 291555196928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -709122883584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 1315347578880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -1774069137408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 1444670390272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 67802562560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -1993585311744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 2611914915840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -1478915538944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 286445043712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -17529569280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 1277952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -1916928, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 442400768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -224313344, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 22783098880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -99198189568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 324303814656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -807990738944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 1526662463488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -2085293899776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 1695584714752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 129667547136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -2386117165056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 420829511680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -86175350784, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 22439690240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 147456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -770048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 85934080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := -794148864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := 4735057920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -19006767104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 7306985472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -84124876800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 40049754112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 197968740352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -630306258944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 921797181440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -531961757696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -8523923456, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 823582572544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -7145472000, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 49152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -3407872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 10960896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -893911040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 6400819200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -1804992512, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 14762852352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -250788446208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 436681850880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -498984288256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 202467065856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := 62268637184, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := -827066007552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := 485128011776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := -21825568768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -81920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 2490368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -28016640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 131727360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 42876928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -3823763456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := 22578135040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := -74423992320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := 161596522496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := -229054480384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := 154368245760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 103951237120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -291279486976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 24117641216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 2162688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -43188224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 419495936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -2352971776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 1181614080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -19010289664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 28412870656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -21350023168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -16320233472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 58876297216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -42025549824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -70811648, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 327680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -10223616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := 122355712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -782237696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := 439222272, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := -8102871040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 14965669888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -17502830592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 4268294144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 19888603136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -20216610816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 32768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -196608, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 165576704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := -1623851008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := 10451255296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -47831646208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 164346494976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -438299262976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 906415472640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -194884861952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := 1202286985216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 66000912384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -1627570798592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 1820250144768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -101694668800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -196608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 33013760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := -396099584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := 2878881792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -13893042176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 46603943936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -109697302528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 24572280832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := -2743795712, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := -91847573504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := 373159100416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := -51305955328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := 5397086208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := 2096578560, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -393216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 2031616, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -204931072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 1642397696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := -8467578880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := 4391305216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := -83308183552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := 169268609024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := -232561049600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := 138759438336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 139211374592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -313680920576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 24496111616, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 2621440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -58195968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 497025024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -2002780160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 3098542080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := 3715104768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := -19610468352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 18104713216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 11985747968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -168296448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -32768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 7929856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -16580608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 944308224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := -4696866816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := 14596177920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := -26653360128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := 18619695104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 4654137344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -95733350400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := 79461416960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 25972506624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := -3873144832, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 1293025280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -55181312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := 548929536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := -3098443776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := 10647240704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -22327853056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 25144852480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := -632651776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -45575831552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := 62488969216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := -12846628864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -510885888, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -2097152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 26935296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := -176422912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := 594149376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -685768704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := -1697251328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := 6177685504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := -629997568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -828375040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 1162412032, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := -1310720, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -655360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 14548992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -124256256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 500695040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -774635520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := -928776192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := 4902617088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -4526178304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := -2996436992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := 42074112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 655360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -20447232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := 244711424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := -1564475392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := 878444544, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -16205742080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := 29931339776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := -35005661184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := 8536588288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 39777206272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -40433221632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -786432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 143917056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := -1553203200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 1277952000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -28511305728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := 39810760704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 39216218112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := -248608456704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := 351067176960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := -884736000, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -50021007360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 310640640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 8388608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := -107741184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := 705691648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := -2376597504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := 2743074816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := 6789005312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := -24710742016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := 2519990272, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 3313500160, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -4649648128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := 5242880, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := -7602176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := 91422720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := -596770816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := 2333016064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := -818937856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := 9078964224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := -7652245504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := -705036288, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := 73632317440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := -150042378240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := 131550019584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -278593536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := -2686976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := 42270720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := -343736320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := 1619132416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := -4625399808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := 7817265152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := -4680974336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -16861298688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 62886969344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -13800374272, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := 71237632, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := -327680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := 524288, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -93782016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := 479199232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := -1198653440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := 1038090240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := 1796341760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := -1081081856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := 12585467904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -785907712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := -7012352, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := -131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := 4325376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := -52953088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := 310902784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := -945553408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := 1497104384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := -726138880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := -4237819904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := 14844559360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -125960192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := -1048576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := 25165824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := -12582912, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := 679477248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := 211812352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := -5259657216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := 6127878144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 75497472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -6291456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 3145728, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -169869312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := 1314914304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := -1531969536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -18874368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := 393216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := -14352384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := 207618048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := -1560477696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := 6639845376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := -15933505536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := 18360041472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := 4490133504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := -63813844992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := 171265032192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := -37913886720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := 209780736, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 1179648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -4784128, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 405274624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := -160825344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 1622409216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := 1291190272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := -13184270336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := 20315045888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := 9470607360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := -256573440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := 1302528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := -23764992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := 264773632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := -2017460224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := 11143176192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := -46120132608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := 145777598464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := -354561441792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := 657673789440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := -887034568704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := 722335195136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 33901281280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -996792655872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 1305957457920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -739457769472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 143222521856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -8764784640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := -8192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := 638976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := -958464, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := 221200384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := -112156672, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := 11391549440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := -49599094784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := 162151907328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := -403995369472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := 763331231744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := -1042646949888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := 847792357376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := 64833773568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := -1193058582528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := 210414755840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := -43087675392, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := 11219845120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := 73728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := -385024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := 42967040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -397074432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := 2367528960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := -9503383552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := 3653492736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := -42062438400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := 20024877056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := 98984370176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := -315153129472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := 460898590720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := -265980878848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := -4261961728, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := 411791286272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := -3572736000, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := 24576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := -1703936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := 5480448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := -446955520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := 3200409600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := -902496256, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := 7381426176, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := -125394223104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := 218340925440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := -249492144128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := 101233532928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := 31134318592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := -413533003776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := 242564005888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := -10912784384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := -40960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := 1245184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := -14008320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := 65863680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := 21438464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := -1911881728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := 11289067520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := -37211996160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 80798261248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := -114527240192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := 77184122880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := 51975618560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := -145639743488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := 12058820608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := 1081344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := -21594112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := 209747968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := -1176485888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := 590807040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := -9505144832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := 14206435328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := -10675011584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := -8160116736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := 29438148608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := -21012774912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := -35405824, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := 163840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := -5111808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := 61177856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := -391118848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := 219611136, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := -4051435520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := 7482834944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := -8751415296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := 2134147072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := 9944301568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := -10108305408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := 16384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := -98304, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := 82788352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := -811925504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := 5225627648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := -23915823104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := 82173247488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := -219149631488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := 453207736320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := -97442430976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := 601143492608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := 33000456192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := -813785399296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := 910125072384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := -50847334400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := 8192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := -98304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := 16506880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := -198049792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := 1439440896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := -6946521088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := 23301971968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := -54848651264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := 12286140416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := -1371897856, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := -45923786752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := 186579550208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := -25652977664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r450 : ℚ := { num := 2698543104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r451 : ℚ := { num := 1048289280, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r452 : ℚ := { num := -196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r453 : ℚ := { num := 1015808, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r454 : ℚ := { num := -102465536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r455 : ℚ := { num := 821198848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r456 : ℚ := { num := -4233789440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r457 : ℚ := { num := 2195652608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r458 : ℚ := { num := -41654091776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r459 : ℚ := { num := 84634304512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r460 : ℚ := { num := -116280524800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r461 : ℚ := { num := 69379719168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r462 : ℚ := { num := 69605687296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r463 : ℚ := { num := -156840460288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r464 : ℚ := { num := 12248055808, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r465 : ℚ := { num := 1310720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r466 : ℚ := { num := -29097984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r467 : ℚ := { num := 248512512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r468 : ℚ := { num := -1001390080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r469 : ℚ := { num := 1549271040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r470 : ℚ := { num := 1857552384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r471 : ℚ := { num := -9805234176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r472 : ℚ := { num := 9052356608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r473 : ℚ := { num := 5992873984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r474 : ℚ := { num := -84148224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r475 : ℚ := { num := -16384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r476 : ℚ := { num := 3964928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r477 : ℚ := { num := -8290304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r478 : ℚ := { num := 472154112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r479 : ℚ := { num := -2348433408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r480 : ℚ := { num := 7298088960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r481 : ℚ := { num := -13326680064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r482 : ℚ := { num := 9309847552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r483 : ℚ := { num := 2327068672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r484 : ℚ := { num := -47866675200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r485 : ℚ := { num := 39730708480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r486 : ℚ := { num := 12986253312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r487 : ℚ := { num := -1936572416, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r488 : ℚ := { num := 646512640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r489 : ℚ := { num := -27590656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r490 : ℚ := { num := 274464768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r491 : ℚ := { num := -1549221888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r492 : ℚ := { num := 5323620352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r493 : ℚ := { num := -11163926528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r494 : ℚ := { num := 12572426240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r495 : ℚ := { num := -316325888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r496 : ℚ := { num := -22787915776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r497 : ℚ := { num := 31244484608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r498 : ℚ := { num := -6423314432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r499 : ℚ := { num := -255442944, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r500 : ℚ := { num := 32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r501 : ℚ := { num := 13467648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r502 : ℚ := { num := -88211456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r503 : ℚ := { num := 297074688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r504 : ℚ := { num := -342884352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r505 : ℚ := { num := -848625664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r506 : ℚ := { num := 3088842752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r507 : ℚ := { num := -314998784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r508 : ℚ := { num := -414187520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r509 : ℚ := { num := 581206016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r510 : ℚ := { num := -655360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r511 : ℚ := { num := 7274496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r512 : ℚ := { num := -62128128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r513 : ℚ := { num := 250347520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r514 : ℚ := { num := -387317760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r515 : ℚ := { num := -464388096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r516 : ℚ := { num := 2451308544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r517 : ℚ := { num := -2263089152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r518 : ℚ := { num := -1498218496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r519 : ℚ := { num := 21037056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r520 : ℚ := { num := -393216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r521 : ℚ := { num := 71958528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r522 : ℚ := { num := -776601600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r523 : ℚ := { num := 638976000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r524 : ℚ := { num := -14255652864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r525 : ℚ := { num := 19905380352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r526 : ℚ := { num := 19608109056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r527 : ℚ := { num := -124304228352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r528 : ℚ := { num := 175533588480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r529 : ℚ := { num := -442368000, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r530 : ℚ := { num := -25010503680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r531 : ℚ := { num := 155320320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r532 : ℚ := { num := 4194304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r533 : ℚ := { num := -53870592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r534 : ℚ := { num := 352845824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r535 : ℚ := { num := -1188298752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r536 : ℚ := { num := 1371537408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r537 : ℚ := { num := 3394502656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r538 : ℚ := { num := -12355371008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r539 : ℚ := { num := 1259995136, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r540 : ℚ := { num := 1656750080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r541 : ℚ := { num := -2324824064, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r542 : ℚ := { num := 2621440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r543 : ℚ := { num := 131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r544 : ℚ := { num := -3801088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r545 : ℚ := { num := 45711360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r546 : ℚ := { num := -298385408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r547 : ℚ := { num := 1166508032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r548 : ℚ := { num := -409468928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r549 : ℚ := { num := 4539482112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r550 : ℚ := { num := -3826122752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r551 : ℚ := { num := -352518144, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r552 : ℚ := { num := 36816158720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r553 : ℚ := { num := -75021189120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r554 : ℚ := { num := 65775009792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r555 : ℚ := { num := -139296768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r556 : ℚ := { num := -1343488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r557 : ℚ := { num := 21135360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r558 : ℚ := { num := -171868160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r559 : ℚ := { num := 809566208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r560 : ℚ := { num := -2312699904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r561 : ℚ := { num := 3908632576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r562 : ℚ := { num := -2340487168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r563 : ℚ := { num := -8430649344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r564 : ℚ := { num := 31443484672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r565 : ℚ := { num := -6900187136, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r566 : ℚ := { num := 35618816, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r567 : ℚ := { num := -163840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r568 : ℚ := { num := 262144, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r569 : ℚ := { num := -46891008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r570 : ℚ := { num := 239599616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r571 : ℚ := { num := -599326720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r572 : ℚ := { num := 519045120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r573 : ℚ := { num := 898170880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r574 : ℚ := { num := -540540928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r575 : ℚ := { num := 6292733952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r576 : ℚ := { num := -392953856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r577 : ℚ := { num := -3506176, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r578 : ℚ := { num := -26476544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r579 : ℚ := { num := 155451392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r580 : ℚ := { num := -472776704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r581 : ℚ := { num := 748552192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r582 : ℚ := { num := -363069440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r583 : ℚ := { num := -2118909952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r584 : ℚ := { num := 7422279680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r585 : ℚ := { num := -62980096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r586 : ℚ := { num := -524288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r587 : ℚ := { num := 12582912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r588 : ℚ := { num := -6291456, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r589 : ℚ := { num := 339738624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r590 : ℚ := { num := 105906176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r591 : ℚ := { num := -2629828608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r592 : ℚ := { num := 3063939072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r593 : ℚ := { num := 37748736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r594 : ℚ := { num := -3145728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r595 : ℚ := { num := 1572864, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r596 : ℚ := { num := -84934656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r597 : ℚ := { num := 657457152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r598 : ℚ := { num := -765984768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r599 : ℚ := { num := -9437184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r600 : ℚ := { num := 196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r601 : ℚ := { num := -7176192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r602 : ℚ := { num := 103809024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r603 : ℚ := { num := -780238848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r604 : ℚ := { num := 3319922688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r605 : ℚ := { num := -7966752768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r606 : ℚ := { num := 9180020736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r607 : ℚ := { num := 2245066752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r608 : ℚ := { num := -31906922496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r609 : ℚ := { num := 85632516096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r610 : ℚ := { num := -18956943360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r611 : ℚ := { num := 104890368, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r612 : ℚ := { num := 589824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r613 : ℚ := { num := -2392064, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r614 : ℚ := { num := 202637312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r615 : ℚ := { num := -80412672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r616 : ℚ := { num := 811204608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r617 : ℚ := { num := 645595136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r618 : ℚ := { num := -6592135168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r619 : ℚ := { num := 10157522944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r620 : ℚ := { num := 4735303680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r621 : ℚ := { num := -128286720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r622 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r623 : ℚ := { num := 1, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17],[r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34],[r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50],[r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63,r64,r65],[r66,r67,r68,r69,r70,r71,r72,r73,r74,r75,r76,r77,r78,r79],[r80,r81,r82,r83,r84,r85,r86,r87,r88,r89,r90,r91,r92],[0,r93,r94,r95,r96,r97,r98,r99,r100,r101,r102,r103],[],[],[],[],[],[],[0,r104,r105,r106,r107,r108,r109,r110,r111,r112,r113,r114,r115,r116,r117,r118],[r119,r120,r121,r122,r123,r124,r125,r126,r127,r128,r129,r130,r131,r132,r133],[0,r134,r135,r136,r137,r138,r139,r140,r141,r142,r143,r144,r145,r146],[0,0,0,r147,r148,r149,r150,r151,r152,r153,r154,r155,r156],[],[],[],[],[],[],[],[r157,r158,r159,r160,r161,r162,r163,r164,r165,r166,r167,r168,r169,r170],[r80,r147,r171,r172,r173,r174,r175,r176,r177,r178,r179,r180,r181],[r182,r183,r184,r185,r186,r187,r188,r189,r190,r191,r192,r193],[0,r194,r195,r196,r197,r198,r199,r200,r201,r202,r203],[],[],[],[],[],[0,r204,r205,r206,r207,r208,r209,r210,r211,r212,r213,r214],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,0,0,r215,r216,r217,r218,r219,r220,r221,r222,r223,r224,r225,r226],[0,0,r227,r228,r229,r230,r231,r232,r233,r234,r235,r236,r237,r238],[0,0,0,r147,r148,r149,r150,r151,r152,r153,r154,r155,r156],[],[],[],[],[],[],[],[r239,r240,r241,r242,r243,r244,r245,r246,r247,r248,r249,r250,r251],[r182,r252,r253,r254,r255,r256,r257,r258,r259,r260,r261,r262],[r263,r264,r265,r266,r267,r268,r269,r270,r271,r272,r273],[r274,r275,r276,r277,r278,r279,r280,r281,r282,r283],[],[],[],[],[0,0,r284,r285,r286,r287,r288,r289,r290,r291,-1048576],[],[],[],[],[],[r239,r292,r293,r294,r276,r295,r296,r297,262144],[],[],[],[],[],[r298,r299,r300,r301,r302,r303,r304,r305,r306,r307,r308,r309],[r263,r310,r311,r312,r313,r314,r315,r316,r317,r318,r319],[r274,r275,r276,r277,r278,r279,r280,r281,r282,r283],[],[],[],[],[],[r239,r292,r293,r294,r276,r295,r296,r297,262144],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[r80,r320,r321,r322,r323,r324,r325,r326,r327,r328,r329,r330,r331,r332,r333,r334,r335,r336]),(⟨0,0,1⟩,[r337,r338,r339,r340,r341,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351,r352,r353]),(⟨0,0,2⟩,[r354,r355,r356,r357,r358,r359,r360,r361,r362,r363,r364,r365,r366,r367,r368,r369]),(⟨0,0,3⟩,[r370,r371,r372,r373,r374,r375,r376,r377,r378,r379,r380,r381,r382,r383,r384]),(⟨0,0,4⟩,[r385,r386,r387,r388,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398]),(⟨0,0,5⟩,[r18,r399,r400,r401,r402,r403,r404,r405,r406,r407,r408,r409,r410]),(⟨0,0,6⟩,[0,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420,r421]),(⟨0,1,0⟩,[r337,r338,r339,r340,r341,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351,r352,r353]),(⟨0,1,1⟩,[0,r422,r423,r424,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434,r435,r436]),(⟨0,1,2⟩,[r437,r438,r439,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451]),(⟨0,1,3⟩,[0,r452,r453,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464]),(⟨0,1,4⟩,[0,0,0,r465,r466,r467,r468,r469,r470,r471,r472,r473,r474]),(⟨0,2,0⟩,[r354,r355,r356,r357,r358,r359,r360,r361,r362,r363,r364,r365,r366,r367,r368,r369]),(⟨0,2,1⟩,[r437,r438,r439,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451]),(⟨0,2,2⟩,[r475,r476,r477,r478,r479,r480,r481,r482,r483,r484,r485,r486,r487,r488]),(⟨0,2,3⟩,[r18,r465,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498,r499]),(⟨0,2,4⟩,[r500,r284,r501,r502,r503,r504,r505,r506,r507,r508,r509,r510]),(⟨0,2,5⟩,[0,r263,r511,r512,r513,r514,r515,r516,r517,r518,r519]),(⟨0,3,0⟩,[r370,r371,r372,r373,r374,r375,r376,r377,r378,r379,r380,r381,r382,r383,r384]),(⟨0,3,1⟩,[0,r452,r453,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464]),(⟨0,3,2⟩,[r18,r465,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498,r499]),(⟨0,3,3⟩,[0,r93,r94,r95,r96,r97,r98,r99,r100,r101,r102,r103]),(⟨0,4,0⟩,[r385,r386,r387,r388,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398]),(⟨0,4,1⟩,[0,0,0,r465,r466,r467,r468,r469,r470,r471,r472,r473,r474]),(⟨0,4,2⟩,[r500,r284,r501,r502,r503,r504,r505,r506,r507,r508,r509,r510]),(⟨0,5,0⟩,[r18,r399,r400,r401,r402,r403,r404,r405,r406,r407,r408,r409,r410]),(⟨0,5,2⟩,[0,r263,r511,r512,r513,r514,r515,r516,r517,r518,r519]),(⟨0,6,0⟩,[0,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420,r421]),(⟨1,0,0⟩,[r337,r338,r339,r340,r341,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351,r352,r353]),(⟨1,0,1⟩,[0,r422,r423,r424,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434,r435,r436]),(⟨1,0,2⟩,[r437,r438,r439,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451]),(⟨1,0,3⟩,[0,r452,r453,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464]),(⟨1,0,4⟩,[0,0,0,r465,r466,r467,r468,r469,r470,r471,r472,r473,r474]),(⟨1,1,0⟩,[0,r422,r423,r424,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434,r435,r436]),(⟨1,1,1⟩,[0,0,0,r520,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530,r531]),(⟨1,1,2⟩,[0,0,r274,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542]),(⟨1,1,3⟩,[0,0,0,r465,r466,r467,r468,r469,r470,r471,r472,r473,r474]),(⟨1,2,0⟩,[r437,r438,r439,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451]),(⟨1,2,1⟩,[0,0,r274,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542]),(⟨1,2,2⟩,[r543,r544,r545,r546,r547,r548,r549,r550,r551,r552,r553,r554,r555]),(⟨1,2,3⟩,[r500,r556,r557,r558,r559,r560,r561,r562,r563,r564,r565,r566]),(⟨1,2,4⟩,[r567,r568,r569,r570,r571,r572,r573,r574,r575,r576,r577]),(⟨1,2,5⟩,[r0,r81,r578,r579,r580,r581,r582,r583,r584,r585]),(⟨1,3,0⟩,[0,r452,r453,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464]),(⟨1,3,1⟩,[0,0,0,r465,r466,r467,r468,r469,r470,r471,r472,r473,r474]),(⟨1,3,2⟩,[r500,r556,r557,r558,r559,r560,r561,r562,r563,r564,r565,r566]),(⟨1,3,3⟩,[0,0,r586,r587,r588,r589,r590,r591,r592,r593,-524288]),(⟨1,4,0⟩,[0,0,0,r465,r466,r467,r468,r469,r470,r471,r472,r473,r474]),(⟨1,4,2⟩,[r567,r568,r569,r570,r571,r572,r573,r574,r575,r576,r577]),(⟨1,4,4⟩,[r543,r594,r595,r596,r578,r597,r598,r599,131072]),(⟨1,5,2⟩,[r0,r81,r578,r579,r580,r581,r582,r583,r584,r585]),(⟨2,0,0⟩,[r354,r355,r356,r357,r358,r359,r360,r361,r362,r363,r364,r365,r366,r367,r368,r369]),(⟨2,0,1⟩,[r437,r438,r439,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451]),(⟨2,0,2⟩,[r475,r476,r477,r478,r479,r480,r481,r482,r483,r484,r485,r486,r487,r488]),(⟨2,0,3⟩,[r18,r465,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498,r499]),(⟨2,0,4⟩,[r500,r284,r501,r502,r503,r504,r505,r506,r507,r508,r509,r510]),(⟨2,0,5⟩,[0,r263,r511,r512,r513,r514,r515,r516,r517,r518,r519]),(⟨2,1,0⟩,[r437,r438,r439,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451]),(⟨2,1,1⟩,[0,0,r274,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541,r542]),(⟨2,1,2⟩,[r543,r544,r545,r546,r547,r548,r549,r550,r551,r552,r553,r554,r555]),(⟨2,1,3⟩,[r500,r556,r557,r558,r559,r560,r561,r562,r563,r564,r565,r566]),(⟨2,1,4⟩,[r567,r568,r569,r570,r571,r572,r573,r574,r575,r576,r577]),(⟨2,1,5⟩,[r0,r81,r578,r579,r580,r581,r582,r583,r584,r585]),(⟨2,2,0⟩,[r475,r476,r477,r478,r479,r480,r481,r482,r483,r484,r485,r486,r487,r488]),(⟨2,2,1⟩,[r543,r544,r545,r546,r547,r548,r549,r550,r551,r552,r553,r554,r555]),(⟨2,2,2⟩,[r600,r601,r602,r603,r604,r605,r606,r607,r608,r609,r610,r611]),(⟨2,2,3⟩,[r567,r612,r613,r614,r615,r616,r617,r618,r619,r620,r621]),(⟨2,2,4⟩,[r0,r81,r578,r579,r580,r581,r582,r583,r584,r585]),(⟨2,3,0⟩,[r18,r465,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498,r499]),(⟨2,3,1⟩,[r500,r556,r557,r558,r559,r560,r561,r562,r563,r564,r565,r566]),(⟨2,3,2⟩,[r567,r612,r613,r614,r615,r616,r617,r618,r619,r620,r621]),(⟨2,3,4⟩,[r543,r594,r595,r596,r578,r597,r598,r599,131072]),(⟨2,4,0⟩,[r500,r284,r501,r502,r503,r504,r505,r506,r507,r508,r509,r510]),(⟨2,4,1⟩,[r567,r568,r569,r570,r571,r572,r573,r574,r575,r576,r577]),(⟨2,4,2⟩,[r0,r81,r578,r579,r580,r581,r582,r583,r584,r585]),(⟨2,4,3⟩,[r543,r594,r595,r596,r578,r597,r598,r599,131072]),(⟨2,5,0⟩,[0,r263,r511,r512,r513,r514,r515,r516,r517,r518,r519]),(⟨2,5,1⟩,[r0,r81,r578,r579,r580,r581,r582,r583,r584,r585]),(⟨3,0,0⟩,[r370,r371,r372,r373,r374,r375,r376,r377,r378,r379,r380,r381,r382,r383,r384]),(⟨3,0,1⟩,[0,r452,r453,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464]),(⟨3,0,2⟩,[r18,r465,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498,r499]),(⟨3,0,3⟩,[0,r93,r94,r95,r96,r97,r98,r99,r100,r101,r102,r103]),(⟨3,1,0⟩,[0,r452,r453,r454,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464]),(⟨3,1,1⟩,[0,0,0,r465,r466,r467,r468,r469,r470,r471,r472,r473,r474]),(⟨3,1,2⟩,[r500,r556,r557,r558,r559,r560,r561,r562,r563,r564,r565,r566]),(⟨3,1,3⟩,[0,0,r586,r587,r588,r589,r590,r591,r592,r593,-524288]),(⟨3,2,0⟩,[r18,r465,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498,r499]),(⟨3,2,1⟩,[r500,r556,r557,r558,r559,r560,r561,r562,r563,r564,r565,r566]),(⟨3,2,2⟩,[r567,r612,r613,r614,r615,r616,r617,r618,r619,r620,r621]),(⟨3,2,4⟩,[r543,r594,r595,r596,r578,r597,r598,r599,131072]),(⟨3,3,0⟩,[0,r93,r94,r95,r96,r97,r98,r99,r100,r101,r102,r103]),(⟨3,3,1⟩,[0,0,r586,r587,r588,r589,r590,r591,r592,r593,-524288]),(⟨3,4,2⟩,[r543,r594,r595,r596,r578,r597,r598,r599,131072]),(⟨4,0,0⟩,[r385,r386,r387,r388,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398]),(⟨4,0,1⟩,[0,0,0,r465,r466,r467,r468,r469,r470,r471,r472,r473,r474]),(⟨4,0,2⟩,[r500,r284,r501,r502,r503,r504,r505,r506,r507,r508,r509,r510]),(⟨4,1,0⟩,[0,0,0,r465,r466,r467,r468,r469,r470,r471,r472,r473,r474]),(⟨4,1,2⟩,[r567,r568,r569,r570,r571,r572,r573,r574,r575,r576,r577]),(⟨4,1,4⟩,[r543,r594,r595,r596,r578,r597,r598,r599,131072]),(⟨4,2,0⟩,[r500,r284,r501,r502,r503,r504,r505,r506,r507,r508,r509,r510]),(⟨4,2,1⟩,[r567,r568,r569,r570,r571,r572,r573,r574,r575,r576,r577]),(⟨4,2,2⟩,[r0,r81,r578,r579,r580,r581,r582,r583,r584,r585]),(⟨4,2,3⟩,[r543,r594,r595,r596,r578,r597,r598,r599,131072]),(⟨4,3,2⟩,[r543,r594,r595,r596,r578,r597,r598,r599,131072]),(⟨4,4,1⟩,[r543,r594,r595,r596,r578,r597,r598,r599,131072]),(⟨5,0,0⟩,[r18,r399,r400,r401,r402,r403,r404,r405,r406,r407,r408,r409,r410]),(⟨5,0,2⟩,[0,r263,r511,r512,r513,r514,r515,r516,r517,r518,r519]),(⟨5,1,2⟩,[r0,r81,r578,r579,r580,r581,r582,r583,r584,r585]),(⟨5,2,0⟩,[0,r263,r511,r512,r513,r514,r515,r516,r517,r518,r519]),(⟨5,2,1⟩,[r0,r81,r578,r579,r580,r581,r582,r583,r584,r585]),(⟨6,0,0⟩,[0,r411,r412,r413,r414,r415,r416,r417,r418,r419,r420,r421])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[-256,4800,-35712,145856,-387968,744000,-1039488,811328,-95104]),(⟨0,0,1⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨0,0,2⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨0,0,3⟩,[128,-2688,15616,-40192,84608,-123008]),(⟨0,1,0⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨0,1,1⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨0,2,0⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨0,2,2⟩,[-256,3072,-7680,-9216,30464]),(⟨0,3,0⟩,[128,-2688,15616,-40192,84608,-123008]),(⟨1,0,0⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨1,0,1⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨1,1,0⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨2,0,0⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨2,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨2,2,0⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[128,-2688,15616,-40192,84608,-123008])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[128,-2688,24576,-125568,372480,-579456,211968,627840,-719744,92160]),(⟨0,0,1⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920]),(⟨0,0,2⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨0,0,3⟩,[0,1280,-13056,47616,-60928,-24320,82176]),(⟨0,1,0⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920]),(⟨0,2,0⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨0,3,0⟩,[0,1280,-13056,47616,-60928,-24320,82176]),(⟨1,0,0⟩,[0,-896,12672,-73856,221824,-325760,82560,371840,-353920]),(⟨1,2,2⟩,[-512,6144,-15360,-18432,60928]),(⟨2,0,0⟩,[-128,2560,-18048,55808,-56704,-60928,128128,-17920]),(⟨2,1,2⟩,[-512,6144,-15360,-18432,60928]),(⟨2,2,1⟩,[-512,6144,-15360,-18432,60928]),(⟨3,0,0⟩,[0,1280,-13056,47616,-60928,-24320,82176])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 6 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r622) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 12 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r622) sourceRight))).isZero := by decide +kernel

noncomputable def partial16 : Poly := []

theorem partial_sound16 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 16)
      sourceRight).eval u v t=partial16.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨2,0,0⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨2,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨2,2,0⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[128,-2688,15616,-40192,84608,-123008])]

noncomputable def partial12 : Poly := [(⟨2,0,0⟩,[40960,-1482752,23961600,-229621760,1454579712,-6399975424,19935272960,-43726700544,64355950592,-50865135616,-16734167040,99351412736,-104885231616,19576840192,29004488704,-4417781760]),(⟨2,0,1⟩,[0,-286720,8413184,-106430464,774438912,-3628752896,11535736832,-25221595136,36397973504,-27160682496,-12178612224,55650222080,-52027064320,3286097920,16965509120]),(⟨2,0,2⟩,[-73728,2523136,-36782080,299630592,-1494802432,4623335424,-8057880576,3496214528,16731021312,-37264588800,23106338816,19019071488,-27848679424,3666575360]),(⟨2,0,3⟩,[0,638976,-16400384,173686784,-996392960,3349774336,-6373670912,4649680896,6848282624,-19178405888,12188958720,10853629952,-14721007616]),(⟨2,0,4⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨2,0,5⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨2,1,0⟩,[0,-286720,8413184,-106430464,774438912,-3628752896,11535736832,-25221595136,36397973504,-27160682496,-12178612224,55650222080,-52027064320,3286097920,16965509120]),(⟨2,1,2⟩,[0,229376,-5996544,64716800,-372736000,1187971072,-1658781696,-1634009088,10358685696,-14627799040,1806336000,14589460480,-10781818880]),(⟨2,2,0⟩,[-73728,2523136,-36782080,299630592,-1494802432,4623335424,-8057880576,3496214528,16731021312,-37264588800,23106338816,19019071488,-27848679424,3666575360]),(⟨2,2,1⟩,[0,229376,-5996544,64716800,-372736000,1187971072,-1658781696,-1634009088,10358685696,-14627799040,1806336000,14589460480,-10781818880]),(⟨2,2,2⟩,[65536,-2097152,26935296,-176422912,594149376,-685768704,-1697251328,6177685504,-4409982976,-5798625280,8136884224,-1091829760]),(⟨2,2,3⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨2,3,0⟩,[0,638976,-16400384,173686784,-996392960,3349774336,-6373670912,4649680896,6848282624,-19178405888,12188958720,10853629952,-14721007616]),(⟨2,3,2⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨2,4,0⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨2,5,0⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨3,0,0⟩,[16384,-974848,20783104,-235683840,1662287872,-7895949312,26393894912,-63377604608,108178456576,-118773915648,40311906304,113063870464,-193856602112,99617841152,5629091840]),(⟨3,0,1⟩,[0,-114688,4030464,-57507840,460816384,-2376417280,8501002240,-21984509952,41190359040,-51408289792,26584514560,35529850880,-75683758080,43534991360]),(⟨3,0,2⟩,[-16384,901120,-17186816,165494784,-925564928,3161817088,-6449037312,6288736256,3194077184,-18237308928,20861861888,-2687483904,-8577515520]),(⟨3,0,3⟩,[0,163840,-5111808,61177856,-391118848,1537277952,-4051435520,7482834944,-8751415296,2134147072,9944301568,-10108305408]),(⟨3,1,0⟩,[0,-114688,4030464,-57507840,460816384,-2376417280,8501002240,-21984509952,41190359040,-51408289792,26584514560,35529850880,-75683758080,43534991360]),(⟨3,2,0⟩,[-16384,901120,-17186816,165494784,-925564928,3161817088,-6449037312,6288736256,3194077184,-18237308928,20861861888,-2687483904,-8577515520]),(⟨3,2,2⟩,[-163840,4456448,-46891008,239599616,-599326720,519045120,898170880,-3783786496,6292733952,-2750676992,-2920644608]),(⟨3,2,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,3,0⟩,[0,163840,-5111808,61177856,-391118848,1537277952,-4051435520,7482834944,-8751415296,2134147072,9944301568,-10108305408]),(⟨3,4,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,0,0⟩,[-40960,1327104,-17219584,115015680,-392814592,298336256,3232202752,-16170876928,40748818432,-62010376192,43208884224,29497032704,-80756809728,44394004480]),(⟨4,0,2⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨4,1,2⟩,[-163840,4456448,-46891008,239599616,-599326720,519045120,898170880,-3783786496,6292733952,-2750676992,-2920644608]),(⟨4,1,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,2,0⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨4,2,1⟩,[-163840,4456448,-46891008,239599616,-599326720,519045120,898170880,-3783786496,6292733952,-2750676992,-2920644608]),(⟨4,2,2⟩,[-65536,2162688,-26476544,155451392,-472776704,748552192,-363069440,-2118909952,7422279680,-7494631424]),(⟨4,2,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,3,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,4,1⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨5,0,0⟩,[-16384,1081344,-21594112,209747968,-1176485888,4135649280,-9505144832,14206435328,-10675011584,-8160116736,29438148608,-21012774912,-1734885376]),(⟨5,0,2⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨5,1,2⟩,[-65536,2162688,-26476544,155451392,-472776704,748552192,-363069440,-2118909952,7422279680,-7494631424]),(⟨5,2,0⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨5,2,1⟩,[-65536,2162688,-26476544,155451392,-472776704,748552192,-363069440,-2118909952,7422279680,-7494631424]),(⟨6,0,0⟩,[0,163840,-5111808,61177856,-391118848,1537277952,-4051435520,7482834944,-8751415296,2134147072,9944301568,-10108305408])]


theorem partial_checked12 :
    (Poly.add (Poly.add (Poly.mul chunk12 sourceRight) partial16)
      (Poly.scale (K.ofRat (-1)) partial12)).isZero := by decide +kernel

theorem partial_sound12 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 12)
      sourceRight).eval u v t=partial12.eval u v t := by
  change (Poly.mul (chunk12++(sourceLeft.drop 16))
    sourceRight).eval u v t=partial12.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound16 partial_checked12 u v t


noncomputable def chunk8 : Poly := [(⟨0,3,0⟩,[128,-2688,15616,-40192,84608,-123008]),(⟨1,0,0⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨1,0,1⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨1,1,0⟩,[0,0,1024,-12288,30720,36864,-121856])]

noncomputable def partial8 : Poly := [(⟨0,3,0⟩,[16384,-688128,12369920,-129253376,887848960,-4267196416,14858158080,-38156009472,71780483072,-91613233152,52490518528,57413648384,-141829537792,96331743232,-11336417280]),(⟨0,3,1⟩,[0,-114688,4030464,-57507840,460816384,-2376417280,8501002240,-21984509952,41190359040,-51408289792,26584514560,35529850880,-75683758080,43534991360]),(⟨0,3,2⟩,[-16384,671744,-11190272,100777984,-552828928,1973846016,-4790255616,7922745344,-7164608512,-3609509888,19055525888,-17276944384,2204303360]),(⟨0,3,3⟩,[0,163840,-5111808,61177856,-391118848,1537277952,-4051435520,7482834944,-8751415296,2134147072,9944301568,-10108305408]),(⟨0,4,0⟩,[0,-114688,4030464,-57507840,460816384,-2376417280,8501002240,-21984509952,41190359040,-51408289792,26584514560,35529850880,-75683758080,43534991360]),(⟨0,5,0⟩,[-16384,671744,-11190272,100777984,-552828928,1973846016,-4790255616,7922745344,-7164608512,-3609509888,19055525888,-17276944384,2204303360]),(⟨0,6,0⟩,[0,163840,-5111808,61177856,-391118848,1537277952,-4051435520,7482834944,-8751415296,2134147072,9944301568,-10108305408]),(⟨1,0,0⟩,[-8192,409600,-8749056,109469696,-912138240,5409947648,-23737237504,78849794048,-200499552256,387707027456,-543415173120,456631459840,22089867264,-641183203328,811175280640,-409981804544,44879708160]),(⟨1,0,1⟩,[0,57344,-2342912,39231488,-374898688,2358599680,-10675568640,37189459968,-103996653568,231238705152,-375393632256,353896751104,3536289792,-456996478976,500613791744,-183580794880]),(⟨1,0,2⟩,[8192,-401408,8093696,-91619328,665001984,-3317768192,11766235136,-29627056128,49605009408,-40062312448,-33745174528,130929328128,-127543779328,15603703808,34400665600]),(⟨1,0,3⟩,[0,-81920,3080192,-44957696,360382464,-1857372160,6868566016,-19669581824,43443945472,-64872235008,42795204608,34075836416,-81156702208,42201399296]),(⟨1,0,4⟩,[0,0,0,1310720,-29097984,248512512,-1001390080,1549271040,1857552384,-9805234176,9052356608,5992873984,-10013638656]),(⟨1,1,0⟩,[0,57344,-2342912,39231488,-374898688,2358599680,-10675568640,37189459968,-103996653568,231238705152,-375393632256,353896751104,3536289792,-456996478976,500613791744,-183580794880]),(⟨1,1,1⟩,[0,0,0,-1835008,47972352,-517734400,2981888000,-9503768576,13270253568,13072072704,-82869485568,117022392320,-14450688000,-116715683840,86254551040]),(⟨1,1,2⟩,[0,0,-131072,4194304,-53870592,352845824,-1188298752,1371537408,3394502656,-12355371008,8819965952,11597250560,-16273768448,2183659520]),(⟨1,1,3⟩,[0,0,0,1310720,-29097984,248512512,-1001390080,1549271040,1857552384,-9805234176,9052356608,5992873984,-10013638656]),(⟨1,2,0⟩,[8192,-401408,8093696,-91619328,665001984,-3317768192,11766235136,-29627056128,49605009408,-40062312448,-33745174528,130929328128,-127543779328,15603703808,34400665600]),(⟨1,2,1⟩,[0,0,-131072,4194304,-53870592,352845824,-1188298752,1371537408,3394502656,-12355371008,8819965952,11597250560,-16273768448,2183659520]),(⟨1,3,0⟩,[0,-196608,7110656,-102465536,821198848,-4233789440,15369568256,-41654091776,84634304512,-116280524800,69379719168,69605687296,-156840460288,85736390656]),(⟨1,3,1⟩,[0,0,0,1310720,-29097984,248512512,-1001390080,1549271040,1857552384,-9805234176,9052356608,5992873984,-10013638656]),(⟨1,4,0⟩,[0,0,0,1310720,-29097984,248512512,-1001390080,1549271040,1857552384,-9805234176,9052356608,5992873984,-10013638656]),(⟨1,5,2⟩,[-65536,2162688,-26476544,155451392,-472776704,748552192,-363069440,-2118909952,7422279680,-7494631424]),(⟨2,0,0⟩,[40960,-1425408,21487616,-186064896,1017552896,-3532947456,6695018496,1257086976,-50797027328,171103895552,-323437551616,346598154240,-75421065216,-337212080128,438515769344,-176768327680]),(⟨2,0,1⟩,[0,-286720,8413184,-107347968,798425088,-3887620096,13026680832,-29973479424,43033100288,-20624646144,-53613355008,114161418240,-59252408320,-55071744000,60092784640]),(⟨2,0,2⟩,[-73728,2523136,-36782080,299630592,-1494802432,4623335424,-8057880576,3496214528,16731021312,-37264588800,23106338816,19019071488,-27848679424,3666575360]),(⟨2,0,3⟩,[0,638976,-16400384,173686784,-996392960,3349774336,-6373670912,4649680896,6848282624,-19178405888,12188958720,10853629952,-14721007616]),(⟨2,0,4⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨2,0,5⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨2,1,0⟩,[0,-286720,8413184,-107347968,798425088,-3887620096,13026680832,-29973479424,43033100288,-20624646144,-53613355008,114161418240,-59252408320,-55071744000,60092784640]),(⟨2,1,2⟩,[0,229376,-5996544,64716800,-372736000,1187971072,-1658781696,-1634009088,10358685696,-14627799040,1806336000,14589460480,-10781818880]),(⟨2,2,0⟩,[-73728,2523136,-36782080,299630592,-1494802432,4623335424,-8057880576,3496214528,16731021312,-37264588800,23106338816,19019071488,-27848679424,3666575360]),(⟨2,2,1⟩,[0,229376,-5996544,64716800,-372736000,1187971072,-1658781696,-1634009088,10358685696,-14627799040,1806336000,14589460480,-10781818880]),(⟨2,2,2⟩,[98304,-3440640,48070656,-348291072,1403715584,-2998468608,2211381248,3837198336,-12840632320,25644859392,-40164425728,28578643968]),(⟨2,2,3⟩,[0,-327680,6750208,-49545216,143392768,-47579136,-358481920,-178520064,800849920,2993881088,-4921032704]),(⟨2,3,0⟩,[-16384,1310720,-27590656,274464768,-1549221888,5323620352,-11163926528,12572426240,-316325888,-22787915776,31244484608,-6423314432,-12516704256]),(⟨2,3,2⟩,[0,-327680,6750208,-49545216,143392768,-47579136,-358481920,-178520064,800849920,2993881088,-4921032704]),(⟨2,4,0⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨2,4,2⟩,[-65536,2162688,-26476544,155451392,-472776704,748552192,-363069440,-2118909952,7422279680,-7494631424]),(⟨2,5,0⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨2,5,1⟩,[-65536,2162688,-26476544,155451392,-472776704,748552192,-363069440,-2118909952,7422279680,-7494631424]),(⟨3,0,0⟩,[24576,-1376256,28876800,-326385664,2303303680,-10954850304,36669186048,-88252776448,151148339200,-165372264448,48001474560,185482002432,-314175037440,173579386880,-3097518080]),(⟨3,0,1⟩,[0,-114688,3899392,-53313536,406945792,-2023571456,7312703488,-20612972544,44584861696,-63763660800,35404480512,47127101440,-91957526528,45718650880]),(⟨3,0,2⟩,[-16384,901120,-17186816,165494784,-925564928,3161817088,-6449037312,6288736256,3194077184,-18237308928,20861861888,-2687483904,-8577515520]),(⟨3,0,3⟩,[0,163840,-5111808,61177856,-391118848,1537277952,-4051435520,7482834944,-8751415296,2134147072,9944301568,-10108305408]),(⟨3,1,0⟩,[0,-114688,3899392,-53313536,406945792,-2023571456,7312703488,-20612972544,44584861696,-63763660800,35404480512,47127101440,-91957526528,45718650880]),(⟨3,1,2⟩,[32768,-1343488,21135360,-171868160,809566208,-2312699904,3908632576,-2340487168,-8430649344,31443484672,-48301309952,29670473728]),(⟨3,1,3⟩,[0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨3,2,0⟩,[-16384,901120,-17186816,165494784,-925564928,3161817088,-6449037312,6288736256,3194077184,-18237308928,20861861888,-2687483904,-8577515520]),(⟨3,2,1⟩,[32768,-1343488,21135360,-171868160,809566208,-2312699904,3908632576,-2340487168,-8430649344,31443484672,-48301309952,29670473728]),(⟨3,2,2⟩,[-163840,4456448,-47939584,264765440,-813236224,1198522368,1109983232,-9043443712,12420612096,6233522176,-17769529344]),(⟨3,2,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,3,0⟩,[0,327680,-10223616,122355712,-782237696,3074555904,-8102871040,14965669888,-17502830592,4268294144,19888603136,-20216610816]),(⟨3,3,1⟩,[0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨3,4,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,0,0⟩,[-40960,1245184,-14008320,65863680,21438464,-1911881728,11289067520,-37211996160,80798261248,-114527240192,77184122880,51975618560,-145639743488,84411744256]),(⟨4,0,1⟩,[0,0,0,1310720,-29097984,248512512,-1001390080,1549271040,1857552384,-9805234176,9052356608,5992873984,-10013638656]),(⟨4,0,2⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨4,1,0⟩,[0,0,0,1310720,-29097984,248512512,-1001390080,1549271040,1857552384,-9805234176,9052356608,5992873984,-10013638656]),(⟨4,1,2⟩,[-163840,4456448,-46891008,239599616,-599326720,519045120,898170880,-3783786496,6292733952,-2750676992,-2920644608]),(⟨4,1,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,2,0⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨4,2,1⟩,[-163840,4456448,-46891008,239599616,-599326720,519045120,898170880,-3783786496,6292733952,-2750676992,-2920644608]),(⟨4,2,2⟩,[-65536,2162688,-26476544,155451392,-472776704,748552192,-363069440,-2118909952,7422279680,-7494631424]),(⟨4,2,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,3,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,4,1⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨5,0,0⟩,[-16384,1081344,-21594112,209747968,-1176485888,4135649280,-9505144832,14206435328,-10675011584,-8160116736,29438148608,-21012774912,-1734885376]),(⟨5,0,2⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨5,1,2⟩,[-65536,2162688,-26476544,155451392,-472776704,748552192,-363069440,-2118909952,7422279680,-7494631424]),(⟨5,2,0⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨5,2,1⟩,[-65536,2162688,-26476544,155451392,-472776704,748552192,-363069440,-2118909952,7422279680,-7494631424]),(⟨6,0,0⟩,[0,163840,-5111808,61177856,-391118848,1537277952,-4051435520,7482834944,-8751415296,2134147072,9944301568,-10108305408])]


theorem partial_checked8 :
    (Poly.add (Poly.add (Poly.mul chunk8 sourceRight) partial12)
      (Poly.scale (K.ofRat (-1)) partial8)).isZero := by decide +kernel

theorem partial_sound8 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 8)
      sourceRight).eval u v t=partial8.eval u v t := by
  change (Poly.mul (chunk8++(sourceLeft.drop 12))
    sourceRight).eval u v t=partial8.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound12 partial_checked8 u v t


noncomputable def chunk4 : Poly := [(⟨0,1,0⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨0,1,1⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨0,2,0⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨0,2,2⟩,[-256,3072,-7680,-9216,30464])]

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[-8192,409600,-8749056,109469696,-912138240,5409947648,-23737237504,78849794048,-200499552256,387707027456,-543415173120,456631459840,22089867264,-641183203328,811175280640,-409981804544,44879708160]),(⟨0,1,1⟩,[0,57344,-2342912,39231488,-374898688,2358599680,-10675568640,37189459968,-103996653568,231238705152,-375393632256,353896751104,3536289792,-456996478976,500613791744,-183580794880]),(⟨0,1,2⟩,[8192,-401408,8093696,-91619328,665001984,-3317768192,11766235136,-29627056128,49605009408,-40062312448,-33745174528,130929328128,-127543779328,15603703808,34400665600]),(⟨0,1,3⟩,[0,-81920,3080192,-44957696,360382464,-1857372160,6868566016,-19669581824,43443945472,-64872235008,42795204608,34075836416,-81156702208,42201399296]),(⟨0,1,4⟩,[0,0,0,1310720,-29097984,248512512,-1001390080,1549271040,1857552384,-9805234176,9052356608,5992873984,-10013638656]),(⟨0,2,0⟩,[40960,-1425408,21487616,-186064896,1017552896,-3532947456,6695018496,1257086976,-50797027328,171103895552,-323437551616,346598154240,-75421065216,-337212080128,438515769344,-176768327680]),(⟨0,2,1⟩,[0,-286720,8413184,-107347968,798425088,-3887620096,13026680832,-29973479424,43033100288,-20624646144,-53613355008,114161418240,-59252408320,-55071744000,60092784640]),(⟨0,2,2⟩,[-73728,2523136,-36782080,299630592,-1494802432,4623335424,-8057880576,3496214528,16731021312,-37264588800,23106338816,19019071488,-27848679424,3666575360]),(⟨0,2,3⟩,[0,638976,-16400384,173686784,-996392960,3349774336,-6373670912,4649680896,6848282624,-19178405888,12188958720,10853629952,-14721007616]),(⟨0,2,4⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨0,2,5⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨0,3,0⟩,[24576,-1376256,28876800,-326385664,2303303680,-10954850304,36669186048,-88252776448,151148339200,-165372264448,48001474560,185482002432,-314175037440,173579386880,-3097518080]),(⟨0,3,1⟩,[0,-114688,3899392,-53313536,406945792,-2023571456,7312703488,-20612972544,44584861696,-63763660800,35404480512,47127101440,-91957526528,45718650880]),(⟨0,3,2⟩,[-16384,901120,-17186816,165494784,-925564928,3161817088,-6449037312,6288736256,3194077184,-18237308928,20861861888,-2687483904,-8577515520]),(⟨0,3,3⟩,[0,163840,-5111808,61177856,-391118848,1537277952,-4051435520,7482834944,-8751415296,2134147072,9944301568,-10108305408]),(⟨0,4,0⟩,[-40960,1245184,-14008320,65863680,21438464,-1911881728,11289067520,-37211996160,80798261248,-114527240192,77184122880,51975618560,-145639743488,84411744256]),(⟨0,4,1⟩,[0,0,0,1310720,-29097984,248512512,-1001390080,1549271040,1857552384,-9805234176,9052356608,5992873984,-10013638656]),(⟨0,4,2⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨0,5,0⟩,[-16384,1081344,-21594112,209747968,-1176485888,4135649280,-9505144832,14206435328,-10675011584,-8160116736,29438148608,-21012774912,-1734885376]),(⟨0,5,2⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨0,6,0⟩,[0,163840,-5111808,61177856,-391118848,1537277952,-4051435520,7482834944,-8751415296,2134147072,9944301568,-10108305408]),(⟨1,0,0⟩,[-8192,409600,-8749056,109469696,-912138240,5409947648,-23737237504,78849794048,-200499552256,387707027456,-543415173120,456631459840,22089867264,-641183203328,811175280640,-409981804544,44879708160]),(⟨1,0,1⟩,[0,57344,-2342912,39231488,-374898688,2358599680,-10675568640,37189459968,-103996653568,231238705152,-375393632256,353896751104,3536289792,-456996478976,500613791744,-183580794880]),(⟨1,0,2⟩,[8192,-401408,8093696,-91619328,665001984,-3317768192,11766235136,-29627056128,49605009408,-40062312448,-33745174528,130929328128,-127543779328,15603703808,34400665600]),(⟨1,0,3⟩,[0,-81920,3080192,-44957696,360382464,-1857372160,6868566016,-19669581824,43443945472,-64872235008,42795204608,34075836416,-81156702208,42201399296]),(⟨1,0,4⟩,[0,0,0,1310720,-29097984,248512512,-1001390080,1549271040,1857552384,-9805234176,9052356608,5992873984,-10013638656]),(⟨1,1,0⟩,[0,114688,-4816896,82788352,-811925504,5225627648,-23915823104,82173247488,-219149631488,453207736320,-682097016832,601143492608,33000456192,-813785399296,910125072384,-355931340800]),(⟨1,1,1⟩,[0,0,0,-2752512,71958528,-776601600,4472832000,-14255652864,19905380352,19608109056,-124304228352,175533588480,-21676032000,-175073525760,129381826560]),(⟨1,1,2⟩,[0,0,-131072,4194304,-53870592,352845824,-1188298752,1371537408,3394502656,-12355371008,8819965952,11597250560,-16273768448,2183659520]),(⟨1,1,3⟩,[0,0,0,1310720,-29097984,248512512,-1001390080,1549271040,1857552384,-9805234176,9052356608,5992873984,-10013638656]),(⟨1,2,0⟩,[8192,-688128,16506880,-198049792,1439440896,-6946521088,23301971968,-54848651264,86002982912,-67222994944,-45923786752,186579550208,-179570843648,18889801728,51366174720]),(⟨1,2,1⟩,[0,0,-131072,4194304,-53870592,352845824,-1188298752,1371537408,3394502656,-12355371008,8819965952,11597250560,-16273768448,2183659520]),(⟨1,2,2⟩,[0,229376,-5996544,64716800,-372736000,1187971072,-1658781696,-1634009088,10358685696,-14627799040,1806336000,14589460480,-10781818880]),(⟨1,3,0⟩,[0,-196608,7110656,-102465536,821198848,-4233789440,15369568256,-41654091776,84634304512,-116280524800,69379719168,69605687296,-156840460288,85736390656]),(⟨1,3,1⟩,[0,0,0,1310720,-29097984,248512512,-1001390080,1549271040,1857552384,-9805234176,9052356608,5992873984,-10013638656]),(⟨1,3,2⟩,[32768,-1343488,21135360,-171868160,809566208,-2312699904,3908632576,-2340487168,-8430649344,31443484672,-48301309952,29670473728]),(⟨1,3,3⟩,[0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨1,4,0⟩,[0,0,0,1310720,-29097984,248512512,-1001390080,1549271040,1857552384,-9805234176,9052356608,5992873984,-10013638656]),(⟨1,4,2⟩,[-163840,4456448,-46891008,239599616,-599326720,519045120,898170880,-3783786496,6292733952,-2750676992,-2920644608]),(⟨1,4,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨1,5,2⟩,[-65536,2162688,-26476544,155451392,-472776704,748552192,-363069440,-2118909952,7422279680,-7494631424]),(⟨2,0,0⟩,[40960,-1425408,21487616,-186064896,1017552896,-3532947456,6695018496,1257086976,-50797027328,171103895552,-323437551616,346598154240,-75421065216,-337212080128,438515769344,-176768327680]),(⟨2,0,1⟩,[0,-286720,8413184,-107347968,798425088,-3887620096,13026680832,-29973479424,43033100288,-20624646144,-53613355008,114161418240,-59252408320,-55071744000,60092784640]),(⟨2,0,2⟩,[-73728,2523136,-36782080,299630592,-1494802432,4623335424,-8057880576,3496214528,16731021312,-37264588800,23106338816,19019071488,-27848679424,3666575360]),(⟨2,0,3⟩,[0,638976,-16400384,173686784,-996392960,3349774336,-6373670912,4649680896,6848282624,-19178405888,12188958720,10853629952,-14721007616]),(⟨2,0,4⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨2,0,5⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨2,1,0⟩,[8192,-688128,16506880,-198049792,1439440896,-6946521088,23301971968,-54848651264,86002982912,-67222994944,-45923786752,186579550208,-179570843648,18889801728,51366174720]),(⟨2,1,1⟩,[0,0,-131072,4194304,-53870592,352845824,-1188298752,1371537408,3394502656,-12355371008,8819965952,11597250560,-16273768448,2183659520]),(⟨2,1,2⟩,[0,229376,-5996544,64716800,-372736000,1187971072,-1658781696,-1634009088,10358685696,-14627799040,1806336000,14589460480,-10781818880]),(⟨2,2,0⟩,[-114688,3964928,-58032128,472154112,-2348433408,7298088960,-13326680064,9309847552,16289480704,-47866675200,39730708480,12986253312,-32921731072,4525588480]),(⟨2,2,1⟩,[0,229376,-5996544,64716800,-372736000,1187971072,-1658781696,-1634009088,10358685696,-14627799040,1806336000,14589460480,-10781818880]),(⟨2,2,2⟩,[163840,-5832704,82673664,-608370688,2510356480,-5654052864,5271388160,4585553920,-23476273152,54189031424,-84397293568,57703202816]),(⟨2,2,3⟩,[0,-327680,6225920,-36962304,36438016,292159488,-252575744,-2808348672,3864788992,7485980672,-12345475072]),(⟨2,3,0⟩,[-16384,1310720,-27590656,274464768,-1549221888,5323620352,-11163926528,12572426240,-316325888,-22787915776,31244484608,-6423314432,-12516704256]),(⟨2,3,1⟩,[32768,-1343488,21135360,-171868160,809566208,-2312699904,3908632576,-2340487168,-8430649344,31443484672,-48301309952,29670473728]),(⟨2,3,2⟩,[-163840,4128768,-40665088,202637312,-562888704,811204608,645595136,-6592135168,10157522944,4735303680,-15266119680]),(⟨2,3,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,4,0⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨2,4,1⟩,[-163840,4456448,-46891008,239599616,-599326720,519045120,898170880,-3783786496,6292733952,-2750676992,-2920644608]),(⟨2,4,2⟩,[-65536,2162688,-26476544,155451392,-472776704,748552192,-363069440,-2118909952,7422279680,-7494631424]),(⟨2,4,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,5,0⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨2,5,1⟩,[-65536,2162688,-26476544,155451392,-472776704,748552192,-363069440,-2118909952,7422279680,-7494631424]),(⟨3,0,0⟩,[24576,-1376256,28876800,-326385664,2303303680,-10954850304,36669186048,-88252776448,151148339200,-165372264448,48001474560,185482002432,-314175037440,173579386880,-3097518080]),(⟨3,0,1⟩,[0,-114688,3899392,-53313536,406945792,-2023571456,7312703488,-20612972544,44584861696,-63763660800,35404480512,47127101440,-91957526528,45718650880]),(⟨3,0,2⟩,[-16384,901120,-17186816,165494784,-925564928,3161817088,-6449037312,6288736256,3194077184,-18237308928,20861861888,-2687483904,-8577515520]),(⟨3,0,3⟩,[0,163840,-5111808,61177856,-391118848,1537277952,-4051435520,7482834944,-8751415296,2134147072,9944301568,-10108305408]),(⟨3,1,0⟩,[0,-196608,7110656,-102465536,821198848,-4233789440,15369568256,-41654091776,84634304512,-116280524800,69379719168,69605687296,-156840460288,85736390656]),(⟨3,1,1⟩,[0,0,0,1310720,-29097984,248512512,-1001390080,1549271040,1857552384,-9805234176,9052356608,5992873984,-10013638656]),(⟨3,1,2⟩,[32768,-1343488,21135360,-171868160,809566208,-2312699904,3908632576,-2340487168,-8430649344,31443484672,-48301309952,29670473728]),(⟨3,1,3⟩,[0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨3,2,0⟩,[-16384,1310720,-27590656,274464768,-1549221888,5323620352,-11163926528,12572426240,-316325888,-22787915776,31244484608,-6423314432,-12516704256]),(⟨3,2,1⟩,[32768,-1343488,21135360,-171868160,809566208,-2312699904,3908632576,-2340487168,-8430649344,31443484672,-48301309952,29670473728]),(⟨3,2,2⟩,[-163840,4128768,-40665088,202637312,-562888704,811204608,645595136,-6592135168,10157522944,4735303680,-15266119680]),(⟨3,2,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,3,0⟩,[0,327680,-10223616,122355712,-782237696,3074555904,-8102871040,14965669888,-17502830592,4268294144,19888603136,-20216610816]),(⟨3,3,1⟩,[0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨3,4,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,0,0⟩,[-40960,1245184,-14008320,65863680,21438464,-1911881728,11289067520,-37211996160,80798261248,-114527240192,77184122880,51975618560,-145639743488,84411744256]),(⟨4,0,1⟩,[0,0,0,1310720,-29097984,248512512,-1001390080,1549271040,1857552384,-9805234176,9052356608,5992873984,-10013638656]),(⟨4,0,2⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨4,1,0⟩,[0,0,0,1310720,-29097984,248512512,-1001390080,1549271040,1857552384,-9805234176,9052356608,5992873984,-10013638656]),(⟨4,1,2⟩,[-163840,4456448,-46891008,239599616,-599326720,519045120,898170880,-3783786496,6292733952,-2750676992,-2920644608]),(⟨4,1,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,2,0⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨4,2,1⟩,[-163840,4456448,-46891008,239599616,-599326720,519045120,898170880,-3783786496,6292733952,-2750676992,-2920644608]),(⟨4,2,2⟩,[-65536,2162688,-26476544,155451392,-472776704,748552192,-363069440,-2118909952,7422279680,-7494631424]),(⟨4,2,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,3,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,4,1⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨5,0,0⟩,[-16384,1081344,-21594112,209747968,-1176485888,4135649280,-9505144832,14206435328,-10675011584,-8160116736,29438148608,-21012774912,-1734885376]),(⟨5,0,2⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨5,1,2⟩,[-65536,2162688,-26476544,155451392,-472776704,748552192,-363069440,-2118909952,7422279680,-7494631424]),(⟨5,2,0⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨5,2,1⟩,[-65536,2162688,-26476544,155451392,-472776704,748552192,-363069440,-2118909952,7422279680,-7494631424]),(⟨6,0,0⟩,[0,163840,-5111808,61177856,-391118848,1537277952,-4051435520,7482834944,-8751415296,2134147072,9944301568,-10108305408])]


theorem partial_checked4 :
    (Poly.add (Poly.add (Poly.mul chunk4 sourceRight) partial8)
      (Poly.scale (K.ofRat (-1)) partial4)).isZero := by decide +kernel

theorem partial_sound4 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 4)
      sourceRight).eval u v t=partial4.eval u v t := by
  change (Poly.mul (chunk4++(sourceLeft.drop 8))
    sourceRight).eval u v t=partial4.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound8 partial_checked4 u v t


noncomputable def chunk0 : Poly := [(⟨0,0,0⟩,[-256,4800,-35712,145856,-387968,744000,-1039488,811328,-95104]),(⟨0,0,1⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨0,0,2⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨0,0,3⟩,[128,-2688,15616,-40192,84608,-123008])]

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[-32768,1302528,-23764992,264773632,-2017460224,11143176192,-46120132608,145777598464,-354561441792,657673789440,-887034568704,722335195136,33901281280,-996792655872,1305957457920,-739457769472,143222521856,-8764784640]),(⟨0,0,1⟩,[-8192,638976,-16293888,221200384,-1906663424,11391549440,-49599094784,162151907328,-403995369472,763331231744,-1042646949888,847792357376,64833773568,-1193058582528,1472903290880,-732490481664,78538915840]),(⟨0,0,2⟩,[73728,-2695168,42967040,-397074432,2367528960,-9503383552,25574449152,-42062438400,20024877056,98984370176,-315153129472,460898590720,-265980878848,-208836124672,411791286272,-175064064000]),(⟨0,0,3⟩,[24576,-1703936,38363136,-446955520,3200409600,-15342436352,51669983232,-125394223104,218340925440,-249492144128,101233532928,217940230144,-413533003776,242564005888,-10912784384]),(⟨0,0,4⟩,[-40960,1245184,-14008320,65863680,21438464,-1911881728,11289067520,-37211996160,80798261248,-114527240192,77184122880,51975618560,-145639743488,84411744256]),(⟨0,0,5⟩,[-16384,1081344,-21594112,209747968,-1176485888,4135649280,-9505144832,14206435328,-10675011584,-8160116736,29438148608,-21012774912,-1734885376]),(⟨0,0,6⟩,[0,163840,-5111808,61177856,-391118848,1537277952,-4051435520,7482834944,-8751415296,2134147072,9944301568,-10108305408]),(⟨0,1,0⟩,[-8192,638976,-16293888,221200384,-1906663424,11391549440,-49599094784,162151907328,-403995369472,763331231744,-1042646949888,847792357376,64833773568,-1193058582528,1472903290880,-732490481664,78538915840]),(⟨0,1,1⟩,[0,114688,-4816896,82788352,-811925504,5225627648,-23915823104,82173247488,-219149631488,453207736320,-682097016832,601143492608,33000456192,-813785399296,910125072384,-355931340800]),(⟨0,1,2⟩,[8192,-688128,16506880,-198049792,1439440896,-6946521088,23301971968,-54848651264,86002982912,-67222994944,-45923786752,186579550208,-179570843648,18889801728,51366174720]),(⟨0,1,3⟩,[0,-196608,7110656,-102465536,821198848,-4233789440,15369568256,-41654091776,84634304512,-116280524800,69379719168,69605687296,-156840460288,85736390656]),(⟨0,1,4⟩,[0,0,0,1310720,-29097984,248512512,-1001390080,1549271040,1857552384,-9805234176,9052356608,5992873984,-10013638656]),(⟨0,2,0⟩,[73728,-2695168,42967040,-397074432,2367528960,-9503383552,25574449152,-42062438400,20024877056,98984370176,-315153129472,460898590720,-265980878848,-208836124672,411791286272,-175064064000]),(⟨0,2,1⟩,[8192,-688128,16506880,-198049792,1439440896,-6946521088,23301971968,-54848651264,86002982912,-67222994944,-45923786752,186579550208,-179570843648,18889801728,51366174720]),(⟨0,2,2⟩,[-114688,3964928,-58032128,472154112,-2348433408,7298088960,-13326680064,9309847552,16289480704,-47866675200,39730708480,12986253312,-32921731072,4525588480]),(⟨0,2,3⟩,[-16384,1310720,-27590656,274464768,-1549221888,5323620352,-11163926528,12572426240,-316325888,-22787915776,31244484608,-6423314432,-12516704256]),(⟨0,2,4⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨0,2,5⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨0,3,0⟩,[24576,-1703936,38363136,-446955520,3200409600,-15342436352,51669983232,-125394223104,218340925440,-249492144128,101233532928,217940230144,-413533003776,242564005888,-10912784384]),(⟨0,3,1⟩,[0,-196608,7110656,-102465536,821198848,-4233789440,15369568256,-41654091776,84634304512,-116280524800,69379719168,69605687296,-156840460288,85736390656]),(⟨0,3,2⟩,[-16384,1310720,-27590656,274464768,-1549221888,5323620352,-11163926528,12572426240,-316325888,-22787915776,31244484608,-6423314432,-12516704256]),(⟨0,3,3⟩,[0,327680,-10223616,122355712,-782237696,3074555904,-8102871040,14965669888,-17502830592,4268294144,19888603136,-20216610816]),(⟨0,4,0⟩,[-40960,1245184,-14008320,65863680,21438464,-1911881728,11289067520,-37211996160,80798261248,-114527240192,77184122880,51975618560,-145639743488,84411744256]),(⟨0,4,1⟩,[0,0,0,1310720,-29097984,248512512,-1001390080,1549271040,1857552384,-9805234176,9052356608,5992873984,-10013638656]),(⟨0,4,2⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨0,5,0⟩,[-16384,1081344,-21594112,209747968,-1176485888,4135649280,-9505144832,14206435328,-10675011584,-8160116736,29438148608,-21012774912,-1734885376]),(⟨0,5,2⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨0,6,0⟩,[0,163840,-5111808,61177856,-391118848,1537277952,-4051435520,7482834944,-8751415296,2134147072,9944301568,-10108305408]),(⟨1,0,0⟩,[-8192,638976,-16293888,221200384,-1906663424,11391549440,-49599094784,162151907328,-403995369472,763331231744,-1042646949888,847792357376,64833773568,-1193058582528,1472903290880,-732490481664,78538915840]),(⟨1,0,1⟩,[0,114688,-4816896,82788352,-811925504,5225627648,-23915823104,82173247488,-219149631488,453207736320,-682097016832,601143492608,33000456192,-813785399296,910125072384,-355931340800]),(⟨1,0,2⟩,[8192,-688128,16506880,-198049792,1439440896,-6946521088,23301971968,-54848651264,86002982912,-67222994944,-45923786752,186579550208,-179570843648,18889801728,51366174720]),(⟨1,0,3⟩,[0,-196608,7110656,-102465536,821198848,-4233789440,15369568256,-41654091776,84634304512,-116280524800,69379719168,69605687296,-156840460288,85736390656]),(⟨1,0,4⟩,[0,0,0,1310720,-29097984,248512512,-1001390080,1549271040,1857552384,-9805234176,9052356608,5992873984,-10013638656]),(⟨1,1,0⟩,[0,114688,-4816896,82788352,-811925504,5225627648,-23915823104,82173247488,-219149631488,453207736320,-682097016832,601143492608,33000456192,-813785399296,910125072384,-355931340800]),(⟨1,1,1⟩,[0,0,0,-2752512,71958528,-776601600,4472832000,-14255652864,19905380352,19608109056,-124304228352,175533588480,-21676032000,-175073525760,129381826560]),(⟨1,1,2⟩,[0,0,-131072,4194304,-53870592,352845824,-1188298752,1371537408,3394502656,-12355371008,8819965952,11597250560,-16273768448,2183659520]),(⟨1,1,3⟩,[0,0,0,1310720,-29097984,248512512,-1001390080,1549271040,1857552384,-9805234176,9052356608,5992873984,-10013638656]),(⟨1,2,0⟩,[8192,-688128,16506880,-198049792,1439440896,-6946521088,23301971968,-54848651264,86002982912,-67222994944,-45923786752,186579550208,-179570843648,18889801728,51366174720]),(⟨1,2,1⟩,[0,0,-131072,4194304,-53870592,352845824,-1188298752,1371537408,3394502656,-12355371008,8819965952,11597250560,-16273768448,2183659520]),(⟨1,2,2⟩,[131072,-3801088,45711360,-298385408,1166508032,-2866282496,4539482112,-3826122752,-5992808448,36816158720,-75021189120,65775009792,-16576315392]),(⟨1,2,3⟩,[32768,-1343488,21135360,-171868160,809566208,-2312699904,3908632576,-2340487168,-8430649344,31443484672,-48301309952,29670473728]),(⟨1,2,4⟩,[-163840,4456448,-46891008,239599616,-599326720,519045120,898170880,-3783786496,6292733952,-2750676992,-2920644608]),(⟨1,2,5⟩,[-65536,2162688,-26476544,155451392,-472776704,748552192,-363069440,-2118909952,7422279680,-7494631424]),(⟨1,3,0⟩,[0,-196608,7110656,-102465536,821198848,-4233789440,15369568256,-41654091776,84634304512,-116280524800,69379719168,69605687296,-156840460288,85736390656]),(⟨1,3,1⟩,[0,0,0,1310720,-29097984,248512512,-1001390080,1549271040,1857552384,-9805234176,9052356608,5992873984,-10013638656]),(⟨1,3,2⟩,[32768,-1343488,21135360,-171868160,809566208,-2312699904,3908632576,-2340487168,-8430649344,31443484672,-48301309952,29670473728]),(⟨1,3,3⟩,[0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨1,4,0⟩,[0,0,0,1310720,-29097984,248512512,-1001390080,1549271040,1857552384,-9805234176,9052356608,5992873984,-10013638656]),(⟨1,4,2⟩,[-163840,4456448,-46891008,239599616,-599326720,519045120,898170880,-3783786496,6292733952,-2750676992,-2920644608]),(⟨1,4,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨1,5,2⟩,[-65536,2162688,-26476544,155451392,-472776704,748552192,-363069440,-2118909952,7422279680,-7494631424]),(⟨2,0,0⟩,[73728,-2695168,42967040,-397074432,2367528960,-9503383552,25574449152,-42062438400,20024877056,98984370176,-315153129472,460898590720,-265980878848,-208836124672,411791286272,-175064064000]),(⟨2,0,1⟩,[8192,-688128,16506880,-198049792,1439440896,-6946521088,23301971968,-54848651264,86002982912,-67222994944,-45923786752,186579550208,-179570843648,18889801728,51366174720]),(⟨2,0,2⟩,[-114688,3964928,-58032128,472154112,-2348433408,7298088960,-13326680064,9309847552,16289480704,-47866675200,39730708480,12986253312,-32921731072,4525588480]),(⟨2,0,3⟩,[-16384,1310720,-27590656,274464768,-1549221888,5323620352,-11163926528,12572426240,-316325888,-22787915776,31244484608,-6423314432,-12516704256]),(⟨2,0,4⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨2,0,5⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨2,1,0⟩,[8192,-688128,16506880,-198049792,1439440896,-6946521088,23301971968,-54848651264,86002982912,-67222994944,-45923786752,186579550208,-179570843648,18889801728,51366174720]),(⟨2,1,1⟩,[0,0,-131072,4194304,-53870592,352845824,-1188298752,1371537408,3394502656,-12355371008,8819965952,11597250560,-16273768448,2183659520]),(⟨2,1,2⟩,[131072,-3801088,45711360,-298385408,1166508032,-2866282496,4539482112,-3826122752,-5992808448,36816158720,-75021189120,65775009792,-16576315392]),(⟨2,1,3⟩,[32768,-1343488,21135360,-171868160,809566208,-2312699904,3908632576,-2340487168,-8430649344,31443484672,-48301309952,29670473728]),(⟨2,1,4⟩,[-163840,4456448,-46891008,239599616,-599326720,519045120,898170880,-3783786496,6292733952,-2750676992,-2920644608]),(⟨2,1,5⟩,[-65536,2162688,-26476544,155451392,-472776704,748552192,-363069440,-2118909952,7422279680,-7494631424]),(⟨2,2,0⟩,[-114688,3964928,-58032128,472154112,-2348433408,7298088960,-13326680064,9309847552,16289480704,-47866675200,39730708480,12986253312,-32921731072,4525588480]),(⟨2,2,1⟩,[131072,-3801088,45711360,-298385408,1166508032,-2866282496,4539482112,-3826122752,-5992808448,36816158720,-75021189120,65775009792,-16576315392]),(⟨2,2,2⟩,[196608,-7176192,103809024,-780238848,3319922688,-7966752768,9180020736,2245066752,-31906922496,85632516096,-132698603520,87373676544]),(⟨2,2,3⟩,[-163840,4128768,-40665088,202637312,-562888704,811204608,645595136,-6592135168,10157522944,4735303680,-15266119680]),(⟨2,2,4⟩,[-65536,2162688,-26476544,155451392,-472776704,748552192,-363069440,-2118909952,7422279680,-7494631424]),(⟨2,3,0⟩,[-16384,1310720,-27590656,274464768,-1549221888,5323620352,-11163926528,12572426240,-316325888,-22787915776,31244484608,-6423314432,-12516704256]),(⟨2,3,1⟩,[32768,-1343488,21135360,-171868160,809566208,-2312699904,3908632576,-2340487168,-8430649344,31443484672,-48301309952,29670473728]),(⟨2,3,2⟩,[-163840,4128768,-40665088,202637312,-562888704,811204608,645595136,-6592135168,10157522944,4735303680,-15266119680]),(⟨2,3,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,4,0⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨2,4,1⟩,[-163840,4456448,-46891008,239599616,-599326720,519045120,898170880,-3783786496,6292733952,-2750676992,-2920644608]),(⟨2,4,2⟩,[-65536,2162688,-26476544,155451392,-472776704,748552192,-363069440,-2118909952,7422279680,-7494631424]),(⟨2,4,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,5,0⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨2,5,1⟩,[-65536,2162688,-26476544,155451392,-472776704,748552192,-363069440,-2118909952,7422279680,-7494631424]),(⟨3,0,0⟩,[24576,-1703936,38363136,-446955520,3200409600,-15342436352,51669983232,-125394223104,218340925440,-249492144128,101233532928,217940230144,-413533003776,242564005888,-10912784384]),(⟨3,0,1⟩,[0,-196608,7110656,-102465536,821198848,-4233789440,15369568256,-41654091776,84634304512,-116280524800,69379719168,69605687296,-156840460288,85736390656]),(⟨3,0,2⟩,[-16384,1310720,-27590656,274464768,-1549221888,5323620352,-11163926528,12572426240,-316325888,-22787915776,31244484608,-6423314432,-12516704256]),(⟨3,0,3⟩,[0,327680,-10223616,122355712,-782237696,3074555904,-8102871040,14965669888,-17502830592,4268294144,19888603136,-20216610816]),(⟨3,1,0⟩,[0,-196608,7110656,-102465536,821198848,-4233789440,15369568256,-41654091776,84634304512,-116280524800,69379719168,69605687296,-156840460288,85736390656]),(⟨3,1,1⟩,[0,0,0,1310720,-29097984,248512512,-1001390080,1549271040,1857552384,-9805234176,9052356608,5992873984,-10013638656]),(⟨3,1,2⟩,[32768,-1343488,21135360,-171868160,809566208,-2312699904,3908632576,-2340487168,-8430649344,31443484672,-48301309952,29670473728]),(⟨3,1,3⟩,[0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨3,2,0⟩,[-16384,1310720,-27590656,274464768,-1549221888,5323620352,-11163926528,12572426240,-316325888,-22787915776,31244484608,-6423314432,-12516704256]),(⟨3,2,1⟩,[32768,-1343488,21135360,-171868160,809566208,-2312699904,3908632576,-2340487168,-8430649344,31443484672,-48301309952,29670473728]),(⟨3,2,2⟩,[-163840,4128768,-40665088,202637312,-562888704,811204608,645595136,-6592135168,10157522944,4735303680,-15266119680]),(⟨3,2,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,3,0⟩,[0,327680,-10223616,122355712,-782237696,3074555904,-8102871040,14965669888,-17502830592,4268294144,19888603136,-20216610816]),(⟨3,3,1⟩,[0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨3,4,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,0,0⟩,[-40960,1245184,-14008320,65863680,21438464,-1911881728,11289067520,-37211996160,80798261248,-114527240192,77184122880,51975618560,-145639743488,84411744256]),(⟨4,0,1⟩,[0,0,0,1310720,-29097984,248512512,-1001390080,1549271040,1857552384,-9805234176,9052356608,5992873984,-10013638656]),(⟨4,0,2⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨4,1,0⟩,[0,0,0,1310720,-29097984,248512512,-1001390080,1549271040,1857552384,-9805234176,9052356608,5992873984,-10013638656]),(⟨4,1,2⟩,[-163840,4456448,-46891008,239599616,-599326720,519045120,898170880,-3783786496,6292733952,-2750676992,-2920644608]),(⟨4,1,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,2,0⟩,[32768,-1048576,13467648,-88211456,297074688,-342884352,-848625664,3088842752,-2204991488,-2899312640,4068442112,-545914880]),(⟨4,2,1⟩,[-163840,4456448,-46891008,239599616,-599326720,519045120,898170880,-3783786496,6292733952,-2750676992,-2920644608]),(⟨4,2,2⟩,[-65536,2162688,-26476544,155451392,-472776704,748552192,-363069440,-2118909952,7422279680,-7494631424]),(⟨4,2,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,3,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,4,1⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨5,0,0⟩,[-16384,1081344,-21594112,209747968,-1176485888,4135649280,-9505144832,14206435328,-10675011584,-8160116736,29438148608,-21012774912,-1734885376]),(⟨5,0,2⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨5,1,2⟩,[-65536,2162688,-26476544,155451392,-472776704,748552192,-363069440,-2118909952,7422279680,-7494631424]),(⟨5,2,0⟩,[0,-327680,7274496,-62128128,250347520,-387317760,-464388096,2451308544,-2263089152,-1498218496,2503409664]),(⟨5,2,1⟩,[-65536,2162688,-26476544,155451392,-472776704,748552192,-363069440,-2118909952,7422279680,-7494631424]),(⟨6,0,0⟩,[0,163840,-5111808,61177856,-391118848,1537277952,-4051435520,7482834944,-8751415296,2134147072,9944301568,-10108305408])]


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
    (Poly.add (Poly.scale (K.ofRat r623) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 6 12).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r622*r622 : ℚ)=r623 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 6 12 r622 r622 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 6=12 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 6 12).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C120

#print axioms Coulomb8.Columns.C120.sound
