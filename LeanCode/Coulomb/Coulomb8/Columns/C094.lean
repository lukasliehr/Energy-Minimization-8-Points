import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C094

def r0 : ℚ := { num := -65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 131072, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -31981568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 242024448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -863305728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -1103429632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 29821763584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -171544936448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 575567364096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -1253205082112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 105082519552, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -250713800704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 275343933440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -71915864064, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 5088554516480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -3827393232896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 1167485042688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -119776739328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 393216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := -6750208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := 430440448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := -303300608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := 3542089728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 23216259072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -189985456128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 686606974976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -1483205378048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 1985520009216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -1805681950720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 46297645056, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -4734795382784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 382794072064, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -4138438754304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 101010898944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -524288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 38010880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -19660800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := -577765376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := 8300789760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -38921830400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 91817902080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -76522323968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -137088204800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 21468807168, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -162042740736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -2127822848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -935135019008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 1897152118784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := -148097597440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -5242880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 79167488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -11534336, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 1534328832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 5170003968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -59133788160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := 226228174848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -457482567680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 475896217600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -2202796032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 542871912448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := -1383870758912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := 1235680231424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := -181462237184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := 131072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 5636096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -173211648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 1175257088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -2343239680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := -9788194816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 9789374464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -164225286144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := 167257833472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := -60648194048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := 12304056320, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := -610916433920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := 68927291392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 2490368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -31916032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 152567808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := 7864320, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := -4395368448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := 18596102144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := -33084145664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := 16876240896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 4492492800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := 51331792896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := -87225794560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := 594411520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 524288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := -11665408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 4849664, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -86507520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := -1663565824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := 8921546752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -17682399232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 9415688192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := 3289382912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 31924813824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := -55665098752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := 1048576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -655360, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 405405696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -2686582784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 9096265728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -4863033344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := -92415197184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 424699232256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -915864289280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 1042121883648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := -918945792, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 1640909635584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -247637606400, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 5018345799680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -322908717056, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := -4718592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := 9568256, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := -467533824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := 29360128, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 1313341440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -27265990656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 99859824640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := -176787161088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := 153972899840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -6928334848, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 304255991808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -51678281728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := -206474051584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 68716986368, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := -1572864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := 6029312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := -438829056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := 303169536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := -3122790400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -16012804096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 91832713216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -191191842816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 159189303296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := -53282603008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := 314431242240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := -768409206784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := 76836634624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := 1966080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -21299200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 92930048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -20709376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := -167510016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 3272998912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -6553600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := -7014514688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -11443765248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 25530662912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := 68905205760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := -1008074752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 99221504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := -56098816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := 571998208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := 763625472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := -3165913088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := 947388416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 214958080, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 4296933376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -92930048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := -131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := 2883584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := -16252928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -13500416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := 1655832576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := -8900182016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := 23300407296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := -25925255168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -5076025344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := 19079888896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 36218339328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -27239514112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -10044178432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 775028736, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 262144, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -55312384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := 292159488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := -283901952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -3997171712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 19547553792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -2089025536, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 17794203648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := 2144075776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := 60802465792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -85571534848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := -1667235840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -23330816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 9699328, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -173015040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := -3327131648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := 17843093504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -35364798464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 18831376384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := 6578765824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 63849627648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -111330197504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := 123469824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := -1312555008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := 1031012352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := -20606877696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := 20631257088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 4927782912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -65184202752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -3161456640, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := 315108360192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := 12431130624, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -291990405120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := 1853620224, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := -1048576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := 4063232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := -44695552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := 1774845952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -5235933184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 796655616, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := 9061007360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := -3632529408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := 2742288384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := -6083182592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 128409796608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := -19820314624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -17694720, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 2097152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -46661632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 393740288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -1495269376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 1679818752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := 4421844992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := -7297040384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := -24874319872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := 34443624448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := 94203543552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := -1249378304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := 3932160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := -393216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := 279183360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -835190784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 16252928, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := 15990784, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -4858576896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := 262275072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -4696834048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := 18941345792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := 472645632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := -38010880, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := -262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := 6815744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := -524288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := 163577856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := 63438848, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := -9574547456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := 28498198528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := -24876417024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -61121757184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := 174575845376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -146801164288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := 239075328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := 1048576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := -74973184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := 295698432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := 247988224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := -6186598400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := 20201865216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -2497708032, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -43430182912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := 16486760448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := -96993280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := 262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := -5767168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := 5242880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := 33554432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := -1202192384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := 4090494976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := -1699741696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := -12838764544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := 2551971840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := -3670016, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := -6291456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := 45088768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := -2097152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := -1235746816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := 648019968, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := -1892679680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := -14761852928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := 157024256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := -25165824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := 12582912, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := -679477248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -211812352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 5259657216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -6127878144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := -75497472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := 3145728, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := -169869312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := -52953088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := 1314914304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := -1531969536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := -18874368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := -32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := 65536, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -15990784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := 121012224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := -431652864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -551714816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 14910881792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -85772468224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 287783682048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -626602541056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 52541259776, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -125356900352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 137671966720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := -35957932032, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 2544277258240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -1913696616448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := 583742521344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := -59888369664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := 196608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := -3375104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := 215220224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := -151650304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := 1771044864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := 11608129536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -94992728064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 343303487488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -741602689024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 992760004608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := -902840975360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := 23148822528, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -2367397691392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 191397036032, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -2069219377152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 50505449472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := 65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := -262144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := 19005440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := -9830400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := -288882688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := 4150394880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := -19460915200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := 45908951040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := -38261161984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := -68544102400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := 10734403584, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := -81021370368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := -1063911424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := -467567509504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := 948576059392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := -74048798720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := -2621440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := 39583744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := -5767168, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := 767164416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := 2585001984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := -29566894080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := 113114087424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -228741283840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := 237948108800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := -1101398016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := 271435956224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := -691935379456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := 617840115712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := -90731118592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := 65536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := 2818048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := -86605824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := 587628544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := -1171619840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := -4894097408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := 4894687232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := -82112643072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := 83628916736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := -30324097024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := 6152028160, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := -305458216960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := 34463645696, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := 1245184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := -15958016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := 76283904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := 3932160, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := -2197684224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := 9298051072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := -16542072832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := 8438120448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := 2246246400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := 25665896448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := -43612897280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := 297205760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := -5832704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := 2424832, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := -43253760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := -831782912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 4460773376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := -8841199616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := 4707844096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := 1644691456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := 15962406912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := -27832549376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := -327680, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := 202702848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := -1343291392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := 4548132864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := -2431516672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := -46207598592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := 212349616128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := -457932144640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := 521060941824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := -459472896, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := 820454817792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := -123818803200, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := 2509172899840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := -161454358528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := -2359296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := 4784128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := -233766912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := 14680064, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := 656670720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := -13632995328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := 49929912320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := -88393580544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := 76986449920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := -3464167424, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := 152127995904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := -25839140864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := -103237025792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := 34358493184, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := -786432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := 3014656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := -219414528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := 151584768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := -1561395200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := -8006402048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := 45916356608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := -95595921408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := 79594651648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := -26641301504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := 157215621120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := -384204603392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := 38418317312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := 983040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := -10649600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := 46465024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := -10354688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := -83755008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := 1636499456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := -3276800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := -3507257344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := -5721882624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := 12765331456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r450 : ℚ := { num := 34452602880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r451 : ℚ := { num := -504037376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r452 : ℚ := { num := 49610752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r453 : ℚ := { num := -28049408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r454 : ℚ := { num := 285999104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r455 : ℚ := { num := 381812736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r456 : ℚ := { num := -1582956544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r457 : ℚ := { num := 473694208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r458 : ℚ := { num := 107479040, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r459 : ℚ := { num := 2148466688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r460 : ℚ := { num := -46465024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r461 : ℚ := { num := 1441792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r462 : ℚ := { num := -8126464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r463 : ℚ := { num := 827916288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r464 : ℚ := { num := -4450091008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r465 : ℚ := { num := 11650203648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r466 : ℚ := { num := -12962627584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r467 : ℚ := { num := -2538012672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r468 : ℚ := { num := 9539944448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r469 : ℚ := { num := 18109169664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r470 : ℚ := { num := -13619757056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r471 : ℚ := { num := -5022089216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r472 : ℚ := { num := 387514368, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r473 : ℚ := { num := -27656192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r474 : ℚ := { num := 146079744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r475 : ℚ := { num := -141950976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r476 : ℚ := { num := -1998585856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r477 : ℚ := { num := 9773776896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r478 : ℚ := { num := -1044512768, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r479 : ℚ := { num := 8897101824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r480 : ℚ := { num := 1072037888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r481 : ℚ := { num := 30401232896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r482 : ℚ := { num := -42785767424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r483 : ℚ := { num := -833617920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r484 : ℚ := { num := 61734912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r485 : ℚ := { num := -656277504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r486 : ℚ := { num := 515506176, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r487 : ℚ := { num := -10303438848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r488 : ℚ := { num := 10315628544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r489 : ℚ := { num := 2463891456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r490 : ℚ := { num := -32592101376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r491 : ℚ := { num := -1580728320, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r492 : ℚ := { num := 157554180096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r493 : ℚ := { num := 6215565312, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r494 : ℚ := { num := -145995202560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r495 : ℚ := { num := 926810112, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r496 : ℚ := { num := -524288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r497 : ℚ := { num := 2031616, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r498 : ℚ := { num := -22347776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r499 : ℚ := { num := 887422976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r500 : ℚ := { num := -2617966592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r501 : ℚ := { num := 398327808, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r502 : ℚ := { num := 4530503680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r503 : ℚ := { num := -1816264704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r504 : ℚ := { num := 1371144192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r505 : ℚ := { num := -3041591296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r506 : ℚ := { num := 64204898304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r507 : ℚ := { num := -9910157312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r508 : ℚ := { num := -8847360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r509 : ℚ := { num := 196870144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r510 : ℚ := { num := -747634688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r511 : ℚ := { num := 839909376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r512 : ℚ := { num := 2210922496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r513 : ℚ := { num := -3648520192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r514 : ℚ := { num := -12437159936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r515 : ℚ := { num := 17221812224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r516 : ℚ := { num := 47101771776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r517 : ℚ := { num := -624689152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r518 : ℚ := { num := -196608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r519 : ℚ := { num := 139591680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r520 : ℚ := { num := -417595392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r521 : ℚ := { num := 8126464, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r522 : ℚ := { num := 7995392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r523 : ℚ := { num := -2429288448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r524 : ℚ := { num := 131137536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r525 : ℚ := { num := -2348417024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r526 : ℚ := { num := 9470672896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r527 : ℚ := { num := 236322816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r528 : ℚ := { num := -19005440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r529 : ℚ := { num := 3407872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r530 : ℚ := { num := -262144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r531 : ℚ := { num := 81788928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r532 : ℚ := { num := 31719424, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r533 : ℚ := { num := -4787273728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r534 : ℚ := { num := 14249099264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r535 : ℚ := { num := -12438208512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r536 : ℚ := { num := -30560878592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r537 : ℚ := { num := 87287922688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r538 : ℚ := { num := -73400582144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r539 : ℚ := { num := 119537664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r540 : ℚ := { num := 524288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r541 : ℚ := { num := -37486592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r542 : ℚ := { num := 147849216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r543 : ℚ := { num := 123994112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r544 : ℚ := { num := -3093299200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r545 : ℚ := { num := 10100932608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r546 : ℚ := { num := -1248854016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r547 : ℚ := { num := -21715091456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r548 : ℚ := { num := 8243380224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r549 : ℚ := { num := -48496640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r550 : ℚ := { num := -2883584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r551 : ℚ := { num := 2621440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r552 : ℚ := { num := 16777216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r553 : ℚ := { num := -601096192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r554 : ℚ := { num := 2045247488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r555 : ℚ := { num := -849870848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r556 : ℚ := { num := -6419382272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r557 : ℚ := { num := 1275985920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r558 : ℚ := { num := -1835008, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r559 : ℚ := { num := -3145728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r560 : ℚ := { num := 22544384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r561 : ℚ := { num := -617873408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r562 : ℚ := { num := 324009984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r563 : ℚ := { num := -946339840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r564 : ℚ := { num := -7380926464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r565 : ℚ := { num := 78512128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r566 : ℚ := { num := -12582912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r567 : ℚ := { num := 6291456, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r568 : ℚ := { num := -339738624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r569 : ℚ := { num := -105906176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r570 : ℚ := { num := 2629828608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r571 : ℚ := { num := -3063939072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r572 : ℚ := { num := -37748736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r573 : ℚ := { num := 1572864, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r574 : ℚ := { num := -84934656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r575 : ℚ := { num := -26476544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r576 : ℚ := { num := 657457152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r577 : ℚ := { num := -765984768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r578 : ℚ := { num := -9437184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r579 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r580 : ℚ := { num := 1, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17],[r0,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33],[r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49],[r34,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63],[r0,r64,r65,r66,r67,r68,r69,r70,r71,r72,r73,r74,r75,r76],[r0,r77,r78,r79,r80,r81,r82,r83,r84,r85,r86,r87,r88],[0,r89,r90,r91,r92,r93,r94,r95,r96,r97,r98,r99],[],[],[],[],[],[],[0,r100,r101,r102,r103,r104,r105,r106,r107,r108,r109,r110,r111,r112,r113,r114],[r34,r115,r116,r117,r118,r119,r120,r121,r122,r123,r124,r125,r126,r127,r128],[0,r129,r130,r131,r132,r133,r134,r135,r136,r137,r138,r139,r140,r141],[r0,r142,r143,r144,r145,r146,r147,r148,r149,r150,r151,r152,r153],[0,r89,r90,r154,r155,r156,r157,r158,r159,r160,r161,r162],[],[],[],[],[],[],[r163,r164,r165,r166,r167,r168,r169,r170,r171,r172,r173,r174,r175,r176],[r163,r177,r178,r179,r180,r181,r182,r183,r184,r185,r186,r187,r188],[0,r89,r90,r154,r155,r156,r157,r158,r159,r160,r161,r162],[],[],[],[],[],[],[0,r100,r189,r190,r191,r192,r193,r194,r195,r196,r197,r198],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,0,r115,r199,r200,r201,r202,r203,r204,r205,r206,r207,r208,r209,r210],[0,r211,r212,r213,r214,r215,r216,r217,r218,r219,r220,r221,r222,r223],[0,0,r224,r225,r226,r227,r228,r229,r230,r231,r232,r233,r234],[],[],[],[],[],[],[],[r163,r235,r236,r237,r238,r239,r240,r241,r242,r243,r244,r245,r246],[0,r89,r90,r154,r155,r156,r157,r158,r159,r160,r161,r162],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[r247,r248,r249,r250,r251,r252,r253,r254,r255,r256,r257,r258],[r247,r259,r260,r261,r262,r263,r264,r265,r266,r267,r268],[r269,r270,r271,r272,r273,r274,r275,r276,r277,r278],[r269,r279,r280,r281,r282,r283,r284,r285,r286],[],[],[],[0,r100,r287,r288,r289,r290,r291,r292,r293,1048576],[r269,r279,r294,r295,r296,r297,r298,r299,262144],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[r300,r301,r302,r303,r304,r305,r306,r307,r308,r309,r310,r311,r312,r313,r314,r315,r316,r317]),(⟨0,0,1⟩,[r300,r318,r319,r320,r321,r322,r323,r324,r325,r326,r327,r328,r329,r330,r331,r332,r333]),(⟨0,0,2⟩,[r334,r335,r336,r337,r338,r339,r340,r341,r342,r343,r344,r345,r346,r347,r348,r349]),(⟨0,0,3⟩,[r334,r350,r351,r352,r353,r354,r355,r356,r357,r358,r359,r360,r361,r362,r363]),(⟨0,0,4⟩,[r300,r364,r365,r366,r367,r368,r369,r370,r371,r372,r373,r374,r375,r376]),(⟨0,0,5⟩,[r300,r377,r378,r379,r380,r381,r382,r383,r384,r385,r386,r387,r388]),(⟨0,0,6⟩,[0,r269,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398]),(⟨0,1,0⟩,[r300,r318,r319,r320,r321,r322,r323,r324,r325,r326,r327,r328,r329,r330,r331,r332,r333]),(⟨0,1,1⟩,[0,r89,r399,r400,r401,r402,r403,r404,r405,r406,r407,r408,r409,r410,r411,r412]),(⟨0,1,2⟩,[r334,r413,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426]),(⟨0,1,3⟩,[0,r427,r428,r429,r430,r431,r432,r433,r434,r435,r436,r437,r438,r439]),(⟨0,1,4⟩,[r300,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451]),(⟨0,1,5⟩,[0,r269,r389,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨0,2,0⟩,[r334,r335,r336,r337,r338,r339,r340,r341,r342,r343,r344,r345,r346,r347,r348,r349]),(⟨0,2,1⟩,[r334,r413,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426]),(⟨0,2,2⟩,[r0,r461,r462,r19,r463,r464,r465,r466,r467,r468,r469,r470,r471,r472]),(⟨0,2,3⟩,[r0,r1,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483]),(⟨0,2,4⟩,[0,r269,r389,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨0,3,0⟩,[r334,r350,r351,r352,r353,r354,r355,r356,r357,r358,r359,r360,r361,r362,r363]),(⟨0,3,1⟩,[0,r427,r428,r429,r430,r431,r432,r433,r434,r435,r436,r437,r438,r439]),(⟨0,3,2⟩,[r0,r1,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483]),(⟨0,3,3⟩,[0,r89,r90,r91,r92,r93,r94,r95,r96,r97,r98,r99]),(⟨0,4,0⟩,[r300,r364,r365,r366,r367,r368,r369,r370,r371,r372,r373,r374,r375,r376]),(⟨0,4,1⟩,[r300,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451]),(⟨0,4,2⟩,[0,r269,r389,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨0,5,0⟩,[r300,r377,r378,r379,r380,r381,r382,r383,r384,r385,r386,r387,r388]),(⟨0,5,1⟩,[0,r269,r389,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨0,6,0⟩,[0,r269,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398]),(⟨1,0,0⟩,[r300,r318,r319,r320,r321,r322,r323,r324,r325,r326,r327,r328,r329,r330,r331,r332,r333]),(⟨1,0,1⟩,[0,r89,r399,r400,r401,r402,r403,r404,r405,r406,r407,r408,r409,r410,r411,r412]),(⟨1,0,2⟩,[r334,r413,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426]),(⟨1,0,3⟩,[0,r427,r428,r429,r430,r431,r432,r433,r434,r435,r436,r437,r438,r439]),(⟨1,0,4⟩,[r300,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451]),(⟨1,0,5⟩,[0,r269,r389,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨1,1,0⟩,[0,r89,r399,r400,r401,r402,r403,r404,r405,r406,r407,r408,r409,r410,r411,r412]),(⟨1,1,1⟩,[0,0,r413,r484,r485,r486,r487,r488,r489,r490,r491,r492,r493,r494,r495]),(⟨1,1,2⟩,[0,r496,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508]),(⟨1,1,3⟩,[0,0,r100,r189,r509,r510,r511,r512,r513,r514,r515,r516,r517]),(⟨1,2,0⟩,[r334,r413,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426]),(⟨1,2,1⟩,[0,r496,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508]),(⟨1,2,2⟩,[r0,r142,r518,r519,r520,r521,r522,r523,r524,r525,r526,r527,r528]),(⟨1,2,3⟩,[0,r269,r389,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨1,3,0⟩,[0,r427,r428,r429,r430,r431,r432,r433,r434,r435,r436,r437,r438,r439]),(⟨1,3,1⟩,[0,0,r100,r189,r509,r510,r511,r512,r513,r514,r515,r516,r517]),(⟨1,3,2⟩,[0,r269,r389,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨1,4,0⟩,[r300,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451]),(⟨1,5,0⟩,[0,r269,r389,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨2,0,0⟩,[r334,r335,r336,r337,r338,r339,r340,r341,r342,r343,r344,r345,r346,r347,r348,r349]),(⟨2,0,1⟩,[r334,r413,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426]),(⟨2,0,2⟩,[r0,r461,r462,r19,r463,r464,r465,r466,r467,r468,r469,r470,r471,r472]),(⟨2,0,3⟩,[r0,r1,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483]),(⟨2,0,4⟩,[0,r269,r389,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨2,1,0⟩,[r334,r413,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426]),(⟨2,1,1⟩,[0,r496,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508]),(⟨2,1,2⟩,[r0,r142,r518,r519,r520,r521,r522,r523,r524,r525,r526,r527,r528]),(⟨2,1,3⟩,[0,r269,r389,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨2,2,0⟩,[r0,r461,r462,r19,r463,r464,r465,r466,r467,r468,r469,r470,r471,r472]),(⟨2,2,1⟩,[r0,r142,r518,r519,r520,r521,r522,r523,r524,r525,r526,r527,r528]),(⟨2,2,2⟩,[r163,r529,r530,r531,r532,r533,r534,r535,r536,r537,r538,r539]),(⟨2,2,3⟩,[r163,r540,r541,r542,r543,r544,r545,r546,r547,r548,r549]),(⟨2,2,4⟩,[r34,r550,r551,r552,r553,r554,r555,r556,r557,r558]),(⟨2,2,5⟩,[r34,r559,r560,r211,r561,r562,r563,r564,r565]),(⟨2,3,0⟩,[r0,r1,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483]),(⟨2,3,1⟩,[0,r269,r389,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨2,3,2⟩,[r163,r540,r541,r542,r543,r544,r545,r546,r547,r548,r549]),(⟨2,3,3⟩,[0,r89,r566,r567,r568,r569,r570,r571,r572,524288]),(⟨2,3,4⟩,[r34,r559,r573,r574,r575,r576,r577,r578,131072]),(⟨2,4,0⟩,[0,r269,r389,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨2,4,2⟩,[r34,r550,r551,r552,r553,r554,r555,r556,r557,r558]),(⟨2,4,3⟩,[r34,r559,r573,r574,r575,r576,r577,r578,131072]),(⟨2,5,2⟩,[r34,r559,r560,r211,r561,r562,r563,r564,r565]),(⟨3,0,0⟩,[r334,r350,r351,r352,r353,r354,r355,r356,r357,r358,r359,r360,r361,r362,r363]),(⟨3,0,1⟩,[0,r427,r428,r429,r430,r431,r432,r433,r434,r435,r436,r437,r438,r439]),(⟨3,0,2⟩,[r0,r1,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483]),(⟨3,0,3⟩,[0,r89,r90,r91,r92,r93,r94,r95,r96,r97,r98,r99]),(⟨3,1,0⟩,[0,r427,r428,r429,r430,r431,r432,r433,r434,r435,r436,r437,r438,r439]),(⟨3,1,1⟩,[0,0,r100,r189,r509,r510,r511,r512,r513,r514,r515,r516,r517]),(⟨3,1,2⟩,[0,r269,r389,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨3,2,0⟩,[r0,r1,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483]),(⟨3,2,1⟩,[0,r269,r389,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨3,2,2⟩,[r163,r540,r541,r542,r543,r544,r545,r546,r547,r548,r549]),(⟨3,2,3⟩,[0,r89,r566,r567,r568,r569,r570,r571,r572,524288]),(⟨3,2,4⟩,[r34,r559,r573,r574,r575,r576,r577,r578,131072]),(⟨3,3,0⟩,[0,r89,r90,r91,r92,r93,r94,r95,r96,r97,r98,r99]),(⟨3,3,2⟩,[0,r89,r566,r567,r568,r569,r570,r571,r572,524288]),(⟨3,4,2⟩,[r34,r559,r573,r574,r575,r576,r577,r578,131072]),(⟨4,0,0⟩,[r300,r364,r365,r366,r367,r368,r369,r370,r371,r372,r373,r374,r375,r376]),(⟨4,0,1⟩,[r300,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451]),(⟨4,0,2⟩,[0,r269,r389,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨4,1,0⟩,[r300,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451]),(⟨4,2,0⟩,[0,r269,r389,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨4,2,2⟩,[r34,r550,r551,r552,r553,r554,r555,r556,r557,r558]),(⟨4,2,3⟩,[r34,r559,r573,r574,r575,r576,r577,r578,131072]),(⟨4,3,2⟩,[r34,r559,r573,r574,r575,r576,r577,r578,131072]),(⟨5,0,0⟩,[r300,r377,r378,r379,r380,r381,r382,r383,r384,r385,r386,r387,r388]),(⟨5,0,1⟩,[0,r269,r389,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨5,1,0⟩,[0,r269,r389,r452,r453,r454,r455,r456,r457,r458,r459,r460]),(⟨5,2,2⟩,[r34,r559,r560,r211,r561,r562,r563,r564,r565]),(⟨6,0,0⟩,[0,r269,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[128,-1792,5120,30720,-231808,574208,-567040,116736]),(⟨0,0,1⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨0,0,2⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨0,0,3⟩,[-128,1536,256,-37376,76672]),(⟨0,1,0⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨0,1,1⟩,[0,-512,6144,-15360,-18432,60928]),(⟨0,1,2⟩,[-128,1536,-3840,-4608,15232]),(⟨0,2,0⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨0,2,1⟩,[-128,1536,-3840,-4608,15232]),(⟨0,3,0⟩,[-128,1536,256,-37376,76672]),(⟨1,0,0⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨1,0,1⟩,[0,-512,6144,-15360,-18432,60928]),(⟨1,0,2⟩,[-128,1536,-3840,-4608,15232]),(⟨1,1,0⟩,[0,-512,6144,-15360,-18432,60928]),(⟨1,2,0⟩,[-128,1536,-3840,-4608,15232]),(⟨2,0,0⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨2,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨2,1,0⟩,[-128,1536,-3840,-4608,15232]),(⟨3,0,0⟩,[-128,1536,256,-37376,76672])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[-256,5120,-43008,199936,-545280,801024,-457728,253696,-1684736,2508544,-513024]),(⟨0,0,1⟩,[0,1536,-21760,121088,-327424,405248,-133888,235264,-1327360,1571584]),(⟨0,0,2⟩,[256,-4608,28416,-75264,67840,43520,25856,-250368,-32256]),(⟨0,0,3⟩,[0,-2048,20992,-74240,87040,37888,31232,-363008]),(⟨0,1,0⟩,[0,1536,-21760,121088,-327424,405248,-133888,235264,-1327360,1571584]),(⟨0,1,1⟩,[0,0,0,0,4096,-49152,122880,147456,-487424]),(⟨0,2,0⟩,[256,-4608,28416,-75264,67840,43520,25856,-250368,-32256]),(⟨0,3,0⟩,[0,-2048,20992,-74240,87040,37888,31232,-363008]),(⟨1,0,0⟩,[0,1536,-21760,121088,-327424,405248,-133888,235264,-1327360,1571584]),(⟨1,0,1⟩,[0,0,0,0,4096,-49152,122880,147456,-487424]),(⟨1,1,0⟩,[0,0,0,0,4096,-49152,122880,147456,-487424]),(⟨2,0,0⟩,[256,-4608,28416,-75264,67840,43520,25856,-250368,-32256]),(⟨2,2,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨3,0,0⟩,[0,-2048,20992,-74240,87040,37888,31232,-363008])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 3 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r579) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 13 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r579) sourceRight))).isZero := by decide +kernel

noncomputable def partial19 : Poly := []

theorem partial_sound19 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 19)
      sourceRight).eval u v t=partial19.eval u v t := by rfl

noncomputable def chunk16 : Poly := [(⟨2,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨2,1,0⟩,[-128,1536,-3840,-4608,15232]),(⟨3,0,0⟩,[-128,1536,256,-37376,76672])]

noncomputable def partial16 : Poly := [(⟨2,0,1⟩,[32768,-1048576,14352384,-110133248,514555904,-1431666688,1806434304,1746599936,-9633824768,10427367424,2247032832,1206747136,-35251257344,40574156800,-7814381568]),(⟨2,0,2⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨2,0,3⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨2,0,4⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨2,1,0⟩,[32768,-1048576,14352384,-110133248,514555904,-1431666688,1806434304,1746599936,-9633824768,10427367424,2247032832,1206747136,-35251257344,40574156800,-7814381568]),(⟨2,1,1⟩,[0,-393216,10289152,-109641728,608763904,-1792212992,2014969856,3122528256,-11618615296,7292583936,8775073792,7330267136,-54920413184,47876734976]),(⟨2,1,2⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨2,1,3⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨2,2,0⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨2,2,1⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨2,3,0⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨2,3,1⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨2,4,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨3,0,0⟩,[32768,-1048576,13303808,-80773120,154894336,1111130112,-9620946944,35179397120,-71258636288,75680251904,-41089564672,82274254848,-223062753280,211509870592,-39334576128]),(⟨3,0,1⟩,[0,-393216,10289152,-103350272,469303296,-488833024,-4630904832,22951100416,-45563117568,37541904384,-12597002240,71717027840,-187971076096,144434855936]),(⟨3,0,2⟩,[-32768,983040,-10649600,42532864,74317824,-1323433984,4965728256,-7883587584,3306913792,-373096448,14395867136,-13498515456,-9897574400]),(⟨3,0,3⟩,[0,262144,-5832704,41222144,-43253760,-831782912,4460773376,-8841199616,4707844096,1644691456,15962406912,-27832549376]),(⟨3,1,0⟩,[0,-393216,10289152,-103350272,469303296,-488833024,-4630904832,22951100416,-45563117568,37541904384,-12597002240,71717027840,-187971076096,144434855936]),(⟨3,1,1⟩,[0,0,0,0,-1572864,37748736,-304087040,683671552,2683305984,-14331936768,9913237504,38507905024,-52220657664]),(⟨3,2,0⟩,[-32768,983040,-10649600,42532864,74317824,-1323433984,4965728256,-7883587584,3306913792,-373096448,14395867136,-13498515456,-9897574400]),(⟨3,3,0⟩,[0,262144,-5832704,41222144,-43253760,-831782912,4460773376,-8841199616,4707844096,1644691456,15962406912,-27832549376]),(⟨4,0,0⟩,[0,-196608,5144576,-48529408,164921344,407273472,-5638389760,21389836288,-39753809920,33895612416,-16984539136,68051894272,-160510869504,120496488448]),(⟨4,0,1⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,492503040,-1550188544,2824568832,-7616659456,5456756736,25858736128,-37863096320]),(⟨4,1,0⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,492503040,-1550188544,2824568832,-7616659456,5456756736,25858736128,-37863096320]),(⟨4,2,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,3,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨5,0,0⟩,[-32768,983040,-10649600,42532864,74842112,-1336016896,5072683008,-8223326208,3201007616,2256732160,11331928064,-17990615040,-2473132032]),(⟨5,0,1⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨5,1,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨5,2,2⟩,[131072,-3145728,22544384,-1048576,-617873408,2268069888,-946339840,-7380926464,9342943232]),(⟨6,0,0⟩,[0,262144,-5832704,41222144,-43253760,-831782912,4460773376,-8841199616,4707844096,1644691456,15962406912,-27832549376])]


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

noncomputable def partial12 : Poly := [(⟨1,0,2⟩,[32768,-1048576,14352384,-110133248,514555904,-1431666688,1806434304,1746599936,-9633824768,10427367424,2247032832,1206747136,-35251257344,40574156800,-7814381568]),(⟨1,0,3⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨1,0,4⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨1,0,5⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨1,1,0⟩,[0,131072,-4194304,57409536,-440532992,2058223616,-5726666752,7225737216,6986399744,-38535299072,41709469696,8988131328,4826988544,-141005029376,162296627200,-31257526272]),(⟨1,1,1⟩,[0,0,-786432,20578304,-219283456,1217527808,-3584425984,4029939712,6245056512,-23237230592,14585167872,17550147584,14660534272,-109840826368,95753469952]),(⟨1,1,2⟩,[0,-327680,9076736,-101613568,583565312,-1729200128,1753546752,3891986432,-12026839040,5058592768,10210017280,10350723072,-42120085504,21973073920]),(⟨1,1,3⟩,[0,0,1048576,-23330816,197918720,-772800512,1037041664,1866989568,-6225920000,-735051776,10372513792,13085966336,-29541793792]),(⟨1,2,0⟩,[32768,-1048576,13565952,-89554944,295272448,-214138880,-1777991680,5776539648,-3388768256,-12809863168,16832200704,18756894720,-20590723072,-69266669568,87939088384]),(⟨1,2,1⟩,[0,-196608,5144576,-54820864,304381952,-898203648,1057816576,1133445120,-4450353152,4069916672,-6131777536,15920889856,-9491808256,-5759401984]),(⟨1,2,2⟩,[-65536,1966080,-23396352,139591680,-416546816,373030912,1165361152,-3108765696,706150400,2911240192,3342794752,-7329939456,-982646784]),(⟨1,2,3⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨1,3,0⟩,[0,-327680,9076736,-101613568,583565312,-1729200128,1753546752,3891986432,-12026839040,5058592768,10210017280,10350723072,-42120085504,21973073920]),(⟨1,3,1⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨1,3,2⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨1,4,0⟩,[-32768,983040,-10649600,46465024,-9830400,-598867968,1726676992,-27131904,-5978750976,3350396928,8979972096,4928897024,-22608674816]),(⟨1,5,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨2,0,0⟩,[32768,-983040,11730944,-65175552,74612736,1311866880,-9628483584,33827258368,-68341104640,76297797632,-49574510592,84584660992,-208272392192,213348614144,-67124396032,6435373056]),(⟨2,0,1⟩,[32768,-1245184,19103744,-151519232,630128640,-883294208,-3824287744,22152478720,-47719481344,45763330048,-20020494336,67463020544,-185175506944,166455934976,-27528331264]),(⟨2,0,2⟩,[-32768,524288,1081344,-78446592,718340096,-3120103424,6807420928,-4706140160,-7757791232,8204451840,18701778944,-9272623104,-54021718016,48281354240]),(⟨2,0,3⟩,[-32768,1245184,-17006592,103546880,-216793088,-662568960,4701093888,-9533390848,5696094208,-1184694272,19069304832,-24795152384,-3362193408]),(⟨2,0,4⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨2,1,0⟩,[32768,-1245184,18317312,-130940928,410845184,334233600,-7408713728,26182418432,-41474424832,22526099456,-5435326464,85013168128,-170514972672,56615108608,68225138688]),(⟨2,1,1⟩,[0,-393216,10289152,-109641728,608239616,-1782775808,1991901184,2627600384,-7855276032,-464781312,1655242752,45263552512,-72679620608,24293212160]),(⟨2,1,2⟩,[-32768,983040,-11698176,69795840,-209321984,211681280,368771072,-874905600,564887552,-3804037120,7799275520,5319229440,-15340208128]),(⟨2,1,3⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨2,2,0⟩,[-32768,524288,1081344,-78446592,718340096,-3122200576,6857752576,-5133959168,-6398836736,8628076544,8182464512,2983133184,-36053319680,18583584768]),(⟨2,2,1⟩,[-32768,983040,-11698176,69795840,-209321984,211681280,368771072,-874905600,564887552,-3804037120,7799275520,5319229440,-15340208128]),(⟨2,3,0⟩,[-32768,1245184,-17006592,103546880,-216793088,-662568960,4701093888,-9533390848,5696094208,-1184694272,19069304832,-24795152384,-3362193408]),(⟨2,3,1⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨2,4,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨3,0,0⟩,[32768,-1245184,18055168,-122159104,270467072,1659502592,-15251668992,55585275904,-109344292864,111016214528,-63357091840,148530528256,-372987002880,337391648768,-59048525824]),(⟨3,0,1⟩,[0,-393216,10289152,-103350272,468779008,-477298688,-4704305152,22883991552,-43158732800,29360914432,-9197518848,97394556928,-223698681856,150549102592]),(⟨3,0,2⟩,[-65536,1966080,-22347776,112328704,-133955584,-1136918528,5548408832,-9437970432,3659988992,1082523648,16067264512,-17163485184,-10388897792]),(⟨3,0,3⟩,[0,262144,-5832704,41222144,-43253760,-831782912,4460773376,-8841199616,4707844096,1644691456,15962406912,-27832549376]),(⟨3,1,0⟩,[0,-524288,14221312,-150142976,747962368,-1310392320,-3958243328,25214713856,-49376264192,30773215232,-3375038464,104080146432,-238358560768,148583809024]),(⟨3,1,1⟩,[0,0,0,0,-1572864,37748736,-304087040,683671552,2683305984,-14331936768,9913237504,38507905024,-52220657664]),(⟨3,2,0⟩,[-65536,1966080,-22347776,112328704,-133955584,-1136918528,5548408832,-9437970432,3659988992,1082523648,16067264512,-17163485184,-10388897792]),(⟨3,2,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,3,0⟩,[0,262144,-5832704,41222144,-43253760,-831782912,4460773376,-8841199616,4707844096,1644691456,15962406912,-27832549376]),(⟨3,3,2⟩,[0,524288,-12582912,106954752,-339738624,-105906176,2629828608,-3063939072,-4492099584,7424442368]),(⟨3,4,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,0,0⟩,[-32768,720896,-4063232,-17334272,274497536,-920616960,-845938688,13561167872,-35892985856,34807480320,-7057833984,51449004032,-159612174336,120901107712]),(⟨4,0,1⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,492503040,-1550188544,2824568832,-7616659456,5456756736,25858736128,-37863096320]),(⟨4,0,2⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨4,1,0⟩,[-32768,983040,-10649600,46465024,-10354688,-586285056,1636499456,-22937600,-3507257344,-5721882624,12765331456,34452602880,-59980447744]),(⟨4,2,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨4,2,2⟩,[131072,-2883584,18350080,16777216,-601096192,2045247488,-849870848,-6419382272,8931901440,-1528561664]),(⟨4,2,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,3,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨5,0,0⟩,[-32768,1245184,-15958016,76283904,66846720,-2197684224,9298051072,-16542072832,8438120448,2246246400,25665896448,-43612897280,2080440320]),(⟨5,0,1⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨5,1,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨5,2,2⟩,[131072,-3145728,22544384,-1048576,-617873408,2268069888,-946339840,-7380926464,9342943232]),(⟨6,0,0⟩,[0,262144,-5832704,41222144,-43253760,-831782912,4460773376,-8841199616,4707844096,1644691456,15962406912,-27832549376])]


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

noncomputable def partial8 : Poly := [(⟨0,2,1⟩,[32768,-1048576,14352384,-110133248,514555904,-1431666688,1806434304,1746599936,-9633824768,10427367424,2247032832,1206747136,-35251257344,40574156800,-7814381568]),(⟨0,2,2⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨0,2,3⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨0,2,4⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨0,3,0⟩,[32768,-1048576,13303808,-80773120,154894336,1111130112,-9620946944,35179397120,-71258636288,75680251904,-41089564672,82274254848,-223062753280,211509870592,-39334576128]),(⟨0,3,1⟩,[0,-393216,10289152,-103350272,469303296,-488833024,-4630904832,22951100416,-45563117568,37541904384,-12597002240,71717027840,-187971076096,144434855936]),(⟨0,3,2⟩,[-32768,983040,-10649600,42532864,74317824,-1323433984,4965728256,-7883587584,3306913792,-373096448,14395867136,-13498515456,-9897574400]),(⟨0,3,3⟩,[0,262144,-5832704,41222144,-43253760,-831782912,4460773376,-8841199616,4707844096,1644691456,15962406912,-27832549376]),(⟨0,4,0⟩,[0,-196608,5144576,-48529408,164921344,407273472,-5638389760,21389836288,-39753809920,33895612416,-16984539136,68051894272,-160510869504,120496488448]),(⟨0,4,1⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,492503040,-1550188544,2824568832,-7616659456,5456756736,25858736128,-37863096320]),(⟨0,5,0⟩,[-32768,983040,-10649600,42532864,74842112,-1336016896,5072683008,-8223326208,3201007616,2256732160,11331928064,-17990615040,-2473132032]),(⟨0,5,1⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨0,6,0⟩,[0,262144,-5832704,41222144,-43253760,-831782912,4460773376,-8841199616,4707844096,1644691456,15962406912,-27832549376]),(⟨1,0,0⟩,[-32768,1179648,-18087936,152862720,-738426880,1536983040,4381933568,-45844267008,174183972864,-388122869760,531614269440,-470681354240,520003223552,-1091877568512,1571203514368,-1023117688832,170077716480]),(⟨1,0,1⟩,[0,327680,-10125312,130056192,-892174336,3309993984,-4141481984,-19327352832,110746468352,-257808269312,309883404288,-211752812544,351519145984,-948386496512,1188933599232,-552269053952]),(⟨1,0,2⟩,[65536,-2162688,28737536,-192380928,603226112,122978304,-8152219648,30115430400,-49811947520,29277290496,3780411392,50903810048,-117810102272,1695842304,98632597504]),(⟨1,0,3⟩,[0,-589824,15958016,-170885120,896696320,-1980203008,-2294611968,24593629184,-58246496256,53880029184,-13056245760,63486197760,-187966128128,142317486080]),(⟨1,0,4⟩,[-32768,983040,-10649600,46465024,-9830400,-598867968,1726676992,-27131904,-5978750976,3350396928,8979972096,4928897024,-22608674816]),(⟨1,0,5⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨1,1,0⟩,[0,327680,-10125312,130056192,-892174336,3309993984,-4141481984,-19327352832,110746468352,-257808269312,309883404288,-211752812544,351519145984,-948386496512,1188933599232,-552269053952]),(⟨1,1,1⟩,[0,0,-1572864,41156608,-438042624,2420375552,-7018905600,7468482560,11994136576,-34101264384,-11233394688,70068207616,116181434368,-450496299008,353097744384]),(⟨1,1,2⟩,[0,-327680,9076736,-101613568,583565312,-1731297280,1803878400,3464167424,-10667884544,5482217472,-309297152,22606479360,-24151687168,-7724695552]),(⟨1,1,3⟩,[0,0,1048576,-23330816,197918720,-772800512,1037041664,1866989568,-6225920000,-735051776,10372513792,13085966336,-29541793792]),(⟨1,2,0⟩,[65536,-2162688,28737536,-192380928,603226112,122978304,-8152219648,30115430400,-49811947520,29277290496,3780411392,50903810048,-117810102272,1695842304,98632597504]),(⟨1,2,1⟩,[0,-524288,14221312,-156434432,887947264,-2627403776,2811363328,5025431552,-16477192192,9128509440,4078239744,26271612928,-51611893760,16213671936]),(⟨1,2,2⟩,[-65536,1966080,-23396352,139591680,-417071104,385613824,1058406400,-2769027072,812056576,281411584,6406733824,-2837839872,-8407089152]),(⟨1,2,3⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨1,3,0⟩,[0,-786432,21102592,-219414528,1061617664,-1572929536,-7933001728,45983465472,-98000306176,87775641600,-30040784896,131538092032,-348476997632,262813974528]),(⟨1,3,1⟩,[0,0,1048576,-23330816,196870144,-747634688,839909376,2210922496,-3648520192,-12437159936,17221812224,47101771776,-74338009088]),(⟨1,3,2⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨1,4,0⟩,[-32768,983040,-10649600,46465024,-10354688,-586285056,1636499456,-22937600,-3507257344,-5721882624,12765331456,34452602880,-59980447744]),(⟨1,5,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨2,0,0⟩,[32768,-786432,5799936,7471104,-377028608,2563637248,-8043298816,7274168320,35418963968,-142975172608,218599424000,-136156282880,138419765248,-594032852992,959512576000,-514576154624]),(⟨2,0,1⟩,[32768,-1245184,18317312,-130940928,411369472,319553536,-7258767360,25591021568,-41970401280,34899296256,-45839056896,119981080576,-83654606848,-174199537664,229815943168]),(⟨2,0,2⟩,[-32768,524288,1081344,-78446592,718340096,-3122200576,6857752576,-5133959168,-6398836736,8628076544,8182464512,2983133184,-36053319680,18583584768]),(⟨2,0,3⟩,[-32768,1245184,-17006592,103546880,-216793088,-662568960,4701093888,-9533390848,5696094208,-1184694272,19069304832,-24795152384,-3362193408]),(⟨2,0,4⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨2,1,0⟩,[32768,-1245184,18317312,-130940928,411369472,319553536,-7258767360,25591021568,-41970401280,34899296256,-45839056896,119981080576,-83654606848,-174199537664,229815943168]),(⟨2,1,1⟩,[0,-393216,10289152,-109641728,608239616,-1784872960,2042232832,2199781376,-6496321536,-41156608,-8864071680,57519308800,-54711222272,-5404557312]),(⟨2,1,2⟩,[-32768,983040,-11698176,69795840,-209321984,211681280,368771072,-874905600,564887552,-3804037120,7799275520,5319229440,-15340208128]),(⟨2,1,3⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨2,2,0⟩,[-32768,524288,1081344,-78446592,718340096,-3122200576,6857752576,-5133959168,-6398836736,8628076544,8182464512,2983133184,-36053319680,18583584768]),(⟨2,2,1⟩,[-65536,1966080,-23396352,139591680,-417595392,398196736,951451648,-2429288448,917962752,-2348417024,9470672896,1654259712,-15831531520]),(⟨2,3,0⟩,[-65536,2228224,-27656192,146079744,-141950976,-1998585856,9773776896,-17756717056,8897101824,1072037888,30401232896,-42785767424,-5835325440]),(⟨2,3,1⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨2,4,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨2,4,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,5,2⟩,[131072,-3145728,22544384,-1048576,-617873408,2268069888,-946339840,-7380926464,9342943232]),(⟨3,0,0⟩,[65536,-2359296,33226752,-224985088,578420736,1996619776,-21625896960,79924166656,-155767472128,153103368192,-76408881152,180677443584,-470206382080,408354160640,-48355016704]),(⟨3,0,1⟩,[0,-524288,14221312,-150142976,747962368,-1310392320,-3958243328,25214713856,-49376264192,30773215232,-3375038464,104080146432,-238358560768,148583809024]),(⟨3,0,2⟩,[-65536,1966080,-22347776,112328704,-133955584,-1136918528,5548408832,-9437970432,3659988992,1082523648,16067264512,-17163485184,-10388897792]),(⟨3,0,3⟩,[0,262144,-5832704,41222144,-43253760,-831782912,4460773376,-8841199616,4707844096,1644691456,15962406912,-27832549376]),(⟨3,1,0⟩,[0,-524288,14221312,-150142976,747962368,-1310392320,-3958243328,25214713856,-49376264192,30773215232,-3375038464,104080146432,-238358560768,148583809024]),(⟨3,1,1⟩,[0,0,0,0,-1572864,37748736,-304087040,683671552,2683305984,-14331936768,9913237504,38507905024,-52220657664]),(⟨3,2,0⟩,[-65536,1966080,-22347776,112328704,-133955584,-1136918528,5548408832,-9437970432,3659988992,1082523648,16067264512,-17163485184,-10388897792]),(⟨3,2,1⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨3,2,2⟩,[-131072,3670016,-37486592,147849216,123994112,-3093299200,10100932608,-8741978112,-21715091456,57703661568,-40397701120]),(⟨3,2,3⟩,[0,524288,-12582912,106954752,-339738624,-105906176,2629828608,-3063939072,-4492099584,7424442368]),(⟨3,2,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,3,0⟩,[0,524288,-11665408,82444288,-86507520,-1663565824,8921546752,-17682399232,9415688192,3289382912,31924813824,-55665098752]),(⟨3,3,2⟩,[0,524288,-12582912,106954752,-339738624,-105906176,2629828608,-3063939072,-4492099584,7424442368]),(⟨3,4,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,0,0⟩,[-32768,458752,2818048,-86605824,587628544,-1171619840,-4894097408,34262810624,-82112643072,83628916736,-30324097024,104584478720,-305458216960,241245519872]),(⟨4,0,1⟩,[-32768,983040,-10649600,46465024,-10354688,-586285056,1636499456,-22937600,-3507257344,-5721882624,12765331456,34452602880,-59980447744]),(⟨4,0,2⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨4,1,0⟩,[-32768,983040,-10649600,46465024,-10354688,-586285056,1636499456,-22937600,-3507257344,-5721882624,12765331456,34452602880,-59980447744]),(⟨4,2,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨4,2,2⟩,[131072,-2883584,18350080,16777216,-601096192,2045247488,-849870848,-6419382272,8931901440,-1528561664]),(⟨4,2,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,3,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨5,0,0⟩,[-32768,1245184,-15958016,76283904,66846720,-2197684224,9298051072,-16542072832,8438120448,2246246400,25665896448,-43612897280,2080440320]),(⟨5,0,1⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨5,1,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨5,2,2⟩,[131072,-3145728,22544384,-1048576,-617873408,2268069888,-946339840,-7380926464,9342943232]),(⟨6,0,0⟩,[0,262144,-5832704,41222144,-43253760,-831782912,4460773376,-8841199616,4707844096,1644691456,15962406912,-27832549376])]


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

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[-32768,1179648,-18087936,152862720,-738426880,1536983040,4381933568,-45844267008,174183972864,-388122869760,531614269440,-470681354240,520003223552,-1091877568512,1571203514368,-1023117688832,170077716480]),(⟨0,1,1⟩,[0,327680,-10125312,130056192,-892174336,3309993984,-4141481984,-19327352832,110746468352,-257808269312,309883404288,-211752812544,351519145984,-948386496512,1188933599232,-552269053952]),(⟨0,1,2⟩,[65536,-2162688,28737536,-192380928,603226112,122978304,-8152219648,30115430400,-49811947520,29277290496,3780411392,50903810048,-117810102272,1695842304,98632597504]),(⟨0,1,3⟩,[0,-589824,15958016,-170885120,896696320,-1980203008,-2294611968,24593629184,-58246496256,53880029184,-13056245760,63486197760,-187966128128,142317486080]),(⟨0,1,4⟩,[-32768,983040,-10649600,46465024,-9830400,-598867968,1726676992,-27131904,-5978750976,3350396928,8979972096,4928897024,-22608674816]),(⟨0,1,5⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨0,2,0⟩,[32768,-786432,5799936,7471104,-377028608,2563637248,-8043298816,7274168320,35418963968,-142975172608,218599424000,-136156282880,138419765248,-594032852992,959512576000,-514576154624]),(⟨0,2,1⟩,[32768,-1245184,18317312,-130940928,411369472,319553536,-7258767360,25591021568,-41970401280,34899296256,-45839056896,119981080576,-83654606848,-174199537664,229815943168]),(⟨0,2,2⟩,[-32768,524288,1081344,-78446592,718340096,-3122200576,6857752576,-5133959168,-6398836736,8628076544,8182464512,2983133184,-36053319680,18583584768]),(⟨0,2,3⟩,[-32768,1245184,-17006592,103546880,-216793088,-662568960,4701093888,-9533390848,5696094208,-1184694272,19069304832,-24795152384,-3362193408]),(⟨0,2,4⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨0,3,0⟩,[65536,-2359296,33226752,-224985088,578420736,1996619776,-21625896960,79924166656,-155767472128,153103368192,-76408881152,180677443584,-470206382080,408354160640,-48355016704]),(⟨0,3,1⟩,[0,-524288,14221312,-150142976,747962368,-1310392320,-3958243328,25214713856,-49376264192,30773215232,-3375038464,104080146432,-238358560768,148583809024]),(⟨0,3,2⟩,[-65536,1966080,-22347776,112328704,-133955584,-1136918528,5548408832,-9437970432,3659988992,1082523648,16067264512,-17163485184,-10388897792]),(⟨0,3,3⟩,[0,262144,-5832704,41222144,-43253760,-831782912,4460773376,-8841199616,4707844096,1644691456,15962406912,-27832549376]),(⟨0,4,0⟩,[-32768,458752,2818048,-86605824,587628544,-1171619840,-4894097408,34262810624,-82112643072,83628916736,-30324097024,104584478720,-305458216960,241245519872]),(⟨0,4,1⟩,[-32768,983040,-10649600,46465024,-10354688,-586285056,1636499456,-22937600,-3507257344,-5721882624,12765331456,34452602880,-59980447744]),(⟨0,4,2⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨0,5,0⟩,[-32768,1245184,-15958016,76283904,66846720,-2197684224,9298051072,-16542072832,8438120448,2246246400,25665896448,-43612897280,2080440320]),(⟨0,5,1⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨0,6,0⟩,[0,262144,-5832704,41222144,-43253760,-831782912,4460773376,-8841199616,4707844096,1644691456,15962406912,-27832549376]),(⟨1,0,0⟩,[-32768,1179648,-18087936,152862720,-738426880,1536983040,4381933568,-45844267008,174183972864,-388122869760,531614269440,-470681354240,520003223552,-1091877568512,1571203514368,-1023117688832,170077716480]),(⟨1,0,1⟩,[0,327680,-10125312,130056192,-892174336,3309993984,-4141481984,-19327352832,110746468352,-257808269312,309883404288,-211752812544,351519145984,-948386496512,1188933599232,-552269053952]),(⟨1,0,2⟩,[65536,-2162688,28737536,-192380928,603226112,122978304,-8152219648,30115430400,-49811947520,29277290496,3780411392,50903810048,-117810102272,1695842304,98632597504]),(⟨1,0,3⟩,[0,-589824,15958016,-170885120,896696320,-1980203008,-2294611968,24593629184,-58246496256,53880029184,-13056245760,63486197760,-187966128128,142317486080]),(⟨1,0,4⟩,[-32768,983040,-10649600,46465024,-9830400,-598867968,1726676992,-27131904,-5978750976,3350396928,8979972096,4928897024,-22608674816]),(⟨1,0,5⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨1,1,0⟩,[0,524288,-16056320,202702848,-1343815680,4561764352,-2556297216,-45880442880,214506536960,-477081239552,578057338880,-432493756416,698211303424,-1755767963648,2215570571264,-1073280581632]),(⟨1,1,1⟩,[0,0,-2359296,61734912,-656801792,3623223296,-10453385216,10907025408,17743216640,-44965298176,-37051957248,122586267648,217702334464,-791151771648,610442018816]),(⟨1,1,2⟩,[0,-524288,14221312,-156434432,887947264,-2629500928,2861694976,4597612544,-15118237696,9552134144,-6441074688,38527369216,-33643495424,-13484097536]),(⟨1,1,3⟩,[0,0,1048576,-23330816,197394432,-760217600,930086912,2206728192,-6120013824,-3364880384,13436452864,17578065920,-36966236160]),(⟨1,2,0⟩,[65536,-2359296,33488896,-233766912,719323136,656670720,-13632995328,49929912320,-88393580544,76986449920,-58890846208,152127995904,-180873986048,-103237025792,240509452288]),(⟨1,2,1⟩,[0,-524288,14221312,-156434432,887422976,-2617966592,2788294656,4530503680,-12713852928,1371144192,-3041591296,64204898304,-69371101184,-7369850880]),(⟨1,2,2⟩,[-65536,1966080,-23396352,139591680,-417595392,398196736,951451648,-2429288448,917962752,-2348417024,9470672896,1654259712,-15831531520]),(⟨1,2,3⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨1,3,0⟩,[0,-786432,21102592,-219414528,1061093376,-1561395200,-8006402048,45916356608,-95595921408,79594651648,-26641301504,157215621120,-384204603392,268928221184]),(⟨1,3,1⟩,[0,0,1048576,-23330816,196870144,-747634688,839909376,2210922496,-3648520192,-12437159936,17221812224,47101771776,-74338009088]),(⟨1,3,2⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨1,4,0⟩,[-32768,983040,-10649600,46465024,-10354688,-586285056,1636499456,-22937600,-3507257344,-5721882624,12765331456,34452602880,-59980447744]),(⟨1,5,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨2,0,0⟩,[32768,-786432,5799936,7471104,-377028608,2563637248,-8043298816,7274168320,35418963968,-142975172608,218599424000,-136156282880,138419765248,-594032852992,959512576000,-514576154624]),(⟨2,0,1⟩,[32768,-1245184,18317312,-130940928,411369472,319553536,-7258767360,25591021568,-41970401280,34899296256,-45839056896,119981080576,-83654606848,-174199537664,229815943168]),(⟨2,0,2⟩,[-32768,524288,1081344,-78446592,718340096,-3122200576,6857752576,-5133959168,-6398836736,8628076544,8182464512,2983133184,-36053319680,18583584768]),(⟨2,0,3⟩,[-32768,1245184,-17006592,103546880,-216793088,-662568960,4701093888,-9533390848,5696094208,-1184694272,19069304832,-24795152384,-3362193408]),(⟨2,0,4⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨2,1,0⟩,[65536,-2359296,33488896,-233766912,719323136,656670720,-13632995328,49929912320,-88393580544,76986449920,-58890846208,152127995904,-180873986048,-103237025792,240509452288]),(⟨2,1,1⟩,[0,-524288,14221312,-156434432,887422976,-2617966592,2788294656,4530503680,-12713852928,1371144192,-3041591296,64204898304,-69371101184,-7369850880]),(⟨2,1,2⟩,[-65536,1966080,-23396352,139591680,-417595392,398196736,951451648,-2429288448,917962752,-2348417024,9470672896,1654259712,-15831531520]),(⟨2,1,3⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨2,2,0⟩,[-65536,1441792,-8126464,-47251456,827916288,-4450091008,11650203648,-12962627584,-2538012672,9539944448,18109169664,-13619757056,-35154624512,18988204032]),(⟨2,2,1⟩,[-65536,1966080,-23396352,139591680,-417595392,398196736,951451648,-2429288448,917962752,-2348417024,9470672896,1654259712,-15831531520]),(⟨2,3,0⟩,[-65536,2228224,-27656192,146079744,-141950976,-1998585856,9773776896,-17756717056,8897101824,1072037888,30401232896,-42785767424,-5835325440]),(⟨2,3,1⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨2,3,2⟩,[-131072,3670016,-37486592,147849216,123994112,-3093299200,10100932608,-8741978112,-21715091456,57703661568,-40397701120]),(⟨2,3,3⟩,[0,524288,-12582912,106954752,-339738624,-105906176,2629828608,-3063939072,-4492099584,7424442368]),(⟨2,3,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,4,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨2,4,2⟩,[131072,-2883584,18350080,16777216,-601096192,2045247488,-849870848,-6419382272,8931901440,-1528561664]),(⟨2,4,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,5,2⟩,[131072,-3145728,22544384,-1048576,-617873408,2268069888,-946339840,-7380926464,9342943232]),(⟨3,0,0⟩,[65536,-2359296,33226752,-224985088,578420736,1996619776,-21625896960,79924166656,-155767472128,153103368192,-76408881152,180677443584,-470206382080,408354160640,-48355016704]),(⟨3,0,1⟩,[0,-524288,14221312,-150142976,747962368,-1310392320,-3958243328,25214713856,-49376264192,30773215232,-3375038464,104080146432,-238358560768,148583809024]),(⟨3,0,2⟩,[-65536,1966080,-22347776,112328704,-133955584,-1136918528,5548408832,-9437970432,3659988992,1082523648,16067264512,-17163485184,-10388897792]),(⟨3,0,3⟩,[0,262144,-5832704,41222144,-43253760,-831782912,4460773376,-8841199616,4707844096,1644691456,15962406912,-27832549376]),(⟨3,1,0⟩,[0,-786432,21102592,-219414528,1061093376,-1561395200,-8006402048,45916356608,-95595921408,79594651648,-26641301504,157215621120,-384204603392,268928221184]),(⟨3,1,1⟩,[0,0,1048576,-23330816,196870144,-747634688,839909376,2210922496,-3648520192,-12437159936,17221812224,47101771776,-74338009088]),(⟨3,1,2⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨3,2,0⟩,[-65536,2228224,-27656192,146079744,-141950976,-1998585856,9773776896,-17756717056,8897101824,1072037888,30401232896,-42785767424,-5835325440]),(⟨3,2,1⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨3,2,2⟩,[-131072,3670016,-37486592,147849216,123994112,-3093299200,10100932608,-8741978112,-21715091456,57703661568,-40397701120]),(⟨3,2,3⟩,[0,524288,-12582912,106954752,-339738624,-105906176,2629828608,-3063939072,-4492099584,7424442368]),(⟨3,2,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,3,0⟩,[0,524288,-11665408,82444288,-86507520,-1663565824,8921546752,-17682399232,9415688192,3289382912,31924813824,-55665098752]),(⟨3,3,2⟩,[0,524288,-12582912,106954752,-339738624,-105906176,2629828608,-3063939072,-4492099584,7424442368]),(⟨3,4,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,0,0⟩,[-32768,458752,2818048,-86605824,587628544,-1171619840,-4894097408,34262810624,-82112643072,83628916736,-30324097024,104584478720,-305458216960,241245519872]),(⟨4,0,1⟩,[-32768,983040,-10649600,46465024,-10354688,-586285056,1636499456,-22937600,-3507257344,-5721882624,12765331456,34452602880,-59980447744]),(⟨4,0,2⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨4,1,0⟩,[-32768,983040,-10649600,46465024,-10354688,-586285056,1636499456,-22937600,-3507257344,-5721882624,12765331456,34452602880,-59980447744]),(⟨4,2,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨4,2,2⟩,[131072,-2883584,18350080,16777216,-601096192,2045247488,-849870848,-6419382272,8931901440,-1528561664]),(⟨4,2,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,3,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨5,0,0⟩,[-32768,1245184,-15958016,76283904,66846720,-2197684224,9298051072,-16542072832,8438120448,2246246400,25665896448,-43612897280,2080440320]),(⟨5,0,1⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨5,1,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨5,2,2⟩,[131072,-3145728,22544384,-1048576,-617873408,2268069888,-946339840,-7380926464,9342943232]),(⟨6,0,0⟩,[0,262144,-5832704,41222144,-43253760,-831782912,4460773376,-8841199616,4707844096,1644691456,15962406912,-27832549376])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[-32768,1114112,-15990784,121012224,-431652864,-551714816,14910881792,-85772468224,287783682048,-626602541056,893201416192,-877498302464,963703767040,-1761938669568,2544277258240,-1913696616448,583742521344,-59888369664]),(⟨0,0,1⟩,[-32768,1376256,-23625728,215220224,-1061552128,1771044864,11608129536,-94992728064,343303487488,-741602689024,992760004608,-902840975360,1134292303872,-2367397691392,3253749612544,-2069219377152,353538146304]),(⟨0,0,2⟩,[65536,-1835008,19005440,-68812800,-288882688,4150394880,-19460915200,45908951040,-38261161984,-68544102400,182484860928,-81021370368,-7447379968,-467567509504,948576059392,-518341591040]),(⟨0,0,3⟩,[65536,-2621440,39583744,-282591232,767164416,2585001984,-29566894080,113114087424,-228741283840,237948108800,-131066363904,271435956224,-691935379456,617840115712,-90731118592]),(⟨0,0,4⟩,[-32768,458752,2818048,-86605824,587628544,-1171619840,-4894097408,34262810624,-82112643072,83628916736,-30324097024,104584478720,-305458216960,241245519872]),(⟨0,0,5⟩,[-32768,1245184,-15958016,76283904,66846720,-2197684224,9298051072,-16542072832,8438120448,2246246400,25665896448,-43612897280,2080440320]),(⟨0,0,6⟩,[0,262144,-5832704,41222144,-43253760,-831782912,4460773376,-8841199616,4707844096,1644691456,15962406912,-27832549376]),(⟨0,1,0⟩,[-32768,1376256,-23625728,215220224,-1061552128,1771044864,11608129536,-94992728064,343303487488,-741602689024,992760004608,-902840975360,1134292303872,-2367397691392,3253749612544,-2069219377152,353538146304]),(⟨0,1,1⟩,[0,524288,-16056320,202702848,-1343291392,4548132864,-2431516672,-46207598592,212349616128,-457932144640,521060941824,-382740922368,820454817792,-2104919654400,2509172899840,-1130180509696]),(⟨0,1,2⟩,[65536,-2359296,33488896,-233766912,719323136,656670720,-13632995328,49929912320,-88393580544,76986449920,-58890846208,152127995904,-180873986048,-103237025792,240509452288]),(⟨0,1,3⟩,[0,-786432,21102592,-219414528,1061093376,-1561395200,-8006402048,45916356608,-95595921408,79594651648,-26641301504,157215621120,-384204603392,268928221184]),(⟨0,1,4⟩,[-32768,983040,-10649600,46465024,-10354688,-586285056,1636499456,-22937600,-3507257344,-5721882624,12765331456,34452602880,-59980447744]),(⟨0,1,5⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨0,2,0⟩,[65536,-1835008,19005440,-68812800,-288882688,4150394880,-19460915200,45908951040,-38261161984,-68544102400,182484860928,-81021370368,-7447379968,-467567509504,948576059392,-518341591040]),(⟨0,2,1⟩,[65536,-2359296,33488896,-233766912,719323136,656670720,-13632995328,49929912320,-88393580544,76986449920,-58890846208,152127995904,-180873986048,-103237025792,240509452288]),(⟨0,2,2⟩,[-65536,1441792,-8126464,-47251456,827916288,-4450091008,11650203648,-12962627584,-2538012672,9539944448,18109169664,-13619757056,-35154624512,18988204032]),(⟨0,2,3⟩,[-65536,2228224,-27656192,146079744,-141950976,-1998585856,9773776896,-17756717056,8897101824,1072037888,30401232896,-42785767424,-5835325440]),(⟨0,2,4⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨0,3,0⟩,[65536,-2621440,39583744,-282591232,767164416,2585001984,-29566894080,113114087424,-228741283840,237948108800,-131066363904,271435956224,-691935379456,617840115712,-90731118592]),(⟨0,3,1⟩,[0,-786432,21102592,-219414528,1061093376,-1561395200,-8006402048,45916356608,-95595921408,79594651648,-26641301504,157215621120,-384204603392,268928221184]),(⟨0,3,2⟩,[-65536,2228224,-27656192,146079744,-141950976,-1998585856,9773776896,-17756717056,8897101824,1072037888,30401232896,-42785767424,-5835325440]),(⟨0,3,3⟩,[0,524288,-11665408,82444288,-86507520,-1663565824,8921546752,-17682399232,9415688192,3289382912,31924813824,-55665098752]),(⟨0,4,0⟩,[-32768,458752,2818048,-86605824,587628544,-1171619840,-4894097408,34262810624,-82112643072,83628916736,-30324097024,104584478720,-305458216960,241245519872]),(⟨0,4,1⟩,[-32768,983040,-10649600,46465024,-10354688,-586285056,1636499456,-22937600,-3507257344,-5721882624,12765331456,34452602880,-59980447744]),(⟨0,4,2⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨0,5,0⟩,[-32768,1245184,-15958016,76283904,66846720,-2197684224,9298051072,-16542072832,8438120448,2246246400,25665896448,-43612897280,2080440320]),(⟨0,5,1⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨0,6,0⟩,[0,262144,-5832704,41222144,-43253760,-831782912,4460773376,-8841199616,4707844096,1644691456,15962406912,-27832549376]),(⟨1,0,0⟩,[-32768,1376256,-23625728,215220224,-1061552128,1771044864,11608129536,-94992728064,343303487488,-741602689024,992760004608,-902840975360,1134292303872,-2367397691392,3253749612544,-2069219377152,353538146304]),(⟨1,0,1⟩,[0,524288,-16056320,202702848,-1343291392,4548132864,-2431516672,-46207598592,212349616128,-457932144640,521060941824,-382740922368,820454817792,-2104919654400,2509172899840,-1130180509696]),(⟨1,0,2⟩,[65536,-2359296,33488896,-233766912,719323136,656670720,-13632995328,49929912320,-88393580544,76986449920,-58890846208,152127995904,-180873986048,-103237025792,240509452288]),(⟨1,0,3⟩,[0,-786432,21102592,-219414528,1061093376,-1561395200,-8006402048,45916356608,-95595921408,79594651648,-26641301504,157215621120,-384204603392,268928221184]),(⟨1,0,4⟩,[-32768,983040,-10649600,46465024,-10354688,-586285056,1636499456,-22937600,-3507257344,-5721882624,12765331456,34452602880,-59980447744]),(⟨1,0,5⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨1,1,0⟩,[0,524288,-16056320,202702848,-1343291392,4548132864,-2431516672,-46207598592,212349616128,-457932144640,521060941824,-382740922368,820454817792,-2104919654400,2509172899840,-1130180509696]),(⟨1,1,1⟩,[0,0,-2359296,61734912,-656277504,3608543232,-10303438848,10315628544,17247240192,-32592101376,-77455687680,157554180096,304562700288,-1021966417920,772032823296]),(⟨1,1,2⟩,[0,-524288,14221312,-156434432,887422976,-2617966592,2788294656,4530503680,-12713852928,1371144192,-3041591296,64204898304,-69371101184,-7369850880]),(⟨1,1,3⟩,[0,0,1048576,-23330816,196870144,-747634688,839909376,2210922496,-3648520192,-12437159936,17221812224,47101771776,-74338009088]),(⟨1,2,0⟩,[65536,-2359296,33488896,-233766912,719323136,656670720,-13632995328,49929912320,-88393580544,76986449920,-58890846208,152127995904,-180873986048,-103237025792,240509452288]),(⟨1,2,1⟩,[0,-524288,14221312,-156434432,887422976,-2617966592,2788294656,4530503680,-12713852928,1371144192,-3041591296,64204898304,-69371101184,-7369850880]),(⟨1,2,2⟩,[-65536,1966080,-23396352,139591680,-417595392,398196736,951451648,-2429288448,917962752,-2348417024,9470672896,1654259712,-15831531520]),(⟨1,2,3⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨1,3,0⟩,[0,-786432,21102592,-219414528,1061093376,-1561395200,-8006402048,45916356608,-95595921408,79594651648,-26641301504,157215621120,-384204603392,268928221184]),(⟨1,3,1⟩,[0,0,1048576,-23330816,196870144,-747634688,839909376,2210922496,-3648520192,-12437159936,17221812224,47101771776,-74338009088]),(⟨1,3,2⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨1,4,0⟩,[-32768,983040,-10649600,46465024,-10354688,-586285056,1636499456,-22937600,-3507257344,-5721882624,12765331456,34452602880,-59980447744]),(⟨1,5,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨2,0,0⟩,[65536,-1835008,19005440,-68812800,-288882688,4150394880,-19460915200,45908951040,-38261161984,-68544102400,182484860928,-81021370368,-7447379968,-467567509504,948576059392,-518341591040]),(⟨2,0,1⟩,[65536,-2359296,33488896,-233766912,719323136,656670720,-13632995328,49929912320,-88393580544,76986449920,-58890846208,152127995904,-180873986048,-103237025792,240509452288]),(⟨2,0,2⟩,[-65536,1441792,-8126464,-47251456,827916288,-4450091008,11650203648,-12962627584,-2538012672,9539944448,18109169664,-13619757056,-35154624512,18988204032]),(⟨2,0,3⟩,[-65536,2228224,-27656192,146079744,-141950976,-1998585856,9773776896,-17756717056,8897101824,1072037888,30401232896,-42785767424,-5835325440]),(⟨2,0,4⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨2,1,0⟩,[65536,-2359296,33488896,-233766912,719323136,656670720,-13632995328,49929912320,-88393580544,76986449920,-58890846208,152127995904,-180873986048,-103237025792,240509452288]),(⟨2,1,1⟩,[0,-524288,14221312,-156434432,887422976,-2617966592,2788294656,4530503680,-12713852928,1371144192,-3041591296,64204898304,-69371101184,-7369850880]),(⟨2,1,2⟩,[-65536,1966080,-23396352,139591680,-417595392,398196736,951451648,-2429288448,917962752,-2348417024,9470672896,1654259712,-15831531520]),(⟨2,1,3⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨2,2,0⟩,[-65536,1441792,-8126464,-47251456,827916288,-4450091008,11650203648,-12962627584,-2538012672,9539944448,18109169664,-13619757056,-35154624512,18988204032]),(⟨2,2,1⟩,[-65536,1966080,-23396352,139591680,-417595392,398196736,951451648,-2429288448,917962752,-2348417024,9470672896,1654259712,-15831531520]),(⟨2,2,2⟩,[-131072,3407872,-31195136,81788928,539230208,-4787273728,14249099264,-12438208512,-30560878592,87287922688,-73400582144,14224982016]),(⟨2,2,3⟩,[-131072,3670016,-37486592,147849216,123994112,-3093299200,10100932608,-8741978112,-21715091456,57703661568,-40397701120]),(⟨2,2,4⟩,[131072,-2883584,18350080,16777216,-601096192,2045247488,-849870848,-6419382272,8931901440,-1528561664]),(⟨2,2,5⟩,[131072,-3145728,22544384,-1048576,-617873408,2268069888,-946339840,-7380926464,9342943232]),(⟨2,3,0⟩,[-65536,2228224,-27656192,146079744,-141950976,-1998585856,9773776896,-17756717056,8897101824,1072037888,30401232896,-42785767424,-5835325440]),(⟨2,3,1⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨2,3,2⟩,[-131072,3670016,-37486592,147849216,123994112,-3093299200,10100932608,-8741978112,-21715091456,57703661568,-40397701120]),(⟨2,3,3⟩,[0,524288,-12582912,106954752,-339738624,-105906176,2629828608,-3063939072,-4492099584,7424442368]),(⟨2,3,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,4,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨2,4,2⟩,[131072,-2883584,18350080,16777216,-601096192,2045247488,-849870848,-6419382272,8931901440,-1528561664]),(⟨2,4,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,5,2⟩,[131072,-3145728,22544384,-1048576,-617873408,2268069888,-946339840,-7380926464,9342943232]),(⟨3,0,0⟩,[65536,-2621440,39583744,-282591232,767164416,2585001984,-29566894080,113114087424,-228741283840,237948108800,-131066363904,271435956224,-691935379456,617840115712,-90731118592]),(⟨3,0,1⟩,[0,-786432,21102592,-219414528,1061093376,-1561395200,-8006402048,45916356608,-95595921408,79594651648,-26641301504,157215621120,-384204603392,268928221184]),(⟨3,0,2⟩,[-65536,2228224,-27656192,146079744,-141950976,-1998585856,9773776896,-17756717056,8897101824,1072037888,30401232896,-42785767424,-5835325440]),(⟨3,0,3⟩,[0,524288,-11665408,82444288,-86507520,-1663565824,8921546752,-17682399232,9415688192,3289382912,31924813824,-55665098752]),(⟨3,1,0⟩,[0,-786432,21102592,-219414528,1061093376,-1561395200,-8006402048,45916356608,-95595921408,79594651648,-26641301504,157215621120,-384204603392,268928221184]),(⟨3,1,1⟩,[0,0,1048576,-23330816,196870144,-747634688,839909376,2210922496,-3648520192,-12437159936,17221812224,47101771776,-74338009088]),(⟨3,1,2⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨3,2,0⟩,[-65536,2228224,-27656192,146079744,-141950976,-1998585856,9773776896,-17756717056,8897101824,1072037888,30401232896,-42785767424,-5835325440]),(⟨3,2,1⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨3,2,2⟩,[-131072,3670016,-37486592,147849216,123994112,-3093299200,10100932608,-8741978112,-21715091456,57703661568,-40397701120]),(⟨3,2,3⟩,[0,524288,-12582912,106954752,-339738624,-105906176,2629828608,-3063939072,-4492099584,7424442368]),(⟨3,2,4⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,3,0⟩,[0,524288,-11665408,82444288,-86507520,-1663565824,8921546752,-17682399232,9415688192,3289382912,31924813824,-55665098752]),(⟨3,3,2⟩,[0,524288,-12582912,106954752,-339738624,-105906176,2629828608,-3063939072,-4492099584,7424442368]),(⟨3,4,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,0,0⟩,[-32768,458752,2818048,-86605824,587628544,-1171619840,-4894097408,34262810624,-82112643072,83628916736,-30324097024,104584478720,-305458216960,241245519872]),(⟨4,0,1⟩,[-32768,983040,-10649600,46465024,-10354688,-586285056,1636499456,-22937600,-3507257344,-5721882624,12765331456,34452602880,-59980447744]),(⟨4,0,2⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨4,1,0⟩,[-32768,983040,-10649600,46465024,-10354688,-586285056,1636499456,-22937600,-3507257344,-5721882624,12765331456,34452602880,-59980447744]),(⟨4,2,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨4,2,2⟩,[131072,-2883584,18350080,16777216,-601096192,2045247488,-849870848,-6419382272,8931901440,-1528561664]),(⟨4,2,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,3,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨5,0,0⟩,[-32768,1245184,-15958016,76283904,66846720,-2197684224,9298051072,-16542072832,8438120448,2246246400,25665896448,-43612897280,2080440320]),(⟨5,0,1⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨5,1,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨5,2,2⟩,[131072,-3145728,22544384,-1048576,-617873408,2268069888,-946339840,-7380926464,9342943232]),(⟨6,0,0⟩,[0,262144,-5832704,41222144,-43253760,-831782912,4460773376,-8841199616,4707844096,1644691456,15962406912,-27832549376])]


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
    (Poly.add (Poly.scale (K.ofRat r580) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 3 13).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r579*r579 : ℚ)=r580 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 3 13 r579 r579 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 3=13 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 3 13).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C094

#print axioms Coulomb8.Columns.C094.sound
