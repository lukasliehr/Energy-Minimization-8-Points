import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C088

def r0 : ℚ := { num := 32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -1064960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 13942784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -86949888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 143540224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 34996224, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -849281024, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 53150056448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -88094212096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -88815845376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 3124412416, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -2543734734848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 4187988443136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -4291241148416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 150185148416, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -721597431808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 10608967680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 49152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -1736704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 24854528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -177930240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 534052864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := 1294204928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := -18825248768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := 273219584, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := -151517609984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -45143851008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 1097797353472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -190000594944, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 5221774884864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -5001156820992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 359985250304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -8413184000, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -49152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 1212416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -9158656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -9437184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 531890176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := -456622080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := 6887964672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 10089922560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -97613692928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 244756873216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -31386386432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -301185630208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 1111527751680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -1290255695872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 79739650048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -98304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 3080192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -35848192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 167247872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 122585088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -4921229312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 22603759616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -5568724992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -45280690176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 55867408384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -135409500160, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 1217171554304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -770649128960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 18401853440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := 376832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := -1359872, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := 84852736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := -34357248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -136544256, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 8816132096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -192643072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 4176773120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 124401139712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -355216539648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := 66229649408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := -5141610496, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -1343488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 11780096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -17104896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := -297435136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := 1688272896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := -2462482432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -5944377344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 4506271744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -61828792320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 54696001536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -1180237824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -524288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 5521408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -2097152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -111902720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 837287936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -1592360960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -2337275904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := 2364719104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -1987051520, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := 3974676480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -1474560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := 25952256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := -230260736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 1023967232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -968294400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -13586989056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 78301691904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -190552113152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 112008593408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := 703584141312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := -2448129490944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 230656409600, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -478106222592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 25146097664, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := -81920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 2392064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -25772032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 107642880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := 17793024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := -426508288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := 11286577152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := -10988224512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -51516424192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 219022131200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -373696905216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 256674660352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := 13821607936, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := -4063559680, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := 1933312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := -28360704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := 188121088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := -410419200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := -1802567680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := 13840187392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -4736745472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 6177701888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := 3387129856, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := -65695531008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := 81203265536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := -5859508224, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -720896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 4292608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 163840, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -145686528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := 209977344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := 1799815168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := -8041332736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := 11418370048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 8440709120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -7552598016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 64913408, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 6045696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -4194304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 1867776, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := 243793920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := -998866944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := 1250951168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 1133723648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := -812646400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 6635520, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -425984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -3997696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 14712832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -699236352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 1771765760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 1198391296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -1032126464, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 43485593600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -46566506496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := -2043215872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := 7287767040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := -517242880, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := -1277952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := 10371072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := -10715136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -237010944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := 968687616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 234127360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -9329115136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := 1625276416, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := -45471072256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 35621257216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := 150568960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := -16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := 393216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -475136, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 7602176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := 62750720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := -529530880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := 1526366208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := -934543360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -4295049216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := 1248198656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -5488640, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 655360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := 4194304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := -150274048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := 511311872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -212467712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := -1604845568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := 318996480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := -458752, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -786432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := 5636096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := -262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -154468352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 81002496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := -236584960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := -1845231616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := 19628032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := 786432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := -7700480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := 2621440, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := -161808384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := 127926272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := 38076416, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := -9045540864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := 22248521728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -38707920896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 5063802880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := -589824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 1441792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := 30932992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := -235208704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 484835328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := 63569920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -19922944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 158564352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := 1769472, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -1572864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 12320768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := -21495808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := -161087488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := 731381760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := -428081152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := -2125987840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := 23527424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := 786432, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := -42467328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -13238272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := 328728576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := -382992384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := -4718592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -393216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := 12779520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -164560896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := 1052442624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := -3106996224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := -126222336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := 39907885056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := -141014728704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := 206391214080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := 62797578240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -15901851648, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := 25718882304, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := -887685120, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 1343488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -20447232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := 144539648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -59670528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := -442171392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := 6614941696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := -18658164736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := 16945020928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := 33318404096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := -109452984320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := 13657473024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -10649600, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := 262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := -7208960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := 73007104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := -2621440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := 228589568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := 2839281664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -11165499392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 15209070592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := 12015370240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := -9929097216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := 81395712, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := -28114944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := -148766720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := 954466304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := -14548992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := -32374784, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := 7452033024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -10928521216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := -207028224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := 13828096, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := 131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := -3145728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := 1572864, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := -84934656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -26476544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 657457152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -765984768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := -9437184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := 393216, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := -21233664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := -6619136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := 164364288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := -191496192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := -2359296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := -6291456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := 3145728, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -169869312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := -52953088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := 1314914304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -1531969536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := -18874368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -1441792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 1310720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := 8388608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := -300548096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := 1022623744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := -424935424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := -3209691136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 637992960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -917504, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := 24641536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := -42991616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := -322174976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := 1462763520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := -856162304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := -4251975680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := 47054848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := -532480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := 6971392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := -43474944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := 71770112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 17498112, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := -424640512, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := 26575028224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -44047106048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := -44407922688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := 1562206208, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := -1271867367424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := 2093994221568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := -2145620574208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := 75092574208, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := -360798715904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := 5304483840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := 24576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := -868352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := 12427264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := -88965120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := 267026432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := 647102464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := -9412624384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := 136609792, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := -75758804992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := -22571925504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := 548898676736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := -95000297472, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := 2610887442432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := -2500578410496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := 179992625152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := -4206592000, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := -24576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := 606208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -4579328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := -4718592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := 265945088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := -228311040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := 3443982336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := 5044961280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := -48806846464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := 122378436608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := -15693193216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := -150592815104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := 555763875840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := -645127847936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := 39869825024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := 1540096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := -17924096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := 83623936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := 61292544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := -2460614656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := 11301879808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := -2784362496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := -22640345088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := 27933704192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := -67704750080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := 608585777152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := -385324564480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := 9200926720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := 188416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := -679936, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := 42426368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := -17178624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := -68272128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := 4408066048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := -96321536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := 2088386560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := 62200569856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := -177608269824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 33114824704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := -2570805248, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := -671744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := 5890048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := -8552448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := -148717568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := 844136448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := -1231241216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := -2972188672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := 2253135872, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := -30914396160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := 27348000768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := -590118912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := 8192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := 2760704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := -1048576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := -55951360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := 418643968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := -796180480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := -1168637952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := 1182359552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := -993525760, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := 1987338240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := -737280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := 12976128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := -115130368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := 511983616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := -484147200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := -6793494528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := 39150845952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := -95276056576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := 56004296704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := 351792070656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := -1224064745472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := 115328204800, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := -239053111296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := 12573048832, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := -40960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := 1196032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := -12886016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := 53821440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := 8896512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := -213254144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := 5643288576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := -5494112256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := -25758212096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := 109511065600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := -186848452608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := 128337330176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := 6910803968, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := -2031779840, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := 966656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := -14180352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := 94060544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := -205209600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := -901283840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := 6920093696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r450 : ℚ := { num := -2368372736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r451 : ℚ := { num := 3088850944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r452 : ℚ := { num := 1693564928, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r453 : ℚ := { num := -32847765504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r454 : ℚ := { num := 40601632768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r455 : ℚ := { num := -2929754112, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r456 : ℚ := { num := -360448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r457 : ℚ := { num := 2146304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r458 : ℚ := { num := 81920, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r459 : ℚ := { num := -72843264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r460 : ℚ := { num := 104988672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r461 : ℚ := { num := 899907584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r462 : ℚ := { num := -4020666368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r463 : ℚ := { num := 5709185024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r464 : ℚ := { num := 4220354560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r465 : ℚ := { num := -3776299008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r466 : ℚ := { num := 32456704, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r467 : ℚ := { num := 3022848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r468 : ℚ := { num := 933888, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r469 : ℚ := { num := 121896960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r470 : ℚ := { num := -499433472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r471 : ℚ := { num := 625475584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r472 : ℚ := { num := 566861824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r473 : ℚ := { num := -406323200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r474 : ℚ := { num := 3317760, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r475 : ℚ := { num := -212992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r476 : ℚ := { num := -1998848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r477 : ℚ := { num := 7356416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r478 : ℚ := { num := -349618176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r479 : ℚ := { num := 885882880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r480 : ℚ := { num := 599195648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r481 : ℚ := { num := -516063232, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r482 : ℚ := { num := 21742796800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r483 : ℚ := { num := -23283253248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r484 : ℚ := { num := -1021607936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r485 : ℚ := { num := 3643883520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r486 : ℚ := { num := -258621440, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r487 : ℚ := { num := -638976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r488 : ℚ := { num := 5185536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r489 : ℚ := { num := -5357568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r490 : ℚ := { num := -118505472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r491 : ℚ := { num := 484343808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r492 : ℚ := { num := 117063680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r493 : ℚ := { num := -4664557568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r494 : ℚ := { num := 812638208, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r495 : ℚ := { num := -22735536128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r496 : ℚ := { num := 17810628608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r497 : ℚ := { num := 75284480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r498 : ℚ := { num := -8192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r499 : ℚ := { num := 196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r500 : ℚ := { num := -237568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r501 : ℚ := { num := 3801088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r502 : ℚ := { num := 31375360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r503 : ℚ := { num := -264765440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r504 : ℚ := { num := 763183104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r505 : ℚ := { num := -467271680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r506 : ℚ := { num := -2147524608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r507 : ℚ := { num := 624099328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r508 : ℚ := { num := -2744320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r509 : ℚ := { num := 327680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r510 : ℚ := { num := 2097152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r511 : ℚ := { num := -75137024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r512 : ℚ := { num := 255655936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r513 : ℚ := { num := -106233856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r514 : ℚ := { num := -802422784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r515 : ℚ := { num := 159498240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r516 : ℚ := { num := -229376, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r517 : ℚ := { num := 2818048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r518 : ℚ := { num := -131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r519 : ℚ := { num := -77234176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r520 : ℚ := { num := 40501248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r521 : ℚ := { num := -118292480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r522 : ℚ := { num := -922615808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r523 : ℚ := { num := 9814016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r524 : ℚ := { num := -3850240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r525 : ℚ := { num := 1310720, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r526 : ℚ := { num := -80904192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r527 : ℚ := { num := 63963136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r528 : ℚ := { num := 19038208, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r529 : ℚ := { num := -4522770432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r530 : ℚ := { num := 11124260864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r531 : ℚ := { num := -19353960448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r532 : ℚ := { num := 2531901440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r533 : ℚ := { num := -294912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r534 : ℚ := { num := 720896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r535 : ℚ := { num := 15466496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r536 : ℚ := { num := -117604352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r537 : ℚ := { num := 242417664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r538 : ℚ := { num := 31784960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r539 : ℚ := { num := -9961472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r540 : ℚ := { num := 79282176, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r541 : ℚ := { num := 884736, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r542 : ℚ := { num := 6160384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r543 : ℚ := { num := -10747904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r544 : ℚ := { num := -80543744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r545 : ℚ := { num := 365690880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r546 : ℚ := { num := -214040576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r547 : ℚ := { num := -1062993920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r548 : ℚ := { num := 11763712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r549 : ℚ := { num := -196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r550 : ℚ := { num := 6389760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r551 : ℚ := { num := -82280448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r552 : ℚ := { num := 526221312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r553 : ℚ := { num := -1553498112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r554 : ℚ := { num := -63111168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r555 : ℚ := { num := 19953942528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r556 : ℚ := { num := -70507364352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r557 : ℚ := { num := 103195607040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r558 : ℚ := { num := 31398789120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r559 : ℚ := { num := -7950925824, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r560 : ℚ := { num := 12859441152, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r561 : ℚ := { num := -443842560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r562 : ℚ := { num := 671744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r563 : ℚ := { num := -10223616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r564 : ℚ := { num := 72269824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r565 : ℚ := { num := -29835264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r566 : ℚ := { num := -221085696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r567 : ℚ := { num := 3307470848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r568 : ℚ := { num := -9329082368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r569 : ℚ := { num := 8472510464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r570 : ℚ := { num := 16659202048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r571 : ℚ := { num := -54726492160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r572 : ℚ := { num := 6828736512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r573 : ℚ := { num := -5324800, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r574 : ℚ := { num := -3604480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r575 : ℚ := { num := 36503552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r576 : ℚ := { num := -1310720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r577 : ℚ := { num := 114294784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r578 : ℚ := { num := 1419640832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r579 : ℚ := { num := -5582749696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r580 : ℚ := { num := 7604535296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r581 : ℚ := { num := 6007685120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r582 : ℚ := { num := -4964548608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r583 : ℚ := { num := 40697856, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r584 : ℚ := { num := -14057472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r585 : ℚ := { num := -74383360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r586 : ℚ := { num := 477233152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r587 : ℚ := { num := -7274496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r588 : ℚ := { num := -16187392, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r589 : ℚ := { num := 3726016512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r590 : ℚ := { num := -5464260608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r591 : ℚ := { num := -103514112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r592 : ℚ := { num := 6914048, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r593 : ℚ := { num := 196608, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r594 : ℚ := { num := -10616832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r595 : ℚ := { num := -3309568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r596 : ℚ := { num := 82182144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r597 : ℚ := { num := -95748096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r598 : ℚ := { num := -1179648, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r599 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r600 : ℚ := { num := 1, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16],[r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32],[r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47],[r48,r49,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61],[0,r62,r63,r64,r65,r66,r67,r68,r69,r70,r71,r72,r73],[r17,r74,r75,r76,r77,r78,r79,r80,r81,r82,r83,r84],[r85,r86,r87,r88,r89,r90,r91,r92,r93,r94,r95],[],[],[],[],[],[],[r0,r96,r97,r98,r99,r100,r101,r102,r103,r104,r105,r106,r107,r108,r109],[r110,r111,r112,r113,r114,r115,r116,r117,r118,r119,r120,r121,r122,r123],[r33,r124,r125,r126,r127,r128,r129,r130,r131,r132,r133,r134,r135],[r0,r136,r137,r138,r139,r140,r141,r142,r143,r144,r145,r146],[r85,r86,r147,r148,r149,r150,r151,r152,r153,r154,r155],[],[],[],[],[],[],[r0,r156,r157,r158,r159,r160,r161,r162,r163,r164,r165,r166,r167],[r17,r168,r169,r170,r171,r172,r173,r174,r175,r176,r177,r178],[r179,r180,r181,r182,r183,r184,r185,r186,r187,r188,r189],[r0,r136,r190,r191,r192,r193,r194,r195,r196,r197],[r0,r198,r199,r200,r201,r202,r203,r204,r205],[],[],[],[],[r206,r207,r208,r209,r210,r211,r212,r213,r214,r215,r216],[r0,r217,r218,r219,r220,r221,r222,r223,r224,r225],[r226,r227,r228,r229,r230,r231,r232,r233,r234],[],[],[],[],[r226,r227,r235,r236,r237,r238,r239,r240,65536],[],[],[],[],[],[],[],[],[0,r241,r242,r243,r244,r245,r246,r247,r248,r249,r250,r251,r252,r253],[r206,r254,r255,r256,r257,r258,r259,r260,r261,r262,r263,r264,r265],[0,r266,r267,r268,r269,r270,r271,r272,r273,r274,r275,r276],[],[],[],[],[],[],[],[r226,r227,r242,r277,r278,r279,r280,r281,r282,r283,r284,r285],[r179,r180,r181,r182,r183,r184,r185,r186,r187,r188,r189],[0,r286,r287,r288,r289,r290,r291,r292,r293,131072],[r0,r198,r294,r295,r296,r297,r298,r299,32768],[],[],[],[],[0,r266,r300,r301,r302,r303,r304,r305,r306,262144],[r0,r198,r294,r295,r296,r297,r298,r299,32768],[],[],[],[],[],[],[],[],[],[],[],[r226,r307,r308,r309,r310,r311,r312,r313,r314,r315],[r226,r227,r235,r236,r237,r238,r239,r240,65536],[],[],[],[],[r286,r287,r316,r317,r318,r319,r320,r321,r322],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[r85,r323,r324,r325,r326,r327,r328,r329,r330,r331,r332,r333,r334,r335,r336,r337,r338]),(⟨0,0,1⟩,[r339,r340,r341,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351,r352,r353,r354]),(⟨0,0,2⟩,[r355,r356,r357,r358,r359,r360,r361,r362,r363,r364,r365,r366,r367,r368,r369]),(⟨0,0,3⟩,[r33,r370,r371,r372,r373,r374,r375,r376,r377,r378,r379,r380,r381,r382]),(⟨0,0,4⟩,[0,r383,r384,r385,r386,r387,r388,r389,r390,r391,r392,r393,r394]),(⟨0,0,5⟩,[r339,r395,r396,r397,r398,r399,r400,r401,r402,r403,r404,r405]),(⟨0,0,6⟩,[r406,r200,r407,r408,r409,r410,r411,r412,r413,r414,r415]),(⟨0,1,0⟩,[r339,r340,r341,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351,r352,r353,r354]),(⟨0,1,1⟩,[r85,r416,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427,r428,r429]),(⟨0,1,2⟩,[r430,r431,r432,r433,r434,r435,r436,r437,r438,r439,r440,r441,r442,r443]),(⟨0,1,3⟩,[r355,r444,r445,r446,r447,r448,r449,r450,r451,r452,r453,r454,r455]),(⟨0,1,4⟩,[r85,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466]),(⟨0,1,5⟩,[r406,r200,r467,r88,r468,r469,r470,r471,r472,r473,r474]),(⟨0,2,0⟩,[r355,r356,r357,r358,r359,r360,r361,r362,r363,r364,r365,r366,r367,r368,r369]),(⟨0,2,1⟩,[r430,r431,r432,r433,r434,r435,r436,r437,r438,r439,r440,r441,r442,r443]),(⟨0,2,2⟩,[r85,r475,r476,r477,r478,r479,r480,r481,r482,r483,r484,r485,r486]),(⟨0,2,3⟩,[r339,r487,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497]),(⟨0,2,4⟩,[r498,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508]),(⟨0,2,5⟩,[r85,r456,r509,r510,r511,r512,r513,r514,r515,r516]),(⟨0,2,6⟩,[r85,r241,r517,r518,r519,r520,r521,r522,r523]),(⟨0,3,0⟩,[r33,r370,r371,r372,r373,r374,r375,r376,r377,r378,r379,r380,r381,r382]),(⟨0,3,1⟩,[r355,r444,r445,r446,r447,r448,r449,r450,r451,r452,r453,r454,r455]),(⟨0,3,2⟩,[r339,r487,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497]),(⟨0,3,3⟩,[r179,r180,r524,r525,r526,r527,r528,r529,r530,r531,r532]),(⟨0,3,4⟩,[r85,r533,r534,r535,r536,r537,r538,r539,r540,r541]),(⟨0,3,5⟩,[r0,r198,r542,r543,r544,r545,r546,r547,r548]),(⟨0,4,0⟩,[0,r383,r384,r385,r386,r387,r388,r389,r390,r391,r392,r393,r394]),(⟨0,4,1⟩,[r85,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466]),(⟨0,4,2⟩,[r498,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508]),(⟨0,4,3⟩,[r85,r533,r534,r535,r536,r537,r538,r539,r540,r541]),(⟨0,4,4⟩,[r0,r198,r294,r295,r296,r297,r298,r299,32768]),(⟨0,5,0⟩,[r339,r395,r396,r397,r398,r399,r400,r401,r402,r403,r404,r405]),(⟨0,5,1⟩,[r406,r200,r467,r88,r468,r469,r470,r471,r472,r473,r474]),(⟨0,5,2⟩,[r85,r456,r509,r510,r511,r512,r513,r514,r515,r516]),(⟨0,5,3⟩,[r0,r198,r542,r543,r544,r545,r546,r547,r548]),(⟨0,6,0⟩,[r406,r200,r407,r408,r409,r410,r411,r412,r413,r414,r415]),(⟨0,6,2⟩,[r85,r241,r517,r518,r519,r520,r521,r522,r523]),(⟨1,0,0⟩,[r339,r340,r341,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351,r352,r353,r354]),(⟨1,0,1⟩,[r85,r416,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427,r428,r429]),(⟨1,0,2⟩,[r430,r431,r432,r433,r434,r435,r436,r437,r438,r439,r440,r441,r442,r443]),(⟨1,0,3⟩,[r355,r444,r445,r446,r447,r448,r449,r450,r451,r452,r453,r454,r455]),(⟨1,0,4⟩,[r85,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466]),(⟨1,0,5⟩,[r406,r200,r467,r88,r468,r469,r470,r471,r472,r473,r474]),(⟨1,1,0⟩,[r85,r416,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427,r428,r429]),(⟨1,1,1⟩,[0,r549,r550,r551,r552,r553,r554,r555,r556,r557,r558,r559,r560,r561]),(⟨1,1,2⟩,[r179,r562,r563,r564,r565,r566,r567,r568,r569,r570,r571,r572,r573]),(⟨1,1,3⟩,[0,r286,r574,r575,r576,r577,r578,r579,r580,r581,r582,r583]),(⟨1,2,0⟩,[r430,r431,r432,r433,r434,r435,r436,r437,r438,r439,r440,r441,r442,r443]),(⟨1,2,1⟩,[r179,r562,r563,r564,r565,r566,r567,r568,r569,r570,r571,r572,r573]),(⟨1,2,2⟩,[r0,r198,r550,r584,r585,r586,r587,r588,r589,r590,r591,r592]),(⟨1,2,3⟩,[r498,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508]),(⟨1,2,4⟩,[0,r226,r227,r235,r236,r237,r238,r239,r240,65536]),(⟨1,2,5⟩,[r85,r241,r593,r594,r595,r596,r597,r598,16384]),(⟨1,3,0⟩,[r355,r444,r445,r446,r447,r448,r449,r450,r451,r452,r453,r454,r455]),(⟨1,3,1⟩,[0,r286,r574,r575,r576,r577,r578,r579,r580,r581,r582,r583]),(⟨1,3,2⟩,[r498,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508]),(⟨1,3,3⟩,[0,r286,r287,r288,r289,r290,r291,r292,r293,131072]),(⟨1,3,4⟩,[r85,r241,r593,r594,r595,r596,r597,r598,16384]),(⟨1,4,0⟩,[r85,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466]),(⟨1,4,2⟩,[0,r226,r227,r235,r236,r237,r238,r239,r240,65536]),(⟨1,4,3⟩,[r85,r241,r593,r594,r595,r596,r597,r598,16384]),(⟨1,5,0⟩,[r406,r200,r467,r88,r468,r469,r470,r471,r472,r473,r474]),(⟨1,5,2⟩,[r85,r241,r593,r594,r595,r596,r597,r598,16384]),(⟨2,0,0⟩,[r355,r356,r357,r358,r359,r360,r361,r362,r363,r364,r365,r366,r367,r368,r369]),(⟨2,0,1⟩,[r430,r431,r432,r433,r434,r435,r436,r437,r438,r439,r440,r441,r442,r443]),(⟨2,0,2⟩,[r85,r475,r476,r477,r478,r479,r480,r481,r482,r483,r484,r485,r486]),(⟨2,0,3⟩,[r339,r487,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497]),(⟨2,0,4⟩,[r498,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508]),(⟨2,0,5⟩,[r85,r456,r509,r510,r511,r512,r513,r514,r515,r516]),(⟨2,0,6⟩,[r85,r241,r517,r518,r519,r520,r521,r522,r523]),(⟨2,1,0⟩,[r430,r431,r432,r433,r434,r435,r436,r437,r438,r439,r440,r441,r442,r443]),(⟨2,1,1⟩,[r179,r562,r563,r564,r565,r566,r567,r568,r569,r570,r571,r572,r573]),(⟨2,1,2⟩,[r0,r198,r550,r584,r585,r586,r587,r588,r589,r590,r591,r592]),(⟨2,1,3⟩,[r498,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508]),(⟨2,1,4⟩,[0,r226,r227,r235,r236,r237,r238,r239,r240,65536]),(⟨2,1,5⟩,[r85,r241,r593,r594,r595,r596,r597,r598,16384]),(⟨2,2,0⟩,[r85,r475,r476,r477,r478,r479,r480,r481,r482,r483,r484,r485,r486]),(⟨2,2,1⟩,[r0,r198,r550,r584,r585,r586,r587,r588,r589,r590,r591,r592]),(⟨2,2,3⟩,[r0,r136,r190,r191,r192,r193,r194,r195,r196,r197]),(⟨2,2,4⟩,[r0,r198,r294,r295,r296,r297,r298,r299,32768]),(⟨2,3,0⟩,[r339,r487,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497]),(⟨2,3,1⟩,[r498,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508]),(⟨2,3,2⟩,[r0,r136,r190,r191,r192,r193,r194,r195,r196,r197]),(⟨2,3,3⟩,[r226,r227,r228,r229,r230,r231,r232,r233,r234]),(⟨2,4,0⟩,[r498,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508]),(⟨2,4,1⟩,[0,r226,r227,r235,r236,r237,r238,r239,r240,65536]),(⟨2,4,2⟩,[r0,r198,r294,r295,r296,r297,r298,r299,32768]),(⟨2,5,0⟩,[r85,r456,r509,r510,r511,r512,r513,r514,r515,r516]),(⟨2,5,1⟩,[r85,r241,r593,r594,r595,r596,r597,r598,16384]),(⟨2,6,0⟩,[r85,r241,r517,r518,r519,r520,r521,r522,r523]),(⟨3,0,0⟩,[r33,r370,r371,r372,r373,r374,r375,r376,r377,r378,r379,r380,r381,r382]),(⟨3,0,1⟩,[r355,r444,r445,r446,r447,r448,r449,r450,r451,r452,r453,r454,r455]),(⟨3,0,2⟩,[r339,r487,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497]),(⟨3,0,3⟩,[r179,r180,r524,r525,r526,r527,r528,r529,r530,r531,r532]),(⟨3,0,4⟩,[r85,r533,r534,r535,r536,r537,r538,r539,r540,r541]),(⟨3,0,5⟩,[r0,r198,r542,r543,r544,r545,r546,r547,r548]),(⟨3,1,0⟩,[r355,r444,r445,r446,r447,r448,r449,r450,r451,r452,r453,r454,r455]),(⟨3,1,1⟩,[0,r286,r574,r575,r576,r577,r578,r579,r580,r581,r582,r583]),(⟨3,1,2⟩,[r498,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508]),(⟨3,1,3⟩,[0,r286,r287,r288,r289,r290,r291,r292,r293,131072]),(⟨3,1,4⟩,[r85,r241,r593,r594,r595,r596,r597,r598,16384]),(⟨3,2,0⟩,[r339,r487,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497]),(⟨3,2,1⟩,[r498,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508]),(⟨3,2,2⟩,[r0,r136,r190,r191,r192,r193,r194,r195,r196,r197]),(⟨3,2,3⟩,[r226,r227,r228,r229,r230,r231,r232,r233,r234]),(⟨3,3,0⟩,[r179,r180,r524,r525,r526,r527,r528,r529,r530,r531,r532]),(⟨3,3,1⟩,[0,r286,r287,r288,r289,r290,r291,r292,r293,131072]),(⟨3,3,2⟩,[r226,r227,r228,r229,r230,r231,r232,r233,r234]),(⟨3,4,0⟩,[r85,r533,r534,r535,r536,r537,r538,r539,r540,r541]),(⟨3,4,1⟩,[r85,r241,r593,r594,r595,r596,r597,r598,16384]),(⟨3,5,0⟩,[r0,r198,r542,r543,r544,r545,r546,r547,r548]),(⟨4,0,0⟩,[0,r383,r384,r385,r386,r387,r388,r389,r390,r391,r392,r393,r394]),(⟨4,0,1⟩,[r85,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466]),(⟨4,0,2⟩,[r498,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508]),(⟨4,0,3⟩,[r85,r533,r534,r535,r536,r537,r538,r539,r540,r541]),(⟨4,0,4⟩,[r0,r198,r294,r295,r296,r297,r298,r299,32768]),(⟨4,1,0⟩,[r85,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466]),(⟨4,1,2⟩,[0,r226,r227,r235,r236,r237,r238,r239,r240,65536]),(⟨4,1,3⟩,[r85,r241,r593,r594,r595,r596,r597,r598,16384]),(⟨4,2,0⟩,[r498,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508]),(⟨4,2,1⟩,[0,r226,r227,r235,r236,r237,r238,r239,r240,65536]),(⟨4,2,2⟩,[r0,r198,r294,r295,r296,r297,r298,r299,32768]),(⟨4,3,0⟩,[r85,r533,r534,r535,r536,r537,r538,r539,r540,r541]),(⟨4,3,1⟩,[r85,r241,r593,r594,r595,r596,r597,r598,16384]),(⟨4,4,0⟩,[r0,r198,r294,r295,r296,r297,r298,r299,32768]),(⟨5,0,0⟩,[r339,r395,r396,r397,r398,r399,r400,r401,r402,r403,r404,r405]),(⟨5,0,1⟩,[r406,r200,r467,r88,r468,r469,r470,r471,r472,r473,r474]),(⟨5,0,2⟩,[r85,r456,r509,r510,r511,r512,r513,r514,r515,r516]),(⟨5,0,3⟩,[r0,r198,r542,r543,r544,r545,r546,r547,r548]),(⟨5,1,0⟩,[r406,r200,r467,r88,r468,r469,r470,r471,r472,r473,r474]),(⟨5,1,2⟩,[r85,r241,r593,r594,r595,r596,r597,r598,16384]),(⟨5,2,0⟩,[r85,r456,r509,r510,r511,r512,r513,r514,r515,r516]),(⟨5,2,1⟩,[r85,r241,r593,r594,r595,r596,r597,r598,16384]),(⟨5,3,0⟩,[r0,r198,r542,r543,r544,r545,r546,r547,r548]),(⟨6,0,0⟩,[r406,r200,r407,r408,r409,r410,r411,r412,r413,r414,r415]),(⟨6,0,2⟩,[r85,r241,r517,r518,r519,r520,r521,r522,r523]),(⟨6,2,0⟩,[r85,r241,r517,r518,r519,r520,r521,r522,r523])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[128,-1792,5120,30720,-231808,574208,-567040,116736]),(⟨0,0,1⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨0,0,2⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨0,0,3⟩,[-128,1536,256,-37376,76672]),(⟨0,1,0⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨0,1,1⟩,[0,-512,6144,-15360,-18432,60928]),(⟨0,1,2⟩,[-128,1536,-3840,-4608,15232]),(⟨0,2,0⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨0,2,1⟩,[-128,1536,-3840,-4608,15232]),(⟨0,3,0⟩,[-128,1536,256,-37376,76672]),(⟨1,0,0⟩,[128,-2048,8192,10752,-148864,373248,-331520]),(⟨1,0,1⟩,[0,-512,6144,-15360,-18432,60928]),(⟨1,0,2⟩,[-128,1536,-3840,-4608,15232]),(⟨1,1,0⟩,[0,-512,6144,-15360,-18432,60928]),(⟨1,2,0⟩,[-128,1536,-3840,-4608,15232]),(⟨2,0,0⟩,[-128,1280,1280,-34816,69504,-12544]),(⟨2,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨2,1,0⟩,[-128,1536,-3840,-4608,15232]),(⟨3,0,0⟩,[-128,1536,256,-37376,76672])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[128,-2368,16192,-48960,27712,296128,-1096256,1862976,-1545664,318080]),(⟨0,0,1⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨0,0,2⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨0,0,3⟩,[-64,1280,-6336,2560,43072,-131840,181440]),(⟨0,1,0⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨0,1,1⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248]),(⟨0,2,0⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨0,2,3⟩,[-128,1536,-3840,-4608,15232]),(⟨0,3,0⟩,[-64,1280,-6336,2560,43072,-131840,181440]),(⟨0,3,2⟩,[-128,1536,-3840,-4608,15232]),(⟨1,0,0⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨1,0,1⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248]),(⟨1,1,0⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248]),(⟨2,0,0⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨2,0,3⟩,[-128,1536,-3840,-4608,15232]),(⟨2,3,0⟩,[-128,1536,-3840,-4608,15232]),(⟨3,0,0⟩,[-64,1280,-6336,2560,43072,-131840,181440]),(⟨3,0,2⟩,[-128,1536,-3840,-4608,15232]),(⟨3,2,0⟩,[-128,1536,-3840,-4608,15232])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 3 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r599) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 7 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r599) sourceRight))).isZero := by decide +kernel

noncomputable def partial19 : Poly := []

theorem partial_sound19 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 19)
      sourceRight).eval u v t=partial19.eval u v t := by rfl

noncomputable def chunk16 : Poly := [(⟨2,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨2,1,0⟩,[-128,1536,-3840,-4608,15232]),(⟨3,0,0⟩,[-128,1536,256,-37376,76672])]

noncomputable def partial16 : Poly := [(⟨2,0,1⟩,[-16384,499712,-6201344,39641088,-128065536,81985536,961003520,-3932897280,6326550528,-6512640,-18858844160,34277842944,-25009266688,4844994560]),(⟨2,0,2⟩,[-8192,286720,-3997696,28319744,-102326272,107331584,590610432,-2713305088,4444921856,120315904,-13228113920,22214320128,-13136076800]),(⟨2,0,3⟩,[16384,-425984,4046848,-15515648,2916352,155975680,-461799424,428965888,610222080,-2417197056,2531049472,-368492544]),(⟨2,0,4⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨2,1,0⟩,[-16384,499712,-6201344,39641088,-128065536,81985536,961003520,-3932897280,6326550528,-6512640,-18858844160,34277842944,-25009266688,4844994560]),(⟨2,1,1⟩,[-16384,573440,-7995392,56639488,-204652544,214663168,1181220864,-5426610176,8889843712,240631808,-26456227840,44428640256,-26272153600]),(⟨2,1,2⟩,[16384,-393216,3194880,-7028736,-37191680,238616576,-432832512,-137592832,1863008256,-2732130304,-362299392,2879700992]),(⟨2,1,3⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨2,2,0⟩,[-8192,286720,-3997696,28319744,-102326272,107331584,590610432,-2713305088,4444921856,120315904,-13228113920,22214320128,-13136076800]),(⟨2,2,1⟩,[16384,-393216,3194880,-7028736,-37191680,238616576,-432832512,-137592832,1863008256,-2732130304,-362299392,2879700992]),(⟨2,2,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,3,0⟩,[16384,-425984,4046848,-15515648,2916352,155975680,-461799424,428965888,610222080,-2417197056,2531049472,-368492544]),(⟨2,3,1⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨2,3,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,4,0⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨2,4,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,0,0⟩,[-16384,499712,-5677056,25747456,23715840,-794624000,3673669632,-6636126208,-6164611072,61740457984,-153589850112,200690262016,-130397708288,24387829760]),(⟨3,0,1⟩,[-16384,573440,-7733248,48513024,-104775680,-419725312,3339190272,-8285552640,2260746240,39783481344,-113685430272,146262409216,-79258009600]),(⟨3,0,2⟩,[16384,-393216,2670592,4505600,-129466368,541130752,-519864320,-2360049664,9240788992,-15208611840,10190045184,1393344512]),(⟨3,0,3⟩,[8192,-262144,2760704,-7340032,-55951360,418643968,-796180480,-1168637952,8276516864,-16889937920,13911367680]),(⟨3,1,0⟩,[-16384,573440,-7733248,48513024,-104775680,-419725312,3339190272,-8285552640,2260746240,39783481344,-113685430272,146262409216,-79258009600]),(⟨3,1,1⟩,[0,98304,-2555904,24412160,-97255424,50790400,932052992,-3585015808,5102632960,3740237824,-23374790656,22846537728]),(⟨3,2,0⟩,[16384,-393216,2670592,4505600,-129466368,541130752,-519864320,-2360049664,9240788992,-15208611840,10190045184,1393344512]),(⟨3,2,3⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904]),(⟨3,3,0⟩,[8192,-262144,2760704,-7340032,-55951360,418643968,-796180480,-1168637952,8276516864,-16889937920,13911367680]),(⟨3,3,2⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904]),(⟨4,0,0⟩,[-8192,286720,-3735552,20193280,-2449408,-527056896,2748579840,-5572247552,-2184175616,39663165440,-100457316352,124048089088,-66121932800]),(⟨4,0,1⟩,[16384,-393216,3194880,-8077312,-14123008,41484288,412319744,-2022932480,3207282688,1952907264,-15057043456,15981658112]),(⟨4,0,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,1,0⟩,[16384,-393216,3194880,-8077312,-14123008,41484288,412319744,-2022932480,3207282688,1952907264,-15057043456,15981658112]),(⟨4,1,3⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,3,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,4,0⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨5,0,0⟩,[16384,-425984,3522560,-3981312,-89358336,458489856,-548831232,-1793490944,7988002816,-14893678592,13083394048,-1854849024]),(⟨5,0,1⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨5,0,3⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨5,1,0⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨5,1,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨5,2,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨5,3,0⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨6,0,0⟩,[8192,-262144,2760704,-7340032,-55951360,418643968,-796180480,-1168637952,8276516864,-16889937920,13911367680]),(⟨6,0,2⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904]),(⟨6,2,0⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904])]


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

noncomputable def partial12 : Poly := [(⟨1,0,2⟩,[-16384,499712,-6201344,39641088,-128065536,81985536,961003520,-3932897280,6326550528,-6512640,-18858844160,34277842944,-25009266688,4844994560]),(⟨1,0,3⟩,[-8192,286720,-3997696,28319744,-102326272,107331584,590610432,-2713305088,4444921856,120315904,-13228113920,22214320128,-13136076800]),(⟨1,0,4⟩,[16384,-425984,4046848,-15515648,2916352,155975680,-461799424,428965888,610222080,-2417197056,2531049472,-368492544]),(⟨1,0,5⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨1,1,0⟩,[0,-65536,1998848,-24805376,158564352,-512262144,327942144,3844014080,-15731589120,25306202112,-26050560,-75435376640,137111371776,-100037066752,19379978240]),(⟨1,1,1⟩,[0,-32768,1146880,-15990784,113278976,-409305088,429326336,2362441728,-10853220352,17779687424,481263616,-52912455680,88857280512,-52544307200]),(⟨1,1,2⟩,[-8192,352256,-5701632,44507136,-164388864,118996992,1214513152,-4560502784,6160785408,2561204224,-22896902144,32338518016,-14610046976]),(⟨1,1,3⟩,[0,65536,-1900544,20578304,-98828288,146145280,516554752,-2564292608,3754688512,1952514048,-14270398464,14302969856]),(⟨1,2,0⟩,[-16384,466944,-5054464,23650304,-14786560,-327319552,1390329856,-1570455552,-4526669824,17773174784,-18377580544,-18634612736,63848013824,-47699312640]),(⟨1,2,1⟩,[-8192,286720,-3866624,24911872,-68378624,-53100544,921174016,-2597437440,2178686976,5131460608,-14487846912,10640924672,-143302656]),(⟨1,2,2⟩,[32768,-851968,8093696,-31031296,5832704,311951360,-923598848,857931776,1220444160,-4834394112,5062098944,-736985088]),(⟨1,2,3⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨1,2,5⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨1,3,0⟩,[-8192,352256,-5701632,44507136,-164388864,118996992,1214513152,-4560502784,6160785408,2561204224,-22896902144,32338518016,-14610046976]),(⟨1,3,1⟩,[0,32768,-851968,8486912,-40108032,82640896,28966912,-566558720,1252786176,-314933248,-2893348864,3248193536]),(⟨1,3,2⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨1,3,3⟩,[0,65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨1,3,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨1,4,0⟩,[16384,-393216,2998272,-3424256,-55803904,219480064,25788416,-1568768000,3112124416,-149749760,-8846000128,10686283776]),(⟨1,4,2⟩,[0,65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨1,4,3⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨1,5,0⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨1,5,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,0,0⟩,[-16384,466944,-4939776,19505152,45850624,-795033600,3414540288,-5833474048,-6590496768,58767155200,-146341486592,197456699392,-141873274880,41496641536,-3989995520]),(⟨2,0,1⟩,[-24576,770048,-9494528,55508992,-112672768,-455081984,3533651968,-8909815808,3794804736,37534875648,-114178023424,156611117056,-99971006464,15662940160]),(⟨2,0,2⟩,[0,180224,-5062656,55771136,-294109184,630489088,724926464,-7157776384,16449437696,-14026883072,-13109051392,40754610176,-25968689152]),(⟨2,0,3⟩,[24576,-638976,5562368,-11599872,-96550912,624263168,-1115242496,-1316290560,9646956544,-18752847872,13902307328,603717632]),(⟨2,0,4⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨2,1,0⟩,[-24576,737280,-8347648,39518208,606208,-864387072,3962978304,-6547374080,-7058415616,55314563072,-113696759808,103698661376,-11113725952,-36881367040]),(⟨2,1,1⟩,[-16384,606208,-8650752,59490304,-180731904,-72318976,2353004544,-7597752320,9022881792,9207169024,-43797970944,49250353152,-15954362368]),(⟨2,1,2⟩,[16384,-360448,2342912,1458176,-77299712,321257472,-403865600,-704151552,3115794432,-3047063552,-3255648256,6127894528]),(⟨2,1,3⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨2,2,0⟩,[0,180224,-4931584,52363264,-260161536,470056960,1055490048,-7041908736,14183202816,-9015738368,-14368784384,29181214720,-12975915008]),(⟨2,2,1⟩,[16384,-360448,2342912,1458176,-77299712,321257472,-403865600,-704151552,3115794432,-3047063552,-3255648256,6127894528]),(⟨2,2,3⟩,[16384,-360448,2293760,2097152,-75137024,255655936,-106233856,-802422784,1116487680,-191070208]),(⟨2,2,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,3,0⟩,[24576,-638976,5562368,-11599872,-96550912,624263168,-1115242496,-1316290560,9646956544,-18752847872,13902307328,603717632]),(⟨2,3,1⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨2,3,2⟩,[16384,-360448,2293760,2097152,-75137024,255655936,-106233856,-802422784,1116487680,-191070208]),(⟨2,3,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,4,0⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨2,4,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,0,0⟩,[-24576,770048,-8970240,41615360,39108608,-1331691520,6246318080,-11613044736,-8696356864,99281846272,-248909029376,323023536128,-205359448064,35205775360]),(⟨3,0,1⟩,[-16384,606208,-8519680,54771712,-114802688,-546275328,4180410368,-10572562432,4660019200,43738873856,-129767440384,162657517568,-81932992512]),(⟨3,0,2⟩,[32768,-819200,6717440,-11010048,-126550016,697106432,-981663744,-1931083776,9851011072,-17625808896,12721094656,1024851968]),(⟨3,0,3⟩,[8192,-262144,2760704,-7340032,-55951360,418643968,-796180480,-1168637952,8276516864,-16889937920,13911367680]),(⟨3,0,5⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,1,0⟩,[-16384,671744,-10223616,70959104,-176865280,-534609920,4804313088,-12419760128,6375882752,46179762176,-139436228608,172781715456,-83406962688]),(⟨3,1,1⟩,[0,98304,-2555904,24412160,-97255424,50790400,932052992,-3585015808,5102632960,3740237824,-23374790656,22846537728]),(⟨3,1,3⟩,[0,65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,2,0⟩,[32768,-819200,6717440,-11010048,-126550016,697106432,-981663744,-1931083776,9851011072,-17625808896,12721094656,1024851968]),(⟨3,2,3⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨3,3,0⟩,[8192,-262144,2760704,-7340032,-55951360,418643968,-796180480,-1168637952,8276516864,-16889937920,13911367680]),(⟨3,3,2⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨3,4,0⟩,[0,65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,5,0⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,0,0⟩,[8192,-106496,-802816,19324928,-91906048,-111230976,2292285440,-7303413760,5375418368,25395650560,-87110139904,120374059008,-65818468352]),(⟨4,0,1⟩,[16384,-393216,3194880,-8077312,-14123008,41484288,412319744,-2022932480,3207282688,1952907264,-15057043456,15981658112]),(⟨4,0,2⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨4,0,3⟩,[16384,-360448,2293760,2097152,-75137024,255655936,-106233856,-802422784,1116487680,-191070208]),(⟨4,0,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,1,0⟩,[16384,-360448,2146304,4014080,-72843264,104988672,899907584,-4020666368,5709185024,4220354560,-26434093056,27036434432]),(⟨4,1,2⟩,[0,65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,1,3⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,2,0⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨4,2,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,3,0⟩,[16384,-294912,720896,15466496,-117604352,242417664,222494720,-1185415168,554975232,736985088]),(⟨4,3,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,4,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,0,0⟩,[24576,-671744,5890048,-8552448,-148717568,844136448,-1231241216,-2972188672,15771951104,-30914396160,27348000768,-4130832384]),(⟨5,0,1⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨5,0,2⟩,[16384,-360448,2293760,2097152,-75137024,255655936,-106233856,-802422784,1116487680,-191070208]),(⟨5,0,3⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨5,1,0⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨5,1,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨5,2,0⟩,[16384,-360448,2293760,2097152,-75137024,255655936,-106233856,-802422784,1116487680,-191070208]),(⟨5,2,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨5,3,0⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨6,0,0⟩,[8192,-262144,2760704,-7340032,-55951360,418643968,-796180480,-1168637952,8276516864,-16889937920,13911367680]),(⟨6,0,2⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904]),(⟨6,2,0⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904])]


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

noncomputable def partial8 : Poly := [(⟨0,2,1⟩,[-16384,499712,-6201344,39641088,-128065536,81985536,961003520,-3932897280,6326550528,-6512640,-18858844160,34277842944,-25009266688,4844994560]),(⟨0,2,2⟩,[-8192,286720,-3997696,28319744,-102326272,107331584,590610432,-2713305088,4444921856,120315904,-13228113920,22214320128,-13136076800]),(⟨0,2,3⟩,[16384,-425984,4046848,-15515648,2916352,155975680,-461799424,428965888,610222080,-2417197056,2531049472,-368492544]),(⟨0,2,4⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨0,3,0⟩,[-16384,499712,-5677056,25747456,23715840,-794624000,3673669632,-6636126208,-6164611072,61740457984,-153589850112,200690262016,-130397708288,24387829760]),(⟨0,3,1⟩,[-16384,573440,-7733248,48513024,-104775680,-419725312,3339190272,-8285552640,2260746240,39783481344,-113685430272,146262409216,-79258009600]),(⟨0,3,2⟩,[16384,-393216,2670592,4505600,-129466368,541130752,-519864320,-2360049664,9240788992,-15208611840,10190045184,1393344512]),(⟨0,3,3⟩,[8192,-262144,2760704,-7340032,-55951360,418643968,-796180480,-1168637952,8276516864,-16889937920,13911367680]),(⟨0,4,0⟩,[-8192,286720,-3735552,20193280,-2449408,-527056896,2748579840,-5572247552,-2184175616,39663165440,-100457316352,124048089088,-66121932800]),(⟨0,4,1⟩,[16384,-393216,3194880,-8077312,-14123008,41484288,412319744,-2022932480,3207282688,1952907264,-15057043456,15981658112]),(⟨0,4,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨0,5,0⟩,[16384,-425984,3522560,-3981312,-89358336,458489856,-548831232,-1793490944,7988002816,-14893678592,13083394048,-1854849024]),(⟨0,5,1⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨0,5,3⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨0,6,0⟩,[8192,-262144,2760704,-7340032,-55951360,418643968,-796180480,-1168637952,8276516864,-16889937920,13911367680]),(⟨0,6,2⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904]),(⟨1,0,0⟩,[16384,-565248,7970816,-57450496,191946752,154451968,-4382883840,19324485632,-37577293824,-10827341824,271252365312,-798691041280,1292296577024,-1241880461312,631141253120,-105449881600]),(⟨1,0,1⟩,[8192,-385024,7028736,-65101824,314269696,-517865472,-2571124736,18047647744,-46197907456,28897845248,168215232512,-592012238848,952340226048,-818922668032,305282826240]),(⟨1,0,2⟩,[-32768,958464,-10575872,49389568,-15245312,-847183872,3647225856,-4806066176,-10577231872,55350829056,-101514272768,82956722176,2157109248,-39679180800]),(⟨1,0,3⟩,[-16384,647168,-9658368,67608576,-192733184,-247676928,3330293760,-8719351808,2873753600,39366123520,-113395032064,143768231936,-74761035776]),(⟨1,0,4⟩,[16384,-393216,2998272,-3424256,-55803904,219480064,25788416,-1568768000,3112124416,-149749760,-8846000128,10686283776]),(⟨1,0,5⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨1,1,0⟩,[8192,-385024,7028736,-65101824,314269696,-517865472,-2571124736,18047647744,-46197907456,28897845248,168215232512,-592012238848,952340226048,-818922668032,305282826240]),(⟨1,1,1⟩,[0,-98304,3276800,-43417600,288686080,-927137792,282066944,9013755904,-34355675136,52178223104,10947526656,-182777577472,298894819328,-175784591360]),(⟨1,1,2⟩,[-8192,352256,-5570560,41099264,-130441216,-41435136,1545076736,-4444635136,3894550528,7572348928,-24156635136,20765122560,-1617272832]),(⟨1,1,3⟩,[0,65536,-1900544,20578304,-98828288,146145280,516554752,-2564292608,3754688512,1952514048,-14270398464,14302969856]),(⟨1,2,0⟩,[-32768,958464,-10575872,49389568,-15245312,-847183872,3647225856,-4806066176,-10577231872,55350829056,-101514272768,82956722176,2157109248,-39679180800]),(⟨1,2,1⟩,[-16384,638976,-9568256,69419008,-232767488,65896448,2135687168,-7157940224,8339472384,7692664832,-37384749056,42979442688,-14753349632]),(⟨1,2,2⟩,[32768,-819200,7241728,-22544384,-34275328,394592256,-894631936,291373056,2473230336,-5149327360,2168750080,2511208448]),(⟨1,2,3⟩,[-8192,196608,-1662976,3801088,31375360,-264765440,763183104,-467271680,-2147524608,4368695296,-2286018560]),(⟨1,2,4⟩,[0,65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨1,2,5⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨1,3,0⟩,[-24576,933888,-13393920,87801856,-195182592,-774733824,6078873600,-14291599360,689577984,79029288960,-213852348416,267816321024,-140882968576]),(⟨1,3,1⟩,[0,131072,-3604480,36503552,-155975680,114294784,1419640832,-5582749696,7604535296,6007685120,-34751840256,33901314048]),(⟨1,3,2⟩,[-8192,196608,-1662976,3801088,31375360,-264765440,763183104,-467271680,-2147524608,4368695296,-2286018560]),(⟨1,3,3⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨1,3,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨1,4,0⟩,[16384,-360448,2146304,4014080,-72843264,104988672,899907584,-4020666368,5709185024,4220354560,-26434093056,27036434432]),(⟨1,4,2⟩,[0,65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨1,4,3⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨1,5,0⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨1,5,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,0,0⟩,[-8192,147456,90112,-20791296,201555968,-800636928,515473408,8370159616,-37056815104,62358798336,21899796480,-319120162816,673355579392,-677388959744,281912852480]),(⟨2,0,1⟩,[-24576,704512,-7364608,28082176,62734336,-972914688,3386392576,-2258501632,-19707650048,71933411328,-103711760384,26745995264,110066532352,-107577344000]),(⟨2,0,2⟩,[0,180224,-4931584,52363264,-260161536,470056960,1055490048,-7041908736,14183202816,-9015738368,-14368784384,29181214720,-12975915008]),(⟨2,0,3⟩,[24576,-638976,5562368,-11599872,-96550912,624263168,-1115242496,-1316290560,9646956544,-18752847872,13902307328,603717632]),(⟨2,0,4⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨2,1,0⟩,[-24576,704512,-7364608,28082176,62734336,-972914688,3386392576,-2258501632,-19707650048,71933411328,-103711760384,26745995264,110066532352,-107577344000]),(⟨2,1,1⟩,[-16384,606208,-8519680,56082432,-146784256,-232751104,2683568128,-7481884672,6756646912,14218313728,-45057703936,37676957696,-2961588224]),(⟨2,1,2⟩,[16384,-360448,2342912,1458176,-77299712,321257472,-403865600,-704151552,3115794432,-3047063552,-3255648256,6127894528]),(⟨2,1,3⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨2,2,0⟩,[0,180224,-4931584,52363264,-260161536,470056960,1055490048,-7041908736,14183202816,-9015738368,-14368784384,29181214720,-12975915008]),(⟨2,2,1⟩,[32768,-786432,6389760,-14057472,-74383360,477233152,-865665024,-275185664,3726016512,-5464260608,-724598784,5759401984]),(⟨2,2,3⟩,[16384,-360448,2293760,2097152,-75137024,255655936,-106233856,-802422784,1116487680,-191070208]),(⟨2,2,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,3,0⟩,[40960,-1064960,9084928,-15581184,-185909248,1082753024,-1664073728,-3109781504,17634959360,-33646526464,26985701376,-1251131392]),(⟨2,3,1⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨2,3,2⟩,[16384,-360448,2293760,2097152,-75137024,255655936,-106233856,-802422784,1116487680,-191070208]),(⟨2,3,3⟩,[49152,-1179648,9502720,-21364736,-83853312,447873024,-309788672,-1203372032,1631895552]),(⟨2,4,0⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨2,4,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,5,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,6,0⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904]),(⟨3,0,0⟩,[-40960,1261568,-14491648,67354624,38649856,-1851555840,8503214080,-14848655360,-14746918912,136859500544,-332045721600,424614871040,-267050352640,43225907200]),(⟨3,0,1⟩,[-16384,671744,-10223616,70959104,-176865280,-534609920,4804313088,-12419760128,6375882752,46179762176,-139436228608,172781715456,-83406962688]),(⟨3,0,2⟩,[32768,-819200,6717440,-11010048,-126550016,697106432,-981663744,-1931083776,9851011072,-17625808896,12721094656,1024851968]),(⟨3,0,3⟩,[-8192,196608,-1925120,11141120,-40452096,31981568,466436096,-2261385216,5562130432,-9676980224,8861655040]),(⟨3,0,4⟩,[0,65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,0,5⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,1,0⟩,[-16384,671744,-10223616,70959104,-176865280,-534609920,4804313088,-12419760128,6375882752,46179762176,-139436228608,172781715456,-83406962688]),(⟨3,1,1⟩,[0,98304,-2555904,24412160,-97255424,50790400,932052992,-3585015808,5102632960,3740237824,-23374790656,22846537728]),(⟨3,1,3⟩,[0,65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,2,0⟩,[32768,-819200,6717440,-11010048,-126550016,697106432,-981663744,-1931083776,9851011072,-17625808896,12721094656,1024851968]),(⟨3,2,1⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨3,2,3⟩,[49152,-1179648,9502720,-21364736,-83853312,447873024,-309788672,-1203372032,1631895552]),(⟨3,3,0⟩,[0,-65536,835584,3801088,-96403456,450625536,-329744384,-3430023168,13838647296,-26566918144,22773022720]),(⟨3,3,1⟩,[0,65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,3,2⟩,[49152,-1179648,8978432,-10878976,-157777920,649199616,-332333056,-1985609728,2567749632]),(⟨3,4,0⟩,[0,65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,4,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,5,0⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨4,0,0⟩,[0,188416,-4759552,42426368,-120250368,-477904896,4408066048,-11462262784,2088386560,62200569856,-177608269824,231803772928,-125969457152]),(⟨4,0,1⟩,[16384,-360448,2146304,4014080,-72843264,104988672,899907584,-4020666368,5709185024,4220354560,-26434093056,27036434432]),(⟨4,0,2⟩,[-8192,196608,-1662976,3801088,31375360,-264765440,763183104,-467271680,-2147524608,4368695296,-2286018560]),(⟨4,0,3⟩,[16384,-294912,720896,15466496,-117604352,242417664,222494720,-1185415168,554975232,736985088]),(⟨4,0,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,1,0⟩,[16384,-360448,2146304,4014080,-72843264,104988672,899907584,-4020666368,5709185024,4220354560,-26434093056,27036434432]),(⟨4,1,2⟩,[0,65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,1,3⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,2,0⟩,[-8192,196608,-1662976,3801088,31375360,-264765440,763183104,-467271680,-2147524608,4368695296,-2286018560]),(⟨4,2,1⟩,[0,65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,2,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,3,0⟩,[16384,-294912,720896,15466496,-117604352,242417664,222494720,-1185415168,554975232,736985088]),(⟨4,3,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,4,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,0,0⟩,[24576,-671744,5890048,-8552448,-148717568,844136448,-1231241216,-2972188672,15771951104,-30914396160,27348000768,-4130832384]),(⟨5,0,1⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨5,0,2⟩,[16384,-360448,2293760,2097152,-75137024,255655936,-106233856,-802422784,1116487680,-191070208]),(⟨5,0,3⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨5,1,0⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨5,1,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨5,2,0⟩,[16384,-360448,2293760,2097152,-75137024,255655936,-106233856,-802422784,1116487680,-191070208]),(⟨5,2,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨5,3,0⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨6,0,0⟩,[8192,-262144,2760704,-7340032,-55951360,418643968,-796180480,-1168637952,8276516864,-16889937920,13911367680]),(⟨6,0,2⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904]),(⟨6,2,0⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904])]


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

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[16384,-565248,7970816,-57450496,191946752,154451968,-4382883840,19324485632,-37577293824,-10827341824,271252365312,-798691041280,1292296577024,-1241880461312,631141253120,-105449881600]),(⟨0,1,1⟩,[8192,-385024,7028736,-65101824,314269696,-517865472,-2571124736,18047647744,-46197907456,28897845248,168215232512,-592012238848,952340226048,-818922668032,305282826240]),(⟨0,1,2⟩,[-32768,958464,-10575872,49389568,-15245312,-847183872,3647225856,-4806066176,-10577231872,55350829056,-101514272768,82956722176,2157109248,-39679180800]),(⟨0,1,3⟩,[-16384,647168,-9658368,67608576,-192733184,-247676928,3330293760,-8719351808,2873753600,39366123520,-113395032064,143768231936,-74761035776]),(⟨0,1,4⟩,[16384,-393216,2998272,-3424256,-55803904,219480064,25788416,-1568768000,3112124416,-149749760,-8846000128,10686283776]),(⟨0,1,5⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨0,2,0⟩,[-8192,147456,90112,-20791296,201555968,-800636928,515473408,8370159616,-37056815104,62358798336,21899796480,-319120162816,673355579392,-677388959744,281912852480]),(⟨0,2,1⟩,[-24576,704512,-7364608,28082176,62734336,-972914688,3386392576,-2258501632,-19707650048,71933411328,-103711760384,26745995264,110066532352,-107577344000]),(⟨0,2,2⟩,[0,180224,-4931584,52363264,-260161536,470056960,1055490048,-7041908736,14183202816,-9015738368,-14368784384,29181214720,-12975915008]),(⟨0,2,3⟩,[24576,-638976,5562368,-11599872,-96550912,624263168,-1115242496,-1316290560,9646956544,-18752847872,13902307328,603717632]),(⟨0,2,4⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨0,3,0⟩,[-40960,1261568,-14491648,67354624,38649856,-1851555840,8503214080,-14848655360,-14746918912,136859500544,-332045721600,424614871040,-267050352640,43225907200]),(⟨0,3,1⟩,[-16384,671744,-10223616,70959104,-176865280,-534609920,4804313088,-12419760128,6375882752,46179762176,-139436228608,172781715456,-83406962688]),(⟨0,3,2⟩,[32768,-819200,6717440,-11010048,-126550016,697106432,-981663744,-1931083776,9851011072,-17625808896,12721094656,1024851968]),(⟨0,3,3⟩,[-8192,196608,-1925120,11141120,-40452096,31981568,466436096,-2261385216,5562130432,-9676980224,8861655040]),(⟨0,3,4⟩,[0,65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨0,3,5⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨0,4,0⟩,[0,188416,-4759552,42426368,-120250368,-477904896,4408066048,-11462262784,2088386560,62200569856,-177608269824,231803772928,-125969457152]),(⟨0,4,1⟩,[16384,-360448,2146304,4014080,-72843264,104988672,899907584,-4020666368,5709185024,4220354560,-26434093056,27036434432]),(⟨0,4,2⟩,[-8192,196608,-1662976,3801088,31375360,-264765440,763183104,-467271680,-2147524608,4368695296,-2286018560]),(⟨0,4,3⟩,[16384,-294912,720896,15466496,-117604352,242417664,222494720,-1185415168,554975232,736985088]),(⟨0,4,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨0,5,0⟩,[24576,-671744,5890048,-8552448,-148717568,844136448,-1231241216,-2972188672,15771951104,-30914396160,27348000768,-4130832384]),(⟨0,5,1⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨0,5,2⟩,[16384,-360448,2293760,2097152,-75137024,255655936,-106233856,-802422784,1116487680,-191070208]),(⟨0,5,3⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨0,6,0⟩,[8192,-262144,2760704,-7340032,-55951360,418643968,-796180480,-1168637952,8276516864,-16889937920,13911367680]),(⟨0,6,2⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904]),(⟨1,0,0⟩,[16384,-565248,7970816,-57450496,191946752,154451968,-4382883840,19324485632,-37577293824,-10827341824,271252365312,-798691041280,1292296577024,-1241880461312,631141253120,-105449881600]),(⟨1,0,1⟩,[8192,-385024,7028736,-65101824,314269696,-517865472,-2571124736,18047647744,-46197907456,28897845248,168215232512,-592012238848,952340226048,-818922668032,305282826240]),(⟨1,0,2⟩,[-32768,958464,-10575872,49389568,-15245312,-847183872,3647225856,-4806066176,-10577231872,55350829056,-101514272768,82956722176,2157109248,-39679180800]),(⟨1,0,3⟩,[-16384,647168,-9658368,67608576,-192733184,-247676928,3330293760,-8719351808,2873753600,39366123520,-113395032064,143768231936,-74761035776]),(⟨1,0,4⟩,[16384,-393216,2998272,-3424256,-55803904,219480064,25788416,-1568768000,3112124416,-149749760,-8846000128,10686283776]),(⟨1,0,5⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨1,1,0⟩,[16384,-704512,12058624,-105398272,469975040,-523468800,-5470191616,32251281408,-76664225792,32489488384,336456515584,-1108589101056,1767569080320,-1537808269312,591185674240]),(⟨1,1,1⟩,[0,-163840,5406720,-70844416,464093184,-1444970496,134807552,15665070080,-57858129920,86576758784,21413789696,-312642699264,508932358144,-299024875520]),(⟨1,1,2⟩,[-16384,638976,-9437184,66011136,-198819840,-94535680,2466250752,-7042072576,6073237504,12703809536,-38644482048,31406047232,-1760575488]),(⟨1,1,3⟩,[0,98304,-2752512,29065216,-138936320,228786176,545521664,-3130851328,5007474688,1637580800,-17163747328,17551163392]),(⟨1,2,0⟩,[-40960,1196032,-12886016,53821440,62275584,-1492779008,5643288576,-5494112256,-25758212096,109511065600,-186848452608,128337330176,48375627776,-99557212160]),(⟨1,2,1⟩,[-16384,671744,-10223616,72269824,-208846848,-221085696,3307470848,-9329082368,8472510464,16659202048,-54726492160,47801155584,-4435558400]),(⟨1,2,2⟩,[32768,-786432,6389760,-14057472,-74383360,477233152,-865665024,-275185664,3726016512,-5464260608,-724598784,5759401984]),(⟨1,2,3⟩,[-8192,196608,-1662976,3801088,31375360,-264765440,763183104,-467271680,-2147524608,4368695296,-2286018560]),(⟨1,2,4⟩,[0,65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨1,2,5⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨1,3,0⟩,[-24576,966656,-14180352,94060544,-205209600,-901283840,6920093696,-16578609152,3088850944,82984681472,-229934358528,284211429376,-143557951488]),(⟨1,3,1⟩,[0,131072,-3604480,36503552,-155975680,114294784,1419640832,-5582749696,7604535296,6007685120,-34751840256,33901314048]),(⟨1,3,2⟩,[-8192,196608,-1662976,3801088,31375360,-264765440,763183104,-467271680,-2147524608,4368695296,-2286018560]),(⟨1,3,3⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨1,3,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨1,4,0⟩,[16384,-360448,2146304,4014080,-72843264,104988672,899907584,-4020666368,5709185024,4220354560,-26434093056,27036434432]),(⟨1,4,2⟩,[0,65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨1,4,3⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨1,5,0⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨1,5,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,0,0⟩,[-8192,147456,90112,-20791296,201555968,-800636928,515473408,8370159616,-37056815104,62358798336,21899796480,-319120162816,673355579392,-677388959744,281912852480]),(⟨2,0,1⟩,[-24576,704512,-7364608,28082176,62734336,-972914688,3386392576,-2258501632,-19707650048,71933411328,-103711760384,26745995264,110066532352,-107577344000]),(⟨2,0,2⟩,[0,180224,-4931584,52363264,-260161536,470056960,1055490048,-7041908736,14183202816,-9015738368,-14368784384,29181214720,-12975915008]),(⟨2,0,3⟩,[24576,-638976,5562368,-11599872,-96550912,624263168,-1115242496,-1316290560,9646956544,-18752847872,13902307328,603717632]),(⟨2,0,4⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨2,1,0⟩,[-40960,1196032,-12886016,53821440,62275584,-1492779008,5643288576,-5494112256,-25758212096,109511065600,-186848452608,128337330176,48375627776,-99557212160]),(⟨2,1,1⟩,[-16384,671744,-10223616,72269824,-208846848,-221085696,3307470848,-9329082368,8472510464,16659202048,-54726492160,47801155584,-4435558400]),(⟨2,1,2⟩,[32768,-786432,6389760,-14057472,-74383360,477233152,-865665024,-275185664,3726016512,-5464260608,-724598784,5759401984]),(⟨2,1,3⟩,[-8192,196608,-1662976,3801088,31375360,-264765440,763183104,-467271680,-2147524608,4368695296,-2286018560]),(⟨2,1,4⟩,[0,65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,1,5⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,2,0⟩,[16384,-212992,-1998848,51494912,-349618176,885882880,599195648,-8773074944,21742796800,-23283253248,-1021607936,25507184640,-12672450560]),(⟨2,2,1⟩,[32768,-786432,6389760,-14057472,-74383360,477233152,-865665024,-275185664,3726016512,-5464260608,-724598784,5759401984]),(⟨2,2,3⟩,[32768,-720896,4587520,4194304,-150274048,511311872,-212467712,-1604845568,2232975360,-382140416]),(⟨2,2,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,3,0⟩,[40960,-1064960,9084928,-15581184,-185909248,1082753024,-1664073728,-3109781504,17634959360,-33646526464,26985701376,-1251131392]),(⟨2,3,1⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨2,3,2⟩,[16384,-360448,2293760,2097152,-75137024,255655936,-106233856,-802422784,1116487680,-191070208]),(⟨2,3,3⟩,[49152,-1179648,9502720,-21364736,-83853312,447873024,-309788672,-1203372032,1631895552]),(⟨2,4,0⟩,[-8192,196608,-1662976,3801088,31375360,-264765440,763183104,-467271680,-2147524608,4368695296,-2286018560]),(⟨2,4,1⟩,[0,65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,4,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,5,0⟩,[16384,-360448,2293760,2097152,-75137024,255655936,-106233856,-802422784,1116487680,-191070208]),(⟨2,5,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,6,0⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904]),(⟨3,0,0⟩,[-40960,1261568,-14491648,67354624,38649856,-1851555840,8503214080,-14848655360,-14746918912,136859500544,-332045721600,424614871040,-267050352640,43225907200]),(⟨3,0,1⟩,[-16384,671744,-10223616,70959104,-176865280,-534609920,4804313088,-12419760128,6375882752,46179762176,-139436228608,172781715456,-83406962688]),(⟨3,0,2⟩,[32768,-819200,6717440,-11010048,-126550016,697106432,-981663744,-1931083776,9851011072,-17625808896,12721094656,1024851968]),(⟨3,0,3⟩,[-8192,196608,-1925120,11141120,-40452096,31981568,466436096,-2261385216,5562130432,-9676980224,8861655040]),(⟨3,0,4⟩,[0,65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,0,5⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,1,0⟩,[-24576,966656,-14180352,94060544,-205209600,-901283840,6920093696,-16578609152,3088850944,82984681472,-229934358528,284211429376,-143557951488]),(⟨3,1,1⟩,[0,131072,-3604480,36503552,-155975680,114294784,1419640832,-5582749696,7604535296,6007685120,-34751840256,33901314048]),(⟨3,1,2⟩,[-8192,196608,-1662976,3801088,31375360,-264765440,763183104,-467271680,-2147524608,4368695296,-2286018560]),(⟨3,1,3⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,1,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,2,0⟩,[40960,-1064960,9084928,-15581184,-185909248,1082753024,-1664073728,-3109781504,17634959360,-33646526464,26985701376,-1251131392]),(⟨3,2,1⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨3,2,2⟩,[16384,-360448,2293760,2097152,-75137024,255655936,-106233856,-802422784,1116487680,-191070208]),(⟨3,2,3⟩,[49152,-1179648,9502720,-21364736,-83853312,447873024,-309788672,-1203372032,1631895552]),(⟨3,3,0⟩,[-16384,393216,-3850240,22282240,-80904192,63963136,932872192,-4522770432,11124260864,-19353960448,17723310080]),(⟨3,3,1⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,3,2⟩,[65536,-1572864,12320768,-21495808,-161087488,731381760,-428081152,-2125987840,2799763456]),(⟨3,4,0⟩,[16384,-294912,720896,15466496,-117604352,242417664,222494720,-1185415168,554975232,736985088]),(⟨3,4,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,5,0⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨4,0,0⟩,[0,188416,-4759552,42426368,-120250368,-477904896,4408066048,-11462262784,2088386560,62200569856,-177608269824,231803772928,-125969457152]),(⟨4,0,1⟩,[16384,-360448,2146304,4014080,-72843264,104988672,899907584,-4020666368,5709185024,4220354560,-26434093056,27036434432]),(⟨4,0,2⟩,[-8192,196608,-1662976,3801088,31375360,-264765440,763183104,-467271680,-2147524608,4368695296,-2286018560]),(⟨4,0,3⟩,[16384,-294912,720896,15466496,-117604352,242417664,222494720,-1185415168,554975232,736985088]),(⟨4,0,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,1,0⟩,[16384,-360448,2146304,4014080,-72843264,104988672,899907584,-4020666368,5709185024,4220354560,-26434093056,27036434432]),(⟨4,1,2⟩,[0,65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,1,3⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,2,0⟩,[-8192,196608,-1662976,3801088,31375360,-264765440,763183104,-467271680,-2147524608,4368695296,-2286018560]),(⟨4,2,1⟩,[0,65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,2,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,3,0⟩,[16384,-294912,720896,15466496,-117604352,242417664,222494720,-1185415168,554975232,736985088]),(⟨4,3,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,4,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,0,0⟩,[24576,-671744,5890048,-8552448,-148717568,844136448,-1231241216,-2972188672,15771951104,-30914396160,27348000768,-4130832384]),(⟨5,0,1⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨5,0,2⟩,[16384,-360448,2293760,2097152,-75137024,255655936,-106233856,-802422784,1116487680,-191070208]),(⟨5,0,3⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨5,1,0⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨5,1,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨5,2,0⟩,[16384,-360448,2293760,2097152,-75137024,255655936,-106233856,-802422784,1116487680,-191070208]),(⟨5,2,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨5,3,0⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨6,0,0⟩,[8192,-262144,2760704,-7340032,-55951360,418643968,-796180480,-1168637952,8276516864,-16889937920,13911367680]),(⟨6,0,2⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904]),(⟨6,2,0⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[16384,-532480,6971392,-43474944,71770112,857407488,-7218888704,26575028224,-44047106048,-44407922688,451477594112,-1271867367424,2093994221568,-2145620574208,1276573761536,-360798715904,37131386880]),(⟨0,0,1⟩,[24576,-868352,12427264,-88965120,267026432,647102464,-9412624384,39480229888,-75758804992,-22571925504,548898676736,-1615005057024,2610887442432,-2500578410496,1259948376064,-206123008000]),(⟨0,0,2⟩,[-24576,606208,-4579328,-4718592,265945088,-1598177280,3443982336,5044961280,-48806846464,122378436608,-109852352512,-150592815104,555763875840,-645127847936,279088775168]),(⟨0,0,3⟩,[-49152,1540096,-17924096,83623936,61292544,-2460614656,11301879808,-19490537472,-22640345088,195535929344,-473933250560,608585777152,-385324564480,64406487040]),(⟨0,0,4⟩,[0,188416,-4759552,42426368,-120250368,-477904896,4408066048,-11462262784,2088386560,62200569856,-177608269824,231803772928,-125969457152]),(⟨0,0,5⟩,[24576,-671744,5890048,-8552448,-148717568,844136448,-1231241216,-2972188672,15771951104,-30914396160,27348000768,-4130832384]),(⟨0,0,6⟩,[8192,-262144,2760704,-7340032,-55951360,418643968,-796180480,-1168637952,8276516864,-16889937920,13911367680]),(⟨0,1,0⟩,[24576,-868352,12427264,-88965120,267026432,647102464,-9412624384,39480229888,-75758804992,-22571925504,548898676736,-1615005057024,2610887442432,-2500578410496,1259948376064,-206123008000]),(⟨0,1,1⟩,[16384,-737280,12976128,-115130368,511983616,-484147200,-6793494528,39150845952,-95276056576,56004296704,351792070656,-1224064745472,1960579481600,-1673371779072,616079392768]),(⟨0,1,2⟩,[-40960,1196032,-12886016,53821440,62275584,-1492779008,5643288576,-5494112256,-25758212096,109511065600,-186848452608,128337330176,48375627776,-99557212160]),(⟨0,1,3⟩,[-24576,966656,-14180352,94060544,-205209600,-901283840,6920093696,-16578609152,3088850944,82984681472,-229934358528,284211429376,-143557951488]),(⟨0,1,4⟩,[16384,-360448,2146304,4014080,-72843264,104988672,899907584,-4020666368,5709185024,4220354560,-26434093056,27036434432]),(⟨0,1,5⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨0,2,0⟩,[-24576,606208,-4579328,-4718592,265945088,-1598177280,3443982336,5044961280,-48806846464,122378436608,-109852352512,-150592815104,555763875840,-645127847936,279088775168]),(⟨0,2,1⟩,[-40960,1196032,-12886016,53821440,62275584,-1492779008,5643288576,-5494112256,-25758212096,109511065600,-186848452608,128337330176,48375627776,-99557212160]),(⟨0,2,2⟩,[16384,-212992,-1998848,51494912,-349618176,885882880,599195648,-8773074944,21742796800,-23283253248,-1021607936,25507184640,-12672450560]),(⟨0,2,3⟩,[24576,-638976,5185536,-5357568,-118505472,484343808,117063680,-4664557568,13814849536,-22735536128,17810628608,526991360]),(⟨0,2,4⟩,[-8192,196608,-1662976,3801088,31375360,-264765440,763183104,-467271680,-2147524608,4368695296,-2286018560]),(⟨0,2,5⟩,[16384,-360448,2293760,2097152,-75137024,255655936,-106233856,-802422784,1116487680,-191070208]),(⟨0,2,6⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904]),(⟨0,3,0⟩,[-49152,1540096,-17924096,83623936,61292544,-2460614656,11301879808,-19490537472,-22640345088,195535929344,-473933250560,608585777152,-385324564480,64406487040]),(⟨0,3,1⟩,[-24576,966656,-14180352,94060544,-205209600,-901283840,6920093696,-16578609152,3088850944,82984681472,-229934358528,284211429376,-143557951488]),(⟨0,3,2⟩,[24576,-638976,5185536,-5357568,-118505472,484343808,117063680,-4664557568,13814849536,-22735536128,17810628608,526991360]),(⟨0,3,3⟩,[-16384,393216,-3850240,22282240,-80904192,63963136,932872192,-4522770432,11124260864,-19353960448,17723310080]),(⟨0,3,4⟩,[16384,-294912,720896,15466496,-117604352,242417664,222494720,-1185415168,554975232,736985088]),(⟨0,3,5⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨0,4,0⟩,[0,188416,-4759552,42426368,-120250368,-477904896,4408066048,-11462262784,2088386560,62200569856,-177608269824,231803772928,-125969457152]),(⟨0,4,1⟩,[16384,-360448,2146304,4014080,-72843264,104988672,899907584,-4020666368,5709185024,4220354560,-26434093056,27036434432]),(⟨0,4,2⟩,[-8192,196608,-1662976,3801088,31375360,-264765440,763183104,-467271680,-2147524608,4368695296,-2286018560]),(⟨0,4,3⟩,[16384,-294912,720896,15466496,-117604352,242417664,222494720,-1185415168,554975232,736985088]),(⟨0,4,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨0,5,0⟩,[24576,-671744,5890048,-8552448,-148717568,844136448,-1231241216,-2972188672,15771951104,-30914396160,27348000768,-4130832384]),(⟨0,5,1⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨0,5,2⟩,[16384,-360448,2293760,2097152,-75137024,255655936,-106233856,-802422784,1116487680,-191070208]),(⟨0,5,3⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨0,6,0⟩,[8192,-262144,2760704,-7340032,-55951360,418643968,-796180480,-1168637952,8276516864,-16889937920,13911367680]),(⟨0,6,2⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904]),(⟨1,0,0⟩,[24576,-868352,12427264,-88965120,267026432,647102464,-9412624384,39480229888,-75758804992,-22571925504,548898676736,-1615005057024,2610887442432,-2500578410496,1259948376064,-206123008000]),(⟨1,0,1⟩,[16384,-737280,12976128,-115130368,511983616,-484147200,-6793494528,39150845952,-95276056576,56004296704,351792070656,-1224064745472,1960579481600,-1673371779072,616079392768]),(⟨1,0,2⟩,[-40960,1196032,-12886016,53821440,62275584,-1492779008,5643288576,-5494112256,-25758212096,109511065600,-186848452608,128337330176,48375627776,-99557212160]),(⟨1,0,3⟩,[-24576,966656,-14180352,94060544,-205209600,-901283840,6920093696,-16578609152,3088850944,82984681472,-229934358528,284211429376,-143557951488]),(⟨1,0,4⟩,[16384,-360448,2146304,4014080,-72843264,104988672,899907584,-4020666368,5709185024,4220354560,-26434093056,27036434432]),(⟨1,0,5⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨1,1,0⟩,[16384,-737280,12976128,-115130368,511983616,-484147200,-6793494528,39150845952,-95276056576,56004296704,351792070656,-1224064745472,1960579481600,-1673371779072,616079392768]),(⟨1,1,1⟩,[0,-196608,6389760,-82280448,526221312,-1553498112,-441778176,19953942528,-70507364352,103195607040,31398789120,-389595365376,630112616448,-369720852480]),(⟨1,1,2⟩,[-16384,671744,-10223616,72269824,-208846848,-221085696,3307470848,-9329082368,8472510464,16659202048,-54726492160,47801155584,-4435558400]),(⟨1,1,3⟩,[0,131072,-3604480,36503552,-155975680,114294784,1419640832,-5582749696,7604535296,6007685120,-34751840256,33901314048]),(⟨1,2,0⟩,[-40960,1196032,-12886016,53821440,62275584,-1492779008,5643288576,-5494112256,-25758212096,109511065600,-186848452608,128337330176,48375627776,-99557212160]),(⟨1,2,1⟩,[-16384,671744,-10223616,72269824,-208846848,-221085696,3307470848,-9329082368,8472510464,16659202048,-54726492160,47801155584,-4435558400]),(⟨1,2,2⟩,[32768,-786432,6389760,-14057472,-74383360,477233152,-865665024,-275185664,3726016512,-5464260608,-724598784,5759401984]),(⟨1,2,3⟩,[-8192,196608,-1662976,3801088,31375360,-264765440,763183104,-467271680,-2147524608,4368695296,-2286018560]),(⟨1,2,4⟩,[0,65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨1,2,5⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨1,3,0⟩,[-24576,966656,-14180352,94060544,-205209600,-901283840,6920093696,-16578609152,3088850944,82984681472,-229934358528,284211429376,-143557951488]),(⟨1,3,1⟩,[0,131072,-3604480,36503552,-155975680,114294784,1419640832,-5582749696,7604535296,6007685120,-34751840256,33901314048]),(⟨1,3,2⟩,[-8192,196608,-1662976,3801088,31375360,-264765440,763183104,-467271680,-2147524608,4368695296,-2286018560]),(⟨1,3,3⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨1,3,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨1,4,0⟩,[16384,-360448,2146304,4014080,-72843264,104988672,899907584,-4020666368,5709185024,4220354560,-26434093056,27036434432]),(⟨1,4,2⟩,[0,65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨1,4,3⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨1,5,0⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨1,5,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,0,0⟩,[-24576,606208,-4579328,-4718592,265945088,-1598177280,3443982336,5044961280,-48806846464,122378436608,-109852352512,-150592815104,555763875840,-645127847936,279088775168]),(⟨2,0,1⟩,[-40960,1196032,-12886016,53821440,62275584,-1492779008,5643288576,-5494112256,-25758212096,109511065600,-186848452608,128337330176,48375627776,-99557212160]),(⟨2,0,2⟩,[16384,-212992,-1998848,51494912,-349618176,885882880,599195648,-8773074944,21742796800,-23283253248,-1021607936,25507184640,-12672450560]),(⟨2,0,3⟩,[24576,-638976,5185536,-5357568,-118505472,484343808,117063680,-4664557568,13814849536,-22735536128,17810628608,526991360]),(⟨2,0,4⟩,[-8192,196608,-1662976,3801088,31375360,-264765440,763183104,-467271680,-2147524608,4368695296,-2286018560]),(⟨2,0,5⟩,[16384,-360448,2293760,2097152,-75137024,255655936,-106233856,-802422784,1116487680,-191070208]),(⟨2,0,6⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904]),(⟨2,1,0⟩,[-40960,1196032,-12886016,53821440,62275584,-1492779008,5643288576,-5494112256,-25758212096,109511065600,-186848452608,128337330176,48375627776,-99557212160]),(⟨2,1,1⟩,[-16384,671744,-10223616,72269824,-208846848,-221085696,3307470848,-9329082368,8472510464,16659202048,-54726492160,47801155584,-4435558400]),(⟨2,1,2⟩,[32768,-786432,6389760,-14057472,-74383360,477233152,-865665024,-275185664,3726016512,-5464260608,-724598784,5759401984]),(⟨2,1,3⟩,[-8192,196608,-1662976,3801088,31375360,-264765440,763183104,-467271680,-2147524608,4368695296,-2286018560]),(⟨2,1,4⟩,[0,65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,1,5⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,2,0⟩,[16384,-212992,-1998848,51494912,-349618176,885882880,599195648,-8773074944,21742796800,-23283253248,-1021607936,25507184640,-12672450560]),(⟨2,2,1⟩,[32768,-786432,6389760,-14057472,-74383360,477233152,-865665024,-275185664,3726016512,-5464260608,-724598784,5759401984]),(⟨2,2,3⟩,[32768,-720896,4587520,4194304,-150274048,511311872,-212467712,-1604845568,2232975360,-382140416]),(⟨2,2,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,3,0⟩,[24576,-638976,5185536,-5357568,-118505472,484343808,117063680,-4664557568,13814849536,-22735536128,17810628608,526991360]),(⟨2,3,1⟩,[-8192,196608,-1662976,3801088,31375360,-264765440,763183104,-467271680,-2147524608,4368695296,-2286018560]),(⟨2,3,2⟩,[32768,-720896,4587520,4194304,-150274048,511311872,-212467712,-1604845568,2232975360,-382140416]),(⟨2,3,3⟩,[65536,-1572864,12320768,-21495808,-161087488,731381760,-428081152,-2125987840,2799763456]),(⟨2,4,0⟩,[-8192,196608,-1662976,3801088,31375360,-264765440,763183104,-467271680,-2147524608,4368695296,-2286018560]),(⟨2,4,1⟩,[0,65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,4,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,5,0⟩,[16384,-360448,2293760,2097152,-75137024,255655936,-106233856,-802422784,1116487680,-191070208]),(⟨2,5,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨2,6,0⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904]),(⟨3,0,0⟩,[-49152,1540096,-17924096,83623936,61292544,-2460614656,11301879808,-19490537472,-22640345088,195535929344,-473933250560,608585777152,-385324564480,64406487040]),(⟨3,0,1⟩,[-24576,966656,-14180352,94060544,-205209600,-901283840,6920093696,-16578609152,3088850944,82984681472,-229934358528,284211429376,-143557951488]),(⟨3,0,2⟩,[24576,-638976,5185536,-5357568,-118505472,484343808,117063680,-4664557568,13814849536,-22735536128,17810628608,526991360]),(⟨3,0,3⟩,[-16384,393216,-3850240,22282240,-80904192,63963136,932872192,-4522770432,11124260864,-19353960448,17723310080]),(⟨3,0,4⟩,[16384,-294912,720896,15466496,-117604352,242417664,222494720,-1185415168,554975232,736985088]),(⟨3,0,5⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨3,1,0⟩,[-24576,966656,-14180352,94060544,-205209600,-901283840,6920093696,-16578609152,3088850944,82984681472,-229934358528,284211429376,-143557951488]),(⟨3,1,1⟩,[0,131072,-3604480,36503552,-155975680,114294784,1419640832,-5582749696,7604535296,6007685120,-34751840256,33901314048]),(⟨3,1,2⟩,[-8192,196608,-1662976,3801088,31375360,-264765440,763183104,-467271680,-2147524608,4368695296,-2286018560]),(⟨3,1,3⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,1,4⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,2,0⟩,[24576,-638976,5185536,-5357568,-118505472,484343808,117063680,-4664557568,13814849536,-22735536128,17810628608,526991360]),(⟨3,2,1⟩,[-8192,196608,-1662976,3801088,31375360,-264765440,763183104,-467271680,-2147524608,4368695296,-2286018560]),(⟨3,2,2⟩,[32768,-720896,4587520,4194304,-150274048,511311872,-212467712,-1604845568,2232975360,-382140416]),(⟨3,2,3⟩,[65536,-1572864,12320768,-21495808,-161087488,731381760,-428081152,-2125987840,2799763456]),(⟨3,3,0⟩,[-16384,393216,-3850240,22282240,-80904192,63963136,932872192,-4522770432,11124260864,-19353960448,17723310080]),(⟨3,3,1⟩,[0,131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,3,2⟩,[65536,-1572864,12320768,-21495808,-161087488,731381760,-428081152,-2125987840,2799763456]),(⟨3,4,0⟩,[16384,-294912,720896,15466496,-117604352,242417664,222494720,-1185415168,554975232,736985088]),(⟨3,4,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨3,5,0⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨4,0,0⟩,[0,188416,-4759552,42426368,-120250368,-477904896,4408066048,-11462262784,2088386560,62200569856,-177608269824,231803772928,-125969457152]),(⟨4,0,1⟩,[16384,-360448,2146304,4014080,-72843264,104988672,899907584,-4020666368,5709185024,4220354560,-26434093056,27036434432]),(⟨4,0,2⟩,[-8192,196608,-1662976,3801088,31375360,-264765440,763183104,-467271680,-2147524608,4368695296,-2286018560]),(⟨4,0,3⟩,[16384,-294912,720896,15466496,-117604352,242417664,222494720,-1185415168,554975232,736985088]),(⟨4,0,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,1,0⟩,[16384,-360448,2146304,4014080,-72843264,104988672,899907584,-4020666368,5709185024,4220354560,-26434093056,27036434432]),(⟨4,1,2⟩,[0,65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,1,3⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,2,0⟩,[-8192,196608,-1662976,3801088,31375360,-264765440,763183104,-467271680,-2147524608,4368695296,-2286018560]),(⟨4,2,1⟩,[0,65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,2,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,3,0⟩,[16384,-294912,720896,15466496,-117604352,242417664,222494720,-1185415168,554975232,736985088]),(⟨4,3,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨4,4,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,0,0⟩,[24576,-671744,5890048,-8552448,-148717568,844136448,-1231241216,-2972188672,15771951104,-30914396160,27348000768,-4130832384]),(⟨5,0,1⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨5,0,2⟩,[16384,-360448,2293760,2097152,-75137024,255655936,-106233856,-802422784,1116487680,-191070208]),(⟨5,0,3⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨5,1,0⟩,[8192,-262144,3022848,-14680064,15876096,121896960,-499433472,625475584,566861824,-2844262400,2763694080]),(⟨5,1,2⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨5,2,0⟩,[16384,-360448,2293760,2097152,-75137024,255655936,-106233856,-802422784,1116487680,-191070208]),(⟨5,2,1⟩,[16384,-393216,3342336,-10616832,-3309568,82182144,-95748096,-140378112,232013824]),(⟨5,3,0⟩,[32768,-786432,6160384,-10747904,-80543744,365690880,-214040576,-1062993920,1399881728]),(⟨6,0,0⟩,[8192,-262144,2760704,-7340032,-55951360,418643968,-796180480,-1168637952,8276516864,-16889937920,13911367680]),(⟨6,0,2⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904]),(⟨6,2,0⟩,[16384,-393216,2818048,-131072,-77234176,283508736,-118292480,-922615808,1167867904])]


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
    (Poly.add (Poly.scale (K.ofRat r600) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 3 7).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r599*r599 : ℚ)=r600 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 3 7 r599 r599 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 3=7 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 3 7).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C088

#print axioms Coulomb8.Columns.C088.sound
