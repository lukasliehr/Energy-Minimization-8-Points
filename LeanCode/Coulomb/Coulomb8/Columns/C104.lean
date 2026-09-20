import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C104

def r0 : ℚ := { num := 196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -8060928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 148504576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := -1631453184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := 11940134912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := -61397008384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := 226907783168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := -86156967936, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 1131774083072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -1461870067712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 1397769502720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -1660148514816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 174802337792, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -3865843204096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 2361860161536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -14033289216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := -405861367808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := 11688738816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -8781824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 10158080, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -1986330624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 14917369856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -11001266176, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 279016374272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -708306468864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 176205594624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -1447399915520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 1369209241600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -2047310233600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 3807745998848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -4265211985920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 1851825979392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 386291400704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -44212355072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -393216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 13697024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -205783040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 1749942272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := -1317273600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := 30457135104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -57505742848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 31989825536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 103544389632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -218127990784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 102293569536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -1911947264, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 698707607552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -1067038474240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 49484136448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 3520724992, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := 17301504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := -316801024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := 3222405120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -1195376640, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 11866865664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -220457074688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := 363473403904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -339526156288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 234210197504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -529625907200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 1063664615424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := -775826964480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -27756462080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 13768851456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -4063232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 15073280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := 17104896, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := -3919773696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := 1303707648, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := -69339971584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 121705201664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -107649105920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := 69518229504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := -216657428480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := 60952608768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := -14383120384, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -7270105088, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := -8519680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := 142934016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := -1236271104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := 123731968, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := -16991911936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := 24561975296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := -11312562176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := 2050686976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := -44136792064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := 61678878720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 42467328, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -182321152, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -1572864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 43384832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -475922432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := 2688024576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := -8259108864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := 12707954688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -6360924160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 2727870464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -28025290752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 35888955392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 278790144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 131072, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := -35717120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := 369819648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := -56688640, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := 15599534080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := -64868646912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 3968532480, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -402126209024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 533564096512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := -443083849728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 549620613120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -1573654298624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 2692521525248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -1860042424320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := -18762235904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := 11175985152, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := -2686976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -327680, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 563412992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -5058920448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 24347672576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := -4212850688, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := 135230783488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -175309258752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 191359287296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -4300931072, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 174989049856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := -137840230400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := 45238321152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -7251230720, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := -4194304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := 59244544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -503054336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 2932015104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -12339118080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 36991074304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := -4351066112, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := 5112856576, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := -54568943616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := 13012434944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := -293677563904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := 372628979712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := -108118147072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -10151460864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := -131072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 23003136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -235864064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 1281556480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -3840999424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 5051908096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := 4839309312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := -29519642624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 38584975360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 9743564800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -6727991296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -8499167232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 153550848, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := 1966080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := -196608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 139591680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -59506688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 373030912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := 68550656, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := -3108765696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := 706150400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := 415891456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 3342794752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := -1047134208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := -1179648, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := 524288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -11665408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 99221504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -56098816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := 571998208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 763625472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := -3165913088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := 947388416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := 214958080, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := 4296933376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -92930048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 393216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -13631488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 27918336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := -1504182272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := 6724517888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -17346068480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := 22603890688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -6747586560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := -135659520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -51594133504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 90776141824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := -932708352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -2157707264, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 2088239104, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 1769472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := 33292288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := -627507200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := 4270653440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -14976942080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 27684503552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := -3275882496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 9343270912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -35361718272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := 9858449408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := -7548502016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := 794755072, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -1048576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := 25165824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := -12582912, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := 679477248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 211812352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -5259657216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := 6127878144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 75497472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := -131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 3932160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -49938432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := 365953024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := -1784938496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := 6122110976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -14187495424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 1129316352, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -11309547520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 11278221312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -49364992000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 57118031872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := 276824064, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := 1179648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := -33226752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := 398917632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := -385744896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := 11322261504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -29292822528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 36772577280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := 34303377408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -13943832576, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 22720217088, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := -1175912448, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -565395456000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := 232868806656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := 159782731776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := -1408303104, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := 65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := -2097152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := 27787264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := -200146944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := 861601792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := -2234646528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := 2949513216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := 1255407616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := -14926020608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 33141030912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -35917135872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := 26088177664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -274006016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := -2785673216, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := 243138560, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := -1310720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -345505792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := 1890320384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := -5633212416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := 7066877952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := 7961837568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -41138257920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := 45877559296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := 18518638592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := -39765671936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := -16344940544, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := 211025920, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := 50331648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := -25165824, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := 1358954496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := 423624704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := -10519314432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := 12255756288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := 150994944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := -417595392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := 8126464, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := 7995392, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := -2429288448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := 131137536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := -2348417024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := 9470672896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := 236322816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := -19005440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := 1048576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := -23330816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := 198443008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := -112197632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := 1143996416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 1527250944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -6331826176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := 1894776832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := 429916160, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := 8593866752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := -185860096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := 786432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := -25952256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := 353370112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -2551447552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := 10297540608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := -2993160192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := 4887412736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 71885651968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -146841796608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 98350399488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := 1035993088, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := -23330816, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -24117248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 298844160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := -1918894080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 6656884736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -10401873920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := -5405409280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := 49155145728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := -71663091712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := 3834642432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := 16777216, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := -786432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := 22544384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := -248512512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := 75497472, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := -393740288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -701497344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 11931746304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := -1975517184, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := 3407872, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := 3670016, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 23068672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -5242880, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 77594624, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -2722627584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := -1147142144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := 12124684288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := -1700790272, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := -786432, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := -262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := 6815744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := -9699328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := 18874368, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := -661127168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := -13631488, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := 647495680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := -10022289408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := 359923712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := 27787264, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := 262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := -6291456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := 3145728, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := -169869312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := -52953088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := 1314914304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := -1531969536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := -18874368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := 98304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := -4030464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := 74252288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := -815726592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := 5970067456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := -30698504192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := 113453891584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := -43078483968, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := 565887041536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := -730935033856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := 698884751360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := -830074257408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := 87401168896, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := -1932921602048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := 1180930080768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := -7016644608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := -202930683904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := 5844369408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := -4390912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := 5079040, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := -993165312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := 7458684928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := -5500633088, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := 139508187136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := -354153234432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := 88102797312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := -723699957760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := 684604620800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := -1023655116800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := 1903872999424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := -2132605992960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := 925912989696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := 193145700352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := -22106177536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := 6848512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := -102891520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 874971136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := -658636800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := 15228567552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := -28752871424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := 15994912768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := 51772194816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := -109063995392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := 51146784768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := -955973632, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := 349353803776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := -533519237120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := 24742068224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := 1760362496, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := 8650752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := -158400512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := 1611202560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := -597688320, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := 5933432832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := -110228537344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := 181736701952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := -169763078144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := 117105098752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := -264812953600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := 531832307712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := -387913482240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := -13878231040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := 6884425728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := -2031616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := 7536640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := 8552448, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := -1959886848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := 651853824, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := -34669985792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := 60852600832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := -53824552960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := 34759114752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := -108328714240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := 30476304384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := -7191560192, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := -3635052544, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := -4259840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := 71467008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := -618135552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := 61865984, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := -8495955968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := 12280987648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := -5656281088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := 1025343488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := -22068396032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := 30839439360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := 21233664, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := -91160576, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := 21692416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := -237961216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := 1344012288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := -4129554432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := 6353977344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r450 : ℚ := { num := -3180462080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r451 : ℚ := { num := 1363935232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r452 : ℚ := { num := -14012645376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r453 : ℚ := { num := 17944477696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r454 : ℚ := { num := 139395072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r455 : ℚ := { num := -32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r456 : ℚ := { num := 65536, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r457 : ℚ := { num := -17858560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r458 : ℚ := { num := 184909824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r459 : ℚ := { num := -28344320, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r460 : ℚ := { num := 7799767040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r461 : ℚ := { num := -32434323456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r462 : ℚ := { num := 1984266240, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r463 : ℚ := { num := -201063104512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r464 : ℚ := { num := 266782048256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r465 : ℚ := { num := -221541924864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r466 : ℚ := { num := 274810306560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r467 : ℚ := { num := -786827149312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r468 : ℚ := { num := 1346260762624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r469 : ℚ := { num := -930021212160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r470 : ℚ := { num := -9381117952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r471 : ℚ := { num := 5587992576, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r472 : ℚ := { num := -1343488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r473 : ℚ := { num := -163840, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r474 : ℚ := { num := 281706496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r475 : ℚ := { num := -2529460224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r476 : ℚ := { num := 12173836288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r477 : ℚ := { num := -2106425344, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r478 : ℚ := { num := 67615391744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r479 : ℚ := { num := -87654629376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r480 : ℚ := { num := 95679643648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r481 : ℚ := { num := -2150465536, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r482 : ℚ := { num := 87494524928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r483 : ℚ := { num := -68920115200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r484 : ℚ := { num := 22619160576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r485 : ℚ := { num := -3625615360, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r486 : ℚ := { num := 29622272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r487 : ℚ := { num := -251527168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r488 : ℚ := { num := 1466007552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r489 : ℚ := { num := -6169559040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r490 : ℚ := { num := 18495537152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r491 : ℚ := { num := -2175533056, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r492 : ℚ := { num := 2556428288, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r493 : ℚ := { num := -27284471808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r494 : ℚ := { num := 6506217472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r495 : ℚ := { num := -146838781952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r496 : ℚ := { num := 186314489856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r497 : ℚ := { num := -54059073536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r498 : ℚ := { num := -5075730432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r499 : ℚ := { num := -65536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r500 : ℚ := { num := 11501568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r501 : ℚ := { num := -117932032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r502 : ℚ := { num := 640778240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r503 : ℚ := { num := -1920499712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r504 : ℚ := { num := 2525954048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r505 : ℚ := { num := 2419654656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r506 : ℚ := { num := -14759821312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r507 : ℚ := { num := 19292487680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r508 : ℚ := { num := 4871782400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r509 : ℚ := { num := -3363995648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r510 : ℚ := { num := -4249583616, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r511 : ℚ := { num := 76775424, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r512 : ℚ := { num := 983040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r513 : ℚ := { num := -98304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r514 : ℚ := { num := 69795840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r515 : ℚ := { num := -29753344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r516 : ℚ := { num := 186515456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r517 : ℚ := { num := 34275328, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r518 : ℚ := { num := -1554382848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r519 : ℚ := { num := 353075200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r520 : ℚ := { num := 207945728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r521 : ℚ := { num := 1671397376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r522 : ℚ := { num := -523567104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r523 : ℚ := { num := -589824, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r524 : ℚ := { num := -5832704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r525 : ℚ := { num := 49610752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r526 : ℚ := { num := -28049408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r527 : ℚ := { num := 285999104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r528 : ℚ := { num := 381812736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r529 : ℚ := { num := -1582956544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r530 : ℚ := { num := 473694208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r531 : ℚ := { num := 107479040, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r532 : ℚ := { num := 2148466688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r533 : ℚ := { num := -46465024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r534 : ℚ := { num := -6815744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r535 : ℚ := { num := 13959168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r536 : ℚ := { num := -752091136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r537 : ℚ := { num := 3362258944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r538 : ℚ := { num := -8673034240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r539 : ℚ := { num := 11301945344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r540 : ℚ := { num := -3373793280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r541 : ℚ := { num := -67829760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r542 : ℚ := { num := -25797066752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r543 : ℚ := { num := 45388070912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r544 : ℚ := { num := -466354176, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r545 : ℚ := { num := -1078853632, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r546 : ℚ := { num := 1044119552, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r547 : ℚ := { num := -98304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r548 : ℚ := { num := 884736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r549 : ℚ := { num := 16646144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r550 : ℚ := { num := -313753600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r551 : ℚ := { num := 2135326720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r552 : ℚ := { num := -7488471040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r553 : ℚ := { num := 13842251776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r554 : ℚ := { num := -1637941248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r555 : ℚ := { num := 4671635456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r556 : ℚ := { num := -17680859136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r557 : ℚ := { num := 4929224704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r558 : ℚ := { num := -3774251008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r559 : ℚ := { num := 397377536, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r560 : ℚ := { num := -524288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r561 : ℚ := { num := 12582912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r562 : ℚ := { num := -6291456, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r563 : ℚ := { num := 339738624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r564 : ℚ := { num := 105906176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r565 : ℚ := { num := -2629828608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r566 : ℚ := { num := 3063939072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r567 : ℚ := { num := 37748736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r568 : ℚ := { num := -24969216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r569 : ℚ := { num := 182976512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r570 : ℚ := { num := -892469248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r571 : ℚ := { num := 3061055488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r572 : ℚ := { num := -7093747712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r573 : ℚ := { num := 564658176, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r574 : ℚ := { num := -5654773760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r575 : ℚ := { num := 5639110656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r576 : ℚ := { num := -24682496000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r577 : ℚ := { num := 28559015936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r578 : ℚ := { num := 138412032, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r579 : ℚ := { num := 589824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r580 : ℚ := { num := -16613376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r581 : ℚ := { num := 199458816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r582 : ℚ := { num := -192872448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r583 : ℚ := { num := 5661130752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r584 : ℚ := { num := -14646411264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r585 : ℚ := { num := 18386288640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r586 : ℚ := { num := 17151688704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r587 : ℚ := { num := -6971916288, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r588 : ℚ := { num := 11360108544, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r589 : ℚ := { num := -587956224, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r590 : ℚ := { num := -282697728000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r591 : ℚ := { num := 116434403328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r592 : ℚ := { num := 79891365888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r593 : ℚ := { num := -704151552, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r594 : ℚ := { num := 32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r595 : ℚ := { num := 13893632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r596 : ℚ := { num := -100073472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r597 : ℚ := { num := 430800896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r598 : ℚ := { num := -1117323264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r599 : ℚ := { num := 1474756608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r600 : ℚ := { num := 627703808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r601 : ℚ := { num := -7463010304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r602 : ℚ := { num := 16570515456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r603 : ℚ := { num := -17958567936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r604 : ℚ := { num := 13044088832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r605 : ℚ := { num := -137003008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r606 : ℚ := { num := -1392836608, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r607 : ℚ := { num := 121569280, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r608 : ℚ := { num := -655360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r609 : ℚ := { num := -172752896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r610 : ℚ := { num := 945160192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r611 : ℚ := { num := -2816606208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r612 : ℚ := { num := 3533438976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r613 : ℚ := { num := 3980918784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r614 : ℚ := { num := -20569128960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r615 : ℚ := { num := 22938779648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r616 : ℚ := { num := 9259319296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r617 : ℚ := { num := -19882835968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r618 : ℚ := { num := -8172470272, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r619 : ℚ := { num := 105512960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r620 : ℚ := { num := -208797696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r621 : ℚ := { num := 4063232, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r622 : ℚ := { num := 3997696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r623 : ℚ := { num := -1214644224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r624 : ℚ := { num := 65568768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r625 : ℚ := { num := -1174208512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r626 : ℚ := { num := 4735336448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r627 : ℚ := { num := 118161408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r628 : ℚ := { num := -9502720, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r629 : ℚ := { num := -12976128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r630 : ℚ := { num := 176685056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r631 : ℚ := { num := -1275723776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r632 : ℚ := { num := 5148770304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r633 : ℚ := { num := -1496580096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r634 : ℚ := { num := 2443706368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r635 : ℚ := { num := 35942825984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r636 : ℚ := { num := -73420898304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r637 : ℚ := { num := 49175199744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r638 : ℚ := { num := 517996544, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r639 : ℚ := { num := -11665408, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r640 : ℚ := { num := -12058624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r641 : ℚ := { num := 149422080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r642 : ℚ := { num := -959447040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r643 : ℚ := { num := 3328442368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r644 : ℚ := { num := -5200936960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r645 : ℚ := { num := -2702704640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r646 : ℚ := { num := 24577572864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r647 : ℚ := { num := -35831545856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r648 : ℚ := { num := 1917321216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r649 : ℚ := { num := 8388608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r650 : ℚ := { num := 11272192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r651 : ℚ := { num := -124256256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r652 : ℚ := { num := 37748736, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r653 : ℚ := { num := -196870144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r654 : ℚ := { num := -350748672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r655 : ℚ := { num := 5965873152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r656 : ℚ := { num := -987758592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r657 : ℚ := { num := 1703936, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r658 : ℚ := { num := 1835008, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r659 : ℚ := { num := 11534336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r660 : ℚ := { num := -2621440, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r661 : ℚ := { num := 38797312, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r662 : ℚ := { num := -1361313792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r663 : ℚ := { num := -573571072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r664 : ℚ := { num := 6062342144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r665 : ℚ := { num := -850395136, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r666 : ℚ := { num := -393216, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r667 : ℚ := { num := 3407872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r668 : ℚ := { num := -4849664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r669 : ℚ := { num := 9437184, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r670 : ℚ := { num := -330563584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r671 : ℚ := { num := -6815744, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r672 : ℚ := { num := 323747840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r673 : ℚ := { num := -5011144704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r674 : ℚ := { num := 179961856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r675 : ℚ := { num := 13893632, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r676 : ℚ := { num := -3145728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r677 : ℚ := { num := 1572864, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r678 : ℚ := { num := -84934656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r679 : ℚ := { num := -26476544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r680 : ℚ := { num := 657457152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r681 : ℚ := { num := -765984768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r682 : ℚ := { num := -9437184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r683 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r684 : ℚ := { num := 1, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17],[0,r0,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33],[0,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49],[0,r34,r50,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63],[0,r0,r64,r65,r66,r67,r68,r69,r70,r71,r72,r73,r74,r75,r76],[0,r0,r77,r78,r79,r80,r81,r82,r83,r84,r85,r86,r87,r88],[0,0,r89,r90,r91,r92,r93,r94,r95,r96,r97,r98,r99],[],[],[],[],[],[],[r100,r101,r102,r103,r104,r105,r106,r107,r108,r109,r110,r111,r112,r113,r114,r115,r116],[0,r0,r117,r118,r119,r120,r121,r122,r123,r124,r125,r126,r127,r128,r129,r130],[r131,r132,r133,r134,r135,r136,r137,r138,r139,r140,r141,r142,r143,r144,r145],[0,r146,r147,r148,r149,r150,r151,r152,r153,r154,r155,r156,r157,r158],[r100,r159,r160,r161,r162,r163,r164,r165,r166,r167,r168,r169,r170],[0,r171,r172,r173,r174,r175,r176,r177,r178,r179,r180,r181],[],[],[],[],[],[0,r182,r183,r184,r185,r186,r187,r188,r189,r190,r191,r192,r193,r194,r195],[0,r196,r197,r198,r199,r200,r201,r202,r203,r204,r205,r206,r207,r208],[0,0,0,0,r209,r210,r211,r212,r213,r214,r215,r216,-1048576],[],[],[],[],[],[],[r217,r218,r219,r220,r221,r222,r223,r224,r225,r226,r227,r228,r229],[0,r171,r172,r173,r174,r175,r176,r177,r178,r179,r180,r181],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,r230,r231,r232,r233,r234,r235,r236,r237,r238,r239,r240,r241,r242,r243,r244],[r245,r246,r247,r248,r249,r250,r251,r252,r253,r254,r255,r256,r257,r258,r259],[0,r260,r198,r261,r262,r263,r264,r265,r266,r267,r268,r269,r270,r271],[0,0,0,0,r246,r272,r273,r274,r275,r276,r277,r278,-2097152],[],[],[],[],[],[],[],[r100,r159,r160,r161,r279,r280,r281,r282,r283,r284,r285,r286,r287],[],[],[],[],[],[],[0,r288,r289,r290,r291,r292,r293,r294,r295,r296,r297,r298],[],[],[],[],[],[],[],[],[],[],[],[0,r299,r300,r301,r302,r303,r304,r305,r306,r307,r308,r309,r310],[0,r299,r311,r312,r313,r314,r315,r316,r317,r318,r319,r320],[0,r321,r322,r323,r324,r325,r326,r327,r328,r329,r330],[0,r321,r331,r332,r333,r334,r335,r336,r337,r338],[],[],[],[r339,r340,r341,r342,r343,r344,r345,r346,r347,r348,-1835008],[],[r349,r350,r351,r352,r353,r354,r355,r356,262144],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,r357,r358,r359,r360,r361,r362,r363,r364,r365,r366,r367,r368,r369,r370,r371,r372,r373,r374]),(⟨0,0,1⟩,[0,r357,r375,r376,r377,r378,r379,r380,r381,r382,r383,r384,r385,r386,r387,r388,r389,r390]),(⟨0,0,2⟩,[0,r196,r391,r392,r393,r394,r395,r396,r397,r398,r399,r400,r401,r402,r403,r404,r405]),(⟨0,0,3⟩,[0,r196,r406,r407,r408,r409,r410,r411,r412,r413,r414,r415,r416,r417,r418,r419]),(⟨0,0,4⟩,[0,r357,r420,r421,r422,r423,r424,r425,r426,r427,r428,r429,r430,r431,r432]),(⟨0,0,5⟩,[0,r357,r433,r434,r435,r436,r437,r438,r439,r440,r441,r442,r443,r444]),(⟨0,0,6⟩,[0,0,r321,r445,r446,r447,r448,r449,r450,r451,r452,r453,r454]),(⟨0,1,0⟩,[0,r357,r375,r376,r377,r378,r379,r380,r381,r382,r383,r384,r385,r386,r387,r388,r389,r390]),(⟨0,1,1⟩,[r455,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466,r467,r468,r469,r470,r471]),(⟨0,1,2⟩,[0,r357,r472,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483,r484,r485]),(⟨0,1,3⟩,[r245,r246,r486,r487,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498]),(⟨0,1,4⟩,[0,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508,r509,r510,r511]),(⟨0,1,5⟩,[r455,r512,r513,r514,r515,r516,r517,r518,r519,r520,r521,r522,r523]),(⟨0,1,6⟩,[0,r349,r524,r525,r526,r527,r528,r529,r530,r531,r532,r533]),(⟨0,2,0⟩,[0,r196,r391,r392,r393,r394,r395,r396,r397,r398,r399,r400,r401,r402,r403,r404,r405]),(⟨0,2,1⟩,[0,r357,r472,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483,r484,r485]),(⟨0,2,2⟩,[0,r0,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543,r544,r545,r546]),(⟨0,2,3⟩,[0,r547,r548,r549,r550,r551,r552,r553,r554,r555,r556,r557,r558,r559]),(⟨0,2,4⟩,[0,0,0,0,r560,r561,r562,r563,r564,r565,r566,r567,-524288]),(⟨0,3,0⟩,[0,r196,r406,r407,r408,r409,r410,r411,r412,r413,r414,r415,r416,r417,r418,r419]),(⟨0,3,1⟩,[r245,r246,r486,r487,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498]),(⟨0,3,2⟩,[0,r547,r548,r549,r550,r551,r552,r553,r554,r555,r556,r557,r558,r559]),(⟨0,3,3⟩,[r100,r159,r568,r569,r570,r571,r572,r573,r574,r575,r576,r577,r578]),(⟨0,3,4⟩,[0,r349,r524,r525,r526,r527,r528,r529,r530,r531,r532,r533]),(⟨0,4,0⟩,[0,r357,r420,r421,r422,r423,r424,r425,r426,r427,r428,r429,r430,r431,r432]),(⟨0,4,1⟩,[0,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508,r509,r510,r511]),(⟨0,4,2⟩,[0,0,0,0,r560,r561,r562,r563,r564,r565,r566,r567,-524288]),(⟨0,4,3⟩,[0,r349,r524,r525,r526,r527,r528,r529,r530,r531,r532,r533]),(⟨0,5,0⟩,[0,r357,r433,r434,r435,r436,r437,r438,r439,r440,r441,r442,r443,r444]),(⟨0,5,1⟩,[r455,r512,r513,r514,r515,r516,r517,r518,r519,r520,r521,r522,r523]),(⟨0,6,0⟩,[0,0,r321,r445,r446,r447,r448,r449,r450,r451,r452,r453,r454]),(⟨0,6,1⟩,[0,r349,r524,r525,r526,r527,r528,r529,r530,r531,r532,r533]),(⟨1,0,0⟩,[0,r357,r375,r376,r377,r378,r379,r380,r381,r382,r383,r384,r385,r386,r387,r388,r389,r390]),(⟨1,0,1⟩,[r455,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466,r467,r468,r469,r470,r471]),(⟨1,0,2⟩,[0,r357,r472,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483,r484,r485]),(⟨1,0,3⟩,[r245,r246,r486,r487,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498]),(⟨1,0,4⟩,[0,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508,r509,r510,r511]),(⟨1,0,5⟩,[r455,r512,r513,r514,r515,r516,r517,r518,r519,r520,r521,r522,r523]),(⟨1,0,6⟩,[0,r349,r524,r525,r526,r527,r528,r529,r530,r531,r532,r533]),(⟨1,1,0⟩,[r455,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466,r467,r468,r469,r470,r471]),(⟨1,1,1⟩,[0,r579,r580,r581,r582,r583,r584,r585,r586,r587,r588,r589,r590,r591,r592,r593]),(⟨1,1,2⟩,[r594,r209,r595,r596,r597,r598,r599,r600,r601,r602,r603,r604,r605,r606,r607]),(⟨1,1,3⟩,[0,r608,r549,r609,r610,r611,r612,r613,r614,r615,r616,r617,r618,r619]),(⟨1,1,4⟩,[0,0,0,0,r209,r210,r211,r212,r213,r214,r215,r216,-1048576]),(⟨1,2,0⟩,[0,r357,r472,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483,r484,r485]),(⟨1,2,1⟩,[r594,r209,r595,r596,r597,r598,r599,r600,r601,r602,r603,r604,r605,r606,r607]),(⟨1,2,3⟩,[r455,r512,r513,r514,r620,r621,r622,r623,r624,r625,r626,r627,r628]),(⟨1,3,0⟩,[r245,r246,r486,r487,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498]),(⟨1,3,1⟩,[0,r608,r549,r609,r610,r611,r612,r613,r614,r615,r616,r617,r618,r619]),(⟨1,3,2⟩,[r455,r512,r513,r514,r620,r621,r622,r623,r624,r625,r626,r627,r628]),(⟨1,3,3⟩,[0,r171,r172,r173,r174,r175,r176,r177,r178,r179,r180,r181]),(⟨1,4,0⟩,[0,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508,r509,r510,r511]),(⟨1,4,1⟩,[0,0,0,0,r209,r210,r211,r212,r213,r214,r215,r216,-1048576]),(⟨1,5,0⟩,[r455,r512,r513,r514,r515,r516,r517,r518,r519,r520,r521,r522,r523]),(⟨1,6,0⟩,[0,r349,r524,r525,r526,r527,r528,r529,r530,r531,r532,r533]),(⟨2,0,0⟩,[0,r196,r391,r392,r393,r394,r395,r396,r397,r398,r399,r400,r401,r402,r403,r404,r405]),(⟨2,0,1⟩,[0,r357,r472,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483,r484,r485]),(⟨2,0,2⟩,[0,r0,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543,r544,r545,r546]),(⟨2,0,3⟩,[0,r547,r548,r549,r550,r551,r552,r553,r554,r555,r556,r557,r558,r559]),(⟨2,0,4⟩,[0,0,0,0,r560,r561,r562,r563,r564,r565,r566,r567,-524288]),(⟨2,1,0⟩,[0,r357,r472,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483,r484,r485]),(⟨2,1,1⟩,[r594,r209,r595,r596,r597,r598,r599,r600,r601,r602,r603,r604,r605,r606,r607]),(⟨2,1,3⟩,[r455,r512,r513,r514,r620,r621,r622,r623,r624,r625,r626,r627,r628]),(⟨2,2,0⟩,[0,r0,r534,r535,r536,r537,r538,r539,r540,r541,r542,r543,r544,r545,r546]),(⟨2,2,2⟩,[0,r182,r629,r630,r631,r632,r633,r634,r635,r636,r637,r638,r639]),(⟨2,2,3⟩,[0,r182,r640,r641,r642,r643,r644,r645,r646,r647,r648,r649]),(⟨2,2,4⟩,[0,r34,r650,r651,r652,r653,r654,r655,r656,r657,r658]),(⟨2,2,5⟩,[0,r34,r659,r660,r661,r662,r663,r664,r665,r666]),(⟨2,3,0⟩,[0,r547,r548,r549,r550,r551,r552,r553,r554,r555,r556,r557,r558,r559]),(⟨2,3,1⟩,[r455,r512,r513,r514,r620,r621,r622,r623,r624,r625,r626,r627,r628]),(⟨2,3,2⟩,[0,r182,r640,r641,r642,r643,r644,r645,r646,r647,r648,r649]),(⟨2,3,3⟩,[r217,r667,r668,r669,r670,r671,r672,r673,r674,r675,-917504]),(⟨2,3,5⟩,[r131,r676,r677,r678,r679,r680,r681,r682,131072]),(⟨2,4,0⟩,[0,0,0,0,r560,r561,r562,r563,r564,r565,r566,r567,-524288]),(⟨2,4,2⟩,[0,r34,r650,r651,r652,r653,r654,r655,r656,r657,r658]),(⟨2,5,2⟩,[0,r34,r659,r660,r661,r662,r663,r664,r665,r666]),(⟨2,5,3⟩,[r131,r676,r677,r678,r679,r680,r681,r682,131072]),(⟨3,0,0⟩,[0,r196,r406,r407,r408,r409,r410,r411,r412,r413,r414,r415,r416,r417,r418,r419]),(⟨3,0,1⟩,[r245,r246,r486,r487,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498]),(⟨3,0,2⟩,[0,r547,r548,r549,r550,r551,r552,r553,r554,r555,r556,r557,r558,r559]),(⟨3,0,3⟩,[r100,r159,r568,r569,r570,r571,r572,r573,r574,r575,r576,r577,r578]),(⟨3,0,4⟩,[0,r349,r524,r525,r526,r527,r528,r529,r530,r531,r532,r533]),(⟨3,1,0⟩,[r245,r246,r486,r487,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498]),(⟨3,1,1⟩,[0,r608,r549,r609,r610,r611,r612,r613,r614,r615,r616,r617,r618,r619]),(⟨3,1,2⟩,[r455,r512,r513,r514,r620,r621,r622,r623,r624,r625,r626,r627,r628]),(⟨3,1,3⟩,[0,r171,r172,r173,r174,r175,r176,r177,r178,r179,r180,r181]),(⟨3,2,0⟩,[0,r547,r548,r549,r550,r551,r552,r553,r554,r555,r556,r557,r558,r559]),(⟨3,2,1⟩,[r455,r512,r513,r514,r620,r621,r622,r623,r624,r625,r626,r627,r628]),(⟨3,2,2⟩,[0,r182,r640,r641,r642,r643,r644,r645,r646,r647,r648,r649]),(⟨3,2,3⟩,[r217,r667,r668,r669,r670,r671,r672,r673,r674,r675,-917504]),(⟨3,2,5⟩,[r131,r676,r677,r678,r679,r680,r681,r682,131072]),(⟨3,3,0⟩,[r100,r159,r568,r569,r570,r571,r572,r573,r574,r575,r576,r577,r578]),(⟨3,3,1⟩,[0,r171,r172,r173,r174,r175,r176,r177,r178,r179,r180,r181]),(⟨3,3,2⟩,[r217,r667,r668,r669,r670,r671,r672,r673,r674,r675,-917504]),(⟨3,4,0⟩,[0,r349,r524,r525,r526,r527,r528,r529,r530,r531,r532,r533]),(⟨3,5,2⟩,[r131,r676,r677,r678,r679,r680,r681,r682,131072]),(⟨4,0,0⟩,[0,r357,r420,r421,r422,r423,r424,r425,r426,r427,r428,r429,r430,r431,r432]),(⟨4,0,1⟩,[0,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508,r509,r510,r511]),(⟨4,0,2⟩,[0,0,0,0,r560,r561,r562,r563,r564,r565,r566,r567,-524288]),(⟨4,0,3⟩,[0,r349,r524,r525,r526,r527,r528,r529,r530,r531,r532,r533]),(⟨4,1,0⟩,[0,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508,r509,r510,r511]),(⟨4,1,1⟩,[0,0,0,0,r209,r210,r211,r212,r213,r214,r215,r216,-1048576]),(⟨4,2,0⟩,[0,0,0,0,r560,r561,r562,r563,r564,r565,r566,r567,-524288]),(⟨4,2,2⟩,[0,r34,r650,r651,r652,r653,r654,r655,r656,r657,r658]),(⟨4,3,0⟩,[0,r349,r524,r525,r526,r527,r528,r529,r530,r531,r532,r533]),(⟨5,0,0⟩,[0,r357,r433,r434,r435,r436,r437,r438,r439,r440,r441,r442,r443,r444]),(⟨5,0,1⟩,[r455,r512,r513,r514,r515,r516,r517,r518,r519,r520,r521,r522,r523]),(⟨5,1,0⟩,[r455,r512,r513,r514,r515,r516,r517,r518,r519,r520,r521,r522,r523]),(⟨5,2,2⟩,[0,r34,r659,r660,r661,r662,r663,r664,r665,r666]),(⟨5,2,3⟩,[r131,r676,r677,r678,r679,r680,r681,r682,131072]),(⟨5,3,2⟩,[r131,r676,r677,r678,r679,r680,r681,r682,131072]),(⟨6,0,0⟩,[0,0,r321,r445,r446,r447,r448,r449,r450,r451,r452,r453,r454]),(⟨6,0,1⟩,[0,r349,r524,r525,r526,r527,r528,r529,r530,r531,r532,r533]),(⟨6,1,0⟩,[0,r349,r524,r525,r526,r527,r528,r529,r530,r531,r532,r533])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,-384,8064,-64256,246656,-476544,385152,5632,-79744]),(⟨0,0,1⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨0,0,2⟩,[0,384,-6400,33024,-52224,4480,12544]),(⟨0,0,3⟩,[0,384,-6656,34048,-49664,-2688]),(⟨0,1,0⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨0,1,1⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨0,1,3⟩,[-128,1536,-3840,-4608,15232]),(⟨0,2,0⟩,[0,384,-6400,33024,-52224,4480,12544]),(⟨0,3,0⟩,[0,384,-6656,34048,-49664,-2688]),(⟨0,3,1⟩,[-128,1536,-3840,-4608,15232]),(⟨1,0,0⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨1,0,1⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨1,0,3⟩,[-128,1536,-3840,-4608,15232]),(⟨1,1,0⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨1,3,0⟩,[-128,1536,-3840,-4608,15232]),(⟨2,0,0⟩,[0,384,-6400,33024,-52224,4480,12544]),(⟨3,0,0⟩,[0,384,-6656,34048,-49664,-2688]),(⟨3,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨3,1,0⟩,[-128,1536,-3840,-4608,15232])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[-256,5120,-43008,199936,-545280,801024,-457728,253696,-1684736,2508544,-513024]),(⟨0,0,1⟩,[0,1536,-21760,121088,-327424,405248,-133888,235264,-1327360,1571584]),(⟨0,0,2⟩,[256,-4608,28416,-75264,67840,43520,25856,-250368,-32256]),(⟨0,0,3⟩,[0,-2048,20992,-74240,87040,37888,31232,-363008]),(⟨0,1,0⟩,[0,1536,-21760,121088,-327424,405248,-133888,235264,-1327360,1571584]),(⟨0,1,1⟩,[0,0,0,0,4096,-49152,122880,147456,-487424]),(⟨0,2,0⟩,[256,-4608,28416,-75264,67840,43520,25856,-250368,-32256]),(⟨0,3,0⟩,[0,-2048,20992,-74240,87040,37888,31232,-363008]),(⟨1,0,0⟩,[0,1536,-21760,121088,-327424,405248,-133888,235264,-1327360,1571584]),(⟨1,0,1⟩,[0,0,0,0,4096,-49152,122880,147456,-487424]),(⟨1,1,0⟩,[0,0,0,0,4096,-49152,122880,147456,-487424]),(⟨2,0,0⟩,[256,-4608,28416,-75264,67840,43520,25856,-250368,-32256]),(⟨2,2,2⟩,[-1024,12288,-30720,-36864,121856]),(⟨3,0,0⟩,[0,-2048,20992,-74240,87040,37888,31232,-363008])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 4 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r683) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 13 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r683) sourceRight))).isZero := by decide +kernel

noncomputable def partial19 : Poly := []

theorem partial_sound19 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 19)
      sourceRight).eval u v t=partial19.eval u v t := by rfl

noncomputable def chunk16 : Poly := [(⟨3,0,0⟩,[0,384,-6656,34048,-49664,-2688]),(⟨3,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨3,1,0⟩,[-128,1536,-3840,-4608,15232])]

noncomputable def partial16 : Poly := [(⟨3,0,0⟩,[0,-98304,3670016,-59310080,550076416,-3258089472,12866584576,-33887092736,56960679936,-56236605440,41394176000,-85624946688,171814387712,-137523200000,18735857664,1379008512]),(⟨3,0,1⟩,[32768,-1048576,14942208,-128712704,758185984,-3180527616,9340747776,-18105499648,21081260032,-15452995584,25255804928,-65771929600,83547652096,-33909047296,-12038799360]),(⟨3,0,2⟩,[0,-98304,1671168,-4521984,-83263488,826572800,-3388801024,7252869120,-7762673664,3836968960,-5323390976,14931656704,-25185255424,24025071616]),(⟨3,0,3⟩,[-32768,983040,-12484608,91488256,-446234624,1530527744,-3546873856,4799594496,-2827386880,2819555328,-12341248000,14279507968,484442112]),(⟨3,0,4⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨3,1,0⟩,[32768,-1048576,14942208,-128712704,758185984,-3180527616,9340747776,-18105499648,21081260032,-15452995584,25255804928,-65771929600,83547652096,-33909047296,-12038799360]),(⟨3,1,1⟩,[0,-393216,10289152,-109641728,608763904,-1790640128,1968832512,3636330496,-14256832512,12737839104,11069358080,-16919101440,-31109349376,49186930688]),(⟨3,1,2⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨3,1,3⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨3,2,0⟩,[0,-98304,1671168,-4521984,-83263488,826572800,-3388801024,7252869120,-7762673664,3836968960,-5323390976,14931656704,-25185255424,24025071616]),(⟨3,2,1⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨3,3,0⟩,[-32768,983040,-12484608,91488256,-446234624,1530527744,-3546873856,4799594496,-2827386880,2819555328,-12341248000,14279507968,484442112]),(⟨3,3,1⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨3,4,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨4,0,0⟩,[0,0,589824,-18579456,243630080,-1748860928,7534313472,-19852099584,30715084800,-25880363008,23008772096,-66978676736,118798909440,-74483204096,-4224417792]),(⟨4,0,1⟩,[0,-196608,5144576,-54820864,304381952,-894533632,961347584,2075066368,-8447524864,9091547136,6681821184,-20584235008,-3649142784,25248563200]),(⟨4,0,2⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨4,1,0⟩,[0,-196608,5144576,-54820864,304381952,-894533632,961347584,2075066368,-8447524864,9091547136,6681821184,-20584235008,-3649142784,25248563200]),(⟨4,1,1⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨4,2,0⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨5,0,0⟩,[0,98304,-3473408,50298880,-387645440,1722679296,-4396285952,5691604992,-1953366016,190676992,-9710927872,11266523136,2274951168,86704128]),(⟨5,0,1⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨5,1,0⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨5,2,2⟩,[0,-393216,11534336,-128450560,659554304,-1361313792,-573571072,6062342144,-5952765952,-327548928]),(⟨5,2,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨5,3,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨6,0,0⟩,[0,0,-786432,21692416,-237961216,1344012288,-4129554432,6353977344,-3180462080,1363935232,-14012645376,17944477696,975765504]),(⟨6,0,1⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨6,1,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856])]


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

noncomputable def partial12 : Poly := [(⟨1,0,3⟩,[32768,-1048576,14352384,-110133248,514555904,-1431666688,1806434304,1746599936,-9633824768,10427367424,2247032832,1206747136,-35251257344,40574156800,-7814381568]),(⟨1,0,4⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨1,0,5⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨1,0,6⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨1,1,0⟩,[-32768,1114112,-16678912,146178048,-835289088,3231711232,-8271659008,11887935488,481984512,-41921216512,86044475392,-69704253440,21935521792,-119523901440,335721496576,-299647860736,54700670976]),(⟨1,1,1⟩,[0,196608,-5537792,66486272,-450035712,1888616448,-4930371584,6726451200,1879441408,-26193756160,43570200576,-20414103552,4077715456,-104514715648,240098181120,-167568572416]),(⟨1,1,2⟩,[32768,-1048576,13893632,-100073472,429752320,-1091633152,1248264192,1414135808,-7540604928,10131210240,-1231683584,-3181576192,-18538397696,24672141312,3439263744]),(⟨1,1,3⟩,[0,-458752,11501568,-117932032,640778240,-1922072576,2572091392,1905852416,-12121604096,13847232512,2577498112,701399040,-53558149120,62643732480]),(⟨1,1,4⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨1,2,0⟩,[0,196608,-5537792,66486272,-450035712,1888616448,-4930371584,6726451200,1879441408,-26193756160,43570200576,-20414103552,4077715456,-104514715648,240098181120,-167568572416]),(⟨1,2,1⟩,[0,0,0,0,524288,-13631488,135790592,-641728512,1322254336,463470592,-9064939520,20044578816,-5038931968,-46293581824,51971096576]),(⟨1,2,3⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨1,3,0⟩,[65536,-2097152,28246016,-210206720,944308224,-2523299840,3054698496,3160735744,-17174429696,20558577664,1015349248,-1974829056,-53789655040,65246298112,-4375117824]),(⟨1,3,1⟩,[0,-196608,5144576,-54820864,304381952,-896106496,1007484928,1561264128,-5809307648,3646291968,4387536896,3665133568,-27460206592,23938367488]),(⟨1,3,2⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨1,3,3⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨1,4,0⟩,[0,-458752,11501568,-117932032,640778240,-1922072576,2572091392,1905852416,-12121604096,13847232512,2577498112,701399040,-53558149120,62643732480]),(⟨1,4,1⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨1,5,0⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨1,6,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨2,0,0⟩,[0,-98304,3604480,-57737216,534478848,-3177807872,12665847808,-33879556096,58312818688,-59154137088,40776630272,-77140000768,169503981568,-152313561088,16897114112,29168828416,-6435373056]),(⟨2,0,1⟩,[0,0,589824,-18186240,236486656,-1699512320,7393214464,-19859767296,31699042304,-27548516352,21568421888,-61695688704,120594530304,-85069824000,-9609707520,19713949696]),(⟨2,0,2⟩,[0,98304,-3407872,48857088,-376307712,1687945216,-4404412416,5971836928,-2348023808,-469139456,-8366063616,12671746048,887226368,-3285123072,-404619264]),(⟨2,0,3⟩,[0,-196608,4358144,-33652736,73891840,412647424,-3092185088,8150646784,-9512222720,4480958464,-7969931264,23238049792,-28694708224,19384795136]),(⟨2,0,4⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨2,1,0⟩,[0,196608,-4947968,48300032,-213549056,189104128,2462842880,-13133316096,33578483712,-53742272512,65138622464,-82109792256,124672245760,-189584539648,230488473600,-147854622720]),(⟨2,1,1⟩,[0,0,0,0,524288,-12058624,90701824,-144703488,-1244659712,5975834624,-7661944832,-3818913792,22618308608,-46627553280,45856849920]),(⟨2,1,3⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨2,2,0⟩,[0,98304,-3407872,48857088,-375783424,1674313728,-4268621824,5330108416,-1025769472,-5668864,-17431003136,32716324864,-4151705600,-49578704896,51566477312]),(⟨2,3,0⟩,[0,-196608,4358144,-33652736,73891840,412647424,-3092185088,8150646784,-9512222720,4480958464,-7969931264,23238049792,-28694708224,19384795136]),(⟨2,3,1⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨2,4,0⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨3,0,0⟩,[0,-98304,4259840,-77496320,786563072,-4957601792,20259799040,-53746860032,88659722240,-83785121792,62962597888,-147320635392,292408918016,-222593024000,9126150144,21092958208]),(⟨3,0,1⟩,[32768,-1048576,14942208,-128712704,758185984,-3178954752,9295659008,-17608474624,18514345984,-9940631552,26658799616,-89635422208,111204892672,-34243018752,-18153046016]),(⟨3,0,2⟩,[0,-98304,1671168,-4521984,-83263488,826572800,-3388801024,7252869120,-7762673664,3836968960,-5323390976,14931656704,-25185255424,24025071616]),(⟨3,0,3⟩,[-65536,1966080,-24182784,161284096,-654508032,1717043200,-2964193280,3245211648,-2474311680,4275175424,-10669850624,10614538240,-6881280]),(⟨3,0,4⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨3,1,0⟩,[65536,-2097152,28835840,-228786176,1187938304,-4270587904,10543923200,-16194338816,10973741056,190578688,25427116032,-92816998400,92666494976,-9570877440,-14713782272]),(⟨3,1,1⟩,[0,-393216,10289152,-109641728,608763904,-1790640128,1968832512,3636330496,-14256832512,12737839104,11069358080,-16919101440,-31109349376,49186930688]),(⟨3,1,2⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨3,1,3⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨3,2,0⟩,[0,-98304,1671168,-4521984,-83263488,826572800,-3388801024,7252869120,-7762673664,3836968960,-5323390976,14931656704,-25185255424,24025071616]),(⟨3,2,1⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨3,2,5⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,3,0⟩,[-65536,1966080,-24182784,161284096,-654508032,1717043200,-2964193280,3245211648,-2474311680,4275175424,-10669850624,10614538240,-6881280]),(⟨3,3,1⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨3,3,2⟩,[-131072,3407872,-33947648,160432128,-330563584,-115867648,2266234880,-5011144704,1259732992,11573395456,-12992774144]),(⟨3,4,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨3,5,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,0,0⟩,[0,98304,-2818048,30277632,-132677632,-60915712,3129901056,-13880262656,28367060992,-26349502464,14642708480,-54306930688,119686135808,-77768327168,-4629037056]),(⟨4,0,1⟩,[0,-196608,5144576,-54820864,304381952,-894533632,961347584,2075066368,-8447524864,9091547136,6681821184,-20584235008,-3649142784,25248563200]),(⟨4,0,2⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨4,0,3⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨4,1,0⟩,[0,-458752,11501568,-117932032,640778240,-1920499712,2525954048,2419654656,-14759821312,19292487680,4871782400,-23547969536,-29747085312,63953928192]),(⟨4,1,1⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨4,2,0⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨4,2,2⟩,[0,-393216,11272192,-124256256,641728512,-1378091008,-350748672,5965873152,-6914310144,83492864,1528561664]),(⟨4,3,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨5,0,0⟩,[0,98304,-4259840,71467008,-618135552,3031433216,-8495955968,12280987648,-5656281088,1025343488,-22068396032,30839439360,1040449536,-4466868224]),(⟨5,0,1⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨5,1,0⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨5,2,2⟩,[0,-393216,11534336,-128450560,659554304,-1361313792,-573571072,6062342144,-5952765952,-327548928]),(⟨5,2,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨5,3,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨6,0,0⟩,[0,0,-786432,21692416,-237961216,1344012288,-4129554432,6353977344,-3180462080,1363935232,-14012645376,17944477696,975765504]),(⟨6,0,1⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨6,1,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856])]


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

noncomputable def partial8 : Poly := [(⟨0,3,0⟩,[0,-98304,3670016,-59310080,550076416,-3258089472,12866584576,-33887092736,56960679936,-56236605440,41394176000,-85624946688,171814387712,-137523200000,18735857664,1379008512]),(⟨0,3,1⟩,[32768,-1048576,14942208,-128712704,758185984,-3180527616,9340747776,-18105499648,21081260032,-15452995584,25255804928,-65771929600,83547652096,-33909047296,-12038799360]),(⟨0,3,2⟩,[0,-98304,1671168,-4521984,-83263488,826572800,-3388801024,7252869120,-7762673664,3836968960,-5323390976,14931656704,-25185255424,24025071616]),(⟨0,3,3⟩,[-32768,983040,-12484608,91488256,-446234624,1530527744,-3546873856,4799594496,-2827386880,2819555328,-12341248000,14279507968,484442112]),(⟨0,3,4⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨0,4,0⟩,[0,0,589824,-18579456,243630080,-1748860928,7534313472,-19852099584,30715084800,-25880363008,23008772096,-66978676736,118798909440,-74483204096,-4224417792]),(⟨0,4,1⟩,[0,-196608,5144576,-54820864,304381952,-894533632,961347584,2075066368,-8447524864,9091547136,6681821184,-20584235008,-3649142784,25248563200]),(⟨0,4,2⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨0,5,0⟩,[0,98304,-3473408,50298880,-387645440,1722679296,-4396285952,5691604992,-1953366016,190676992,-9710927872,11266523136,2274951168,86704128]),(⟨0,5,1⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨0,6,0⟩,[0,0,-786432,21692416,-237961216,1344012288,-4129554432,6353977344,-3180462080,1363935232,-14012645376,17944477696,975765504]),(⟨0,6,1⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨1,0,0⟩,[0,98304,-3801088,65601536,-672497664,4579426304,-21828632576,74321625088,-180106493952,303328559104,-347441922048,320225738752,-459981684736,826144686080,-884443480064,346850852864,78445543424,-29418848256]),(⟨1,0,1⟩,[-32768,1114112,-17268736,165543936,-1112080384,5516525568,-20378943488,54911860736,-102842007552,122727956480,-88700846080,107440439296,-310560161792,466526633984,-198799458304,-175405891584,144821583872]),(⟨1,0,2⟩,[0,98304,-1933312,10158080,45219840,-828375040,4732387328,-15351775232,32078561280,-46792343552,53307473920,-54487941120,65210286080,-127176474624,221628825600,-169418260480]),(⟨1,0,3⟩,[65536,-2097152,29032448,-232947712,1222377472,-4422270976,11006312448,-17628987392,15311110144,-6916472832,21131755520,-55996612608,39858339840,20758102016,-25191448576]),(⟨1,0,4⟩,[0,-458752,11501568,-117932032,640778240,-1922072576,2572091392,1905852416,-12121604096,13847232512,2577498112,701399040,-53558149120,62643732480]),(⟨1,0,5⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨1,0,6⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨1,1,0⟩,[-32768,1114112,-17268736,165543936,-1112080384,5516525568,-20378943488,54911860736,-102842007552,122727956480,-88700846080,107440439296,-310560161792,466526633984,-198799458304,-175405891584,144821583872]),(⟨1,1,1⟩,[0,393216,-11075584,132972544,-900071424,3775660032,-9812508672,12855214080,7596670976,-65701281792,107944148992,-30017388544,-90154860544,-65703247872,426511368192,-363087986688]),(⟨1,1,2⟩,[32768,-1048576,13893632,-100073472,430276608,-1105264640,1384054784,772407296,-6218350592,10594680832,-10296623104,16863002624,-23577329664,-21621440512,55410360320]),(⟨1,1,3⟩,[0,-458752,11501568,-117932032,640778240,-1922072576,2572091392,1905852416,-12121604096,13847232512,2577498112,701399040,-53558149120,62643732480]),(⟨1,1,4⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨1,2,0⟩,[0,98304,-1933312,10158080,45219840,-828375040,4732387328,-15351775232,32078561280,-46792343552,53307473920,-54487941120,65210286080,-127176474624,221628825600,-169418260480]),(⟨1,2,1⟩,[32768,-1048576,13893632,-100073472,430276608,-1105264640,1384054784,772407296,-6218350592,10594680832,-10296623104,16863002624,-23577329664,-21621440512,55410360320]),(⟨1,2,3⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨1,3,0⟩,[65536,-2097152,29622272,-251527168,1466007552,-6171131904,18540625920,-37481086976,46026194944,-32796835840,44140527616,-122975289344,158657249280,-53725102080,-29415866368]),(⟨1,3,1⟩,[0,-655360,16646144,-172752896,945160192,-2816606208,3533438976,3980918784,-20569128960,22938779648,9259319296,-19882835968,-57207291904,87892295680]),(⟨1,3,2⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨1,3,3⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨1,4,0⟩,[0,-458752,11501568,-117932032,640778240,-1920499712,2525954048,2419654656,-14759821312,19292487680,4871782400,-23547969536,-29747085312,63953928192]),(⟨1,4,1⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨1,5,0⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨1,6,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨2,0,0⟩,[0,-98304,3014656,-38371328,257687552,-892993536,558563328,9144369152,-45011173376,105495035904,-133968691200,100004691968,-162991702016,433736974336,-517623840768,153410797568,83685539840]),(⟨2,0,1⟩,[0,196608,-4947968,48300032,-213549056,187531264,2511077376,-13731004416,37416271872,-67056041984,85942370304,-71298973696,26361954304,-46258356224,176803479552,-175805464576]),(⟨2,0,2⟩,[0,98304,-3407872,48857088,-375783424,1674313728,-4268621824,5330108416,-1025769472,-5668864,-17431003136,32716324864,-4151705600,-49578704896,51566477312]),(⟨2,0,3⟩,[0,-196608,4358144,-33652736,73891840,412647424,-3092185088,8150646784,-9512222720,4480958464,-7969931264,23238049792,-28694708224,19384795136]),(⟨2,0,4⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨2,1,0⟩,[0,196608,-4947968,48300032,-213549056,187531264,2511077376,-13731004416,37416271872,-67056041984,85942370304,-71298973696,26361954304,-46258356224,176803479552,-175805464576]),(⟨2,1,1⟩,[0,0,0,0,1048576,-25690112,226492416,-786432000,77594624,6439305216,-16726884352,16225665024,17579376640,-92921135104,97827946496]),(⟨2,1,3⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨2,2,0⟩,[0,98304,-3407872,48857088,-375783424,1674313728,-4268621824,5330108416,-1025769472,-5668864,-17431003136,32716324864,-4151705600,-49578704896,51566477312]),(⟨2,3,0⟩,[0,-98304,884736,16646144,-313753600,2135326720,-7488471040,13842251776,-11465588736,4671635456,-17680859136,34504572928,-26419757056,19471499264]),(⟨2,3,1⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨2,4,0⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨2,5,2⟩,[0,-393216,11534336,-128450560,659554304,-1361313792,-573571072,6062342144,-5952765952,-327548928]),(⟨2,5,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,0,0⟩,[0,-196608,7864320,-133824512,1281818624,-7674593280,29922557952,-75825086464,118858842112,-104383709184,72699871232,-181394472960,353541488640,-245254782976,-9343205376,19243270144]),(⟨3,0,1⟩,[65536,-2097152,28835840,-228786176,1187938304,-4270587904,10543923200,-16194338816,10973741056,190578688,25427116032,-92816998400,92666494976,-9570877440,-14713782272]),(⟨3,0,2⟩,[0,-98304,1671168,-4521984,-83263488,826572800,-3388801024,7252869120,-7762673664,3836968960,-5323390976,14931656704,-25185255424,24025071616]),(⟨3,0,3⟩,[-65536,1966080,-24182784,161284096,-654508032,1717043200,-2964193280,3245211648,-2474311680,4275175424,-10669850624,10614538240,-6881280]),(⟨3,0,4⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨3,1,0⟩,[65536,-2097152,28835840,-228786176,1187938304,-4270587904,10543923200,-16194338816,10973741056,190578688,25427116032,-92816998400,92666494976,-9570877440,-14713782272]),(⟨3,1,1⟩,[0,-393216,10289152,-109641728,608763904,-1790640128,1968832512,3636330496,-14256832512,12737839104,11069358080,-16919101440,-31109349376,49186930688]),(⟨3,1,2⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨3,1,3⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨3,2,0⟩,[0,-98304,1671168,-4521984,-83263488,826572800,-3388801024,7252869120,-7762673664,3836968960,-5323390976,14931656704,-25185255424,24025071616]),(⟨3,2,1⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨3,2,2⟩,[0,393216,-12058624,149422080,-959447040,3328442368,-5200936960,-2702704640,24577572864,-35831545856,13421248512,6987710464]),(⟨3,2,3⟩,[-131072,3407872,-33947648,160432128,-330563584,-115867648,2266234880,-5011144704,1259732992,11573395456,-12992774144]),(⟨3,2,5⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,3,0⟩,[-65536,1966080,-24969216,182976512,-892469248,3061055488,-7093747712,9599188992,-5654773760,5639110656,-24682496000,28559015936,968884224]),(⟨3,3,1⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨3,3,2⟩,[-131072,3407872,-33947648,160432128,-330563584,-115867648,2266234880,-5011144704,1259732992,11573395456,-12992774144]),(⟨3,4,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨3,5,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,0,0⟩,[0,98304,-2031616,7536640,145391616,-1959886848,11081515008,-34669985792,60852600832,-53824552960,34759114752,-108328714240,213334130688,-122256523264,-25445367808]),(⟨4,0,1⟩,[0,-458752,11501568,-117932032,640778240,-1920499712,2525954048,2419654656,-14759821312,19292487680,4871782400,-23547969536,-29747085312,63953928192]),(⟨4,0,2⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨4,0,3⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨4,1,0⟩,[0,-458752,11501568,-117932032,640778240,-1920499712,2525954048,2419654656,-14759821312,19292487680,4871782400,-23547969536,-29747085312,63953928192]),(⟨4,1,1⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨4,2,0⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨4,2,2⟩,[0,-393216,11272192,-124256256,641728512,-1378091008,-350748672,5965873152,-6914310144,83492864,1528561664]),(⟨4,3,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨5,0,0⟩,[0,98304,-4259840,71467008,-618135552,3031433216,-8495955968,12280987648,-5656281088,1025343488,-22068396032,30839439360,1040449536,-4466868224]),(⟨5,0,1⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨5,1,0⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨5,2,2⟩,[0,-393216,11534336,-128450560,659554304,-1361313792,-573571072,6062342144,-5952765952,-327548928]),(⟨5,2,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨5,3,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨6,0,0⟩,[0,0,-786432,21692416,-237961216,1344012288,-4129554432,6353977344,-3180462080,1363935232,-14012645376,17944477696,975765504]),(⟨6,0,1⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨6,1,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856])]


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

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[0,98304,-3801088,65601536,-672497664,4579426304,-21828632576,74321625088,-180106493952,303328559104,-347441922048,320225738752,-459981684736,826144686080,-884443480064,346850852864,78445543424,-29418848256]),(⟨0,1,1⟩,[-32768,1114112,-17268736,165543936,-1112080384,5516525568,-20378943488,54911860736,-102842007552,122727956480,-88700846080,107440439296,-310560161792,466526633984,-198799458304,-175405891584,144821583872]),(⟨0,1,2⟩,[0,98304,-1933312,10158080,45219840,-828375040,4732387328,-15351775232,32078561280,-46792343552,53307473920,-54487941120,65210286080,-127176474624,221628825600,-169418260480]),(⟨0,1,3⟩,[65536,-2097152,29032448,-232947712,1222377472,-4422270976,11006312448,-17628987392,15311110144,-6916472832,21131755520,-55996612608,39858339840,20758102016,-25191448576]),(⟨0,1,4⟩,[0,-458752,11501568,-117932032,640778240,-1922072576,2572091392,1905852416,-12121604096,13847232512,2577498112,701399040,-53558149120,62643732480]),(⟨0,1,5⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨0,1,6⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨0,2,0⟩,[0,-98304,3014656,-38371328,257687552,-892993536,558563328,9144369152,-45011173376,105495035904,-133968691200,100004691968,-162991702016,433736974336,-517623840768,153410797568,83685539840]),(⟨0,2,1⟩,[0,196608,-4947968,48300032,-213549056,187531264,2511077376,-13731004416,37416271872,-67056041984,85942370304,-71298973696,26361954304,-46258356224,176803479552,-175805464576]),(⟨0,2,2⟩,[0,98304,-3407872,48857088,-375783424,1674313728,-4268621824,5330108416,-1025769472,-5668864,-17431003136,32716324864,-4151705600,-49578704896,51566477312]),(⟨0,2,3⟩,[0,-196608,4358144,-33652736,73891840,412647424,-3092185088,8150646784,-9512222720,4480958464,-7969931264,23238049792,-28694708224,19384795136]),(⟨0,2,4⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨0,3,0⟩,[0,-196608,7864320,-133824512,1281818624,-7674593280,29922557952,-75825086464,118858842112,-104383709184,72699871232,-181394472960,353541488640,-245254782976,-9343205376,19243270144]),(⟨0,3,1⟩,[65536,-2097152,28835840,-228786176,1187938304,-4270587904,10543923200,-16194338816,10973741056,190578688,25427116032,-92816998400,92666494976,-9570877440,-14713782272]),(⟨0,3,2⟩,[0,-98304,1671168,-4521984,-83263488,826572800,-3388801024,7252869120,-7762673664,3836968960,-5323390976,14931656704,-25185255424,24025071616]),(⟨0,3,3⟩,[-65536,1966080,-24182784,161284096,-654508032,1717043200,-2964193280,3245211648,-2474311680,4275175424,-10669850624,10614538240,-6881280]),(⟨0,3,4⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨0,4,0⟩,[0,98304,-2031616,7536640,145391616,-1959886848,11081515008,-34669985792,60852600832,-53824552960,34759114752,-108328714240,213334130688,-122256523264,-25445367808]),(⟨0,4,1⟩,[0,-458752,11501568,-117932032,640778240,-1920499712,2525954048,2419654656,-14759821312,19292487680,4871782400,-23547969536,-29747085312,63953928192]),(⟨0,4,2⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨0,4,3⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨0,5,0⟩,[0,98304,-4259840,71467008,-618135552,3031433216,-8495955968,12280987648,-5656281088,1025343488,-22068396032,30839439360,1040449536,-4466868224]),(⟨0,5,1⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨0,6,0⟩,[0,0,-786432,21692416,-237961216,1344012288,-4129554432,6353977344,-3180462080,1363935232,-14012645376,17944477696,975765504]),(⟨0,6,1⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨1,0,0⟩,[0,98304,-3801088,65601536,-672497664,4579426304,-21828632576,74321625088,-180106493952,303328559104,-347441922048,320225738752,-459981684736,826144686080,-884443480064,346850852864,78445543424,-29418848256]),(⟨1,0,1⟩,[-32768,1114112,-17268736,165543936,-1112080384,5516525568,-20378943488,54911860736,-102842007552,122727956480,-88700846080,107440439296,-310560161792,466526633984,-198799458304,-175405891584,144821583872]),(⟨1,0,2⟩,[0,98304,-1933312,10158080,45219840,-828375040,4732387328,-15351775232,32078561280,-46792343552,53307473920,-54487941120,65210286080,-127176474624,221628825600,-169418260480]),(⟨1,0,3⟩,[65536,-2097152,29032448,-232947712,1222377472,-4422270976,11006312448,-17628987392,15311110144,-6916472832,21131755520,-55996612608,39858339840,20758102016,-25191448576]),(⟨1,0,4⟩,[0,-458752,11501568,-117932032,640778240,-1922072576,2572091392,1905852416,-12121604096,13847232512,2577498112,701399040,-53558149120,62643732480]),(⟨1,0,5⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨1,0,6⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨1,1,0⟩,[-32768,1114112,-17858560,184909824,-1388871680,7801339904,-32486227968,97935785984,-206165999616,287377129472,-263446167552,284585132032,-643055845376,1052577169408,-733320413184,-51163922432,234942496768]),(⟨1,1,1⟩,[0,589824,-16613376,199458816,-1350107136,5662703616,-14694645760,18983976960,13313900544,-105208807424,172318097408,-39620673536,-184387436544,-26891780096,612924555264,-558607400960]),(⟨1,1,2⟩,[32768,-1048576,13893632,-100073472,430800896,-1118896128,1519845376,130678784,-4896096256,11058151424,-19361562624,36907581440,-28616261632,-67915022336,107381456896]),(⟨1,1,3⟩,[0,-655360,16646144,-172752896,945160192,-2818179072,3579576320,3467116544,-17930911744,17493524480,6965035008,4366532608,-81018355712,86582099968]),(⟨1,1,4⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨1,2,0⟩,[0,98304,-1343488,-8028160,281706496,-2529460224,12173836288,-35809230848,67615391744,-87654629376,95679643648,-105372811264,87494524928,-68920115200,158334124032,-177655152640]),(⟨1,2,1⟩,[32768,-1048576,13893632,-100073472,430800896,-1117323264,1474756608,627703808,-7463010304,16570515456,-17958567936,13044088832,-959021056,-68248993792,101267210240]),(⟨1,2,3⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨1,3,0⟩,[65536,-2097152,29622272,-251527168,1466007552,-6169559040,18495537152,-36984061952,43459280896,-27284471808,45543522304,-146838781952,186314489856,-54059073536,-35530113024]),(⟨1,3,1⟩,[0,-655360,16646144,-172752896,945160192,-2816606208,3533438976,3980918784,-20569128960,22938779648,9259319296,-19882835968,-57207291904,87892295680]),(⟨1,3,2⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨1,3,3⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨1,4,0⟩,[0,-458752,11501568,-117932032,640778240,-1920499712,2525954048,2419654656,-14759821312,19292487680,4871782400,-23547969536,-29747085312,63953928192]),(⟨1,4,1⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨1,5,0⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨1,6,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨2,0,0⟩,[0,-98304,3014656,-38371328,257687552,-892993536,558563328,9144369152,-45011173376,105495035904,-133968691200,100004691968,-162991702016,433736974336,-517623840768,153410797568,83685539840]),(⟨2,0,1⟩,[0,196608,-4947968,48300032,-213549056,187531264,2511077376,-13731004416,37416271872,-67056041984,85942370304,-71298973696,26361954304,-46258356224,176803479552,-175805464576]),(⟨2,0,2⟩,[0,98304,-3407872,48857088,-375783424,1674313728,-4268621824,5330108416,-1025769472,-5668864,-17431003136,32716324864,-4151705600,-49578704896,51566477312]),(⟨2,0,3⟩,[0,-196608,4358144,-33652736,73891840,412647424,-3092185088,8150646784,-9512222720,4480958464,-7969931264,23238049792,-28694708224,19384795136]),(⟨2,0,4⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨2,1,0⟩,[0,98304,-1343488,-8028160,281706496,-2529460224,12173836288,-35809230848,67615391744,-87654629376,95679643648,-105372811264,87494524928,-68920115200,158334124032,-177655152640]),(⟨2,1,1⟩,[32768,-1048576,13893632,-100073472,430800896,-1117323264,1474756608,627703808,-7463010304,16570515456,-17958567936,13044088832,-959021056,-68248993792,101267210240]),(⟨2,1,3⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨2,2,0⟩,[0,196608,-6815744,97714176,-752091136,3362258944,-8673034240,11301945344,-3373793280,-474808320,-25797066752,45388070912,-3264479232,-52863827968,51161858048]),(⟨2,3,0⟩,[0,-98304,884736,16646144,-313753600,2135326720,-7488471040,13842251776,-11465588736,4671635456,-17680859136,34504572928,-26419757056,19471499264]),(⟨2,3,1⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨2,3,2⟩,[0,393216,-12058624,149422080,-959447040,3328442368,-5200936960,-2702704640,24577572864,-35831545856,13421248512,6987710464]),(⟨2,3,3⟩,[-131072,3407872,-33947648,160432128,-330563584,-115867648,2266234880,-5011144704,1259732992,11573395456,-12992774144]),(⟨2,3,5⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,4,0⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨2,4,2⟩,[0,-393216,11272192,-124256256,641728512,-1378091008,-350748672,5965873152,-6914310144,83492864,1528561664]),(⟨2,5,2⟩,[0,-393216,11534336,-128450560,659554304,-1361313792,-573571072,6062342144,-5952765952,-327548928]),(⟨2,5,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,0,0⟩,[0,-196608,7864320,-133824512,1281818624,-7674593280,29922557952,-75825086464,118858842112,-104383709184,72699871232,-181394472960,353541488640,-245254782976,-9343205376,19243270144]),(⟨3,0,1⟩,[65536,-2097152,28835840,-228786176,1187938304,-4270587904,10543923200,-16194338816,10973741056,190578688,25427116032,-92816998400,92666494976,-9570877440,-14713782272]),(⟨3,0,2⟩,[0,-98304,1671168,-4521984,-83263488,826572800,-3388801024,7252869120,-7762673664,3836968960,-5323390976,14931656704,-25185255424,24025071616]),(⟨3,0,3⟩,[-65536,1966080,-24182784,161284096,-654508032,1717043200,-2964193280,3245211648,-2474311680,4275175424,-10669850624,10614538240,-6881280]),(⟨3,0,4⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨3,1,0⟩,[65536,-2097152,29622272,-251527168,1466007552,-6169559040,18495537152,-36984061952,43459280896,-27284471808,45543522304,-146838781952,186314489856,-54059073536,-35530113024]),(⟨3,1,1⟩,[0,-655360,16646144,-172752896,945160192,-2816606208,3533438976,3980918784,-20569128960,22938779648,9259319296,-19882835968,-57207291904,87892295680]),(⟨3,1,2⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨3,1,3⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨3,2,0⟩,[0,-98304,884736,16646144,-313753600,2135326720,-7488471040,13842251776,-11465588736,4671635456,-17680859136,34504572928,-26419757056,19471499264]),(⟨3,2,1⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨3,2,2⟩,[0,393216,-12058624,149422080,-959447040,3328442368,-5200936960,-2702704640,24577572864,-35831545856,13421248512,6987710464]),(⟨3,2,3⟩,[-131072,3407872,-33947648,160432128,-330563584,-115867648,2266234880,-5011144704,1259732992,11573395456,-12992774144]),(⟨3,2,5⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,3,0⟩,[-65536,1966080,-24969216,182976512,-892469248,3061055488,-7093747712,9599188992,-5654773760,5639110656,-24682496000,28559015936,968884224]),(⟨3,3,1⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨3,3,2⟩,[-131072,3407872,-33947648,160432128,-330563584,-115867648,2266234880,-5011144704,1259732992,11573395456,-12992774144]),(⟨3,4,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨3,5,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,0,0⟩,[0,98304,-2031616,7536640,145391616,-1959886848,11081515008,-34669985792,60852600832,-53824552960,34759114752,-108328714240,213334130688,-122256523264,-25445367808]),(⟨4,0,1⟩,[0,-458752,11501568,-117932032,640778240,-1920499712,2525954048,2419654656,-14759821312,19292487680,4871782400,-23547969536,-29747085312,63953928192]),(⟨4,0,2⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨4,0,3⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨4,1,0⟩,[0,-458752,11501568,-117932032,640778240,-1920499712,2525954048,2419654656,-14759821312,19292487680,4871782400,-23547969536,-29747085312,63953928192]),(⟨4,1,1⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨4,2,0⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨4,2,2⟩,[0,-393216,11272192,-124256256,641728512,-1378091008,-350748672,5965873152,-6914310144,83492864,1528561664]),(⟨4,3,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨5,0,0⟩,[0,98304,-4259840,71467008,-618135552,3031433216,-8495955968,12280987648,-5656281088,1025343488,-22068396032,30839439360,1040449536,-4466868224]),(⟨5,0,1⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨5,1,0⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨5,2,2⟩,[0,-393216,11534336,-128450560,659554304,-1361313792,-573571072,6062342144,-5952765952,-327548928]),(⟨5,2,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨5,3,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨6,0,0⟩,[0,0,-786432,21692416,-237961216,1344012288,-4129554432,6353977344,-3180462080,1363935232,-14012645376,17944477696,975765504]),(⟨6,0,1⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨6,1,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,98304,-4030464,74252288,-815726592,5970067456,-30698504192,113453891584,-301549387776,565887041536,-730935033856,698884751360,-830074257408,1485819871232,-1932921602048,1180930080768,-49116512256,-202930683904,40910585856]),(⟨0,0,1⟩,[0,98304,-4390912,86343680,-993165312,7458684928,-38504431616,139508187136,-354153234432,616719581184,-723699957760,684604620800,-1023655116800,1903872999424,-2132605992960,925912989696,193145700352,-154743242752]),(⟨0,0,2⟩,[0,-196608,6848512,-102891520,874971136,-4610457600,15228567552,-28752871424,15994912768,51772194816,-109063995392,51146784768,-46842707968,349353803776,-533519237120,173194477568,86257762304]),(⟨0,0,3⟩,[0,-196608,8650752,-158400512,1611202560,-10160701440,41534029824,-110228537344,181736701952,-169763078144,117105098752,-264812953600,531832307712,-387913482240,-13878231040,48190980096]),(⟨0,0,4⟩,[0,98304,-2031616,7536640,145391616,-1959886848,11081515008,-34669985792,60852600832,-53824552960,34759114752,-108328714240,213334130688,-122256523264,-25445367808]),(⟨0,0,5⟩,[0,98304,-4259840,71467008,-618135552,3031433216,-8495955968,12280987648,-5656281088,1025343488,-22068396032,30839439360,1040449536,-4466868224]),(⟨0,0,6⟩,[0,0,-786432,21692416,-237961216,1344012288,-4129554432,6353977344,-3180462080,1363935232,-14012645376,17944477696,975765504]),(⟨0,1,0⟩,[0,98304,-4390912,86343680,-993165312,7458684928,-38504431616,139508187136,-354153234432,616719581184,-723699957760,684604620800,-1023655116800,1903872999424,-2132605992960,925912989696,193145700352,-154743242752]),(⟨0,1,1⟩,[-32768,1114112,-17858560,184909824,-1388871680,7799767040,-32434323456,97229045760,-201063104512,266782048256,-221541924864,274810306560,-786827149312,1346260762624,-930021212160,-65667825664,273811636224]),(⟨0,1,2⟩,[0,98304,-1343488,-8028160,281706496,-2529460224,12173836288,-35809230848,67615391744,-87654629376,95679643648,-105372811264,87494524928,-68920115200,158334124032,-177655152640]),(⟨0,1,3⟩,[65536,-2097152,29622272,-251527168,1466007552,-6169559040,18495537152,-36984061952,43459280896,-27284471808,45543522304,-146838781952,186314489856,-54059073536,-35530113024]),(⟨0,1,4⟩,[0,-458752,11501568,-117932032,640778240,-1920499712,2525954048,2419654656,-14759821312,19292487680,4871782400,-23547969536,-29747085312,63953928192]),(⟨0,1,5⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨0,1,6⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨0,2,0⟩,[0,-196608,6848512,-102891520,874971136,-4610457600,15228567552,-28752871424,15994912768,51772194816,-109063995392,51146784768,-46842707968,349353803776,-533519237120,173194477568,86257762304]),(⟨0,2,1⟩,[0,98304,-1343488,-8028160,281706496,-2529460224,12173836288,-35809230848,67615391744,-87654629376,95679643648,-105372811264,87494524928,-68920115200,158334124032,-177655152640]),(⟨0,2,2⟩,[0,196608,-6815744,97714176,-752091136,3362258944,-8673034240,11301945344,-3373793280,-474808320,-25797066752,45388070912,-3264479232,-52863827968,51161858048]),(⟨0,2,3⟩,[0,-98304,884736,16646144,-313753600,2135326720,-7488471040,13842251776,-11465588736,4671635456,-17680859136,34504572928,-26419757056,19471499264]),(⟨0,2,4⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨0,3,0⟩,[0,-196608,8650752,-158400512,1611202560,-10160701440,41534029824,-110228537344,181736701952,-169763078144,117105098752,-264812953600,531832307712,-387913482240,-13878231040,48190980096]),(⟨0,3,1⟩,[65536,-2097152,29622272,-251527168,1466007552,-6169559040,18495537152,-36984061952,43459280896,-27284471808,45543522304,-146838781952,186314489856,-54059073536,-35530113024]),(⟨0,3,2⟩,[0,-98304,884736,16646144,-313753600,2135326720,-7488471040,13842251776,-11465588736,4671635456,-17680859136,34504572928,-26419757056,19471499264]),(⟨0,3,3⟩,[-65536,1966080,-24969216,182976512,-892469248,3061055488,-7093747712,9599188992,-5654773760,5639110656,-24682496000,28559015936,968884224]),(⟨0,3,4⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨0,4,0⟩,[0,98304,-2031616,7536640,145391616,-1959886848,11081515008,-34669985792,60852600832,-53824552960,34759114752,-108328714240,213334130688,-122256523264,-25445367808]),(⟨0,4,1⟩,[0,-458752,11501568,-117932032,640778240,-1920499712,2525954048,2419654656,-14759821312,19292487680,4871782400,-23547969536,-29747085312,63953928192]),(⟨0,4,2⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨0,4,3⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨0,5,0⟩,[0,98304,-4259840,71467008,-618135552,3031433216,-8495955968,12280987648,-5656281088,1025343488,-22068396032,30839439360,1040449536,-4466868224]),(⟨0,5,1⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨0,6,0⟩,[0,0,-786432,21692416,-237961216,1344012288,-4129554432,6353977344,-3180462080,1363935232,-14012645376,17944477696,975765504]),(⟨0,6,1⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨1,0,0⟩,[0,98304,-4390912,86343680,-993165312,7458684928,-38504431616,139508187136,-354153234432,616719581184,-723699957760,684604620800,-1023655116800,1903872999424,-2132605992960,925912989696,193145700352,-154743242752]),(⟨1,0,1⟩,[-32768,1114112,-17858560,184909824,-1388871680,7799767040,-32434323456,97229045760,-201063104512,266782048256,-221541924864,274810306560,-786827149312,1346260762624,-930021212160,-65667825664,273811636224]),(⟨1,0,2⟩,[0,98304,-1343488,-8028160,281706496,-2529460224,12173836288,-35809230848,67615391744,-87654629376,95679643648,-105372811264,87494524928,-68920115200,158334124032,-177655152640]),(⟨1,0,3⟩,[65536,-2097152,29622272,-251527168,1466007552,-6169559040,18495537152,-36984061952,43459280896,-27284471808,45543522304,-146838781952,186314489856,-54059073536,-35530113024]),(⟨1,0,4⟩,[0,-458752,11501568,-117932032,640778240,-1920499712,2525954048,2419654656,-14759821312,19292487680,4871782400,-23547969536,-29747085312,63953928192]),(⟨1,0,5⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨1,0,6⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨1,1,0⟩,[-32768,1114112,-17858560,184909824,-1388871680,7799767040,-32434323456,97229045760,-201063104512,266782048256,-221541924864,274810306560,-786827149312,1346260762624,-930021212160,-65667825664,273811636224]),(⟨1,1,1⟩,[0,589824,-16613376,199458816,-1350107136,5661130752,-14646411264,18386288640,17151688704,-118522576896,193121845248,-28809854976,-282697728000,116434403328,559239561216,-586558242816]),(⟨1,1,2⟩,[32768,-1048576,13893632,-100073472,430800896,-1117323264,1474756608,627703808,-7463010304,16570515456,-17958567936,13044088832,-959021056,-68248993792,101267210240]),(⟨1,1,3⟩,[0,-655360,16646144,-172752896,945160192,-2816606208,3533438976,3980918784,-20569128960,22938779648,9259319296,-19882835968,-57207291904,87892295680]),(⟨1,1,4⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨1,2,0⟩,[0,98304,-1343488,-8028160,281706496,-2529460224,12173836288,-35809230848,67615391744,-87654629376,95679643648,-105372811264,87494524928,-68920115200,158334124032,-177655152640]),(⟨1,2,1⟩,[32768,-1048576,13893632,-100073472,430800896,-1117323264,1474756608,627703808,-7463010304,16570515456,-17958567936,13044088832,-959021056,-68248993792,101267210240]),(⟨1,2,3⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨1,3,0⟩,[65536,-2097152,29622272,-251527168,1466007552,-6169559040,18495537152,-36984061952,43459280896,-27284471808,45543522304,-146838781952,186314489856,-54059073536,-35530113024]),(⟨1,3,1⟩,[0,-655360,16646144,-172752896,945160192,-2816606208,3533438976,3980918784,-20569128960,22938779648,9259319296,-19882835968,-57207291904,87892295680]),(⟨1,3,2⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨1,3,3⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨1,4,0⟩,[0,-458752,11501568,-117932032,640778240,-1920499712,2525954048,2419654656,-14759821312,19292487680,4871782400,-23547969536,-29747085312,63953928192]),(⟨1,4,1⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨1,5,0⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨1,6,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨2,0,0⟩,[0,-196608,6848512,-102891520,874971136,-4610457600,15228567552,-28752871424,15994912768,51772194816,-109063995392,51146784768,-46842707968,349353803776,-533519237120,173194477568,86257762304]),(⟨2,0,1⟩,[0,98304,-1343488,-8028160,281706496,-2529460224,12173836288,-35809230848,67615391744,-87654629376,95679643648,-105372811264,87494524928,-68920115200,158334124032,-177655152640]),(⟨2,0,2⟩,[0,196608,-6815744,97714176,-752091136,3362258944,-8673034240,11301945344,-3373793280,-474808320,-25797066752,45388070912,-3264479232,-52863827968,51161858048]),(⟨2,0,3⟩,[0,-98304,884736,16646144,-313753600,2135326720,-7488471040,13842251776,-11465588736,4671635456,-17680859136,34504572928,-26419757056,19471499264]),(⟨2,0,4⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨2,1,0⟩,[0,98304,-1343488,-8028160,281706496,-2529460224,12173836288,-35809230848,67615391744,-87654629376,95679643648,-105372811264,87494524928,-68920115200,158334124032,-177655152640]),(⟨2,1,1⟩,[32768,-1048576,13893632,-100073472,430800896,-1117323264,1474756608,627703808,-7463010304,16570515456,-17958567936,13044088832,-959021056,-68248993792,101267210240]),(⟨2,1,3⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨2,2,0⟩,[0,196608,-6815744,97714176,-752091136,3362258944,-8673034240,11301945344,-3373793280,-474808320,-25797066752,45388070912,-3264479232,-52863827968,51161858048]),(⟨2,2,2⟩,[0,393216,-12976128,176685056,-1275723776,5148770304,-10476060672,2443706368,35942825984,-73420898304,49175199744,3625975808,-9717284864]),(⟨2,2,3⟩,[0,393216,-12058624,149422080,-959447040,3328442368,-5200936960,-2702704640,24577572864,-35831545856,13421248512,6987710464]),(⟨2,2,4⟩,[0,-393216,11272192,-124256256,641728512,-1378091008,-350748672,5965873152,-6914310144,83492864,1528561664]),(⟨2,2,5⟩,[0,-393216,11534336,-128450560,659554304,-1361313792,-573571072,6062342144,-5952765952,-327548928]),(⟨2,3,0⟩,[0,-98304,884736,16646144,-313753600,2135326720,-7488471040,13842251776,-11465588736,4671635456,-17680859136,34504572928,-26419757056,19471499264]),(⟨2,3,1⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨2,3,2⟩,[0,393216,-12058624,149422080,-959447040,3328442368,-5200936960,-2702704640,24577572864,-35831545856,13421248512,6987710464]),(⟨2,3,3⟩,[-131072,3407872,-33947648,160432128,-330563584,-115867648,2266234880,-5011144704,1259732992,11573395456,-12992774144]),(⟨2,3,5⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨2,4,0⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨2,4,2⟩,[0,-393216,11272192,-124256256,641728512,-1378091008,-350748672,5965873152,-6914310144,83492864,1528561664]),(⟨2,5,2⟩,[0,-393216,11534336,-128450560,659554304,-1361313792,-573571072,6062342144,-5952765952,-327548928]),(⟨2,5,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,0,0⟩,[0,-196608,8650752,-158400512,1611202560,-10160701440,41534029824,-110228537344,181736701952,-169763078144,117105098752,-264812953600,531832307712,-387913482240,-13878231040,48190980096]),(⟨3,0,1⟩,[65536,-2097152,29622272,-251527168,1466007552,-6169559040,18495537152,-36984061952,43459280896,-27284471808,45543522304,-146838781952,186314489856,-54059073536,-35530113024]),(⟨3,0,2⟩,[0,-98304,884736,16646144,-313753600,2135326720,-7488471040,13842251776,-11465588736,4671635456,-17680859136,34504572928,-26419757056,19471499264]),(⟨3,0,3⟩,[-65536,1966080,-24969216,182976512,-892469248,3061055488,-7093747712,9599188992,-5654773760,5639110656,-24682496000,28559015936,968884224]),(⟨3,0,4⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨3,1,0⟩,[65536,-2097152,29622272,-251527168,1466007552,-6169559040,18495537152,-36984061952,43459280896,-27284471808,45543522304,-146838781952,186314489856,-54059073536,-35530113024]),(⟨3,1,1⟩,[0,-655360,16646144,-172752896,945160192,-2816606208,3533438976,3980918784,-20569128960,22938779648,9259319296,-19882835968,-57207291904,87892295680]),(⟨3,1,2⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨3,1,3⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨3,2,0⟩,[0,-98304,884736,16646144,-313753600,2135326720,-7488471040,13842251776,-11465588736,4671635456,-17680859136,34504572928,-26419757056,19471499264]),(⟨3,2,1⟩,[-32768,983040,-11698176,69795840,-208797696,199098368,475725824,-1214644224,458981376,-1174208512,4735336448,827129856,-7915765760]),(⟨3,2,2⟩,[0,393216,-12058624,149422080,-959447040,3328442368,-5200936960,-2702704640,24577572864,-35831545856,13421248512,6987710464]),(⟨3,2,3⟩,[-131072,3407872,-33947648,160432128,-330563584,-115867648,2266234880,-5011144704,1259732992,11573395456,-12992774144]),(⟨3,2,5⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨3,3,0⟩,[-65536,1966080,-24969216,182976512,-892469248,3061055488,-7093747712,9599188992,-5654773760,5639110656,-24682496000,28559015936,968884224]),(⟨3,3,1⟩,[0,524288,-11665408,99221504,-392691712,571998208,763625472,-3165913088,947388416,3654287360,4296933376,-11058675712]),(⟨3,3,2⟩,[-131072,3407872,-33947648,160432128,-330563584,-115867648,2266234880,-5011144704,1259732992,11573395456,-12992774144]),(⟨3,4,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨3,5,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨4,0,0⟩,[0,98304,-2031616,7536640,145391616,-1959886848,11081515008,-34669985792,60852600832,-53824552960,34759114752,-108328714240,213334130688,-122256523264,-25445367808]),(⟨4,0,1⟩,[0,-458752,11501568,-117932032,640778240,-1920499712,2525954048,2419654656,-14759821312,19292487680,4871782400,-23547969536,-29747085312,63953928192]),(⟨4,0,2⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨4,0,3⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨4,1,0⟩,[0,-458752,11501568,-117932032,640778240,-1920499712,2525954048,2419654656,-14759821312,19292487680,4871782400,-23547969536,-29747085312,63953928192]),(⟨4,1,1⟩,[0,0,0,0,-1048576,25165824,-213909504,679477248,211812352,-5259657216,6127878144,8984199168,-14848884736]),(⟨4,2,0⟩,[0,0,0,0,-524288,12582912,-106954752,339738624,105906176,-2629828608,3063939072,4492099584,-7424442368]),(⟨4,2,2⟩,[0,-393216,11272192,-124256256,641728512,-1378091008,-350748672,5965873152,-6914310144,83492864,1528561664]),(⟨4,3,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨5,0,0⟩,[0,98304,-4259840,71467008,-618135552,3031433216,-8495955968,12280987648,-5656281088,1025343488,-22068396032,30839439360,1040449536,-4466868224]),(⟨5,0,1⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨5,1,0⟩,[-32768,983040,-11698176,69795840,-208273408,186515456,582680576,-1554382848,353075200,1455620096,1671397376,-3664969728,-491323392]),(⟨5,2,2⟩,[0,-393216,11534336,-128450560,659554304,-1361313792,-573571072,6062342144,-5952765952,-327548928]),(⟨5,2,3⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨5,3,2⟩,[131072,-3145728,26738688,-84934656,-26476544,657457152,-765984768,-1123024896,1856110592]),(⟨6,0,0⟩,[0,0,-786432,21692416,-237961216,1344012288,-4129554432,6353977344,-3180462080,1363935232,-14012645376,17944477696,975765504]),(⟨6,0,1⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856]),(⟨6,1,0⟩,[0,262144,-5832704,49610752,-196345856,285999104,381812736,-1582956544,473694208,1827143680,2148466688,-5529337856])]


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
    (Poly.add (Poly.scale (K.ofRat r684) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 4 13).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r683*r683 : ℚ)=r684 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 4 13 r683 r683 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 4=13 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 4 13).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C104

#print axioms Coulomb8.Columns.C104.sound
