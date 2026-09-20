import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C137

def r0 : ℚ := { num := -131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 5062656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -87703552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 912834560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -6487048192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 34122612736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -141244841984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 481597997056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -1383961296896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 3330164572160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -382131027968, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 9762958426112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -10493219930112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := 7002510475264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := -1696047022080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -62354767872, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 756141096960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -17156800512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 3260416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -67387392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 795377664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -6181847040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 34676228096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -21536096256, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 10931208192, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -1592742543360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 3916707676160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -7657936830464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 11241486581760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -11368220753920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 6565346197504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -632496963584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -205926825984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 9655123968, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -9142272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 136691712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := -23805952, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := 6434783232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -24936022016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 72433778688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -9505095680, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := 35993157632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -133809078272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -565692776448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 1828374986752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -2578687131648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 98202124288, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := -6948077568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -7169163264, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 98304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -5652480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 117030912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -1281687552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 8791687168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -42300162048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 156325953536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -469673181184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 1147543519232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -7490289664, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 2888735866880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -335349350400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 708158652416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := 333684948992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := -21933342720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := 3817472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := -5767168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := 9535488, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 283246592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -21315584, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 34802237440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -130059534336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 52278722560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -757736947712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 151877320704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -858787577856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 30785273856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := 2452832256, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := -32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := 2457600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := -51118080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := 72056832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := -2894757888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := 11222319104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := -33375911936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := 4655742976, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := -139012702208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := 155456339968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -74006921216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := -3191504896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 265322496, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := 196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := -8585216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := 124649472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -925630464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 4384227328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -2186674176, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 5835849728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := -77678247936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := 91078459392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -45197492224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := -1228013568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := 16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := -524288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := 1130496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := -80248832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 627163136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -3876487168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 19096649728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := -78273576960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 281810649088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -893493510144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 2347660099584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -673799962624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 952116101120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -5815445782528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 118245900288, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := 8925413376, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := -19342983168, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -1425408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 40124416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := -69697536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := 3493199872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -17163763712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 9134063616, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -188538617856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 431749726208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := -724950466560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := 118303440896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -85915566080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 7197949952, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := -7927349248, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := 6659358720, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 491520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -6668288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 61571072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := -65388544, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := 387055616, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := -742768640, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := 48977870848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := -23214899200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := 434422644736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := -853733752832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := 158990761984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := -792604229632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 16395599872, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := 2939338752, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := -131072, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := 21626880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := -122355712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := 411074560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := -516423680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := -1427898368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 5364383744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -7438336, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -3078750208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 20988952576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := 6653411328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := -90210304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := -262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := 8585216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := -115802112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := 849281024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := -3868000256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := 12491554816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := -33111277568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 75346870272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := -133081989120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 154895056896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -11380523008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -997523456, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 2162098176, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -1464336384, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := 262144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := -2949120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 112984064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -247857152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := -483917824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := 5582225408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -1480065024, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 81169416192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -3678666752, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 238042546176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := -19471794176, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := -167510016, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -5767168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := 7208960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -240123904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 774897664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -2082471936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 4064018432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := -1139802112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -16662134784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := 5243404288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -30277632, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -1703936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := 16580608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := -74973184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := 166854656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := -249298944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := 458358784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 227016704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -3748855808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := 728367104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := -983040, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := -393216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := 1048576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := -50855936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := 181403648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := -440664064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 42991616, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := 465043456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -4694474752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 45481984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := 393216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := -9437184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := 4718592, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := -254803968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := -79429632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := 1972371456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -2297954304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := -28311552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 5111808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -57507840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 370311168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := -28803072, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := 335511552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := 4425646080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := -4115988480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := 29670113280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := 124523839488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -416304955392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 42658922496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := 15204384768, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -36002168832, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 1416167424, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := 753664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -15417344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := 181764096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -1338032128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := 6271401984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := -18261262336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := 28527755264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := 43794432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := -15185182720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := 241428152320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := -256268861440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := 89175932928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := 16723279872, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := -167067648, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 32768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -7176192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := 99647488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -794722304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := 3864330240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -11079712768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 14979497984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := 8117223424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := -9527984128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := 15616409600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := -87742840832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := 8469381120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -56492032, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := 8159232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := -101974016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := 93093888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := -2205155328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := 468910080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := 1865416704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := -54067200, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := 3452698624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := -226590720, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := -133955584, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := 4816896, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := 65536, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := -55181312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := 456392704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := -1972764672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := 4107141120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -912785408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := -14130348032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := 1645150208, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := -2324758528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := -3538944, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -9895936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := 156041216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -4653056, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 986644480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -21126578176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 32814792704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := 5505679360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := -18951831552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := 37390319616, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -4438032384, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := 518848512, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := 67436544, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := 655360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := -2260992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -38928384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := 61341696, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := -1788084224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := 3328376832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := -723255296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -180387840, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 2523267072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -21528576, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 411959296, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -22478848, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := -3145728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 1572864, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -84934656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := -26476544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := 657457152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := -765984768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := -9437184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := -98304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := 393216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := -31260672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := 189136896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -5603328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 1251213312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := 138018816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := -7766016000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := 20359249920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := -398327808, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -418185216, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 96337920, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -1179648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 3145728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -152567808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 544210944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -1321992192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 128974848, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := 1395130368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := -14083424256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := 136445952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := 2531328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := -43851776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := 456417280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := -3243524096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := 17061306368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := -70622420992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := 240798998528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := -691980648448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := 1665082286080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := -191065513984, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := 4881479213056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := -5246609965056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := 3501255237632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := -848023511040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := -31177383936, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := 378070548480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -8578400256, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := 1630208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := -33693696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := 397688832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := -3090923520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := 17338114048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := -10768048128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := 5465604096, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := -796371271680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := 1958353838080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := -3828968415232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := 5620743290880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := -5684110376960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := 3282673098752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := -316248481792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := -102963412992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := 4827561984, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := -4571136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := 68345856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := -11902976, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := 3217391616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := -12468011008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := 36216889344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := -4752547840, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := 17996578816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := -66904539136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := -282846388224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := 914187493376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := -1289343565824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := 49101062144, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := -3474038784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := -3584581632, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := 49152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := -2826240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := 58515456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := -640843776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 4395843584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := -21150081024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := 78162976768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := -234836590592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := 573771759616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := -3745144832, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := 1444367933440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := -167674675200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := 354079326208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := 166842474496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := -10966671360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := 1908736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := -2883584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := 4767744, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := 141623296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := -10657792, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := 17401118720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := -65029767168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := 26139361280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := -378868473856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := 75938660352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := -429393788928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := 15392636928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := 1226416128, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := 1228800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := -25559040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := 36028416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := -1447378944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := 5611159552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := -16687955968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := 2327871488, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := -69506351104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := 77728169984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := -37003460608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := -1595752448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := 132661248, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := -4292608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := 62324736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := -462815232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := 2192113664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := -1093337088, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := 2917924864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := -38839123968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := 45539229696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := -22598746112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := -614006784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := 8192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := 565248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := -40124416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := 313581568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := -1938243584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := 9548324864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := -39136788480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := 140905324544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := -446746755072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := 1173830049792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := -336899981312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r450 : ℚ := { num := 476058050560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r451 : ℚ := { num := -2907722891264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r452 : ℚ := { num := 59122950144, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r453 : ℚ := { num := 4462706688, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r454 : ℚ := { num := -9671491584, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r455 : ℚ := { num := -712704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r456 : ℚ := { num := 20062208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r457 : ℚ := { num := -34848768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r458 : ℚ := { num := 1746599936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r459 : ℚ := { num := -8581881856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r460 : ℚ := { num := 4567031808, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r461 : ℚ := { num := -94269308928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r462 : ℚ := { num := 215874863104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r463 : ℚ := { num := -362475233280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r464 : ℚ := { num := 59151720448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r465 : ℚ := { num := -42957783040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r466 : ℚ := { num := 3598974976, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r467 : ℚ := { num := -3963674624, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r468 : ℚ := { num := 3329679360, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r469 : ℚ := { num := -8192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r470 : ℚ := { num := 245760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r471 : ℚ := { num := -3334144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r472 : ℚ := { num := 30785536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r473 : ℚ := { num := -32694272, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r474 : ℚ := { num := 193527808, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r475 : ℚ := { num := -371384320, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r476 : ℚ := { num := 24488935424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r477 : ℚ := { num := -11607449600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r478 : ℚ := { num := 217211322368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r479 : ℚ := { num := -426866876416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r480 : ℚ := { num := 79495380992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r481 : ℚ := { num := -396302114816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r482 : ℚ := { num := 8197799936, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r483 : ℚ := { num := 1469669376, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r484 : ℚ := { num := -65536, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r485 : ℚ := { num := 10813440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r486 : ℚ := { num := -61177856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r487 : ℚ := { num := 205537280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r488 : ℚ := { num := -258211840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r489 : ℚ := { num := -713949184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r490 : ℚ := { num := 2682191872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r491 : ℚ := { num := -3719168, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r492 : ℚ := { num := -1539375104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r493 : ℚ := { num := 10494476288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r494 : ℚ := { num := 3326705664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r495 : ℚ := { num := -45105152, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r496 : ℚ := { num := 4292608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r497 : ℚ := { num := -57901056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r498 : ℚ := { num := 424640512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r499 : ℚ := { num := -1934000128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r500 : ℚ := { num := 6245777408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r501 : ℚ := { num := -16555638784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r502 : ℚ := { num := 37673435136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r503 : ℚ := { num := -66540994560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r504 : ℚ := { num := 77447528448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r505 : ℚ := { num := -5690261504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r506 : ℚ := { num := -498761728, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r507 : ℚ := { num := 1081049088, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r508 : ℚ := { num := -732168192, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r509 : ℚ := { num := 131072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r510 : ℚ := { num := -1474560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r511 : ℚ := { num := 56492032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r512 : ℚ := { num := -123928576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r513 : ℚ := { num := -241958912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r514 : ℚ := { num := 2791112704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r515 : ℚ := { num := -740032512, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r516 : ℚ := { num := 40584708096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r517 : ℚ := { num := -1839333376, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r518 : ℚ := { num := 119021273088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r519 : ℚ := { num := -9735897088, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r520 : ℚ := { num := -83755008, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r521 : ℚ := { num := -2883584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r522 : ℚ := { num := 3604480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r523 : ℚ := { num := -120061952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r524 : ℚ := { num := 387448832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r525 : ℚ := { num := -1041235968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r526 : ℚ := { num := 2032009216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r527 : ℚ := { num := -569901056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r528 : ℚ := { num := -8331067392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r529 : ℚ := { num := 2621702144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r530 : ℚ := { num := -15138816, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r531 : ℚ := { num := 32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r532 : ℚ := { num := -851968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r533 : ℚ := { num := 8290304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r534 : ℚ := { num := -37486592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r535 : ℚ := { num := 83427328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r536 : ℚ := { num := -124649472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r537 : ℚ := { num := 229179392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r538 : ℚ := { num := 113508352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r539 : ℚ := { num := -1874427904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r540 : ℚ := { num := 364183552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r541 : ℚ := { num := -491520, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r542 : ℚ := { num := 524288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r543 : ℚ := { num := -25427968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r544 : ℚ := { num := 90701824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r545 : ℚ := { num := -220332032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r546 : ℚ := { num := 21495808, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r547 : ℚ := { num := 232521728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r548 : ℚ := { num := -2347237376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r549 : ℚ := { num := 22740992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r550 : ℚ := { num := -4718592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r551 : ℚ := { num := 2359296, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r552 : ℚ := { num := -127401984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r553 : ℚ := { num := -39714816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r554 : ℚ := { num := 986185728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r555 : ℚ := { num := -1148977152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r556 : ℚ := { num := -14155776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r557 : ℚ := { num := 2555904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r558 : ℚ := { num := -28753920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r559 : ℚ := { num := 185155584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r560 : ℚ := { num := -14401536, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r561 : ℚ := { num := 167755776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r562 : ℚ := { num := 2212823040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r563 : ℚ := { num := -2057994240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r564 : ℚ := { num := 14835056640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r565 : ℚ := { num := 62261919744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r566 : ℚ := { num := -208152477696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r567 : ℚ := { num := 21329461248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r568 : ℚ := { num := 7602192384, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r569 : ℚ := { num := -18001084416, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r570 : ℚ := { num := 708083712, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r571 : ℚ := { num := 376832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r572 : ℚ := { num := -7708672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r573 : ℚ := { num := 90882048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r574 : ℚ := { num := -669016064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r575 : ℚ := { num := 3135700992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r576 : ℚ := { num := -9130631168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r577 : ℚ := { num := 14263877632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r578 : ℚ := { num := 21897216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r579 : ℚ := { num := -7592591360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r580 : ℚ := { num := 120714076160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r581 : ℚ := { num := -128134430720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r582 : ℚ := { num := 44587966464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r583 : ℚ := { num := 8361639936, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r584 : ℚ := { num := -83533824, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r585 : ℚ := { num := 16384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r586 : ℚ := { num := -3588096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r587 : ℚ := { num := 49823744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r588 : ℚ := { num := -397361152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r589 : ℚ := { num := 1932165120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r590 : ℚ := { num := -5539856384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r591 : ℚ := { num := 7489748992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r592 : ℚ := { num := 4058611712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r593 : ℚ := { num := -4763992064, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r594 : ℚ := { num := 7808204800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r595 : ℚ := { num := -43871420416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r596 : ℚ := { num := 4234690560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r597 : ℚ := { num := -28246016, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r598 : ℚ := { num := 4079616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r599 : ℚ := { num := -50987008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r600 : ℚ := { num := 46546944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r601 : ℚ := { num := -1102577664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r602 : ℚ := { num := 234455040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r603 : ℚ := { num := 932708352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r604 : ℚ := { num := -27033600, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r605 : ℚ := { num := 1726349312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r606 : ℚ := { num := -113295360, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r607 : ℚ := { num := -66977792, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r608 : ℚ := { num := 2408448, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r609 : ℚ := { num := 32768, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r610 : ℚ := { num := -27590656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r611 : ℚ := { num := 228196352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r612 : ℚ := { num := -986382336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r613 : ℚ := { num := 2053570560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r614 : ℚ := { num := -456392704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r615 : ℚ := { num := -7065174016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r616 : ℚ := { num := 822575104, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r617 : ℚ := { num := -1162379264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r618 : ℚ := { num := -1769472, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r619 : ℚ := { num := -4947968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r620 : ℚ := { num := 78020608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r621 : ℚ := { num := -2326528, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r622 : ℚ := { num := 493322240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r623 : ℚ := { num := -10563289088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r624 : ℚ := { num := 16407396352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r625 : ℚ := { num := 2752839680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r626 : ℚ := { num := -9475915776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r627 : ℚ := { num := 18695159808, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r628 : ℚ := { num := -2219016192, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r629 : ℚ := { num := 259424256, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r630 : ℚ := { num := 33718272, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r631 : ℚ := { num := 327680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r632 : ℚ := { num := -1130496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r633 : ℚ := { num := -19464192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r634 : ℚ := { num := 30670848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r635 : ℚ := { num := -894042112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r636 : ℚ := { num := 1664188416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r637 : ℚ := { num := -361627648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r638 : ℚ := { num := -90193920, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r639 : ℚ := { num := 1261633536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r640 : ℚ := { num := -10764288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r641 : ℚ := { num := 205979648, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r642 : ℚ := { num := -11239424, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r643 : ℚ := { num := -1572864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r644 : ℚ := { num := 786432, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r645 : ℚ := { num := -42467328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r646 : ℚ := { num := -13238272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r647 : ℚ := { num := 328728576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r648 : ℚ := { num := -382992384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r649 : ℚ := { num := -4718592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r650 : ℚ := { num := -49152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r651 : ℚ := { num := 196608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r652 : ℚ := { num := -15630336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r653 : ℚ := { num := 94568448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r654 : ℚ := { num := -2801664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r655 : ℚ := { num := 625606656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r656 : ℚ := { num := 69009408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r657 : ℚ := { num := -3883008000, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r658 : ℚ := { num := 10179624960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r659 : ℚ := { num := -199163904, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r660 : ℚ := { num := -209092608, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r661 : ℚ := { num := 48168960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r662 : ℚ := { num := -589824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r663 : ℚ := { num := 1572864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r664 : ℚ := { num := -76283904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r665 : ℚ := { num := 272105472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r666 : ℚ := { num := -660996096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r667 : ℚ := { num := 64487424, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r668 : ℚ := { num := 697565184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r669 : ℚ := { num := -7041712128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r670 : ℚ := { num := 68222976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r671 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r672 : ℚ := { num := 1, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17],[0,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34],[0,r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50],[0,r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63,r64,r65],[0,r0,r66,r67,r68,r69,r70,r71,r72,r73,r74,r75,r76,r77,r78],[0,r79,r80,r81,r82,r83,r84,r85,r86,r87,r88,r89,r90,r91],[0,0,r92,r93,r94,r95,r96,r97,r98,r99,r100,r101,r102],[],[],[],[],[],[],[r103,r104,r105,r106,r107,r108,r109,r110,r111,r112,r113,r114,r115,r116,r117,r118,r119],[0,0,r120,r121,r122,r123,r124,r125,r126,r127,r128,r129,r130,r131,r132,r133],[r134,r135,r136,r137,r138,r139,r140,r141,r142,r143,r144,r145,r146,r147,r148],[0,r51,r149,r150,r151,r152,r153,r154,r155,r156,r157,r158,r159,r160],[],[],[],[],[],[],[],[0,r161,r162,r163,r164,r165,r166,r167,r168,r169,r170,r171,r172,r173,r174],[0,r79,r80,r81,r82,r83,r84,r85,r86,r87,r88,r89,r90,r91],[],[],[],[],[],[],[],[r18,r175,r176,r177,r178,r179,r180,r181,r182,r183,r184,r185,r186],[0,r35,r187,r188,r189,r190,r191,r192,r193,r194,r195,r196],[r197,r198,r199,r200,r201,r202,r203,r204,r205,r206,r207],[0,r208,r209,r210,r211,r212,r213,r214,r215,r216],[],[],[],[0,0,r217,r218,r219,r220,r221,r222,r223,r224,393216],[],[],[],[],[],[],[],[],[0,r225,r226,r227,r228,r229,r230,r231,r232,r233,r234,r235,r236,r237,r238,r239],[r134,r240,r241,r242,r243,r244,r245,r246,r247,r248,r249,r250,r251,r252,r253],[0,r254,r255,r256,r257,r258,r259,r260,r261,r262,r263,r264,r265,r266],[0,r161,r267,r268,r269,r270,r271,r272,r273,r274,r275,r276,r277],[0,r18,r278,r279,r280,r281,r282,r283,r284,r285,r286,r287],[],[],[],[],[],[0,r35,r288,r289,r290,r291,r292,r293,r294,r295,r296,r297,r298,r299],[r79,r300,r301,r302,r303,r304,r305,r306,r307,r308,r309,r310,r311],[0,r18,r278,r279,r280,r281,r282,r283,r284,r285,r286,r287],[],[],[],[],[],[0,r35,r187,r188,r189,r190,r191,r192,r193,r194,r195,r196],[0,0,r217,r218,r219,r220,r221,r222,r223,r224,393216],[],[],[],[],[],[r312,r313,r314,r315,r316,r317,r318,r319,131072],[],[],[],[],[r320,r321,r322,r323,r324,r325,r326,r327,r328,r329,r330,r331,-4816896],[],[],[],[],[],[],[r197,r198,r199,r200,r201,r202,r203,r204,r205,r206,r207],[],[],[],[],[r312,r313,r314,r315,r316,r317,r318,r319,131072],[],[],[],[0,r332,r333,r334,r335,r336,r337,r338,r339,r340],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,r18,r341,r342,r343,r344,r345,r346,r347,r348,r349,r350,r351,r352,r353,r354,r355,r356,r357]),(⟨0,0,1⟩,[0,r79,r358,r359,r360,r361,r362,r363,r364,r365,r366,r367,r368,r369,r370,r371,r372,r373]),(⟨0,0,2⟩,[0,r312,r374,r375,r376,r377,r378,r379,r380,r381,r382,r383,r384,r385,r386,r387,r388]),(⟨0,0,3⟩,[0,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398,r399,r400,r401,r402,r403]),(⟨0,0,4⟩,[0,r18,r404,r405,r406,r407,r408,r409,r410,r411,r412,r413,r414,r415,r416]),(⟨0,0,5⟩,[0,r134,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427,r428]),(⟨0,0,6⟩,[0,0,r51,r429,r430,r431,r432,r433,r434,r435,r436,r437,r438]),(⟨0,1,0⟩,[0,r79,r358,r359,r360,r361,r362,r363,r364,r365,r366,r367,r368,r369,r370,r371,r372,r373]),(⟨0,1,1⟩,[r439,r161,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451,r452,r453,r454]),(⟨0,1,2⟩,[0,0,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466,r467,r468]),(⟨0,1,3⟩,[r469,r470,r471,r472,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483]),(⟨0,1,4⟩,[0,r389,r484,r485,r486,r487,r488,r489,r490,r491,r492,r493,r494,r495]),(⟨0,2,0⟩,[0,r312,r374,r375,r376,r377,r378,r379,r380,r381,r382,r383,r384,r385,r386,r387,r388]),(⟨0,2,1⟩,[0,0,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466,r467,r468]),(⟨0,2,2⟩,[0,r0,r496,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508]),(⟨0,2,3⟩,[0,r134,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427,r428]),(⟨0,3,0⟩,[0,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398,r399,r400,r401,r402,r403]),(⟨0,3,1⟩,[r469,r470,r471,r472,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483]),(⟨0,3,2⟩,[0,r134,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427,r428]),(⟨0,3,3⟩,[r79,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518,r519,r520]),(⟨0,3,4⟩,[0,r312,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530]),(⟨0,3,5⟩,[r531,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541]),(⟨0,3,6⟩,[0,r225,r542,r543,r544,r545,r546,r547,r548,r549]),(⟨0,4,0⟩,[0,r18,r404,r405,r406,r407,r408,r409,r410,r411,r412,r413,r414,r415,r416]),(⟨0,4,1⟩,[0,r389,r484,r485,r486,r487,r488,r489,r490,r491,r492,r493,r494,r495]),(⟨0,4,3⟩,[0,r312,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530]),(⟨0,4,4⟩,[0,0,r92,r550,r551,r552,r553,r554,r555,r556,196608]),(⟨0,5,0⟩,[0,r134,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427,r428]),(⟨0,5,3⟩,[r531,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541]),(⟨0,6,0⟩,[0,0,r51,r429,r430,r431,r432,r433,r434,r435,r436,r437,r438]),(⟨0,6,3⟩,[0,r225,r542,r543,r544,r545,r546,r547,r548,r549]),(⟨1,0,0⟩,[0,r79,r358,r359,r360,r361,r362,r363,r364,r365,r366,r367,r368,r369,r370,r371,r372,r373]),(⟨1,0,1⟩,[r439,r161,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451,r452,r453,r454]),(⟨1,0,2⟩,[0,0,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466,r467,r468]),(⟨1,0,3⟩,[r469,r470,r471,r472,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483]),(⟨1,0,4⟩,[0,r389,r484,r485,r486,r487,r488,r489,r490,r491,r492,r493,r494,r495]),(⟨1,1,0⟩,[r439,r161,r440,r441,r442,r443,r444,r445,r446,r447,r448,r449,r450,r451,r452,r453,r454]),(⟨1,1,1⟩,[0,r320,r557,r558,r559,r560,r561,r562,r563,r564,r565,r566,r567,r568,r569,r570]),(⟨1,1,2⟩,[r469,r571,r572,r573,r574,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584]),(⟨1,1,3⟩,[0,r585,r586,r587,r588,r589,r590,r591,r592,r593,r594,r595,r596,r597]),(⟨1,1,4⟩,[0,r0,r598,r599,r600,r601,r602,r603,r604,r605,r606,r607,r608]),(⟨1,1,5⟩,[0,r79,r609,r610,r611,r612,r613,r614,r615,r616,r617,r618]),(⟨1,2,0⟩,[0,0,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466,r467,r468]),(⟨1,2,1⟩,[r469,r571,r572,r573,r574,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584]),(⟨1,2,2⟩,[0,r312,r619,r620,r621,r622,r623,r624,r625,r626,r627,r628,r629,r630]),(⟨1,2,3⟩,[r134,r631,r632,r633,r634,r635,r636,r637,r638,r639,r640,r641,r642]),(⟨1,2,4⟩,[0,r79,r609,r610,r611,r612,r613,r614,r615,r616,r617,r618]),(⟨1,3,0⟩,[r469,r470,r471,r472,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483]),(⟨1,3,1⟩,[0,r585,r586,r587,r588,r589,r590,r591,r592,r593,r594,r595,r596,r597]),(⟨1,3,2⟩,[r134,r631,r632,r633,r634,r635,r636,r637,r638,r639,r640,r641,r642]),(⟨1,3,3⟩,[0,r312,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530]),(⟨1,3,4⟩,[0,0,r92,r550,r551,r552,r553,r554,r555,r556,196608]),(⟨1,4,0⟩,[0,r389,r484,r485,r486,r487,r488,r489,r490,r491,r492,r493,r494,r495]),(⟨1,4,1⟩,[0,r0,r598,r599,r600,r601,r602,r603,r604,r605,r606,r607,r608]),(⟨1,4,2⟩,[0,r79,r609,r610,r611,r612,r613,r614,r615,r616,r617,r618]),(⟨1,4,3⟩,[0,0,r92,r550,r551,r552,r553,r554,r555,r556,196608]),(⟨1,4,5⟩,[r197,r643,r644,r645,r646,r647,r648,r649,65536]),(⟨1,5,1⟩,[0,r79,r609,r610,r611,r612,r613,r614,r615,r616,r617,r618]),(⟨1,5,4⟩,[r197,r643,r644,r645,r646,r647,r648,r649,65536]),(⟨2,0,0⟩,[0,r312,r374,r375,r376,r377,r378,r379,r380,r381,r382,r383,r384,r385,r386,r387,r388]),(⟨2,0,1⟩,[0,0,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466,r467,r468]),(⟨2,0,2⟩,[0,r0,r496,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508]),(⟨2,0,3⟩,[0,r134,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427,r428]),(⟨2,1,0⟩,[0,0,r455,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466,r467,r468]),(⟨2,1,1⟩,[r469,r571,r572,r573,r574,r575,r576,r577,r578,r579,r580,r581,r582,r583,r584]),(⟨2,1,2⟩,[0,r312,r619,r620,r621,r622,r623,r624,r625,r626,r627,r628,r629,r630]),(⟨2,1,3⟩,[r134,r631,r632,r633,r634,r635,r636,r637,r638,r639,r640,r641,r642]),(⟨2,1,4⟩,[0,r79,r609,r610,r611,r612,r613,r614,r615,r616,r617,r618]),(⟨2,2,0⟩,[0,r0,r496,r497,r498,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508]),(⟨2,2,1⟩,[0,r312,r619,r620,r621,r622,r623,r624,r625,r626,r627,r628,r629,r630]),(⟨2,2,2⟩,[r650,r651,r652,r653,r654,r655,r656,r657,r658,r659,r660,r661,-2408448]),(⟨2,3,0⟩,[0,r134,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427,r428]),(⟨2,3,1⟩,[r134,r631,r632,r633,r634,r635,r636,r637,r638,r639,r640,r641,r642]),(⟨2,3,3⟩,[r531,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541]),(⟨2,4,1⟩,[0,r79,r609,r610,r611,r612,r613,r614,r615,r616,r617,r618]),(⟨2,4,4⟩,[r197,r643,r644,r645,r646,r647,r648,r649,65536]),(⟨3,0,0⟩,[0,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398,r399,r400,r401,r402,r403]),(⟨3,0,1⟩,[r469,r470,r471,r472,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483]),(⟨3,0,2⟩,[0,r134,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427,r428]),(⟨3,0,3⟩,[r79,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518,r519,r520]),(⟨3,0,4⟩,[0,r312,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530]),(⟨3,0,5⟩,[r531,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541]),(⟨3,0,6⟩,[0,r225,r542,r543,r544,r545,r546,r547,r548,r549]),(⟨3,1,0⟩,[r469,r470,r471,r472,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483]),(⟨3,1,1⟩,[0,r585,r586,r587,r588,r589,r590,r591,r592,r593,r594,r595,r596,r597]),(⟨3,1,2⟩,[r134,r631,r632,r633,r634,r635,r636,r637,r638,r639,r640,r641,r642]),(⟨3,1,3⟩,[0,r312,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530]),(⟨3,1,4⟩,[0,0,r92,r550,r551,r552,r553,r554,r555,r556,196608]),(⟨3,2,0⟩,[0,r134,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427,r428]),(⟨3,2,1⟩,[r134,r631,r632,r633,r634,r635,r636,r637,r638,r639,r640,r641,r642]),(⟨3,2,3⟩,[r531,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541]),(⟨3,3,0⟩,[r79,r509,r510,r511,r512,r513,r514,r515,r516,r517,r518,r519,r520]),(⟨3,3,1⟩,[0,r312,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530]),(⟨3,3,2⟩,[r531,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541]),(⟨3,3,3⟩,[0,r662,r663,r664,r665,r666,r667,r668,r669,r670]),(⟨3,4,0⟩,[0,r312,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530]),(⟨3,4,1⟩,[0,0,r92,r550,r551,r552,r553,r554,r555,r556,196608]),(⟨3,5,0⟩,[r531,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541]),(⟨3,6,0⟩,[0,r225,r542,r543,r544,r545,r546,r547,r548,r549]),(⟨4,0,0⟩,[0,r18,r404,r405,r406,r407,r408,r409,r410,r411,r412,r413,r414,r415,r416]),(⟨4,0,1⟩,[0,r389,r484,r485,r486,r487,r488,r489,r490,r491,r492,r493,r494,r495]),(⟨4,0,3⟩,[0,r312,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530]),(⟨4,0,4⟩,[0,0,r92,r550,r551,r552,r553,r554,r555,r556,196608]),(⟨4,1,0⟩,[0,r389,r484,r485,r486,r487,r488,r489,r490,r491,r492,r493,r494,r495]),(⟨4,1,1⟩,[0,r0,r598,r599,r600,r601,r602,r603,r604,r605,r606,r607,r608]),(⟨4,1,2⟩,[0,r79,r609,r610,r611,r612,r613,r614,r615,r616,r617,r618]),(⟨4,1,3⟩,[0,0,r92,r550,r551,r552,r553,r554,r555,r556,196608]),(⟨4,1,5⟩,[r197,r643,r644,r645,r646,r647,r648,r649,65536]),(⟨4,2,1⟩,[0,r79,r609,r610,r611,r612,r613,r614,r615,r616,r617,r618]),(⟨4,2,4⟩,[r197,r643,r644,r645,r646,r647,r648,r649,65536]),(⟨4,3,0⟩,[0,r312,r521,r522,r523,r524,r525,r526,r527,r528,r529,r530]),(⟨4,3,1⟩,[0,0,r92,r550,r551,r552,r553,r554,r555,r556,196608]),(⟨4,4,0⟩,[0,0,r92,r550,r551,r552,r553,r554,r555,r556,196608]),(⟨4,4,2⟩,[r197,r643,r644,r645,r646,r647,r648,r649,65536]),(⟨4,5,1⟩,[r197,r643,r644,r645,r646,r647,r648,r649,65536]),(⟨5,0,0⟩,[0,r134,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427,r428]),(⟨5,0,3⟩,[r531,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541]),(⟨5,1,1⟩,[0,r79,r609,r610,r611,r612,r613,r614,r615,r616,r617,r618]),(⟨5,1,4⟩,[r197,r643,r644,r645,r646,r647,r648,r649,65536]),(⟨5,3,0⟩,[r531,r532,r533,r534,r535,r536,r537,r538,r539,r540,r541]),(⟨5,4,1⟩,[r197,r643,r644,r645,r646,r647,r648,r649,65536]),(⟨6,0,0⟩,[0,0,r51,r429,r430,r431,r432,r433,r434,r435,r436,r437,r438]),(⟨6,0,3⟩,[0,r225,r542,r543,r544,r545,r546,r547,r548,r549]),(⟨6,3,0⟩,[0,r225,r542,r543,r544,r545,r546,r547,r548,r549])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,-512,11584,-106560,532736,-1621824,3051904,-3282624,1363712,606272,-407232]),(⟨0,0,1⟩,[0,-256,6592,-65600,337472,-994752,1716288,-1563072,348096,460992]),(⟨0,0,2⟩,[0,512,-9792,66304,-201792,309760,-192192,-87808,65856]),(⟨0,0,3⟩,[0,128,-4736,47104,-188672,361600,-281728,-48384]),(⟨0,1,0⟩,[0,-256,6592,-65600,337472,-994752,1716288,-1563072,348096,460992]),(⟨0,1,1⟩,[64,-1024,6144,-20992,42368,-19456,-107520,326144,-373184]),(⟨0,2,0⟩,[0,512,-9792,66304,-201792,309760,-192192,-87808,65856]),(⟨0,3,0⟩,[0,128,-4736,47104,-188672,361600,-281728,-48384]),(⟨0,3,3⟩,[-256,3072,-7680,-9216,30464]),(⟨1,0,0⟩,[0,-256,6592,-65600,337472,-994752,1716288,-1563072,348096,460992]),(⟨1,0,1⟩,[64,-1024,6144,-20992,42368,-19456,-107520,326144,-373184]),(⟨1,1,0⟩,[64,-1024,6144,-20992,42368,-19456,-107520,326144,-373184]),(⟨2,0,0⟩,[0,512,-9792,66304,-201792,309760,-192192,-87808,65856]),(⟨3,0,0⟩,[0,128,-4736,47104,-188672,361600,-281728,-48384]),(⟨3,0,3⟩,[-256,3072,-7680,-9216,30464]),(⟨3,3,0⟩,[-256,3072,-7680,-9216,30464])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[128,-2048,12672,-45312,136064,-378368,739968,-708864,147456]),(⟨0,0,1⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨0,0,2⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨0,0,3⟩,[0,768,-5120,14848,-50176,88832]),(⟨0,1,0⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨0,1,1⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨0,2,0⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨0,3,0⟩,[0,768,-5120,14848,-50176,88832]),(⟨1,0,0⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨1,0,1⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨1,1,0⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨1,1,2⟩,[-256,3072,-7680,-9216,30464]),(⟨1,2,1⟩,[-256,3072,-7680,-9216,30464]),(⟨2,0,0⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨2,1,1⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[0,768,-5120,14848,-50176,88832])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 9 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r671) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 11 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r671) sourceRight))).isZero := by decide +kernel

noncomputable def partial16 : Poly := []

theorem partial_sound16 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 16)
      sourceRight).eval u v t=partial16.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨2,0,0⟩,[0,512,-9792,66304,-201792,309760,-192192,-87808,65856]),(⟨3,0,0⟩,[0,128,-4736,47104,-188672,361600,-281728,-48384]),(⟨3,0,3⟩,[-256,3072,-7680,-9216,30464]),(⟨3,3,0⟩,[-256,3072,-7680,-9216,30464])]

noncomputable def partial12 : Poly := [(⟨2,0,0⟩,[0,65536,-2301952,35028992,-308903936,1806483456,-7746527232,26556678144,-76435685376,182039379968,-336304431104,439820222464,-349364715520,92021047296,82635399168,-59630764032,9710862336]),(⟨2,0,1⟩,[0,0,-262144,7634944,-95223808,693092352,-3466002432,13426409472,-42715185152,109025001472,-207784116224,268399149056,-194648014848,22282158080,67773726720,-27261222912]),(⟨2,0,2⟩,[0,-65536,2170880,-29638656,220135424,-1014284288,3289587712,-8590622720,18802212864,-31328993280,33633951744,-15036399616,-7096893440,6423330816,-885104640]),(⟨2,0,3⟩,[0,0,393216,-10141696,108658688,-665534464,2792357888,-8926494720,21530935296,-35821617152,35519070208,-11689115648,-11104550912,5850120192]),(⟨2,1,0⟩,[0,0,-262144,7634944,-95223808,693092352,-3466002432,13426409472,-42715185152,109025001472,-207784116224,268399149056,-194648014848,22282158080,67773726720,-27261222912]),(⟨2,1,1⟩,[0,0,0,-393216,12238848,-152961024,977485824,-3307732992,4923555840,2798125056,-23438131200,36253335552,-16654417920,-9845735424,6018711552]),(⟨2,2,0⟩,[0,-65536,2170880,-29638656,220135424,-1014284288,3289587712,-8590622720,18802212864,-31328993280,33633951744,-15036399616,-7096893440,6423330816,-885104640]),(⟨2,3,0⟩,[0,0,393216,-10141696,108658688,-665534464,2792357888,-8926494720,21530935296,-35821617152,35519070208,-11689115648,-11104550912,5850120192]),(⟨3,0,0⟩,[0,16384,-1130496,24985600,-281657344,1954693120,-9460678656,35424321536,-109660307456,279997235200,-554442571776,776673673216,-668956803072,239506472960,60528918528,-34395734016]),(⟨3,0,1⟩,[0,0,-65536,2686976,-38912000,297172992,-1572847616,7384858624,-31390138368,103457947648,-236821577728,349162110976,-289479245824,83688062976,26047365120]),(⟨3,0,2⟩,[0,-16384,835584,-15417344,143540224,-781844480,2818801664,-7761461248,18042880000,-33684733952,42209099776,-25314344960,-65716224,650280960]),(⟨3,0,3⟩,[-32768,917504,-10420224,60784640,-186253312,220856320,598999040,-4927193088,20159234048,-51288211456,73482043392,-45552533504,194052096]),(⟨3,0,4⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨3,0,5⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨3,0,6⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨3,1,0⟩,[0,0,-65536,2686976,-38912000,297172992,-1572847616,7384858624,-31390138368,103457947648,-236821577728,349162110976,-289479245824,83688062976,26047365120]),(⟨3,1,1⟩,[0,0,0,-98304,4816896,-82771968,684589056,-2959147008,6160711680,-1369178112,-21195522048,41951330304,-24409964544,-4421910528]),(⟨3,1,2⟩,[0,-131072,4079616,-50987008,325828608,-1102577664,1641185280,932708352,-7812710400,12084445184,-5551472640,-3281911808,2006237184]),(⟨3,1,3⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨3,1,4⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨3,2,0⟩,[0,-16384,835584,-15417344,143540224,-781844480,2818801664,-7761461248,18042880000,-33684733952,42209099776,-25314344960,-65716224,650280960]),(⟨3,2,1⟩,[0,-131072,4079616,-50987008,325828608,-1102577664,1641185280,932708352,-7812710400,12084445184,-5551472640,-3281911808,2006237184]),(⟨3,2,3⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨3,3,0⟩,[-32768,917504,-10420224,60784640,-186253312,220856320,598999040,-4927193088,20159234048,-51288211456,73482043392,-45552533504,194052096]),(⟨3,3,1⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨3,3,2⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨3,3,3⟩,[0,-393216,7340032,-50855936,181403648,-440664064,730857472,465043456,-4694474752,5412356096]),(⟨3,4,0⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨3,4,1⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨3,5,0⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨3,6,0⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨4,0,0⟩,[0,-65536,2105344,-26558464,168984576,-564150272,739254272,2101968896,-17511481344,69330829312,-179749494784,297872375808,-279921721344,99957129216,19143548928]),(⟨4,0,1⟩,[0,0,0,-98304,4816896,-82771968,684589056,-2959147008,6160711680,-1369178112,-21195522048,41951330304,-24409964544,-4421910528]),(⟨4,0,3⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨4,0,4⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨4,1,0⟩,[0,0,0,-98304,4816896,-82771968,684589056,-2959147008,6160711680,-1369178112,-21195522048,41951330304,-24409964544,-4421910528]),(⟨4,1,1⟩,[0,-131072,4079616,-50987008,325828608,-1102577664,1641185280,932708352,-7812710400,12084445184,-5551472640,-3281911808,2006237184]),(⟨4,1,2⟩,[0,-32768,1605632,-27590656,228196352,-986382336,2053570560,-456392704,-7065174016,13983776768,-8136654848,-1473970176]),(⟨4,1,3⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨4,1,5⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,2,1⟩,[0,-32768,1605632,-27590656,228196352,-986382336,2053570560,-456392704,-7065174016,13983776768,-8136654848,-1473970176]),(⟨4,2,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,3,0⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨4,3,1⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨4,4,0⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨4,4,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,5,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,0,0⟩,[0,-16384,1228800,-25559040,252198912,-1447378944,5611159552,-16687955968,39573815296,-69506351104,77728169984,-37003460608,-11170267136,6500401152]),(⟨5,0,3⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨5,1,1⟩,[0,-32768,1605632,-27590656,228196352,-986382336,2053570560,-456392704,-7065174016,13983776768,-8136654848,-1473970176]),(⟨5,1,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,3,0⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨5,4,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨6,0,0⟩,[0,0,98304,-4292608,62324736,-462815232,2192113664,-7653359616,20425474048,-38839123968,45539229696,-22598746112,-4298047488]),(⟨6,0,3⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨6,3,0⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048])]


theorem partial_checked12 :
    (Poly.add (Poly.add (Poly.mul chunk12 sourceRight) partial16)
      (Poly.scale (K.ofRat (-1)) partial12)).isZero := by decide +kernel

theorem partial_sound12 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 12)
      sourceRight).eval u v t=partial12.eval u v t := by
  change (Poly.mul (chunk12++(sourceLeft.drop 16))
    sourceRight).eval u v t=partial12.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound16 partial_checked12 u v t


noncomputable def chunk8 : Poly := [(⟨0,3,3⟩,[-256,3072,-7680,-9216,30464]),(⟨1,0,0⟩,[0,-256,6592,-65600,337472,-994752,1716288,-1563072,348096,460992]),(⟨1,0,1⟩,[64,-1024,6144,-20992,42368,-19456,-107520,326144,-373184]),(⟨1,1,0⟩,[64,-1024,6144,-20992,42368,-19456,-107520,326144,-373184])]

noncomputable def partial8 : Poly := [(⟨0,3,3⟩,[-32768,917504,-10518528,65077248,-248578048,683671552,-1593114624,2726166528,-266240000,-12449087488,27942813696,-22953787392,4492099584]),(⟨0,3,4⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨0,3,5⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨0,3,6⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨0,4,3⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨0,4,4⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨0,5,3⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨0,6,3⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨1,0,0⟩,[0,-32768,1368064,-25141248,272678912,-1983283200,10499645440,-43221491712,145866801152,-414520606720,981392203776,-1856977035264,2642795642880,-2588904161280,1444237713408,-136117739520,-275451789312,67976036352]),(⟨1,0,1⟩,[8192,-262144,3825664,-35831808,254287872,-1467924480,6988603392,-27634270208,92128911360,-259620831232,601140011008,-1079495081984,1377273438208,-1048203345920,182323470336,388511563776,-245856780288]),(⟨1,0,2⟩,[0,0,-450560,12230656,-141295616,936476672,-4107329536,13362929664,-35709190144,82238767104,-158820376576,245160009728,-302355644416,317165305856,-281061466112,148284530688]),(⟨1,0,3⟩,[-8192,245760,-3268608,28098560,-189947904,1057521664,-4740685824,17104076800,-49862008832,113753374720,-190045298688,207305555968,-106822868992,-26303463424,45966434304]),(⟨1,0,4⟩,[0,49152,-1114112,10911744,-65994752,288309248,-942800896,2245197824,-3478519808,1186938880,10419896320,-31456854016,47696904192,-33150681088]),(⟨1,1,0⟩,[8192,-262144,3825664,-35831808,254287872,-1467924480,6988603392,-27634270208,92128911360,-259620831232,601140011008,-1079495081984,1377273438208,-1048203345920,182323470336,388511563776,-245856780288]),(⟨1,1,1⟩,[0,-65536,1703936,-19365888,130859008,-587481088,1791410176,-3704668160,6240960512,-14721056768,37378686976,-39271202816,-96761692160,411435974656,-607103107072,351091507200]),(⟨1,1,2⟩,[-8192,245760,-3121152,23101440,-117645312,446316544,-1254727680,2430533632,-2274713600,-3774332928,19253305344,-36151721984,32403660800,6029950976,-29090439168]),(⟨1,1,3⟩,[0,49152,-1114112,10911744,-65994752,288309248,-942800896,2245197824,-3478519808,1186938880,10419896320,-31456854016,47696904192,-33150681088]),(⟨1,2,0⟩,[0,0,-450560,12230656,-141295616,936476672,-4107329536,13362929664,-35709190144,82238767104,-158820376576,245160009728,-302355644416,317165305856,-281061466112,148284530688]),(⟨1,2,1⟩,[-8192,245760,-3121152,23101440,-117645312,446316544,-1254727680,2430533632,-2274713600,-3774332928,19253305344,-36151721984,32403660800,6029950976,-29090439168]),(⟨1,3,0⟩,[-8192,245760,-3268608,28098560,-189947904,1057521664,-4740685824,17104076800,-49862008832,113753374720,-190045298688,207305555968,-106822868992,-26303463424,45966434304]),(⟨1,3,1⟩,[0,49152,-1114112,10911744,-65994752,288309248,-942800896,2245197824,-3478519808,1186938880,10419896320,-31456854016,47696904192,-33150681088]),(⟨1,3,3⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨1,3,4⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨1,4,0⟩,[0,49152,-1114112,10911744,-65994752,288309248,-942800896,2245197824,-3478519808,1186938880,10419896320,-31456854016,47696904192,-33150681088]),(⟨1,4,3⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨1,4,5⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨1,5,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,0,0⟩,[0,65536,-2170880,30343168,-235995136,1135771648,-3542867968,6810828800,-2099298304,-48632954880,244473470976,-694117793792,1261610369024,-1412067459072,788149297152,16252207104,-181117698048]),(⟨2,0,1⟩,[0,-32768,589824,-1949696,-33505280,457867264,-3074572288,14164017152,-47517171712,113970020352,-187030142976,199014989824,-144879271936,146451300352,-226243985408,169350021120]),(⟨2,0,2⟩,[0,-65536,2121728,-28262400,204505088,-919715840,2956189696,-7965016064,18871222272,-35212001280,43813576704,-24795430912,-17342431232,46548074496,-34991136768]),(⟨2,0,3⟩,[0,0,393216,-10141696,108658688,-665534464,2792357888,-8926494720,21530935296,-35821617152,35519070208,-11689115648,-11104550912,5850120192]),(⟨2,1,0⟩,[0,-32768,589824,-1949696,-33505280,457867264,-3074572288,14164017152,-47517171712,113970020352,-187030142976,199014989824,-144879271936,146451300352,-226243985408,169350021120]),(⟨2,1,1⟩,[0,0,-98304,2359296,-19021824,36175872,310689792,-2056519680,5061574656,-4967890944,-3078881280,16735272960,-37145493504,70403751936,-62193352704]),(⟨2,1,2⟩,[0,65536,-2473984,39010304,-336183296,1726627840,-5281644544,8203698176,1376419840,-33165705216,65433059328,-54365896704,6355894272,14043660288]),(⟨2,1,3⟩,[-16384,458752,-5210112,31522816,-111132672,208535552,23003136,-1294336000,3393208320,-3253010432,-3415179264,13374914560,-11368677376]),(⟨2,2,0⟩,[0,-65536,2121728,-28262400,204505088,-919715840,2956189696,-7965016064,18871222272,-35212001280,43813576704,-24795430912,-17342431232,46548074496,-34991136768]),(⟨2,2,1⟩,[0,65536,-2473984,39010304,-336183296,1726627840,-5281644544,8203698176,1376419840,-33165705216,65433059328,-54365896704,6355894272,14043660288]),(⟨2,2,2⟩,[-32768,917504,-10420224,63045632,-222265344,417071104,46006272,-2588672000,6786416640,-6506020864,-6830358528,26749829120,-22737354752]),(⟨2,3,0⟩,[0,0,393216,-10141696,108658688,-665534464,2792357888,-8926494720,21530935296,-35821617152,35519070208,-11689115648,-11104550912,5850120192]),(⟨2,3,1⟩,[-16384,458752,-5210112,31522816,-111132672,208535552,23003136,-1294336000,3393208320,-3253010432,-3415179264,13374914560,-11368677376]),(⟨2,3,3⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨2,4,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,0,0⟩,[0,49152,-2433024,46997504,-492093440,3243425792,-14967988224,53229527040,-156412444672,381902077952,-729887662080,991720726528,-824782012416,269404946432,92552847360,-40591466496]),(⟨3,0,1⟩,[-8192,245760,-3137536,24412160,-140926976,648921088,-2494177280,9189785600,-33733861376,103566622720,-227747897344,322769420288,-246830047232,49593270272,31062958080]),(⟨3,0,2⟩,[0,-16384,835584,-15417344,143540224,-781844480,2818801664,-7761461248,18042880000,-33684733952,42209099776,-25314344960,-65716224,650280960]),(⟨3,0,3⟩,[-32768,917504,-10420224,60784640,-186253312,220856320,598999040,-4927193088,20159234048,-51288211456,73482043392,-45552533504,194052096]),(⟨3,0,4⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨3,0,5⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨3,0,6⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨3,1,0⟩,[-8192,245760,-3137536,24412160,-140926976,648921088,-2494177280,9189785600,-33733861376,103566622720,-227747897344,322769420288,-246830047232,49593270272,31062958080]),(⟨3,1,1⟩,[0,65536,-2473984,38912000,-331366400,1643855872,-4597055488,5244551168,7537131520,-34534883328,44237537280,-12414566400,-18054070272,9621749760]),(⟨3,1,2⟩,[-16384,327680,-1130496,-19464192,214695936,-894042112,1664188416,-361627648,-4419502080,8831434752,-8966651904,10093002752,-9362440192]),(⟨3,1,3⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨3,1,4⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨3,2,0⟩,[0,-16384,835584,-15417344,143540224,-781844480,2818801664,-7761461248,18042880000,-33684733952,42209099776,-25314344960,-65716224,650280960]),(⟨3,2,1⟩,[-16384,327680,-1130496,-19464192,214695936,-894042112,1664188416,-361627648,-4419502080,8831434752,-8966651904,10093002752,-9362440192]),(⟨3,2,3⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨3,3,0⟩,[-32768,917504,-10420224,60784640,-186253312,220856320,598999040,-4927193088,20159234048,-51288211456,73482043392,-45552533504,194052096]),(⟨3,3,1⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨3,3,2⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨3,3,3⟩,[0,-589824,11010048,-76283904,272105472,-660996096,1096286208,697565184,-7041712128,8118534144]),(⟨3,4,0⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨3,4,1⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨3,5,0⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨3,6,0⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨4,0,0⟩,[0,-65536,1908736,-20185088,81051648,141623296,-3080101888,17401118720,-65029767168,182975528960,-378868473856,531570622464,-429393788928,107748458496,60094390272]),(⟨4,0,1⟩,[0,49152,-1114112,10813440,-61177856,205537280,-258211840,-713949184,2682191872,-182239232,-10775625728,10494476288,23286939648,-37572591616]),(⟨4,0,3⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨4,0,4⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨4,1,0⟩,[0,49152,-1114112,10813440,-61177856,205537280,-258211840,-713949184,2682191872,-182239232,-10775625728,10494476288,23286939648,-37572591616]),(⟨4,1,1⟩,[0,-131072,4079616,-50987008,325828608,-1102577664,1641185280,932708352,-7812710400,12084445184,-5551472640,-3281911808,2006237184]),(⟨4,1,2⟩,[0,-32768,1605632,-27590656,228196352,-986382336,2053570560,-456392704,-7065174016,13983776768,-8136654848,-1473970176]),(⟨4,1,3⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨4,1,5⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,2,1⟩,[0,-32768,1605632,-27590656,228196352,-986382336,2053570560,-456392704,-7065174016,13983776768,-8136654848,-1473970176]),(⟨4,2,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,3,0⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨4,3,1⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨4,4,0⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨4,4,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,5,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,0,0⟩,[0,-16384,1228800,-25559040,252198912,-1447378944,5611159552,-16687955968,39573815296,-69506351104,77728169984,-37003460608,-11170267136,6500401152]),(⟨5,0,3⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨5,1,1⟩,[0,-32768,1605632,-27590656,228196352,-986382336,2053570560,-456392704,-7065174016,13983776768,-8136654848,-1473970176]),(⟨5,1,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,3,0⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨5,4,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨6,0,0⟩,[0,0,98304,-4292608,62324736,-462815232,2192113664,-7653359616,20425474048,-38839123968,45539229696,-22598746112,-4298047488]),(⟨6,0,3⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨6,3,0⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048])]


theorem partial_checked8 :
    (Poly.add (Poly.add (Poly.mul chunk8 sourceRight) partial12)
      (Poly.scale (K.ofRat (-1)) partial8)).isZero := by decide +kernel

theorem partial_sound8 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 8)
      sourceRight).eval u v t=partial8.eval u v t := by
  change (Poly.mul (chunk8++(sourceLeft.drop 12))
    sourceRight).eval u v t=partial8.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound12 partial_checked8 u v t


noncomputable def chunk4 : Poly := [(⟨0,1,0⟩,[0,-256,6592,-65600,337472,-994752,1716288,-1563072,348096,460992]),(⟨0,1,1⟩,[64,-1024,6144,-20992,42368,-19456,-107520,326144,-373184]),(⟨0,2,0⟩,[0,512,-9792,66304,-201792,309760,-192192,-87808,65856]),(⟨0,3,0⟩,[0,128,-4736,47104,-188672,361600,-281728,-48384])]

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[0,-32768,1368064,-25141248,272678912,-1983283200,10499645440,-43221491712,145866801152,-414520606720,981392203776,-1856977035264,2642795642880,-2588904161280,1444237713408,-136117739520,-275451789312,67976036352]),(⟨0,1,1⟩,[8192,-262144,3825664,-35831808,254287872,-1467924480,6988603392,-27634270208,92128911360,-259620831232,601140011008,-1079495081984,1377273438208,-1048203345920,182323470336,388511563776,-245856780288]),(⟨0,1,2⟩,[0,0,-450560,12230656,-141295616,936476672,-4107329536,13362929664,-35709190144,82238767104,-158820376576,245160009728,-302355644416,317165305856,-281061466112,148284530688]),(⟨0,1,3⟩,[-8192,245760,-3268608,28098560,-189947904,1057521664,-4740685824,17104076800,-49862008832,113753374720,-190045298688,207305555968,-106822868992,-26303463424,45966434304]),(⟨0,1,4⟩,[0,49152,-1114112,10911744,-65994752,288309248,-942800896,2245197824,-3478519808,1186938880,10419896320,-31456854016,47696904192,-33150681088]),(⟨0,2,0⟩,[0,65536,-2170880,30343168,-235995136,1135771648,-3542867968,6810828800,-2099298304,-48632954880,244473470976,-694117793792,1261610369024,-1412067459072,788149297152,16252207104,-181117698048]),(⟨0,2,1⟩,[0,-32768,589824,-1949696,-33505280,457867264,-3074572288,14164017152,-47517171712,113970020352,-187030142976,199014989824,-144879271936,146451300352,-226243985408,169350021120]),(⟨0,2,2⟩,[0,-65536,2121728,-28262400,204505088,-919715840,2956189696,-7965016064,18871222272,-35212001280,43813576704,-24795430912,-17342431232,46548074496,-34991136768]),(⟨0,2,3⟩,[0,0,393216,-10141696,108658688,-665534464,2792357888,-8926494720,21530935296,-35821617152,35519070208,-11689115648,-11104550912,5850120192]),(⟨0,3,0⟩,[0,49152,-2433024,46997504,-492093440,3243425792,-14967988224,53229527040,-156412444672,381902077952,-729887662080,991720726528,-824782012416,269404946432,92552847360,-40591466496]),(⟨0,3,1⟩,[-8192,245760,-3137536,24412160,-140926976,648921088,-2494177280,9189785600,-33733861376,103566622720,-227747897344,322769420288,-246830047232,49593270272,31062958080]),(⟨0,3,2⟩,[0,-16384,835584,-15417344,143540224,-781844480,2818801664,-7761461248,18042880000,-33684733952,42209099776,-25314344960,-65716224,650280960]),(⟨0,3,3⟩,[-32768,917504,-10420224,60784640,-186253312,220856320,598999040,-4927193088,20159234048,-51288211456,73482043392,-45552533504,194052096]),(⟨0,3,4⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨0,3,5⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨0,3,6⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨0,4,0⟩,[0,-65536,1908736,-20185088,81051648,141623296,-3080101888,17401118720,-65029767168,182975528960,-378868473856,531570622464,-429393788928,107748458496,60094390272]),(⟨0,4,1⟩,[0,49152,-1114112,10813440,-61177856,205537280,-258211840,-713949184,2682191872,-182239232,-10775625728,10494476288,23286939648,-37572591616]),(⟨0,4,3⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨0,4,4⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨0,5,0⟩,[0,-16384,1228800,-25559040,252198912,-1447378944,5611159552,-16687955968,39573815296,-69506351104,77728169984,-37003460608,-11170267136,6500401152]),(⟨0,5,3⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨0,6,0⟩,[0,0,98304,-4292608,62324736,-462815232,2192113664,-7653359616,20425474048,-38839123968,45539229696,-22598746112,-4298047488]),(⟨0,6,3⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨1,0,0⟩,[0,-32768,1368064,-25141248,272678912,-1983283200,10499645440,-43221491712,145866801152,-414520606720,981392203776,-1856977035264,2642795642880,-2588904161280,1444237713408,-136117739520,-275451789312,67976036352]),(⟨1,0,1⟩,[8192,-262144,3825664,-35831808,254287872,-1467924480,6988603392,-27634270208,92128911360,-259620831232,601140011008,-1079495081984,1377273438208,-1048203345920,182323470336,388511563776,-245856780288]),(⟨1,0,2⟩,[0,0,-450560,12230656,-141295616,936476672,-4107329536,13362929664,-35709190144,82238767104,-158820376576,245160009728,-302355644416,317165305856,-281061466112,148284530688]),(⟨1,0,3⟩,[-8192,245760,-3268608,28098560,-189947904,1057521664,-4740685824,17104076800,-49862008832,113753374720,-190045298688,207305555968,-106822868992,-26303463424,45966434304]),(⟨1,0,4⟩,[0,49152,-1114112,10911744,-65994752,288309248,-942800896,2245197824,-3478519808,1186938880,10419896320,-31456854016,47696904192,-33150681088]),(⟨1,1,0⟩,[8192,-262144,3956736,-40517632,327196672,-2138636288,11192262656,-47380119552,166465298432,-490293166080,1181917913088,-2213433098240,2988248522752,-2552291852288,887837368320,464394534912,-436685340672]),(⟨1,1,1⟩,[0,-98304,2555904,-28950528,192577536,-822706176,2182840320,-2967060480,1438973952,-9776037888,58132660224,-108655362048,-46992949248,535605116928,-901120819200,547702751232]),(⟨1,1,2⟩,[-8192,245760,-3170304,24477696,-133275648,540884992,-1588125696,3056140288,-2205704192,-7657340928,29432930304,-45910753280,22158123008,46154694656,-63196471296]),(⟨1,1,3⟩,[0,49152,-1114112,10911744,-65994752,288309248,-942800896,2245197824,-3478519808,1186938880,10419896320,-31456854016,47696904192,-33150681088]),(⟨1,2,0⟩,[0,0,-712704,20062208,-243941376,1746599936,-8581881856,31969222656,-94269308928,215874863104,-362475233280,414062043136,-300704481280,176349773824,-194220056576,163154288640]),(⟨1,2,1⟩,[-8192,245760,-3170304,24084480,-121036800,387923968,-610639872,-251592704,2717851648,-4859215872,5994799104,-9657417728,5503705088,36308959232,-57177759744]),(⟨1,2,2⟩,[0,65536,-2473984,39010304,-336183296,1726627840,-5281644544,8203698176,1376419840,-33165705216,65433059328,-54365896704,6355894272,14043660288]),(⟨1,2,3⟩,[-16384,458752,-5210112,31522816,-111132672,208535552,23003136,-1294336000,3393208320,-3253010432,-3415179264,13374914560,-11368677376]),(⟨1,3,0⟩,[-8192,245760,-3334144,30785536,-228859904,1354694656,-6313533440,24488935424,-81252147200,217211322368,-426866876416,556467666944,-396302114816,57384599552,72013799424]),(⟨1,3,1⟩,[0,114688,-3588096,49823744,-397361152,1932165120,-5539856384,7489748992,4058611712,-33347944448,54657433600,-43871420416,29642833920,-23528931328]),(⟨1,3,2⟩,[-16384,327680,-1130496,-19464192,214695936,-894042112,1664188416,-361627648,-4419502080,8831434752,-8966651904,10093002752,-9362440192]),(⟨1,3,3⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨1,3,4⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨1,4,0⟩,[0,49152,-1114112,10813440,-61177856,205537280,-258211840,-713949184,2682191872,-182239232,-10775625728,10494476288,23286939648,-37572591616]),(⟨1,4,1⟩,[0,-131072,4079616,-50987008,325828608,-1102577664,1641185280,932708352,-7812710400,12084445184,-5551472640,-3281911808,2006237184]),(⟨1,4,2⟩,[0,-32768,1605632,-27590656,228196352,-986382336,2053570560,-456392704,-7065174016,13983776768,-8136654848,-1473970176]),(⟨1,4,3⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨1,4,5⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨1,5,1⟩,[0,-32768,1605632,-27590656,228196352,-986382336,2053570560,-456392704,-7065174016,13983776768,-8136654848,-1473970176]),(⟨1,5,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,0,0⟩,[0,65536,-2170880,30343168,-235995136,1135771648,-3542867968,6810828800,-2099298304,-48632954880,244473470976,-694117793792,1261610369024,-1412067459072,788149297152,16252207104,-181117698048]),(⟨2,0,1⟩,[0,-32768,589824,-1949696,-33505280,457867264,-3074572288,14164017152,-47517171712,113970020352,-187030142976,199014989824,-144879271936,146451300352,-226243985408,169350021120]),(⟨2,0,2⟩,[0,-65536,2121728,-28262400,204505088,-919715840,2956189696,-7965016064,18871222272,-35212001280,43813576704,-24795430912,-17342431232,46548074496,-34991136768]),(⟨2,0,3⟩,[0,0,393216,-10141696,108658688,-665534464,2792357888,-8926494720,21530935296,-35821617152,35519070208,-11689115648,-11104550912,5850120192]),(⟨2,1,0⟩,[0,0,-712704,20062208,-243941376,1746599936,-8581881856,31969222656,-94269308928,215874863104,-362475233280,414062043136,-300704481280,176349773824,-194220056576,163154288640]),(⟨2,1,1⟩,[-8192,245760,-3170304,24084480,-121036800,387923968,-610639872,-251592704,2717851648,-4859215872,5994799104,-9657417728,5503705088,36308959232,-57177759744]),(⟨2,1,2⟩,[0,65536,-2473984,39010304,-336183296,1726627840,-5281644544,8203698176,1376419840,-33165705216,65433059328,-54365896704,6355894272,14043660288]),(⟨2,1,3⟩,[-16384,458752,-5210112,31522816,-111132672,208535552,23003136,-1294336000,3393208320,-3253010432,-3415179264,13374914560,-11368677376]),(⟨2,2,0⟩,[0,-131072,4292608,-57901056,424640512,-1934000128,6245777408,-16555638784,37673435136,-66540994560,77447528448,-39831830528,-24439324672,52971405312,-35876241408]),(⟨2,2,1⟩,[0,131072,-4947968,78020608,-672366592,3453255680,-10563289088,16407396352,2752839680,-66331410432,130866118656,-108731793408,12711788544,28087320576]),(⟨2,2,2⟩,[-49152,1376256,-15630336,94568448,-333398016,625606656,69009408,-3883008000,10179624960,-9759031296,-10245537792,40124743680,-34106032128]),(⟨2,3,0⟩,[0,-16384,1228800,-25559040,252198912,-1447378944,5611159552,-16687955968,39573815296,-69506351104,77728169984,-37003460608,-11170267136,6500401152]),(⟨2,3,1⟩,[-16384,327680,-1130496,-19464192,214695936,-894042112,1664188416,-361627648,-4419502080,8831434752,-8966651904,10093002752,-9362440192]),(⟨2,3,3⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨2,4,1⟩,[0,-32768,1605632,-27590656,228196352,-986382336,2053570560,-456392704,-7065174016,13983776768,-8136654848,-1473970176]),(⟨2,4,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,0,0⟩,[0,49152,-2433024,46997504,-492093440,3243425792,-14967988224,53229527040,-156412444672,381902077952,-729887662080,991720726528,-824782012416,269404946432,92552847360,-40591466496]),(⟨3,0,1⟩,[-8192,245760,-3137536,24412160,-140926976,648921088,-2494177280,9189785600,-33733861376,103566622720,-227747897344,322769420288,-246830047232,49593270272,31062958080]),(⟨3,0,2⟩,[0,-16384,835584,-15417344,143540224,-781844480,2818801664,-7761461248,18042880000,-33684733952,42209099776,-25314344960,-65716224,650280960]),(⟨3,0,3⟩,[-32768,917504,-10420224,60784640,-186253312,220856320,598999040,-4927193088,20159234048,-51288211456,73482043392,-45552533504,194052096]),(⟨3,0,4⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨3,0,5⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨3,0,6⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨3,1,0⟩,[-8192,245760,-3334144,30785536,-228859904,1354694656,-6313533440,24488935424,-81252147200,217211322368,-426866876416,556467666944,-396302114816,57384599552,72013799424]),(⟨3,1,1⟩,[0,114688,-3588096,49823744,-397361152,1932165120,-5539856384,7489748992,4058611712,-33347944448,54657433600,-43871420416,29642833920,-23528931328]),(⟨3,1,2⟩,[-16384,327680,-1130496,-19464192,214695936,-894042112,1664188416,-361627648,-4419502080,8831434752,-8966651904,10093002752,-9362440192]),(⟨3,1,3⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨3,1,4⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨3,2,0⟩,[0,-16384,1228800,-25559040,252198912,-1447378944,5611159552,-16687955968,39573815296,-69506351104,77728169984,-37003460608,-11170267136,6500401152]),(⟨3,2,1⟩,[-16384,327680,-1130496,-19464192,214695936,-894042112,1664188416,-361627648,-4419502080,8831434752,-8966651904,10093002752,-9362440192]),(⟨3,2,3⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨3,3,0⟩,[-32768,917504,-10321920,56492032,-123928576,-241958912,2791112704,-12580552704,40584708096,-90127335424,119021273088,-68151279616,-4103995392]),(⟨3,3,1⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨3,3,2⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨3,3,3⟩,[0,-589824,11010048,-76283904,272105472,-660996096,1096286208,697565184,-7041712128,8118534144]),(⟨3,4,0⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨3,4,1⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨3,5,0⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨3,6,0⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨4,0,0⟩,[0,-65536,1908736,-20185088,81051648,141623296,-3080101888,17401118720,-65029767168,182975528960,-378868473856,531570622464,-429393788928,107748458496,60094390272]),(⟨4,0,1⟩,[0,49152,-1114112,10813440,-61177856,205537280,-258211840,-713949184,2682191872,-182239232,-10775625728,10494476288,23286939648,-37572591616]),(⟨4,0,3⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨4,0,4⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨4,1,0⟩,[0,49152,-1114112,10813440,-61177856,205537280,-258211840,-713949184,2682191872,-182239232,-10775625728,10494476288,23286939648,-37572591616]),(⟨4,1,1⟩,[0,-131072,4079616,-50987008,325828608,-1102577664,1641185280,932708352,-7812710400,12084445184,-5551472640,-3281911808,2006237184]),(⟨4,1,2⟩,[0,-32768,1605632,-27590656,228196352,-986382336,2053570560,-456392704,-7065174016,13983776768,-8136654848,-1473970176]),(⟨4,1,3⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨4,1,5⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,2,1⟩,[0,-32768,1605632,-27590656,228196352,-986382336,2053570560,-456392704,-7065174016,13983776768,-8136654848,-1473970176]),(⟨4,2,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,3,0⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨4,3,1⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨4,4,0⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨4,4,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,5,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,0,0⟩,[0,-16384,1228800,-25559040,252198912,-1447378944,5611159552,-16687955968,39573815296,-69506351104,77728169984,-37003460608,-11170267136,6500401152]),(⟨5,0,3⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨5,1,1⟩,[0,-32768,1605632,-27590656,228196352,-986382336,2053570560,-456392704,-7065174016,13983776768,-8136654848,-1473970176]),(⟨5,1,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,3,0⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨5,4,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨6,0,0⟩,[0,0,98304,-4292608,62324736,-462815232,2192113664,-7653359616,20425474048,-38839123968,45539229696,-22598746112,-4298047488]),(⟨6,0,3⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨6,3,0⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048])]


theorem partial_checked4 :
    (Poly.add (Poly.add (Poly.mul chunk4 sourceRight) partial8)
      (Poly.scale (K.ofRat (-1)) partial4)).isZero := by decide +kernel

theorem partial_sound4 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 4)
      sourceRight).eval u v t=partial4.eval u v t := by
  change (Poly.mul (chunk4++(sourceLeft.drop 8))
    sourceRight).eval u v t=partial4.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound8 partial_checked4 u v t


noncomputable def chunk0 : Poly := [(⟨0,0,0⟩,[0,-512,11584,-106560,532736,-1621824,3051904,-3282624,1363712,606272,-407232]),(⟨0,0,1⟩,[0,-256,6592,-65600,337472,-994752,1716288,-1563072,348096,460992]),(⟨0,0,2⟩,[0,512,-9792,66304,-201792,309760,-192192,-87808,65856]),(⟨0,0,3⟩,[0,128,-4736,47104,-188672,361600,-281728,-48384])]

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,-65536,2531328,-43851776,456417280,-3243524096,17061306368,-70622420992,240798998528,-691980648448,1665082286080,-3248113737728,4881479213056,-5246609965056,3501255237632,-848023511040,-530015526912,378070548480,-60048801792]),(⟨0,0,1⟩,[0,-32768,1630208,-33693696,397688832,-3090923520,17338114048,-75376336896,267814600704,-796371271680,1958353838080,-3828968415232,5620743290880,-5684110376960,3282673098752,-316248481792,-720743890944,236550537216]),(⟨0,0,2⟩,[0,131072,-4571136,68345856,-583245824,3217391616,-12468011008,36216889344,-80793313280,125976051712,-66904539136,-282846388224,914187493376,-1289343565824,834718056448,-24318271488,-175644499968]),(⟨0,0,3⟩,[0,49152,-2826240,58515456,-640843776,4395843584,-21150081024,78162976768,-234836590592,573771759616,-1082346856448,1444367933440,-1173722726400,354079326208,166842474496,-76766699520]),(⟨0,0,4⟩,[0,-65536,1908736,-20185088,81051648,141623296,-3080101888,17401118720,-65029767168,182975528960,-378868473856,531570622464,-429393788928,107748458496,60094390272]),(⟨0,0,5⟩,[0,-16384,1228800,-25559040,252198912,-1447378944,5611159552,-16687955968,39573815296,-69506351104,77728169984,-37003460608,-11170267136,6500401152]),(⟨0,0,6⟩,[0,0,98304,-4292608,62324736,-462815232,2192113664,-7653359616,20425474048,-38839123968,45539229696,-22598746112,-4298047488]),(⟨0,1,0⟩,[0,-32768,1630208,-33693696,397688832,-3090923520,17338114048,-75376336896,267814600704,-796371271680,1958353838080,-3828968415232,5620743290880,-5684110376960,3282673098752,-316248481792,-720743890944,236550537216]),(⟨0,1,1⟩,[8192,-262144,3956736,-40124416,313581568,-1938243584,9548324864,-39136788480,140905324544,-446746755072,1173830049792,-2358299869184,3332406353920,-2907722891264,1005090152448,531062095872,-473903087616]),(⟨0,1,2⟩,[0,0,-712704,20062208,-243941376,1746599936,-8581881856,31969222656,-94269308928,215874863104,-362475233280,414062043136,-300704481280,176349773824,-194220056576,163154288640]),(⟨0,1,3⟩,[-8192,245760,-3334144,30785536,-228859904,1354694656,-6313533440,24488935424,-81252147200,217211322368,-426866876416,556467666944,-396302114816,57384599552,72013799424]),(⟨0,1,4⟩,[0,49152,-1114112,10813440,-61177856,205537280,-258211840,-713949184,2682191872,-182239232,-10775625728,10494476288,23286939648,-37572591616]),(⟨0,2,0⟩,[0,131072,-4571136,68345856,-583245824,3217391616,-12468011008,36216889344,-80793313280,125976051712,-66904539136,-282846388224,914187493376,-1289343565824,834718056448,-24318271488,-175644499968]),(⟨0,2,1⟩,[0,0,-712704,20062208,-243941376,1746599936,-8581881856,31969222656,-94269308928,215874863104,-362475233280,414062043136,-300704481280,176349773824,-194220056576,163154288640]),(⟨0,2,2⟩,[0,-131072,4292608,-57901056,424640512,-1934000128,6245777408,-16555638784,37673435136,-66540994560,77447528448,-39831830528,-24439324672,52971405312,-35876241408]),(⟨0,2,3⟩,[0,-16384,1228800,-25559040,252198912,-1447378944,5611159552,-16687955968,39573815296,-69506351104,77728169984,-37003460608,-11170267136,6500401152]),(⟨0,3,0⟩,[0,49152,-2826240,58515456,-640843776,4395843584,-21150081024,78162976768,-234836590592,573771759616,-1082346856448,1444367933440,-1173722726400,354079326208,166842474496,-76766699520]),(⟨0,3,1⟩,[-8192,245760,-3334144,30785536,-228859904,1354694656,-6313533440,24488935424,-81252147200,217211322368,-426866876416,556467666944,-396302114816,57384599552,72013799424]),(⟨0,3,2⟩,[0,-16384,1228800,-25559040,252198912,-1447378944,5611159552,-16687955968,39573815296,-69506351104,77728169984,-37003460608,-11170267136,6500401152]),(⟨0,3,3⟩,[-32768,917504,-10321920,56492032,-123928576,-241958912,2791112704,-12580552704,40584708096,-90127335424,119021273088,-68151279616,-4103995392]),(⟨0,3,4⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨0,3,5⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨0,3,6⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨0,4,0⟩,[0,-65536,1908736,-20185088,81051648,141623296,-3080101888,17401118720,-65029767168,182975528960,-378868473856,531570622464,-429393788928,107748458496,60094390272]),(⟨0,4,1⟩,[0,49152,-1114112,10813440,-61177856,205537280,-258211840,-713949184,2682191872,-182239232,-10775625728,10494476288,23286939648,-37572591616]),(⟨0,4,3⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨0,4,4⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨0,5,0⟩,[0,-16384,1228800,-25559040,252198912,-1447378944,5611159552,-16687955968,39573815296,-69506351104,77728169984,-37003460608,-11170267136,6500401152]),(⟨0,5,3⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨0,6,0⟩,[0,0,98304,-4292608,62324736,-462815232,2192113664,-7653359616,20425474048,-38839123968,45539229696,-22598746112,-4298047488]),(⟨0,6,3⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨1,0,0⟩,[0,-32768,1630208,-33693696,397688832,-3090923520,17338114048,-75376336896,267814600704,-796371271680,1958353838080,-3828968415232,5620743290880,-5684110376960,3282673098752,-316248481792,-720743890944,236550537216]),(⟨1,0,1⟩,[8192,-262144,3956736,-40124416,313581568,-1938243584,9548324864,-39136788480,140905324544,-446746755072,1173830049792,-2358299869184,3332406353920,-2907722891264,1005090152448,531062095872,-473903087616]),(⟨1,0,2⟩,[0,0,-712704,20062208,-243941376,1746599936,-8581881856,31969222656,-94269308928,215874863104,-362475233280,414062043136,-300704481280,176349773824,-194220056576,163154288640]),(⟨1,0,3⟩,[-8192,245760,-3334144,30785536,-228859904,1354694656,-6313533440,24488935424,-81252147200,217211322368,-426866876416,556467666944,-396302114816,57384599552,72013799424]),(⟨1,0,4⟩,[0,49152,-1114112,10813440,-61177856,205537280,-258211840,-713949184,2682191872,-182239232,-10775625728,10494476288,23286939648,-37572591616]),(⟨1,1,0⟩,[8192,-262144,3956736,-40124416,313581568,-1938243584,9548324864,-39136788480,140905324544,-446746755072,1173830049792,-2358299869184,3332406353920,-2907722891264,1005090152448,531062095872,-473903087616]),(⟨1,1,1⟩,[0,-98304,2555904,-28753920,185155584,-705675264,1174290432,2212823040,-14405959680,14835056640,62261919744,-208152477696,149306228736,372507426816,-882053136384,589833732096]),(⟨1,1,2⟩,[-8192,376832,-7708672,90882048,-669016064,3135700992,-9130631168,14263877632,21897216,-53148139520,120714076160,-128134430720,44587966464,58531479552,-69583675392]),(⟨1,1,3⟩,[0,114688,-3588096,49823744,-397361152,1932165120,-5539856384,7489748992,4058611712,-33347944448,54657433600,-43871420416,29642833920,-23528931328]),(⟨1,1,4⟩,[0,-131072,4079616,-50987008,325828608,-1102577664,1641185280,932708352,-7812710400,12084445184,-5551472640,-3281911808,2006237184]),(⟨1,1,5⟩,[0,-32768,1605632,-27590656,228196352,-986382336,2053570560,-456392704,-7065174016,13983776768,-8136654848,-1473970176]),(⟨1,2,0⟩,[0,0,-712704,20062208,-243941376,1746599936,-8581881856,31969222656,-94269308928,215874863104,-362475233280,414062043136,-300704481280,176349773824,-194220056576,163154288640]),(⟨1,2,1⟩,[-8192,376832,-7708672,90882048,-669016064,3135700992,-9130631168,14263877632,21897216,-53148139520,120714076160,-128134430720,44587966464,58531479552,-69583675392]),(⟨1,2,2⟩,[0,131072,-4947968,78020608,-672366592,3453255680,-10563289088,16407396352,2752839680,-66331410432,130866118656,-108731793408,12711788544,28087320576]),(⟨1,2,3⟩,[-16384,327680,-1130496,-19464192,214695936,-894042112,1664188416,-361627648,-4419502080,8831434752,-8966651904,10093002752,-9362440192]),(⟨1,2,4⟩,[0,-32768,1605632,-27590656,228196352,-986382336,2053570560,-456392704,-7065174016,13983776768,-8136654848,-1473970176]),(⟨1,3,0⟩,[-8192,245760,-3334144,30785536,-228859904,1354694656,-6313533440,24488935424,-81252147200,217211322368,-426866876416,556467666944,-396302114816,57384599552,72013799424]),(⟨1,3,1⟩,[0,114688,-3588096,49823744,-397361152,1932165120,-5539856384,7489748992,4058611712,-33347944448,54657433600,-43871420416,29642833920,-23528931328]),(⟨1,3,2⟩,[-16384,327680,-1130496,-19464192,214695936,-894042112,1664188416,-361627648,-4419502080,8831434752,-8966651904,10093002752,-9362440192]),(⟨1,3,3⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨1,3,4⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨1,4,0⟩,[0,49152,-1114112,10813440,-61177856,205537280,-258211840,-713949184,2682191872,-182239232,-10775625728,10494476288,23286939648,-37572591616]),(⟨1,4,1⟩,[0,-131072,4079616,-50987008,325828608,-1102577664,1641185280,932708352,-7812710400,12084445184,-5551472640,-3281911808,2006237184]),(⟨1,4,2⟩,[0,-32768,1605632,-27590656,228196352,-986382336,2053570560,-456392704,-7065174016,13983776768,-8136654848,-1473970176]),(⟨1,4,3⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨1,4,5⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨1,5,1⟩,[0,-32768,1605632,-27590656,228196352,-986382336,2053570560,-456392704,-7065174016,13983776768,-8136654848,-1473970176]),(⟨1,5,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,0,0⟩,[0,131072,-4571136,68345856,-583245824,3217391616,-12468011008,36216889344,-80793313280,125976051712,-66904539136,-282846388224,914187493376,-1289343565824,834718056448,-24318271488,-175644499968]),(⟨2,0,1⟩,[0,0,-712704,20062208,-243941376,1746599936,-8581881856,31969222656,-94269308928,215874863104,-362475233280,414062043136,-300704481280,176349773824,-194220056576,163154288640]),(⟨2,0,2⟩,[0,-131072,4292608,-57901056,424640512,-1934000128,6245777408,-16555638784,37673435136,-66540994560,77447528448,-39831830528,-24439324672,52971405312,-35876241408]),(⟨2,0,3⟩,[0,-16384,1228800,-25559040,252198912,-1447378944,5611159552,-16687955968,39573815296,-69506351104,77728169984,-37003460608,-11170267136,6500401152]),(⟨2,1,0⟩,[0,0,-712704,20062208,-243941376,1746599936,-8581881856,31969222656,-94269308928,215874863104,-362475233280,414062043136,-300704481280,176349773824,-194220056576,163154288640]),(⟨2,1,1⟩,[-8192,376832,-7708672,90882048,-669016064,3135700992,-9130631168,14263877632,21897216,-53148139520,120714076160,-128134430720,44587966464,58531479552,-69583675392]),(⟨2,1,2⟩,[0,131072,-4947968,78020608,-672366592,3453255680,-10563289088,16407396352,2752839680,-66331410432,130866118656,-108731793408,12711788544,28087320576]),(⟨2,1,3⟩,[-16384,327680,-1130496,-19464192,214695936,-894042112,1664188416,-361627648,-4419502080,8831434752,-8966651904,10093002752,-9362440192]),(⟨2,1,4⟩,[0,-32768,1605632,-27590656,228196352,-986382336,2053570560,-456392704,-7065174016,13983776768,-8136654848,-1473970176]),(⟨2,2,0⟩,[0,-131072,4292608,-57901056,424640512,-1934000128,6245777408,-16555638784,37673435136,-66540994560,77447528448,-39831830528,-24439324672,52971405312,-35876241408]),(⟨2,2,1⟩,[0,131072,-4947968,78020608,-672366592,3453255680,-10563289088,16407396352,2752839680,-66331410432,130866118656,-108731793408,12711788544,28087320576]),(⟨2,2,2⟩,[-49152,1376256,-15630336,94568448,-333398016,625606656,69009408,-3883008000,10179624960,-9759031296,-10245537792,40124743680,-34106032128]),(⟨2,3,0⟩,[0,-16384,1228800,-25559040,252198912,-1447378944,5611159552,-16687955968,39573815296,-69506351104,77728169984,-37003460608,-11170267136,6500401152]),(⟨2,3,1⟩,[-16384,327680,-1130496,-19464192,214695936,-894042112,1664188416,-361627648,-4419502080,8831434752,-8966651904,10093002752,-9362440192]),(⟨2,3,3⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨2,4,1⟩,[0,-32768,1605632,-27590656,228196352,-986382336,2053570560,-456392704,-7065174016,13983776768,-8136654848,-1473970176]),(⟨2,4,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨3,0,0⟩,[0,49152,-2826240,58515456,-640843776,4395843584,-21150081024,78162976768,-234836590592,573771759616,-1082346856448,1444367933440,-1173722726400,354079326208,166842474496,-76766699520]),(⟨3,0,1⟩,[-8192,245760,-3334144,30785536,-228859904,1354694656,-6313533440,24488935424,-81252147200,217211322368,-426866876416,556467666944,-396302114816,57384599552,72013799424]),(⟨3,0,2⟩,[0,-16384,1228800,-25559040,252198912,-1447378944,5611159552,-16687955968,39573815296,-69506351104,77728169984,-37003460608,-11170267136,6500401152]),(⟨3,0,3⟩,[-32768,917504,-10321920,56492032,-123928576,-241958912,2791112704,-12580552704,40584708096,-90127335424,119021273088,-68151279616,-4103995392]),(⟨3,0,4⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨3,0,5⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨3,0,6⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨3,1,0⟩,[-8192,245760,-3334144,30785536,-228859904,1354694656,-6313533440,24488935424,-81252147200,217211322368,-426866876416,556467666944,-396302114816,57384599552,72013799424]),(⟨3,1,1⟩,[0,114688,-3588096,49823744,-397361152,1932165120,-5539856384,7489748992,4058611712,-33347944448,54657433600,-43871420416,29642833920,-23528931328]),(⟨3,1,2⟩,[-16384,327680,-1130496,-19464192,214695936,-894042112,1664188416,-361627648,-4419502080,8831434752,-8966651904,10093002752,-9362440192]),(⟨3,1,3⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨3,1,4⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨3,2,0⟩,[0,-16384,1228800,-25559040,252198912,-1447378944,5611159552,-16687955968,39573815296,-69506351104,77728169984,-37003460608,-11170267136,6500401152]),(⟨3,2,1⟩,[-16384,327680,-1130496,-19464192,214695936,-894042112,1664188416,-361627648,-4419502080,8831434752,-8966651904,10093002752,-9362440192]),(⟨3,2,3⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨3,3,0⟩,[-32768,917504,-10321920,56492032,-123928576,-241958912,2791112704,-12580552704,40584708096,-90127335424,119021273088,-68151279616,-4103995392]),(⟨3,3,1⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨3,3,2⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨3,3,3⟩,[0,-589824,11010048,-76283904,272105472,-660996096,1096286208,697565184,-7041712128,8118534144]),(⟨3,4,0⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨3,4,1⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨3,5,0⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨3,6,0⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨4,0,0⟩,[0,-65536,1908736,-20185088,81051648,141623296,-3080101888,17401118720,-65029767168,182975528960,-378868473856,531570622464,-429393788928,107748458496,60094390272]),(⟨4,0,1⟩,[0,49152,-1114112,10813440,-61177856,205537280,-258211840,-713949184,2682191872,-182239232,-10775625728,10494476288,23286939648,-37572591616]),(⟨4,0,3⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨4,0,4⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨4,1,0⟩,[0,49152,-1114112,10813440,-61177856,205537280,-258211840,-713949184,2682191872,-182239232,-10775625728,10494476288,23286939648,-37572591616]),(⟨4,1,1⟩,[0,-131072,4079616,-50987008,325828608,-1102577664,1641185280,932708352,-7812710400,12084445184,-5551472640,-3281911808,2006237184]),(⟨4,1,2⟩,[0,-32768,1605632,-27590656,228196352,-986382336,2053570560,-456392704,-7065174016,13983776768,-8136654848,-1473970176]),(⟨4,1,3⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨4,1,5⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,2,1⟩,[0,-32768,1605632,-27590656,228196352,-986382336,2053570560,-456392704,-7065174016,13983776768,-8136654848,-1473970176]),(⟨4,2,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,3,0⟩,[0,131072,-2883584,25231360,-120061952,387448832,-1041235968,2032009216,-569901056,-8331067392,18351915008,-12610633728]),(⟨4,3,1⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨4,4,0⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨4,4,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,5,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,0,0⟩,[0,-16384,1228800,-25559040,252198912,-1447378944,5611159552,-16687955968,39573815296,-69506351104,77728169984,-37003460608,-11170267136,6500401152]),(⟨5,0,3⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨5,1,1⟩,[0,-32768,1605632,-27590656,228196352,-986382336,2053570560,-456392704,-7065174016,13983776768,-8136654848,-1473970176]),(⟨5,1,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,3,0⟩,[32768,-851968,8290304,-37486592,83427328,-124649472,229179392,113508352,-1874427904,2549284864,-409436160]),(⟨5,4,1⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨6,0,0⟩,[0,0,98304,-4292608,62324736,-462815232,2192113664,-7653359616,20425474048,-38839123968,45539229696,-22598746112,-4298047488]),(⟨6,0,3⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨6,3,0⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048])]


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
    (Poly.add (Poly.scale (K.ofRat r672) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 9 11).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r671*r671 : ℚ)=r672 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 9 11 r671 r671 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 9=11 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 9 11).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C137

#print axioms Coulomb8.Columns.C137.sound
