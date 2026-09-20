import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C102

def r0 : ℚ := { num := -98304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 3637248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -59211776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 565510144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -3596091392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 16609935360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -60163096576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 181129576448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -457409658880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 921408012288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -1356594642944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 1292389384192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -617899163648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -12414713856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 114716246016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -3359637504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 3801088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -63668224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 36438016, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := -81526784, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := 18739625984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := -69318213632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := 213383118848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := -544057688064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := 3730964480, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := -1506340470784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := 1280621936640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := -443216625664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -124468330496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 11847401472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -6258688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 83886080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -36634624, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 2862940160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -8845099008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 20038811648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -33433714688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 22517972992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := 78032502784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -257101922304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 288306298880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -673382400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -849641472, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -7471104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 115998720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -988282880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 5328011264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -71041024, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 63353126912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -161518977024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 309140193280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -372972322816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 29388308480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 12134121472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -3840999424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := 2031616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -11108352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -47185920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 881655808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -302383104, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 18877579264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -52579008512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 106504159232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -127150391296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 57324109824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := 1725169664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 524288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -51740672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 365953024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -1505427456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 4398776320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -11112742912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 20699938816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -17959190528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 63438848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := 46956544, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 589824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -14155776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 131858432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -661127168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 2251685888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -6046613504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 1564737536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -8553758720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := -68222976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := 32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := -983040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := 786432, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -114491392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 101744640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -3415539712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := 13112246272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := -6167592960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := 129247444992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -332617547776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 636338962432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -763457896448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 416640958464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 10494083072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -2876964864, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := -65536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := 22642688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := -267321344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := 237109248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := -6835011584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 21538996224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -53711077376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 98362425344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := -123099873280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 16805036032, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -17083727872, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 1772027904, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 262144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -1277952, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 150208512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -42762240, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 2781347840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -9010872320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 25835339776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := -62507581440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := 105159327744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -92042788864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 13954711552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := 3152052224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 327680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := -6946816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := 58785792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -270008320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 774504448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := -87818240, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := 2030698496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -1175977984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := -8265859072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := 4466540544, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := -38469632, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := -851968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := 8290304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := -37486592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := 83427328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := -124649472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := 229179392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 113508352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -1874427904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 364183552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := -491520, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := -196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := -25427968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := 90701824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := -220332032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := 21495808, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 232521728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := -2347237376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 22740992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := 5832704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -68485120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 58916864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -1456340992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 3858890752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := -10336468992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := 22666149888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := -26013007872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := 83165184, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 430899200, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -411500544, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := 786432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := -26509312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := 35127296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := -159711232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := 3357540352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -9080733696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 2875719680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -1546485760, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := 2685140992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := -210403328, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := -4718592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := 2359296, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := -127401984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := -39714816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := 986185728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := -1148977152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -14155776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := -1703936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := 17760256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -103284736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := 430571520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -1571553280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 4961730560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -11866210304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 18157469696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := -12008947712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -253427712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := -393216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := 9437184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := -93978624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := 517865472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := -1740177408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := 3652190208, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -5501878272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 12363497472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := -33260568576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 17524850688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := 161653850112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -57236914176, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := 355663872, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := 65536, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -17104896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := 158007296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := -939229184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := 69861376, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := -6329597952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := 1441792, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := 504922112, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := -49887772672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := 36624334848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 2570649600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -46432256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := 655360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := -15859712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := 22675456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -124256256, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 2826174464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -5134614528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 2711355392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := 10542907392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := -34512699392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := 8046903296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := -49414144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := 6029312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := -10223616, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := 23592960, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := -943849472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -254803968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 4955308032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -5755109376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -475332608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 7602176, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := 5767168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -1310720, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := 19398656, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -680656896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := -286785536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := 3031171072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := -425197568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := -196608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := 393216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := -12058624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := 149422080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -959447040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := 3328442368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := -5200936960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := -2702704640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := 24577572864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := -35831545856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := 1917321216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := 8388608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -2850816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := -24117248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := 279117824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := -999030784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := 1147207680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := 1577058304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -835813376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := 956170240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := -4030464, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := -1572864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := -42467328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := -13238272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := 328728576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -382992384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := -4718592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := 1048576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := -50855936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := 181403648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := -440664064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := 42991616, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := 465043456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := -4694474752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := 45481984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := 5111808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -7274496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := 14155776, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := -495845376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := -10223616, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := 485621760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -7516717056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := 269942784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := 20840448, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -3145728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 1572864, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -84934656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := -26476544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := 657457152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -765984768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := -9437184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := -49152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := 1818624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := -29605888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := 282755072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := -1798045696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := 8304967680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -30081548288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 90564788224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -228704829440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 460704006144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -678297321472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 646194692096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -308949581824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := -6207356928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := 57358123008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := -1679818752, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := 1900544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := -31834112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := 18219008, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := -40763392, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := 9369812992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := -34659106816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := 106691559424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := -272028844032, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := 1865482240, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -753170235392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 640310968320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -221608312832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := -62234165248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := 5923700736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := 98304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -3129344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 41943040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -18317312, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 1431470080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -4422549504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 10019405824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -16716857344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 11258986496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := 39016251392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := -128550961152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := 144153149440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := -336691200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := -424820736, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := -3735552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := 57999360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := -494141440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := 2664005632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := -35520512, den := 49, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := 31676563456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := -80759488512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := 154570096640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := -186486161408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := 14694154240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := 6067060736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := -1920499712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := 1015808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := -5554176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -23592960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := 440827904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := -151191552, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := 9438789632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := -26289504256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := 53252079616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := -63575195648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := 28662054912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := 862584832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := -25870336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := 182976512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := -752713728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := 2199388160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := -5556371456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := 10349969408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := -8979595264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := 31719424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := 23478272, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := 294912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := -7077888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := 65929216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := -330563584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := 1125842944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := -3023306752, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := 782368768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := -4276879360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := -34111488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := 16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := -491520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := 393216, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := -57245696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := 50872320, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := -1707769856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := 6556123136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := -3083796480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := 64623722496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := -166308773888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := 318169481216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := -381728948224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := 208320479232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := 5247041536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := -1438482432, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := -16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := -32768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := 11321344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := -133660672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := 118554624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := -3417505792, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := 10769498112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := -26855538688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := 49181212672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := -61549936640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := 8402518016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := -8541863936, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := 886013952, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := 131072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := -638976, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := 75104256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := -21381120, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := 1390673920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := -4505436160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := 12917669888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := -31253790720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := 52579663872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := -46021394432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := 6977355776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := 1576026112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := 163840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := -3473408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := 29392896, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := -135004160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := 387252224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := -43909120, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := 1015349248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := -587988992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := -4132929536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := 2233270272, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := -19234816, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := -425984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := 4145152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := -18743296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := 41713664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := -62324736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := 114589696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := 56754176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := -937213952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := 182091776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := -245760, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := -12713984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := 45350912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := -110166016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := 10747904, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := 116260864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r450 : ℚ := { num := -1173618688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r451 : ℚ := { num := 11370496, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r452 : ℚ := { num := 2916352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r453 : ℚ := { num := -34242560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r454 : ℚ := { num := 29458432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r455 : ℚ := { num := -728170496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r456 : ℚ := { num := 1929445376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r457 : ℚ := { num := -5168234496, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r458 : ℚ := { num := 11333074944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r459 : ℚ := { num := -13006503936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r460 : ℚ := { num := 41582592, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r461 : ℚ := { num := 215449600, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r462 : ℚ := { num := -205750272, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r463 : ℚ := { num := -13254656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r464 : ℚ := { num := 17563648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r465 : ℚ := { num := -79855616, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r466 : ℚ := { num := 1678770176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r467 : ℚ := { num := -4540366848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r468 : ℚ := { num := 1437859840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r469 : ℚ := { num := -773242880, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r470 : ℚ := { num := 1342570496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r471 : ℚ := { num := -105201664, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r472 : ℚ := { num := -2359296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r473 : ℚ := { num := 1179648, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r474 : ℚ := { num := -63700992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r475 : ℚ := { num := -19857408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r476 : ℚ := { num := 493092864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r477 : ℚ := { num := -574488576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r478 : ℚ := { num := -7077888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r479 : ℚ := { num := 8880128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r480 : ℚ := { num := -51642368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r481 : ℚ := { num := 215285760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r482 : ℚ := { num := -785776640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r483 : ℚ := { num := 2480865280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r484 : ℚ := { num := -5933105152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r485 : ℚ := { num := 9078734848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r486 : ℚ := { num := -6004473856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r487 : ℚ := { num := -126713856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r488 : ℚ := { num := 4718592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r489 : ℚ := { num := -46989312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r490 : ℚ := { num := 258932736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r491 : ℚ := { num := -870088704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r492 : ℚ := { num := 1826095104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r493 : ℚ := { num := -2750939136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r494 : ℚ := { num := 6181748736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r495 : ℚ := { num := -16630284288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r496 : ℚ := { num := 8762425344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r497 : ℚ := { num := 80826925056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r498 : ℚ := { num := -28618457088, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r499 : ℚ := { num := 177831936, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r500 : ℚ := { num := 32768, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r501 : ℚ := { num := -8552448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r502 : ℚ := { num := 79003648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r503 : ℚ := { num := -469614592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r504 : ℚ := { num := 34930688, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r505 : ℚ := { num := -3164798976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r506 : ℚ := { num := 720896, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r507 : ℚ := { num := 252461056, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r508 : ℚ := { num := -24943886336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r509 : ℚ := { num := 18312167424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r510 : ℚ := { num := 1285324800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r511 : ℚ := { num := -23216128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r512 : ℚ := { num := -7929856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r513 : ℚ := { num := 11337728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r514 : ℚ := { num := -62128128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r515 : ℚ := { num := 1413087232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r516 : ℚ := { num := -2567307264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r517 : ℚ := { num := 1355677696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r518 : ℚ := { num := 5271453696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r519 : ℚ := { num := -17256349696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r520 : ℚ := { num := 4023451648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r521 : ℚ := { num := -24707072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r522 : ℚ := { num := 3014656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r523 : ℚ := { num := -5111808, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r524 : ℚ := { num := 11796480, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r525 : ℚ := { num := -471924736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r526 : ℚ := { num := 2477654016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r527 : ℚ := { num := -2877554688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r528 : ℚ := { num := -237666304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r529 : ℚ := { num := 3801088, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r530 : ℚ := { num := 2883584, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r531 : ℚ := { num := -655360, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r532 : ℚ := { num := 9699328, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r533 : ℚ := { num := -340328448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r534 : ℚ := { num := -143392768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r535 : ℚ := { num := 1515585536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r536 : ℚ := { num := -212598784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r537 : ℚ := { num := -98304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r538 : ℚ := { num := -6029312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r539 : ℚ := { num := 74711040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r540 : ℚ := { num := -479723520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r541 : ℚ := { num := 1664221184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r542 : ℚ := { num := -2600468480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r543 : ℚ := { num := -1351352320, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r544 : ℚ := { num := 12288786432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r545 : ℚ := { num := -17915772928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r546 : ℚ := { num := 958660608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r547 : ℚ := { num := 4194304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r548 : ℚ := { num := -1425408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r549 : ℚ := { num := 139558912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r550 : ℚ := { num := -499515392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r551 : ℚ := { num := 573603840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r552 : ℚ := { num := 788529152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r553 : ℚ := { num := -417906688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r554 : ℚ := { num := 478085120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r555 : ℚ := { num := -2015232, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r556 : ℚ := { num := -786432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r557 : ℚ := { num := -21233664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r558 : ℚ := { num := -6619136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r559 : ℚ := { num := 164364288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r560 : ℚ := { num := -191496192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r561 : ℚ := { num := -2359296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r562 : ℚ := { num := 2555904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r563 : ℚ := { num := -3637248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r564 : ℚ := { num := 7077888, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r565 : ℚ := { num := -247922688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r566 : ℚ := { num := -5111808, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r567 : ℚ := { num := 242810880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r568 : ℚ := { num := -3758358528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r569 : ℚ := { num := 134971392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r570 : ℚ := { num := 10420224, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r571 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r572 : ℚ := { num := 1, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15],[0,r0,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29],[0,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41,r42,r43],[0,r30,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53,r54,r55],[0,r0,r56,r57,r58,r59,r60,r61,r62,r63,r64,r65,r66],[0,r0,r67,r68,r69,r70,r71,r72,r73,r74,r75,r76],[0,0,r77,r78,r79,r80,r81,r82,r83,r84,r85],[],[],[],[],[],[],[r86,r87,r88,r89,r90,r91,r92,r93,r94,r95,r96,r97,r98,r99,r100],[0,r101,r102,r103,r104,r105,r106,r107,r108,r109,r110,r111,r112,r113],[r114,r115,r116,r117,r118,r119,r120,r121,r122,r123,r124,r125,r126],[0,r127,r128,r129,r130,r131,r132,r133,r134,r135,r136,r137],[r86,r138,r139,r140,r141,r142,r143,r144,r145,r146,r147],[0,r148,r67,r149,r150,r151,r152,r153,r154,r155],[],[],[],[],[],[0,r148,r156,r157,r158,r159,r160,r161,r162,r163,r164,r165,r166],[0,r86,r167,r168,r169,r170,r171,r172,r173,r174,r175,r176],[0,0,r30,r177,r178,r179,r180,r181,r182,r183,196608],[],[],[],[],[],[],[r184,r185,r186,r187,r188,r189,r190,r191,r192,r193,r194],[0,r148,r67,r149,r150,r151,r152,r153,r154,r155],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,r195,r196,r197,r198,r199,r200,r201,r202,r203,r204,r205,r206,r207],[r101,r208,r209,r210,r211,r212,r213,r214,r215,r216,r217,r218,r219],[0,r220,r221,r222,r223,r224,r225,r226,r227,r228,r229,r230],[0,r148,r231,r232,r233,r234,r235,r236,r237,r238,r239],[0,r148,r240,r241,r242,r243,r244,r245,r246,r247],[],[],[],[],[],[0,r248,r249,r250,r251,r252,r253,r254,r255,r256,r257,r258],[r101,r220,r259,r260,r261,r262,r263,r264,r265,r266,r267],[0,r148,r240,r241,r242,r243,r244,r245,r246,r247],[r184,r268,r88,r269,r270,r271,r272,r273,65536],[],[],[],[],[0,r195,r274,r275,r276,r277,r278,r279,r280,r281],[r184,r268,r88,r269,r270,r271,r272,r273,65536],[],[],[],[],[],[],[],[],[],[],[r148,r282,r283,r284,r285,r286,r287,r288,r289,r290,-1376256],[],[r291,r292,r293,r294,r295,r296,r297,r298,131072],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,r299,r300,r301,r302,r303,r304,r305,r306,r307,r308,r309,r310,r311,r312,r313,r314]),(⟨0,0,1⟩,[0,r299,r315,r316,r317,r318,r319,r320,r321,r322,r323,r324,r325,r326,r327,r328]),(⟨0,0,2⟩,[0,r329,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340,r341,r342]),(⟨0,0,3⟩,[0,r329,r343,r344,r345,r346,r347,r348,r349,r350,r351,r352,r353,r354]),(⟨0,0,4⟩,[0,r299,r355,r356,r357,r358,r359,r360,r361,r362,r363,r364,r365]),(⟨0,0,5⟩,[0,r299,r115,r366,r367,r368,r369,r370,r371,r372,r373,r374]),(⟨0,0,6⟩,[0,0,r375,r376,r377,r378,r379,r380,r381,r382,r383]),(⟨0,1,0⟩,[0,r299,r315,r316,r317,r318,r319,r320,r321,r322,r323,r324,r325,r326,r327,r328]),(⟨0,1,1⟩,[r384,r385,r386,r387,r388,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398]),(⟨0,1,2⟩,[0,r399,r400,r401,r402,r403,r404,r405,r406,r407,r408,r409,r410,r411]),(⟨0,1,3⟩,[r101,r412,r413,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423]),(⟨0,1,4⟩,[0,r424,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434]),(⟨0,1,5⟩,[r384,r435,r436,r437,r438,r439,r440,r441,r442,r443,r444]),(⟨0,1,6⟩,[0,r0,r115,r445,r446,r447,r448,r449,r450,r451]),(⟨0,2,0⟩,[0,r329,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340,r341,r342]),(⟨0,2,1⟩,[0,r399,r400,r401,r402,r403,r404,r405,r406,r407,r408,r409,r410,r411]),(⟨0,2,2⟩,[0,r0,r452,r453,r454,r455,r456,r457,r458,r459,r460,r461,r462]),(⟨0,2,3⟩,[0,r384,r248,r463,r464,r465,r466,r467,r468,r469,r470,r471]),(⟨0,2,4⟩,[0,0,r329,r472,r473,r474,r475,r476,r477,r478,98304]),(⟨0,3,0⟩,[0,r329,r343,r344,r345,r346,r347,r348,r349,r350,r351,r352,r353,r354]),(⟨0,3,1⟩,[r101,r412,r413,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423]),(⟨0,3,2⟩,[0,r384,r248,r463,r464,r465,r466,r467,r468,r469,r470,r471]),(⟨0,3,3⟩,[r86,r138,r479,r480,r481,r482,r483,r484,r485,r486,r487]),(⟨0,3,4⟩,[0,r0,r115,r445,r446,r447,r448,r449,r450,r451]),(⟨0,4,0⟩,[0,r299,r355,r356,r357,r358,r359,r360,r361,r362,r363,r364,r365]),(⟨0,4,1⟩,[0,r424,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434]),(⟨0,4,2⟩,[0,0,r329,r472,r473,r474,r475,r476,r477,r478,98304]),(⟨0,4,3⟩,[0,r0,r115,r445,r446,r447,r448,r449,r450,r451]),(⟨0,5,0⟩,[0,r299,r115,r366,r367,r368,r369,r370,r371,r372,r373,r374]),(⟨0,5,1⟩,[r384,r435,r436,r437,r438,r439,r440,r441,r442,r443,r444]),(⟨0,6,0⟩,[0,0,r375,r376,r377,r378,r379,r380,r381,r382,r383]),(⟨0,6,1⟩,[0,r0,r115,r445,r446,r447,r448,r449,r450,r451]),(⟨1,0,0⟩,[0,r299,r315,r316,r317,r318,r319,r320,r321,r322,r323,r324,r325,r326,r327,r328]),(⟨1,0,1⟩,[r384,r385,r386,r387,r388,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398]),(⟨1,0,2⟩,[0,r399,r400,r401,r402,r403,r404,r405,r406,r407,r408,r409,r410,r411]),(⟨1,0,3⟩,[r101,r412,r413,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423]),(⟨1,0,4⟩,[0,r424,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434]),(⟨1,0,5⟩,[r384,r435,r436,r437,r438,r439,r440,r441,r442,r443,r444]),(⟨1,0,6⟩,[0,r0,r115,r445,r446,r447,r448,r449,r450,r451]),(⟨1,1,0⟩,[r384,r385,r386,r387,r388,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398]),(⟨1,1,1⟩,[0,r148,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498,r499]),(⟨1,1,2⟩,[r399,r500,r501,r502,r503,r504,r505,r506,r507,r508,r509,r510,r511]),(⟨1,1,3⟩,[0,r127,r512,r513,r514,r515,r516,r517,r518,r519,r520,r521]),(⟨1,1,4⟩,[0,r0,r522,r523,r524,r525,r179,r526,r527,r528,r529]),(⟨1,1,5⟩,[0,r0,r530,r531,r532,r533,r534,r535,r536,r537]),(⟨1,2,0⟩,[0,r399,r400,r401,r402,r403,r404,r405,r406,r407,r408,r409,r410,r411]),(⟨1,2,1⟩,[r399,r500,r501,r502,r503,r504,r505,r506,r507,r508,r509,r510,r511]),(⟨1,2,2⟩,[0,r30,r538,r539,r540,r541,r542,r543,r544,r545,r546,r547]),(⟨1,2,3⟩,[r399,r127,r548,r249,r549,r550,r551,r552,r553,r554,r555]),(⟨1,2,4⟩,[0,r0,r530,r531,r532,r533,r534,r535,r536,r537]),(⟨1,2,5⟩,[r86,r556,r386,r557,r558,r559,r560,r561,32768]),(⟨1,3,0⟩,[r101,r412,r413,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423]),(⟨1,3,1⟩,[0,r127,r512,r513,r514,r515,r516,r517,r518,r519,r520,r521]),(⟨1,3,2⟩,[r399,r127,r548,r249,r549,r550,r551,r552,r553,r554,r555]),(⟨1,3,3⟩,[0,r148,r67,r149,r150,r151,r152,r153,r154,r155]),(⟨1,3,4⟩,[r86,r556,r386,r557,r558,r559,r560,r561,32768]),(⟨1,4,0⟩,[0,r424,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434]),(⟨1,4,1⟩,[0,r0,r522,r523,r524,r525,r179,r526,r527,r528,r529]),(⟨1,4,2⟩,[0,r0,r530,r531,r532,r533,r534,r535,r536,r537]),(⟨1,4,3⟩,[r86,r556,r386,r557,r558,r559,r560,r561,32768]),(⟨1,5,0⟩,[r384,r435,r436,r437,r438,r439,r440,r441,r442,r443,r444]),(⟨1,5,1⟩,[0,r0,r530,r531,r532,r533,r534,r535,r536,r537]),(⟨1,5,2⟩,[r86,r556,r386,r557,r558,r559,r560,r561,32768]),(⟨1,6,0⟩,[0,r0,r115,r445,r446,r447,r448,r449,r450,r451]),(⟨2,0,0⟩,[0,r329,r330,r331,r332,r333,r334,r335,r336,r337,r338,r339,r340,r341,r342]),(⟨2,0,1⟩,[0,r399,r400,r401,r402,r403,r404,r405,r406,r407,r408,r409,r410,r411]),(⟨2,0,2⟩,[0,r0,r452,r453,r454,r455,r456,r457,r458,r459,r460,r461,r462]),(⟨2,0,3⟩,[0,r384,r248,r463,r464,r465,r466,r467,r468,r469,r470,r471]),(⟨2,0,4⟩,[0,0,r329,r472,r473,r474,r475,r476,r477,r478,98304]),(⟨2,1,0⟩,[0,r399,r400,r401,r402,r403,r404,r405,r406,r407,r408,r409,r410,r411]),(⟨2,1,1⟩,[r399,r500,r501,r502,r503,r504,r505,r506,r507,r508,r509,r510,r511]),(⟨2,1,2⟩,[0,r30,r538,r539,r540,r541,r542,r543,r544,r545,r546,r547]),(⟨2,1,3⟩,[r399,r127,r548,r249,r549,r550,r551,r552,r553,r554,r555]),(⟨2,1,4⟩,[0,r0,r530,r531,r532,r533,r534,r535,r536,r537]),(⟨2,1,5⟩,[r86,r556,r386,r557,r558,r559,r560,r561,32768]),(⟨2,2,0⟩,[0,r0,r452,r453,r454,r455,r456,r457,r458,r459,r460,r461,r462]),(⟨2,2,1⟩,[0,r30,r538,r539,r540,r541,r542,r543,r544,r545,r546,r547]),(⟨2,2,2⟩,[r0,r562,r563,r564,r565,r566,r567,r568,r569,r570,-688128]),(⟨2,2,4⟩,[r184,r268,r88,r269,r270,r271,r272,r273,65536]),(⟨2,3,0⟩,[0,r384,r248,r463,r464,r465,r466,r467,r468,r469,r470,r471]),(⟨2,3,1⟩,[r399,r127,r548,r249,r549,r550,r551,r552,r553,r554,r555]),(⟨2,4,0⟩,[0,0,r329,r472,r473,r474,r475,r476,r477,r478,98304]),(⟨2,4,1⟩,[0,r0,r530,r531,r532,r533,r534,r535,r536,r537]),(⟨2,4,2⟩,[r184,r268,r88,r269,r270,r271,r272,r273,65536]),(⟨2,5,1⟩,[r86,r556,r386,r557,r558,r559,r560,r561,32768]),(⟨3,0,0⟩,[0,r329,r343,r344,r345,r346,r347,r348,r349,r350,r351,r352,r353,r354]),(⟨3,0,1⟩,[r101,r412,r413,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423]),(⟨3,0,2⟩,[0,r384,r248,r463,r464,r465,r466,r467,r468,r469,r470,r471]),(⟨3,0,3⟩,[r86,r138,r479,r480,r481,r482,r483,r484,r485,r486,r487]),(⟨3,0,4⟩,[0,r0,r115,r445,r446,r447,r448,r449,r450,r451]),(⟨3,1,0⟩,[r101,r412,r413,r414,r415,r416,r417,r418,r419,r420,r421,r422,r423]),(⟨3,1,1⟩,[0,r127,r512,r513,r514,r515,r516,r517,r518,r519,r520,r521]),(⟨3,1,2⟩,[r399,r127,r548,r249,r549,r550,r551,r552,r553,r554,r555]),(⟨3,1,3⟩,[0,r148,r67,r149,r150,r151,r152,r153,r154,r155]),(⟨3,1,4⟩,[r86,r556,r386,r557,r558,r559,r560,r561,32768]),(⟨3,2,0⟩,[0,r384,r248,r463,r464,r465,r466,r467,r468,r469,r470,r471]),(⟨3,2,1⟩,[r399,r127,r548,r249,r549,r550,r551,r552,r553,r554,r555]),(⟨3,3,0⟩,[r86,r138,r479,r480,r481,r482,r483,r484,r485,r486,r487]),(⟨3,3,1⟩,[0,r148,r67,r149,r150,r151,r152,r153,r154,r155]),(⟨3,4,0⟩,[0,r0,r115,r445,r446,r447,r448,r449,r450,r451]),(⟨3,4,1⟩,[r86,r556,r386,r557,r558,r559,r560,r561,32768]),(⟨4,0,0⟩,[0,r299,r355,r356,r357,r358,r359,r360,r361,r362,r363,r364,r365]),(⟨4,0,1⟩,[0,r424,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434]),(⟨4,0,2⟩,[0,0,r329,r472,r473,r474,r475,r476,r477,r478,98304]),(⟨4,0,3⟩,[0,r0,r115,r445,r446,r447,r448,r449,r450,r451]),(⟨4,1,0⟩,[0,r424,r425,r426,r427,r428,r429,r430,r431,r432,r433,r434]),(⟨4,1,1⟩,[0,r0,r522,r523,r524,r525,r179,r526,r527,r528,r529]),(⟨4,1,2⟩,[0,r0,r530,r531,r532,r533,r534,r535,r536,r537]),(⟨4,1,3⟩,[r86,r556,r386,r557,r558,r559,r560,r561,32768]),(⟨4,2,0⟩,[0,0,r329,r472,r473,r474,r475,r476,r477,r478,98304]),(⟨4,2,1⟩,[0,r0,r530,r531,r532,r533,r534,r535,r536,r537]),(⟨4,2,2⟩,[r184,r268,r88,r269,r270,r271,r272,r273,65536]),(⟨4,3,0⟩,[0,r0,r115,r445,r446,r447,r448,r449,r450,r451]),(⟨4,3,1⟩,[r86,r556,r386,r557,r558,r559,r560,r561,32768]),(⟨5,0,0⟩,[0,r299,r115,r366,r367,r368,r369,r370,r371,r372,r373,r374]),(⟨5,0,1⟩,[r384,r435,r436,r437,r438,r439,r440,r441,r442,r443,r444]),(⟨5,1,0⟩,[r384,r435,r436,r437,r438,r439,r440,r441,r442,r443,r444]),(⟨5,1,1⟩,[0,r0,r530,r531,r532,r533,r534,r535,r536,r537]),(⟨5,1,2⟩,[r86,r556,r386,r557,r558,r559,r560,r561,32768]),(⟨5,2,1⟩,[r86,r556,r386,r557,r558,r559,r560,r561,32768]),(⟨6,0,0⟩,[0,0,r375,r376,r377,r378,r379,r380,r381,r382,r383]),(⟨6,0,1⟩,[0,r0,r115,r445,r446,r447,r448,r449,r450,r451]),(⟨6,1,0⟩,[0,r0,r115,r445,r446,r447,r448,r449,r450,r451])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,-384,8064,-64256,246656,-476544,385152,5632,-79744]),(⟨0,0,1⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨0,0,2⟩,[0,384,-6400,33024,-52224,4480,12544]),(⟨0,0,3⟩,[0,384,-6656,34048,-49664,-2688]),(⟨0,1,0⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨0,1,1⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨0,1,3⟩,[-128,1536,-3840,-4608,15232]),(⟨0,2,0⟩,[0,384,-6400,33024,-52224,4480,12544]),(⟨0,3,0⟩,[0,384,-6656,34048,-49664,-2688]),(⟨0,3,1⟩,[-128,1536,-3840,-4608,15232]),(⟨1,0,0⟩,[0,-384,7168,-48384,155136,-241024,127488,57344]),(⟨1,0,1⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨1,0,3⟩,[-128,1536,-3840,-4608,15232]),(⟨1,1,0⟩,[128,-1792,7808,-13824,2432,62720,-106624]),(⟨1,3,0⟩,[-128,1536,-3840,-4608,15232]),(⟨2,0,0⟩,[0,384,-6400,33024,-52224,4480,12544]),(⟨3,0,0⟩,[0,384,-6656,34048,-49664,-2688]),(⟨3,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨3,1,0⟩,[-128,1536,-3840,-4608,15232])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[128,-2048,12672,-45312,136064,-378368,739968,-708864,147456]),(⟨0,0,1⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨0,0,2⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨0,0,3⟩,[0,768,-5120,14848,-50176,88832]),(⟨0,1,0⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨0,1,1⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨0,2,0⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨0,3,0⟩,[0,768,-5120,14848,-50176,88832]),(⟨1,0,0⟩,[0,-512,5120,-21760,72704,-233472,477184,-413952]),(⟨1,0,1⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨1,1,0⟩,[0,0,-768,9216,-23040,-27648,91392]),(⟨1,1,2⟩,[-256,3072,-7680,-9216,30464]),(⟨1,2,1⟩,[-256,3072,-7680,-9216,30464]),(⟨2,0,0⟩,[-128,1792,-7040,12800,-40832,79616,-13440]),(⟨2,1,1⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[0,768,-5120,14848,-50176,88832])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 4 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r571) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 11 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r571) sourceRight))).isZero := by decide +kernel

noncomputable def partial19 : Poly := []

theorem partial_sound19 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 19)
      sourceRight).eval u v t=partial19.eval u v t := by rfl

noncomputable def chunk16 : Poly := [(⟨3,0,0⟩,[0,384,-6656,34048,-49664,-2688]),(⟨3,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨3,1,0⟩,[-128,1536,-3840,-4608,15232])]

noncomputable def partial16 : Poly := [(⟨3,0,0⟩,[0,49152,-1638400,22855680,-177831936,886669312,-3217555456,9651585024,-24715788288,48394780672,-60849586176,38236569600,-5417828352,-396361728]),(⟨3,0,1⟩,[-16384,458752,-5455872,37912576,-184156160,714342400,-2363916288,6642663424,-14969749504,24177606656,-23194124288,7798947840,3358752768]),(⟨3,0,2⟩,[0,16384,98304,-6373376,59113472,-235503616,562364416,-1526104064,4508745728,-8467431424,9629433856,-6269190144]),(⟨3,0,3⟩,[16384,-425984,4440064,-25821184,107642880,-392888320,1240432640,-2966552576,4539367424,-3002236928,-443498496]),(⟨3,0,4⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨3,1,0⟩,[-16384,458752,-5455872,37912576,-184156160,714342400,-2363916288,6642663424,-14969749504,24177606656,-23194124288,7798947840,3358752768]),(⟨3,1,1⟩,[0,131072,-2883584,24936448,-111411200,291110912,-546570240,1011023872,-1000079360,-3784310784,13887340544,-12856295424]),(⟨3,1,2⟩,[16384,-425984,4243456,-21102592,61767680,-126025728,94732288,549847040,-1511702528,432373760,1187364864]),(⟨3,1,3⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨3,2,0⟩,[0,16384,98304,-6373376,59113472,-235503616,562364416,-1526104064,4508745728,-8467431424,9629433856,-6269190144]),(⟨3,2,1⟩,[16384,-425984,4243456,-21102592,61767680,-126025728,94732288,549847040,-1511702528,432373760,1187364864]),(⟨3,3,0⟩,[16384,-425984,4440064,-25821184,107642880,-392888320,1240432640,-2966552576,4539367424,-3002236928,-443498496]),(⟨3,3,1⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨3,4,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨4,0,0⟩,[0,0,-196608,5373952,-59867136,372506624,-1567358976,5279580160,-14836629504,30402150400,-37165531136,19275841536,1112702976]),(⟨4,0,1⟩,[0,65536,-1441792,12320768,-51380224,97386496,-25952256,-4980736,-715128832,381222912,4711383040,-6550978560]),(⟨4,0,2⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨4,1,0⟩,[0,65536,-1441792,12320768,-51380224,97386496,-25952256,-4980736,-715128832,381222912,4711383040,-6550978560]),(⟨4,1,1⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨4,1,2⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨4,1,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,2,0⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨4,2,1⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨4,2,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,3,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,0,0⟩,[0,-49152,1540096,-18989056,119144448,-429228032,1082982400,-2542108672,4793696256,-4301897728,453476352,36126720]),(⟨5,0,1⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨5,1,0⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨5,1,1⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨5,1,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,2,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,0,0⟩,[0,0,294912,-7077888,65929216,-330563584,1125842944,-3023306752,5476581376,-4276879360,-238780416]),(⟨6,0,1⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨6,1,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024])]


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

noncomputable def partial12 : Poly := [(⟨1,0,3⟩,[-16384,458752,-5259264,32538624,-124289024,341835776,-796557312,1363083264,-133120000,-6224543744,13971406848,-11476893696,2246049792]),(⟨1,0,4⟩,[0,65536,-1441792,12615680,-60030976,193724416,-520617984,1016004608,-284950528,-4165533696,9175957504,-6305316864]),(⟨1,0,5⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨1,0,6⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨1,1,0⟩,[16384,-491520,6291456,-46268416,226181120,-818184192,2350252032,-5349048320,8435187712,-3583279104,-25488654336,82991513600,-122999685120,84830355456,-15722348544]),(⟨1,1,1⟩,[0,-65536,1572864,-15958016,95354880,-402096128,1328283648,-3413311488,5961285632,-3516399616,-15512371200,53815967744,-76842336256,44137218048]),(⟨1,1,2⟩,[-16384,458752,-5111808,30015488,-108216320,276955136,-531234816,608698368,248594432,-3546349568,9314500608,-9331933184,1433026560]),(⟨1,1,3⟩,[0,163840,-3473408,29687808,-143654912,483590144,-1241120768,2036334592,-157810688,-8679686144,20097466368,-15776940032]),(⟨1,1,4⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨1,2,0⟩,[0,-65536,1572864,-15958016,95354880,-402096128,1328283648,-3413311488,5961285632,-3516399616,-15512371200,53815967744,-76842336256,44137218048]),(⟨1,2,1⟩,[0,0,-98304,2555904,-25460736,120324096,-247922688,-86900736,1699676160,-3758358528,944799744,8680046592,-9744580608]),(⟨1,2,3⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨1,3,0⟩,[-32768,917504,-10371072,62554112,-232505344,618790912,-1327792128,1971781632,115474432,-9770893312,23285907456,-20808826880,3679076352]),(⟨1,3,1⟩,[0,65536,-1441792,12615680,-60030976,193724416,-520617984,1016004608,-284950528,-4165533696,9175957504,-6305316864]),(⟨1,3,2⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨1,3,3⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨1,4,0⟩,[0,163840,-3473408,29687808,-143654912,483590144,-1241120768,2036334592,-157810688,-8679686144,20097466368,-15776940032]),(⟨1,4,1⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨1,5,0⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨1,6,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨2,0,0⟩,[0,49152,-1605632,22200320,-172818432,868253696,-3181838336,9596534784,-24653070336,48831119360,-62985633792,40458108928,-1594294272,-8231387136,1849688064]),(⟨2,0,1⟩,[0,0,-196608,5242880,-58032128,363003904,-1543241728,5231345664,-14753267712,30653415424,-38724763648,20827340800,4131291136,-5192613888]),(⟨2,0,2⟩,[0,-49152,1507328,-18399232,115834880,-424247296,1088684032,-2540666880,4816699392,-4624072704,546373632,938491904,-168591360]),(⟨2,0,3⟩,[0,65536,-1146880,5734400,3801088,-129761280,595787776,-1998258176,5271322624,-8843231232,8944517120,-5191008256]),(⟨2,0,4⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨2,1,0⟩,[0,-65536,1376256,-10715136,37322752,-39092224,-214958080,1818034176,-8791982080,27137015808,-54237134848,74643308544,-72711045120,38944604160]),(⟨2,1,1⟩,[0,0,-98304,2260992,-17006592,27131904,233373696,-1120468992,1436614656,716046336,-4240932864,8742666240,-8598159360]),(⟨2,1,3⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨2,1,5⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,2,0⟩,[0,-49152,1409024,-15843328,90374144,-303923200,840761344,-2627567616,6516375552,-8382431232,1491173376,9618538496,-9913171968]),(⟨2,2,2⟩,[-32768,851968,-8486912,40108032,-82640896,-28966912,566558720,-1252786176,314933248,2893348864,-3248193536]),(⟨2,2,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,3,0⟩,[0,65536,-1146880,5734400,3801088,-129761280,595787776,-1998258176,5271322624,-8843231232,8944517120,-5191008256]),(⟨2,3,1⟩,[-32768,851968,-8388608,37748736,-62586880,-92667904,546701312,-759693312,-259555328,2051080192,-1856110592]),(⟨2,4,0⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨2,4,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,5,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,0,0⟩,[0,49152,-1835008,28098560,-235864064,1249673216,-4760797184,14882930688,-39469056000,79048196096,-99574349824,59063910400,-1286537216,-5588975616]),(⟨3,0,1⟩,[-16384,458752,-5455872,37617664,-175702016,621150208,-1882619904,5609095168,-15232811008,28652011520,-28379856896,7861567488,4505174016]),(⟨3,0,2⟩,[0,16384,98304,-6373376,59113472,-235503616,562364416,-1526104064,4508745728,-8467431424,9629433856,-6269190144]),(⟨3,0,3⟩,[32768,-851968,8585216,-44564480,149356544,-455213056,1355022336,-2909798400,3602153472,-1727594496,-648216576]),(⟨3,0,4⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨3,1,0⟩,[-32768,917504,-10567680,67633152,-283918336,898105344,-2413854720,6217793536,-14984216576,25105661952,-19065356288,-1470365696,5938200576]),(⟨3,1,1⟩,[0,131072,-2883584,24936448,-111411200,291110912,-546570240,1011023872,-1000079360,-3784310784,13887340544,-12856295424]),(⟨3,1,2⟩,[16384,-524288,7061504,-52166656,222199808,-470548480,7045120,2041315328,-3240280064,453246976,1569505280]),(⟨3,1,3⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨3,1,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,2,0⟩,[0,16384,98304,-6373376,59113472,-235503616,562364416,-1526104064,4508745728,-8467431424,9629433856,-6269190144]),(⟨3,2,1⟩,[-16384,327680,-1425408,-12058624,139558912,-499515392,573603840,788529152,-2925346816,3346595840,-1678688256]),(⟨3,3,0⟩,[32768,-851968,8585216,-44564480,149356544,-455213056,1355022336,-2909798400,3602153472,-1727594496,-648216576]),(⟨3,3,1⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨3,4,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨3,4,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,0,0⟩,[0,-49152,1310720,-13025280,55967744,-51740672,-478674944,2738913280,-10019930112,25778077696,-36619157504,20214333440,944111616]),(⟨4,0,1⟩,[0,65536,-1441792,12320768,-51380224,97386496,-25952256,-4980736,-715128832,381222912,4711383040,-6550978560]),(⟨4,0,2⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨4,0,3⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨4,1,0⟩,[0,163840,-3473408,29392896,-135004160,387252224,-746455040,1015349248,-587988992,-4132929536,15632891904,-16022601728]),(⟨4,1,1⟩,[0,-98304,3014656,-35782656,200540160,-471924736,-127401984,2477654016,-2877554688,-1663664128,3166306304]),(⟨4,1,2⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨4,1,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,2,0⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨4,2,1⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨4,2,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,3,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨4,3,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,0,0⟩,[0,-49152,1835008,-25870336,182976512,-752713728,2199388160,-5556371456,10349969408,-8979595264,222035968,1150435328]),(⟨5,0,1⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨5,1,0⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨5,1,1⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨5,1,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,2,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,0,0⟩,[0,0,294912,-7077888,65929216,-330563584,1125842944,-3023306752,5476581376,-4276879360,-238780416]),(⟨6,0,1⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨6,1,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024])]


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

noncomputable def partial8 : Poly := [(⟨0,3,0⟩,[0,49152,-1638400,22855680,-177831936,886669312,-3217555456,9651585024,-24715788288,48394780672,-60849586176,38236569600,-5417828352,-396361728]),(⟨0,3,1⟩,[-16384,458752,-5455872,37912576,-184156160,714342400,-2363916288,6642663424,-14969749504,24177606656,-23194124288,7798947840,3358752768]),(⟨0,3,2⟩,[0,16384,98304,-6373376,59113472,-235503616,562364416,-1526104064,4508745728,-8467431424,9629433856,-6269190144]),(⟨0,3,3⟩,[16384,-425984,4440064,-25821184,107642880,-392888320,1240432640,-2966552576,4539367424,-3002236928,-443498496]),(⟨0,3,4⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨0,4,0⟩,[0,0,-196608,5373952,-59867136,372506624,-1567358976,5279580160,-14836629504,30402150400,-37165531136,19275841536,1112702976]),(⟨0,4,1⟩,[0,65536,-1441792,12320768,-51380224,97386496,-25952256,-4980736,-715128832,381222912,4711383040,-6550978560]),(⟨0,4,2⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨0,5,0⟩,[0,-49152,1540096,-18989056,119144448,-429228032,1082982400,-2542108672,4793696256,-4301897728,453476352,36126720]),(⟨0,5,1⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨0,6,0⟩,[0,0,294912,-7077888,65929216,-330563584,1125842944,-3023306752,5476581376,-4276879360,-238780416]),(⟨0,6,1⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨1,0,0⟩,[0,-49152,1703936,-25739264,227180544,-1338736640,5788794880,-19917144064,57411043328,-137483632640,256094240768,-335889809408,266368876544,-83479363584,-21850226688,8455716864]),(⟨1,0,1⟩,[16384,-491520,6488064,-51904512,296009728,-1329233920,4931584000,-15398600704,40457977856,-85862416384,132861853696,-121835880448,24219697152,59420082176,-39460012032]),(⟨1,0,2⟩,[0,-16384,-32768,5783552,-66584576,354811904,-1154678784,3041820672,-8201568256,20554825728,-41258352640,64863944704,-73990275072,43366514688]),(⟨1,0,3⟩,[-32768,917504,-10665984,70025216,-312066048,1111359488,-3419373568,8671657984,-16154099712,17703108608,-3670130688,-12361105408,8773058560]),(⟨1,0,4⟩,[0,163840,-3473408,29687808,-143654912,483590144,-1241120768,2036334592,-157810688,-8679686144,20097466368,-15776940032]),(⟨1,0,5⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨1,0,6⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨1,1,0⟩,[16384,-491520,6488064,-51904512,296009728,-1329233920,4931584000,-15398600704,40457977856,-85862416384,132861853696,-121835880448,24219697152,59420082176,-39460012032]),(⟨1,1,1⟩,[0,-131072,3145728,-31621120,181665792,-692125696,1936982016,-4330291200,8021868544,-9059827712,-12591562752,80758276096,-143618736128,93515218944]),(⟨1,1,2⟩,[-16384,458752,-5210112,32571392,-133677056,397279232,-779157504,521797632,1948270592,-7304708096,10259300352,-651886592,-8311554048]),(⟨1,1,3⟩,[0,163840,-3473408,29687808,-143654912,483590144,-1241120768,2036334592,-157810688,-8679686144,20097466368,-15776940032]),(⟨1,1,4⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨1,2,0⟩,[0,-16384,-32768,5783552,-66584576,354811904,-1154678784,3041820672,-8201568256,20554825728,-41258352640,64863944704,-73990275072,43366514688]),(⟨1,2,1⟩,[-16384,458752,-5210112,32571392,-133677056,397279232,-779157504,521797632,1948270592,-7304708096,10259300352,-651886592,-8311554048]),(⟨1,2,3⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨1,3,0⟩,[-32768,917504,-10862592,75399168,-371933184,1483866112,-4986732544,13951238144,-30990729216,48105259008,-40835661824,6914736128,9885761536]),(⟨1,3,1⟩,[0,229376,-4915200,42008576,-195035136,580976640,-1267073024,2031353856,-872939520,-8298463232,24808849408,-22327918592]),(⟨1,3,2⟩,[16384,-425984,4243456,-21102592,61767680,-126025728,94732288,549847040,-1511702528,432373760,1187364864]),(⟨1,3,3⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨1,4,0⟩,[0,163840,-3473408,29392896,-135004160,387252224,-746455040,1015349248,-587988992,-4132929536,15632891904,-16022601728]),(⟨1,4,1⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨1,4,2⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨1,4,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,5,0⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨1,5,1⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨1,5,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,6,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨2,0,0⟩,[0,49152,-1409024,16564224,-102989824,357203968,-600506368,-453017600,7369719808,-33448017920,95364874240,-164369285120,145625088000,-33641660416,-21887975424]),(⟨2,0,1⟩,[0,-65536,1376256,-10420224,28278784,72974336,-934543360,4314365952,-12692684800,25109987328,-35803955200,47769649152,-62645108736,44185387008]),(⟨2,0,2⟩,[0,-49152,1409024,-15843328,90374144,-303923200,840761344,-2627567616,6516375552,-8382431232,1491173376,9618538496,-9913171968]),(⟨2,0,3⟩,[0,65536,-1146880,5734400,3801088,-129761280,595787776,-1998258176,5271322624,-8843231232,8944517120,-5191008256]),(⟨2,0,4⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨2,1,0⟩,[0,-65536,1376256,-10420224,28278784,72974336,-934543360,4314365952,-12692684800,25109987328,-35803955200,47769649152,-62645108736,44185387008]),(⟨2,1,1⟩,[0,0,-196608,4816896,-42467328,147456000,-14548992,-1207369728,3136290816,-3042312192,-3296133120,17422712832,-18342739968]),(⟨2,1,2⟩,[0,98304,-3014656,37355520,-239861760,832110592,-1300234240,-675676160,6144393216,-8957886464,3355312128,1746927616]),(⟨2,1,3⟩,[-32768,851968,-8388608,37748736,-62586880,-92667904,546701312,-759693312,-259555328,2051080192,-1856110592]),(⟨2,1,5⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,2,0⟩,[0,-49152,1409024,-15843328,90374144,-303923200,840761344,-2627567616,6516375552,-8382431232,1491173376,9618538496,-9913171968]),(⟨2,2,1⟩,[0,98304,-3014656,37355520,-239861760,832110592,-1300234240,-675676160,6144393216,-8957886464,3355312128,1746927616]),(⟨2,2,2⟩,[-65536,1703936,-16973824,80216064,-165281792,-57933824,1133117440,-2505572352,629866496,5786697728,-6496387072]),(⟨2,2,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,3,0⟩,[0,16384,393216,-13254656,122945536,-558989312,1678770176,-4540366848,10065018880,-13145128960,9397993472,-5154881536]),(⟨2,3,1⟩,[-16384,425984,-4243456,19005440,-20873216,-154992640,661291008,-702939136,-1196769280,3325722624,-2060828672]),(⟨2,4,0⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨2,4,1⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨2,4,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,5,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,0,0⟩,[0,98304,-3440640,49840128,-397803520,2006581248,-7243759616,21338062848,-53631909888,103119421440,-125320331264,70111887360,1565523968,-6359678976]),(⟨3,0,1⟩,[-32768,917504,-10567680,67633152,-283918336,898105344,-2413854720,6217793536,-14984216576,25105661952,-19065356288,-1470365696,5938200576]),(⟨3,0,2⟩,[0,16384,98304,-6373376,59113472,-235503616,562364416,-1526104064,4508745728,-8467431424,9629433856,-6269190144]),(⟨3,0,3⟩,[32768,-851968,8585216,-44564480,149356544,-455213056,1355022336,-2909798400,3602153472,-1727594496,-648216576]),(⟨3,0,4⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨3,1,0⟩,[-32768,917504,-10567680,67633152,-283918336,898105344,-2413854720,6217793536,-14984216576,25105661952,-19065356288,-1470365696,5938200576]),(⟨3,1,1⟩,[0,229376,-5898240,62291968,-351272960,1123221504,-1846804480,335347712,5144313856,-12742197248,17242652672,-11109367808]),(⟨3,1,2⟩,[-16384,327680,-1425408,-12058624,139558912,-499515392,573603840,788529152,-2925346816,3346595840,-1678688256]),(⟨3,1,3⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨3,1,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,2,0⟩,[0,16384,98304,-6373376,59113472,-235503616,562364416,-1526104064,4508745728,-8467431424,9629433856,-6269190144]),(⟨3,2,1⟩,[-16384,327680,-1425408,-12058624,139558912,-499515392,573603840,788529152,-2925346816,3346595840,-1678688256]),(⟨3,3,0⟩,[32768,-851968,8880128,-51642368,215285760,-785776640,2480865280,-5933105152,9078734848,-6004473856,-886996992]),(⟨3,3,1⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨3,4,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨3,4,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,0,0⟩,[0,-49152,1015808,-5554176,-23592960,440827904,-2570256384,9438789632,-26289504256,53252079616,-63575195648,28662054912,6038093824]),(⟨4,0,1⟩,[0,163840,-3473408,29392896,-135004160,387252224,-746455040,1015349248,-587988992,-4132929536,15632891904,-16022601728]),(⟨4,0,2⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨4,0,3⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨4,1,0⟩,[0,163840,-3473408,29392896,-135004160,387252224,-746455040,1015349248,-587988992,-4132929536,15632891904,-16022601728]),(⟨4,1,1⟩,[0,-98304,3014656,-35782656,200540160,-471924736,-127401984,2477654016,-2877554688,-1663664128,3166306304]),(⟨4,1,2⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨4,1,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,2,0⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨4,2,1⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨4,2,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,3,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨4,3,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,0,0⟩,[0,-49152,1835008,-25870336,182976512,-752713728,2199388160,-5556371456,10349969408,-8979595264,222035968,1150435328]),(⟨5,0,1⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨5,1,0⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨5,1,1⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨5,1,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,2,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,0,0⟩,[0,0,294912,-7077888,65929216,-330563584,1125842944,-3023306752,5476581376,-4276879360,-238780416]),(⟨6,0,1⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨6,1,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024])]


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

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[0,-49152,1703936,-25739264,227180544,-1338736640,5788794880,-19917144064,57411043328,-137483632640,256094240768,-335889809408,266368876544,-83479363584,-21850226688,8455716864]),(⟨0,1,1⟩,[16384,-491520,6488064,-51904512,296009728,-1329233920,4931584000,-15398600704,40457977856,-85862416384,132861853696,-121835880448,24219697152,59420082176,-39460012032]),(⟨0,1,2⟩,[0,-16384,-32768,5783552,-66584576,354811904,-1154678784,3041820672,-8201568256,20554825728,-41258352640,64863944704,-73990275072,43366514688]),(⟨0,1,3⟩,[-32768,917504,-10665984,70025216,-312066048,1111359488,-3419373568,8671657984,-16154099712,17703108608,-3670130688,-12361105408,8773058560]),(⟨0,1,4⟩,[0,163840,-3473408,29687808,-143654912,483590144,-1241120768,2036334592,-157810688,-8679686144,20097466368,-15776940032]),(⟨0,1,5⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨0,1,6⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨0,2,0⟩,[0,49152,-1409024,16564224,-102989824,357203968,-600506368,-453017600,7369719808,-33448017920,95364874240,-164369285120,145625088000,-33641660416,-21887975424]),(⟨0,2,1⟩,[0,-65536,1376256,-10420224,28278784,72974336,-934543360,4314365952,-12692684800,25109987328,-35803955200,47769649152,-62645108736,44185387008]),(⟨0,2,2⟩,[0,-49152,1409024,-15843328,90374144,-303923200,840761344,-2627567616,6516375552,-8382431232,1491173376,9618538496,-9913171968]),(⟨0,2,3⟩,[0,65536,-1146880,5734400,3801088,-129761280,595787776,-1998258176,5271322624,-8843231232,8944517120,-5191008256]),(⟨0,2,4⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨0,3,0⟩,[0,98304,-3440640,49840128,-397803520,2006581248,-7243759616,21338062848,-53631909888,103119421440,-125320331264,70111887360,1565523968,-6359678976]),(⟨0,3,1⟩,[-32768,917504,-10567680,67633152,-283918336,898105344,-2413854720,6217793536,-14984216576,25105661952,-19065356288,-1470365696,5938200576]),(⟨0,3,2⟩,[0,16384,98304,-6373376,59113472,-235503616,562364416,-1526104064,4508745728,-8467431424,9629433856,-6269190144]),(⟨0,3,3⟩,[32768,-851968,8585216,-44564480,149356544,-455213056,1355022336,-2909798400,3602153472,-1727594496,-648216576]),(⟨0,3,4⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨0,4,0⟩,[0,-49152,1015808,-5554176,-23592960,440827904,-2570256384,9438789632,-26289504256,53252079616,-63575195648,28662054912,6038093824]),(⟨0,4,1⟩,[0,163840,-3473408,29392896,-135004160,387252224,-746455040,1015349248,-587988992,-4132929536,15632891904,-16022601728]),(⟨0,4,2⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨0,4,3⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨0,5,0⟩,[0,-49152,1835008,-25870336,182976512,-752713728,2199388160,-5556371456,10349969408,-8979595264,222035968,1150435328]),(⟨0,5,1⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨0,6,0⟩,[0,0,294912,-7077888,65929216,-330563584,1125842944,-3023306752,5476581376,-4276879360,-238780416]),(⟨0,6,1⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨1,0,0⟩,[0,-49152,1703936,-25739264,227180544,-1338736640,5788794880,-19917144064,57411043328,-137483632640,256094240768,-335889809408,266368876544,-83479363584,-21850226688,8455716864]),(⟨1,0,1⟩,[16384,-491520,6488064,-51904512,296009728,-1329233920,4931584000,-15398600704,40457977856,-85862416384,132861853696,-121835880448,24219697152,59420082176,-39460012032]),(⟨1,0,2⟩,[0,-16384,-32768,5783552,-66584576,354811904,-1154678784,3041820672,-8201568256,20554825728,-41258352640,64863944704,-73990275072,43366514688]),(⟨1,0,3⟩,[-32768,917504,-10665984,70025216,-312066048,1111359488,-3419373568,8671657984,-16154099712,17703108608,-3670130688,-12361105408,8773058560]),(⟨1,0,4⟩,[0,163840,-3473408,29687808,-143654912,483590144,-1241120768,2036334592,-157810688,-8679686144,20097466368,-15776940032]),(⟨1,0,5⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨1,0,6⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨1,1,0⟩,[16384,-491520,6684672,-57540608,365838336,-1840283648,7512915968,-25448153088,72480768000,-168141553664,291212361728,-326663274496,171439079424,34009808896,-63197675520]),(⟨1,1,1⟩,[0,-196608,4718592,-47284224,267976704,-982155264,2545680384,-5247270912,10082451456,-14603255808,-9670754304,107700584448,-210395136000,142893219840]),(⟨1,1,2⟩,[-16384,458752,-5308416,35127296,-159137792,517603328,-1027080192,434896896,3647946752,-11063066624,11204100096,8028160000,-18056134656]),(⟨1,1,3⟩,[0,229376,-4915200,42303488,-203685888,677314560,-1761738752,3052339200,-442761216,-12845219840,29273423872,-22082256896]),(⟨1,1,4⟩,[0,0,196608,-4718592,40108032,-127401984,-39714816,986185728,-1148977152,-1684537344,2784165888]),(⟨1,2,0⟩,[0,-16384,-229376,11321344,-133660672,829882368,-3417505792,10769498112,-26855538688,49181212672,-61549936640,58817626112,-59793047552,43414683648]),(⟨1,2,1⟩,[-16384,458752,-5308416,34832384,-150683648,424411136,-545783808,-598671360,3384885248,-6588661760,6018367488,8090779648,-16909713408]),(⟨1,2,2⟩,[0,98304,-3014656,37355520,-239861760,832110592,-1300234240,-675676160,6144393216,-8957886464,3355312128,1746927616]),(⟨1,2,3⟩,[-16384,425984,-4243456,19005440,-20873216,-154992640,661291008,-702939136,-1196769280,3325722624,-2060828672]),(⟨1,2,5⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,3,0⟩,[-32768,917504,-10862592,75104256,-363479040,1390673920,-4505436160,12917669888,-31253790720,52579663872,-46021394432,6977355776,11032182784]),(⟨1,3,1⟩,[0,327680,-7929856,79364096,-434896896,1413087232,-2567307264,1355677696,5271453696,-17256349696,28164161536,-20580990976]),(⟨1,3,2⟩,[-16384,327680,-1425408,-12058624,139558912,-499515392,573603840,788529152,-2925346816,3346595840,-1678688256]),(⟨1,3,3⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨1,3,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,4,0⟩,[0,163840,-3473408,29392896,-135004160,387252224,-746455040,1015349248,-587988992,-4132929536,15632891904,-16022601728]),(⟨1,4,1⟩,[0,-98304,3014656,-35782656,200540160,-471924736,-127401984,2477654016,-2877554688,-1663664128,3166306304]),(⟨1,4,2⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨1,4,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,5,0⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨1,5,1⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨1,5,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,6,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨2,0,0⟩,[0,49152,-1409024,16564224,-102989824,357203968,-600506368,-453017600,7369719808,-33448017920,95364874240,-164369285120,145625088000,-33641660416,-21887975424]),(⟨2,0,1⟩,[0,-65536,1376256,-10420224,28278784,72974336,-934543360,4314365952,-12692684800,25109987328,-35803955200,47769649152,-62645108736,44185387008]),(⟨2,0,2⟩,[0,-49152,1409024,-15843328,90374144,-303923200,840761344,-2627567616,6516375552,-8382431232,1491173376,9618538496,-9913171968]),(⟨2,0,3⟩,[0,65536,-1146880,5734400,3801088,-129761280,595787776,-1998258176,5271322624,-8843231232,8944517120,-5191008256]),(⟨2,0,4⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨2,1,0⟩,[0,-16384,-229376,11321344,-133660672,829882368,-3417505792,10769498112,-26855538688,49181212672,-61549936640,58817626112,-59793047552,43414683648]),(⟨2,1,1⟩,[-16384,458752,-5308416,34832384,-150683648,424411136,-545783808,-598671360,3384885248,-6588661760,6018367488,8090779648,-16909713408]),(⟨2,1,2⟩,[0,98304,-3014656,37355520,-239861760,832110592,-1300234240,-675676160,6144393216,-8957886464,3355312128,1746927616]),(⟨2,1,3⟩,[-16384,425984,-4243456,19005440,-20873216,-154992640,661291008,-702939136,-1196769280,3325722624,-2060828672]),(⟨2,1,5⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,2,0⟩,[0,-98304,2916352,-34242560,206209024,-728170496,1929445376,-5168234496,11333074944,-13006503936,2037547008,10557030400,-10081763328]),(⟨2,2,1⟩,[0,196608,-6029312,74711040,-479723520,1664221184,-2600468480,-1351352320,12288786432,-17915772928,6710624256,3493855232]),(⟨2,2,2⟩,[-98304,2555904,-25460736,120324096,-247922688,-86900736,1699676160,-3758358528,944799744,8680046592,-9744580608]),(⟨2,2,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,3,0⟩,[0,16384,393216,-13254656,122945536,-558989312,1678770176,-4540366848,10065018880,-13145128960,9397993472,-5154881536]),(⟨2,3,1⟩,[-16384,327680,-1425408,-12058624,139558912,-499515392,573603840,788529152,-2925346816,3346595840,-1678688256]),(⟨2,4,0⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨2,4,1⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨2,4,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,5,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,0,0⟩,[0,98304,-3440640,49840128,-397803520,2006581248,-7243759616,21338062848,-53631909888,103119421440,-125320331264,70111887360,1565523968,-6359678976]),(⟨3,0,1⟩,[-32768,917504,-10567680,67633152,-283918336,898105344,-2413854720,6217793536,-14984216576,25105661952,-19065356288,-1470365696,5938200576]),(⟨3,0,2⟩,[0,16384,98304,-6373376,59113472,-235503616,562364416,-1526104064,4508745728,-8467431424,9629433856,-6269190144]),(⟨3,0,3⟩,[32768,-851968,8585216,-44564480,149356544,-455213056,1355022336,-2909798400,3602153472,-1727594496,-648216576]),(⟨3,0,4⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨3,1,0⟩,[-32768,917504,-10862592,75104256,-363479040,1390673920,-4505436160,12917669888,-31253790720,52579663872,-46021394432,6977355776,11032182784]),(⟨3,1,1⟩,[0,327680,-7929856,79364096,-434896896,1413087232,-2567307264,1355677696,5271453696,-17256349696,28164161536,-20580990976]),(⟨3,1,2⟩,[-16384,327680,-1425408,-12058624,139558912,-499515392,573603840,788529152,-2925346816,3346595840,-1678688256]),(⟨3,1,3⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨3,1,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,2,0⟩,[0,16384,393216,-13254656,122945536,-558989312,1678770176,-4540366848,10065018880,-13145128960,9397993472,-5154881536]),(⟨3,2,1⟩,[-16384,327680,-1425408,-12058624,139558912,-499515392,573603840,788529152,-2925346816,3346595840,-1678688256]),(⟨3,3,0⟩,[32768,-851968,8880128,-51642368,215285760,-785776640,2480865280,-5933105152,9078734848,-6004473856,-886996992]),(⟨3,3,1⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨3,4,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨3,4,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,0,0⟩,[0,-49152,1015808,-5554176,-23592960,440827904,-2570256384,9438789632,-26289504256,53252079616,-63575195648,28662054912,6038093824]),(⟨4,0,1⟩,[0,163840,-3473408,29392896,-135004160,387252224,-746455040,1015349248,-587988992,-4132929536,15632891904,-16022601728]),(⟨4,0,2⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨4,0,3⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨4,1,0⟩,[0,163840,-3473408,29392896,-135004160,387252224,-746455040,1015349248,-587988992,-4132929536,15632891904,-16022601728]),(⟨4,1,1⟩,[0,-98304,3014656,-35782656,200540160,-471924736,-127401984,2477654016,-2877554688,-1663664128,3166306304]),(⟨4,1,2⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨4,1,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,2,0⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨4,2,1⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨4,2,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,3,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨4,3,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,0,0⟩,[0,-49152,1835008,-25870336,182976512,-752713728,2199388160,-5556371456,10349969408,-8979595264,222035968,1150435328]),(⟨5,0,1⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨5,1,0⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨5,1,1⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨5,1,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,2,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,0,0⟩,[0,0,294912,-7077888,65929216,-330563584,1125842944,-3023306752,5476581376,-4276879360,-238780416]),(⟨6,0,1⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨6,1,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,-49152,1818624,-29605888,282755072,-1798045696,8304967680,-30081548288,90564788224,-228704829440,460704006144,-678297321472,646194692096,-308949581824,-6207356928,57358123008,-11758731264]),(⟨0,0,1⟩,[0,-49152,1900544,-31834112,309723136,-1997406208,9369812992,-34659106816,106691559424,-272028844032,539124367360,-753170235392,640310968320,-221608312832,-62234165248,41465905152]),(⟨0,0,2⟩,[0,98304,-3129344,41943040,-311394304,1431470080,-4422549504,10019405824,-16716857344,11258986496,39016251392,-128550961152,144153149440,-40066252800,-20816216064]),(⟨0,0,3⟩,[0,98304,-3735552,57999360,-494141440,2664005632,-10265427968,31676563456,-80759488512,154570096640,-186486161408,102859079680,6067060736,-13443497984]),(⟨0,0,4⟩,[0,-49152,1015808,-5554176,-23592960,440827904,-2570256384,9438789632,-26289504256,53252079616,-63575195648,28662054912,6038093824]),(⟨0,0,5⟩,[0,-49152,1835008,-25870336,182976512,-752713728,2199388160,-5556371456,10349969408,-8979595264,222035968,1150435328]),(⟨0,0,6⟩,[0,0,294912,-7077888,65929216,-330563584,1125842944,-3023306752,5476581376,-4276879360,-238780416]),(⟨0,1,0⟩,[0,-49152,1900544,-31834112,309723136,-1997406208,9369812992,-34659106816,106691559424,-272028844032,539124367360,-753170235392,640310968320,-221608312832,-62234165248,41465905152]),(⟨0,1,1⟩,[16384,-491520,6684672,-57245696,356106240,-1707769856,6556123136,-21586575360,64623722496,-166308773888,318169481216,-381728948224,208320479232,36729290752,-70485639168]),(⟨0,1,2⟩,[0,-16384,-229376,11321344,-133660672,829882368,-3417505792,10769498112,-26855538688,49181212672,-61549936640,58817626112,-59793047552,43414683648]),(⟨0,1,3⟩,[-32768,917504,-10862592,75104256,-363479040,1390673920,-4505436160,12917669888,-31253790720,52579663872,-46021394432,6977355776,11032182784]),(⟨0,1,4⟩,[0,163840,-3473408,29392896,-135004160,387252224,-746455040,1015349248,-587988992,-4132929536,15632891904,-16022601728]),(⟨0,1,5⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨0,1,6⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨0,2,0⟩,[0,98304,-3129344,41943040,-311394304,1431470080,-4422549504,10019405824,-16716857344,11258986496,39016251392,-128550961152,144153149440,-40066252800,-20816216064]),(⟨0,2,1⟩,[0,-16384,-229376,11321344,-133660672,829882368,-3417505792,10769498112,-26855538688,49181212672,-61549936640,58817626112,-59793047552,43414683648]),(⟨0,2,2⟩,[0,-98304,2916352,-34242560,206209024,-728170496,1929445376,-5168234496,11333074944,-13006503936,2037547008,10557030400,-10081763328]),(⟨0,2,3⟩,[0,16384,393216,-13254656,122945536,-558989312,1678770176,-4540366848,10065018880,-13145128960,9397993472,-5154881536]),(⟨0,2,4⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨0,3,0⟩,[0,98304,-3735552,57999360,-494141440,2664005632,-10265427968,31676563456,-80759488512,154570096640,-186486161408,102859079680,6067060736,-13443497984]),(⟨0,3,1⟩,[-32768,917504,-10862592,75104256,-363479040,1390673920,-4505436160,12917669888,-31253790720,52579663872,-46021394432,6977355776,11032182784]),(⟨0,3,2⟩,[0,16384,393216,-13254656,122945536,-558989312,1678770176,-4540366848,10065018880,-13145128960,9397993472,-5154881536]),(⟨0,3,3⟩,[32768,-851968,8880128,-51642368,215285760,-785776640,2480865280,-5933105152,9078734848,-6004473856,-886996992]),(⟨0,3,4⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨0,4,0⟩,[0,-49152,1015808,-5554176,-23592960,440827904,-2570256384,9438789632,-26289504256,53252079616,-63575195648,28662054912,6038093824]),(⟨0,4,1⟩,[0,163840,-3473408,29392896,-135004160,387252224,-746455040,1015349248,-587988992,-4132929536,15632891904,-16022601728]),(⟨0,4,2⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨0,4,3⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨0,5,0⟩,[0,-49152,1835008,-25870336,182976512,-752713728,2199388160,-5556371456,10349969408,-8979595264,222035968,1150435328]),(⟨0,5,1⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨0,6,0⟩,[0,0,294912,-7077888,65929216,-330563584,1125842944,-3023306752,5476581376,-4276879360,-238780416]),(⟨0,6,1⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨1,0,0⟩,[0,-49152,1900544,-31834112,309723136,-1997406208,9369812992,-34659106816,106691559424,-272028844032,539124367360,-753170235392,640310968320,-221608312832,-62234165248,41465905152]),(⟨1,0,1⟩,[16384,-491520,6684672,-57245696,356106240,-1707769856,6556123136,-21586575360,64623722496,-166308773888,318169481216,-381728948224,208320479232,36729290752,-70485639168]),(⟨1,0,2⟩,[0,-16384,-229376,11321344,-133660672,829882368,-3417505792,10769498112,-26855538688,49181212672,-61549936640,58817626112,-59793047552,43414683648]),(⟨1,0,3⟩,[-32768,917504,-10862592,75104256,-363479040,1390673920,-4505436160,12917669888,-31253790720,52579663872,-46021394432,6977355776,11032182784]),(⟨1,0,4⟩,[0,163840,-3473408,29392896,-135004160,387252224,-746455040,1015349248,-587988992,-4132929536,15632891904,-16022601728]),(⟨1,0,5⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨1,0,6⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨1,1,0⟩,[16384,-491520,6684672,-57245696,356106240,-1707769856,6556123136,-21586575360,64623722496,-166308773888,318169481216,-381728948224,208320479232,36729290752,-70485639168]),(⟨1,1,1⟩,[0,-196608,4718592,-46989312,258932736,-870088704,1826095104,-2750939136,6181748736,-16630284288,8762425344,80826925056,-200329199616,148134002688]),(⟨1,1,2⟩,[-16384,557056,-8552448,79003648,-469614592,1711603712,-3164798976,12255232,12370591744,-24943886336,18312167424,8997273600,-19339034624]),(⟨1,1,3⟩,[0,327680,-7929856,79364096,-434896896,1413087232,-2567307264,1355677696,5271453696,-17256349696,28164161536,-20580990976]),(⟨1,1,4⟩,[0,-98304,3014656,-35782656,200540160,-471924736,-127401984,2477654016,-2877554688,-1663664128,3166306304]),(⟨1,1,5⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨1,2,0⟩,[0,-16384,-229376,11321344,-133660672,829882368,-3417505792,10769498112,-26855538688,49181212672,-61549936640,58817626112,-59793047552,43414683648]),(⟨1,2,1⟩,[-16384,557056,-8552448,79003648,-469614592,1711603712,-3164798976,12255232,12370591744,-24943886336,18312167424,8997273600,-19339034624]),(⟨1,2,2⟩,[0,196608,-6029312,74711040,-479723520,1664221184,-2600468480,-1351352320,12288786432,-17915772928,6710624256,3493855232]),(⟨1,2,3⟩,[-16384,327680,-1425408,-12058624,139558912,-499515392,573603840,788529152,-2925346816,3346595840,-1678688256]),(⟨1,2,4⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨1,2,5⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,3,0⟩,[-32768,917504,-10862592,75104256,-363479040,1390673920,-4505436160,12917669888,-31253790720,52579663872,-46021394432,6977355776,11032182784]),(⟨1,3,1⟩,[0,327680,-7929856,79364096,-434896896,1413087232,-2567307264,1355677696,5271453696,-17256349696,28164161536,-20580990976]),(⟨1,3,2⟩,[-16384,327680,-1425408,-12058624,139558912,-499515392,573603840,788529152,-2925346816,3346595840,-1678688256]),(⟨1,3,3⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨1,3,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,4,0⟩,[0,163840,-3473408,29392896,-135004160,387252224,-746455040,1015349248,-587988992,-4132929536,15632891904,-16022601728]),(⟨1,4,1⟩,[0,-98304,3014656,-35782656,200540160,-471924736,-127401984,2477654016,-2877554688,-1663664128,3166306304]),(⟨1,4,2⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨1,4,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,5,0⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨1,5,1⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨1,5,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨1,6,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨2,0,0⟩,[0,98304,-3129344,41943040,-311394304,1431470080,-4422549504,10019405824,-16716857344,11258986496,39016251392,-128550961152,144153149440,-40066252800,-20816216064]),(⟨2,0,1⟩,[0,-16384,-229376,11321344,-133660672,829882368,-3417505792,10769498112,-26855538688,49181212672,-61549936640,58817626112,-59793047552,43414683648]),(⟨2,0,2⟩,[0,-98304,2916352,-34242560,206209024,-728170496,1929445376,-5168234496,11333074944,-13006503936,2037547008,10557030400,-10081763328]),(⟨2,0,3⟩,[0,16384,393216,-13254656,122945536,-558989312,1678770176,-4540366848,10065018880,-13145128960,9397993472,-5154881536]),(⟨2,0,4⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨2,1,0⟩,[0,-16384,-229376,11321344,-133660672,829882368,-3417505792,10769498112,-26855538688,49181212672,-61549936640,58817626112,-59793047552,43414683648]),(⟨2,1,1⟩,[-16384,557056,-8552448,79003648,-469614592,1711603712,-3164798976,12255232,12370591744,-24943886336,18312167424,8997273600,-19339034624]),(⟨2,1,2⟩,[0,196608,-6029312,74711040,-479723520,1664221184,-2600468480,-1351352320,12288786432,-17915772928,6710624256,3493855232]),(⟨2,1,3⟩,[-16384,327680,-1425408,-12058624,139558912,-499515392,573603840,788529152,-2925346816,3346595840,-1678688256]),(⟨2,1,4⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨2,1,5⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,2,0⟩,[0,-98304,2916352,-34242560,206209024,-728170496,1929445376,-5168234496,11333074944,-13006503936,2037547008,10557030400,-10081763328]),(⟨2,2,1⟩,[0,196608,-6029312,74711040,-479723520,1664221184,-2600468480,-1351352320,12288786432,-17915772928,6710624256,3493855232]),(⟨2,2,2⟩,[-98304,2555904,-25460736,120324096,-247922688,-86900736,1699676160,-3758358528,944799744,8680046592,-9744580608]),(⟨2,2,4⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,3,0⟩,[0,16384,393216,-13254656,122945536,-558989312,1678770176,-4540366848,10065018880,-13145128960,9397993472,-5154881536]),(⟨2,3,1⟩,[-16384,327680,-1425408,-12058624,139558912,-499515392,573603840,788529152,-2925346816,3346595840,-1678688256]),(⟨2,4,0⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨2,4,1⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨2,4,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,5,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,0,0⟩,[0,98304,-3735552,57999360,-494141440,2664005632,-10265427968,31676563456,-80759488512,154570096640,-186486161408,102859079680,6067060736,-13443497984]),(⟨3,0,1⟩,[-32768,917504,-10862592,75104256,-363479040,1390673920,-4505436160,12917669888,-31253790720,52579663872,-46021394432,6977355776,11032182784]),(⟨3,0,2⟩,[0,16384,393216,-13254656,122945536,-558989312,1678770176,-4540366848,10065018880,-13145128960,9397993472,-5154881536]),(⟨3,0,3⟩,[32768,-851968,8880128,-51642368,215285760,-785776640,2480865280,-5933105152,9078734848,-6004473856,-886996992]),(⟨3,0,4⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨3,1,0⟩,[-32768,917504,-10862592,75104256,-363479040,1390673920,-4505436160,12917669888,-31253790720,52579663872,-46021394432,6977355776,11032182784]),(⟨3,1,1⟩,[0,327680,-7929856,79364096,-434896896,1413087232,-2567307264,1355677696,5271453696,-17256349696,28164161536,-20580990976]),(⟨3,1,2⟩,[-16384,327680,-1425408,-12058624,139558912,-499515392,573603840,788529152,-2925346816,3346595840,-1678688256]),(⟨3,1,3⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨3,1,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,2,0⟩,[0,16384,393216,-13254656,122945536,-558989312,1678770176,-4540366848,10065018880,-13145128960,9397993472,-5154881536]),(⟨3,2,1⟩,[-16384,327680,-1425408,-12058624,139558912,-499515392,573603840,788529152,-2925346816,3346595840,-1678688256]),(⟨3,3,0⟩,[32768,-851968,8880128,-51642368,215285760,-785776640,2480865280,-5933105152,9078734848,-6004473856,-886996992]),(⟨3,3,1⟩,[0,-196608,3670016,-25427968,90701824,-220332032,365428736,232521728,-2347237376,2706178048]),(⟨3,4,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨3,4,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,0,0⟩,[0,-49152,1015808,-5554176,-23592960,440827904,-2570256384,9438789632,-26289504256,53252079616,-63575195648,28662054912,6038093824]),(⟨4,0,1⟩,[0,163840,-3473408,29392896,-135004160,387252224,-746455040,1015349248,-587988992,-4132929536,15632891904,-16022601728]),(⟨4,0,2⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨4,0,3⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨4,1,0⟩,[0,163840,-3473408,29392896,-135004160,387252224,-746455040,1015349248,-587988992,-4132929536,15632891904,-16022601728]),(⟨4,1,1⟩,[0,-98304,3014656,-35782656,200540160,-471924736,-127401984,2477654016,-2877554688,-1663664128,3166306304]),(⟨4,1,2⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨4,1,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,2,0⟩,[0,0,98304,-2359296,20054016,-63700992,-19857408,493092864,-574488576,-842268672,1392082944]),(⟨4,2,1⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨4,2,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨4,3,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨4,3,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,0,0⟩,[0,-49152,1835008,-25870336,182976512,-752713728,2199388160,-5556371456,10349969408,-8979595264,222035968,1150435328]),(⟨5,0,1⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨5,1,0⟩,[16384,-425984,4145152,-18743296,41713664,-62324736,114589696,56754176,-937213952,1274642432,-204718080]),(⟨5,1,1⟩,[0,-98304,2883584,-32112640,164888576,-340328448,-143392768,1515585536,-1488191488,-81887232]),(⟨5,1,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,2,1⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,0,0⟩,[0,0,294912,-7077888,65929216,-330563584,1125842944,-3023306752,5476581376,-4276879360,-238780416]),(⟨6,0,1⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024]),(⟨6,1,0⟩,[0,-98304,1835008,-12713984,45350912,-110166016,182714368,116260864,-1173618688,1353089024])]


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
    (Poly.add (Poly.scale (K.ofRat r572) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 4 11).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r571*r571 : ℚ)=r572 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 4 11 r571 r571 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 4=11 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 4 11).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C102

#print axioms Coulomb8.Columns.C102.sound
