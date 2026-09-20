import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C110

def r0 : ℚ := { num := 2048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := -51200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := 389120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 4096, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -44244992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 394752000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -2067619840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 7311826944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -18263177216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 32502487040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -40513261568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 33675972608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := -986132480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := 3951722496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := -48103424, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -10240, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 892928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -3772416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -21032960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 364359680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -2306793472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 8877490176, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -22969219072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 40955521024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -49561796608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 38299963392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := -16146915328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 313229312, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -4096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 77824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -163840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -6991872, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 79523840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -407248896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 161464320, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := -1408491520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -1116729344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 7363555328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := -12591808512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := 1503850496, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -515837952, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 131072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := -1212416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -593920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 83247104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -658153472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 2685526016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -6682886144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 10455994368, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := -9852837888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := 4653096960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := -55529472, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -10240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := -446464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 5029888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -1527808, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -14364672, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 755834880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -2355429376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 582768640, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -3945351168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 244977664, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -59392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 327680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := 3391488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := -380928, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := 204386304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := -465027072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := 565903360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := -42182656, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -5060608, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -16384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := 212992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 442368, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -16760832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 92487680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -33800192, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 322322432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -29147136, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := -45056, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := 1105920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := -9928704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := 31301632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 16392192, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -1512603648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 408797184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -2696839168, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 33102581760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -37371666432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 25063473152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := -1097654272, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -2048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := 63488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := -483328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := -2076672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := 2920448, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := -309424128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := 991748096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := -1713848320, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 1128347648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := 1244575744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -3014410240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 273010688, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := 49152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := -1007616, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := 5898240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := 7929856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := -238714880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := 1200308224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := -3143106560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 285736960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -4280827904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 242999296, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 106496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -176128, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 1093632, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -21491712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := -1347584, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := 228036608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := -89354240, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := 799752192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := -3739648, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := 24576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := -475136, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := 3350528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := -10354688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := 9216000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 3555328, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := -68952064, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := 425984, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := 4096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := -94208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := 741376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := -2109440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -118784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 9023488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -1175552, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := -28672, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := -32768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := 491520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := -2162688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := 1769472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := 7438336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -98304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := -77824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := 188416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 5242880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := -49668096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := 193732608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := -407977984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := 503087104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := -374845440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := 13602816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := -26402816, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := 8192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := -180224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := 1368064, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -3833856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 253952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := 868352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 425984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 884736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -33521664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 184975360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -67600384, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 644644864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -58294272, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := -65536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 983040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := -4325376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 3538944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := 14876672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -196608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := -102400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := 1056768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -4161536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := -20996096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 49799168, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -286146560, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := 949895168, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := -13995356160, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := 18783989760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := -15065145344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := 47759360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := -12288, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := 507904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := 131072, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := -25927680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := 169435136, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -689881088, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 108560384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -3128619008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 3189862400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := -13205504, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := -327680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := -3309568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := 44523520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := -225943552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := 631799808, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := -1050017792, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := 1016410112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -3895296, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := -1196032, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := 1572864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 30810112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -188612608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := 493797376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := -668205056, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := 3280896, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := 16384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := -360448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := 2736128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := -7667712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 1736704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := 786432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -7012352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 4063232, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := -48103424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := -1572864, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := 181338112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := -18219008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 561152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := -741376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -3952640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 9277440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := 6533120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := -167936, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -8192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 180224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := -1368064, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := 3833856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := -253952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := -868352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := 1024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := -25600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := 194560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 2048, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -22122496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := 197376000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := -1033809920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := 3655913472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := -9131588608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := 16251243520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := -20256630784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := 16837986304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := -493066240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := 1975861248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := -24051712, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := -5120, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := 446464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := -1886208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -10516480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := 182179840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := -1153396736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 4438745088, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -11484609536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := 20477760512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -24780898304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := 19149981696, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := -8073457664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 156614656, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := 38912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := -81920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := -3495936, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := 39761920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := -203624448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := 80732160, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := -704245760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := -558364672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := 3681777664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := -6295904256, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := 751925248, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -257918976, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 65536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := -606208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := -296960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := 41623552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := -329076736, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := 1342763008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := -3341443072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := 5227997184, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := -4926418944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := 2326548480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -27764736, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := -5120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := -223232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := 2514944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := -763904, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -7182336, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := 377917440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -1177714688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 291384320, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -1972675584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 122488832, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -29696, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := 163840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := 1695744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -190464, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := 102193152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := -232513536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := 282951680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := -21091328, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -2530304, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := 221184, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := -8380416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := 46243840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := -16900096, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := 161161216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := -14573568, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -22528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 552960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -4964352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 15650816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := 8196096, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := -756301824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := 204398592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := -1348419584, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := 16551290880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := -18685833216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := 12531736576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := -548827136, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := -1024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := 31744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := -241664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -1038336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 1460224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -154712064, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 495874048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := -856924160, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := 564173824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := 622287872, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := -1507205120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := 136505344, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := -503808, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := 2949120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 3964928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -119357440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 600154112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := -1571553280, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := 142868480, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := -2140413952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := 121499648, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := 53248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := -88064, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := 546816, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := -10745856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := -673792, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := 114018304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := -44677120, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := 399876096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := -1869824, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := 12288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := -237568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := 1675264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := -5177344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := 4608000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := 1777664, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -34476032, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := 212992, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := -47104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := 370688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := -1054720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := 4511744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := -587776, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := -14336, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := 245760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := -1081344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := 3719168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := -49152, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := -38912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := 94208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := 2621440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := -24834048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := 96866304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := -203988992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := 251543552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := -187422720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := 6801408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := -13201408, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := -90112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := 684032, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := -1916928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := 126976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := 434176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := 528384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := -2080768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := -10498048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := 24899584, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := -143073280, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := 474947584, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := -6997678080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := 9391994880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := -7532572672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 23879680, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := -6144, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := 65536, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := -12963840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := 84717568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := -344940544, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := 54280192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := -1564309504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := 1594931200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := -6602752, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := -1654784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := 22261760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := -112971776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := 315899904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := -525008896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := 508205056, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := -1947648, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := -598016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := 15405056, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := -94306304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := 246898688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := -334102528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := 1640448, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := 393216, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := -3506176, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := 2031616, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := -24051712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := -786432, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := 90669056, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := -9109504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := 280576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := -370688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := -1976320, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := 4638720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := 3266560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := -83968, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := 90112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := -684032, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := 1916928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := -126976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := -434176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := 1, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := 1, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14],[r0,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27],[r28,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40],[r28,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51],[r0,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61],[r0,r62,r63,r64,r65,r66,r67,r68,r69,r70],[0,r71,r72,r73,r74,r75,r76,r77,r78],[],[],[],[],[],[],[0,r79,r80,r81,r82,r83,r84,r85,r86,r87,r88,r89,r90],[r91,r92,r93,r94,r95,r96,r97,r98,r99,r100,r101,r102],[0,r103,r104,r105,r106,r107,r108,r109,r110,r111,r112],[r28,r113,r114,r115,r116,r117,r118,r119,r120,r121],[0,r122,r123,r124,r125,r126,r127,r128,r129],[r130,r131,r132,r133,r134,r135,r136,r137],[0,r138,r139,r140,r141,r142,r143],[],[],[],[],[r130,r144,r145,r146,r147,r148,r149,r150,r151,r152,r153],[r0,r62,r63,r64,r65,r66,r67,r68,r69,r70],[0,r122,r123,r124,r125,r126,r127,r128,r129],[0,r154,r155,r156,r157,r158,r159,-8192],[],[],[],[],[],[0,r138,r160,r161,r162,r163,r164,r165,r166],[r130,r131,r132,r133,r134,r135,r136,r137],[],[],[],[],[],[0,r167,r168,r169,r170,r171,r172],[],[],[],[],[],[],[],[],[r130,r173,r174,r175,r176,r177,r178,r179,r180,r181,r182,r183],[r130,r184,r185,r186,r187,r188,r189,r190,r191,r192,r193],[r28,r29,r194,r195,r196,r197,r198,r199,r200,r201],[r28,r41,r202,r203,r204,r205,r206,r207,r208],[0,r209,r210,r211,r212,r185,r213,-16384],[],[],[],[],[],[0,r138,r214,r215,r216,r217,r218,r219,r220,98304],[],[r130,r184,r221,r222,r223,r224,r225,r226],[r227,r228,r229,r230,r231,r232,8192],[],[],[],[],[],[0,r138,r139,r140,r141,r142,r143],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[r233,r234,r235,r236,r237,r238,r239,r240,r241,r242,r243,r244,r245,r246,r247]),(⟨0,0,1⟩,[r233,r248,r249,r250,r251,r252,r253,r254,r255,r256,r257,r258,r259,r260]),(⟨0,0,2⟩,[r91,r261,r262,r263,r264,r265,r266,r267,r268,r269,r270,r271,r272]),(⟨0,0,3⟩,[r91,r273,r274,r275,r276,r277,r278,r279,r280,r281,r282,r283]),(⟨0,0,4⟩,[r233,r284,r285,r286,r287,r288,r289,r290,r291,r292,r293]),(⟨0,0,5⟩,[r233,r294,r295,r296,r297,r298,r299,r300,r301,r302]),(⟨0,0,6⟩,[0,r227,r113,r303,r304,r305,r306,r307,r308]),(⟨0,1,0⟩,[r233,r248,r249,r250,r251,r252,r253,r254,r255,r256,r257,r258,r259,r260]),(⟨0,1,1⟩,[0,r309,r310,r311,r312,r313,r314,r315,r316,r317,r318,r319,r320]),(⟨0,1,2⟩,[r321,r322,r323,r324,r325,r326,r327,r328,r329,r330,r331,r332]),(⟨0,1,3⟩,[0,r122,r333,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨0,1,4⟩,[r91,r342,r343,r344,r345,r346,r347,r348,r349,r350]),(⟨0,1,5⟩,[0,r351,r352,r353,r354,r355,r356,r357,r358]),(⟨0,1,6⟩,[r0,r359,r360,r361,r62,r362,r363,r364]),(⟨0,1,7⟩,[0,r71,r365,r366,r161,r367,r368]),(⟨0,2,0⟩,[r91,r261,r262,r263,r264,r265,r266,r267,r268,r269,r270,r271,r272]),(⟨0,2,1⟩,[r321,r322,r323,r324,r325,r326,r327,r328,r329,r330,r331,r332]),(⟨0,2,2⟩,[r0,r369,r370,r371,r372,r373,r374,r375,r376,r377,r378]),(⟨0,2,3⟩,[r233,r294,r295,r296,r297,r298,r299,r300,r301,r302]),(⟨0,2,4⟩,[0,r351,r352,r353,r354,r355,r356,r357,r358]),(⟨0,2,5⟩,[0,r130,r379,r380,r381,r382,r383,-4096]),(⟨0,3,0⟩,[r91,r273,r274,r275,r276,r277,r278,r279,r280,r281,r282,r283]),(⟨0,3,1⟩,[0,r122,r333,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨0,3,2⟩,[r233,r294,r295,r296,r297,r298,r299,r300,r301,r302]),(⟨0,3,3⟩,[0,r71,r72,r73,r74,r75,r76,r77,r78]),(⟨0,3,4⟩,[r0,r359,r360,r361,r62,r362,r363,r364]),(⟨0,4,0⟩,[r233,r284,r285,r286,r287,r288,r289,r290,r291,r292,r293]),(⟨0,4,1⟩,[r91,r342,r343,r344,r345,r346,r347,r348,r349,r350]),(⟨0,4,2⟩,[0,r351,r352,r353,r354,r355,r356,r357,r358]),(⟨0,4,3⟩,[r0,r359,r360,r361,r62,r362,r363,r364]),(⟨0,4,4⟩,[0,r138,r139,r140,r141,r142,r143]),(⟨0,5,0⟩,[r233,r294,r295,r296,r297,r298,r299,r300,r301,r302]),(⟨0,5,1⟩,[0,r351,r352,r353,r354,r355,r356,r357,r358]),(⟨0,5,2⟩,[0,r130,r379,r380,r381,r382,r383,-4096]),(⟨0,6,0⟩,[0,r227,r113,r303,r304,r305,r306,r307,r308]),(⟨0,6,1⟩,[r0,r359,r360,r361,r62,r362,r363,r364]),(⟨0,7,1⟩,[0,r71,r365,r366,r161,r367,r368]),(⟨1,0,0⟩,[r233,r248,r249,r250,r251,r252,r253,r254,r255,r256,r257,r258,r259,r260]),(⟨1,0,1⟩,[0,r309,r310,r311,r312,r313,r314,r315,r316,r317,r318,r319,r320]),(⟨1,0,2⟩,[r321,r322,r323,r324,r325,r326,r327,r328,r329,r330,r331,r332]),(⟨1,0,3⟩,[0,r122,r333,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨1,0,4⟩,[r91,r342,r343,r344,r345,r346,r347,r348,r349,r350]),(⟨1,0,5⟩,[0,r351,r352,r353,r354,r355,r356,r357,r358]),(⟨1,0,6⟩,[r0,r359,r360,r361,r62,r362,r363,r364]),(⟨1,0,7⟩,[0,r71,r365,r366,r161,r367,r368]),(⟨1,1,0⟩,[0,r309,r310,r311,r312,r313,r314,r315,r316,r317,r318,r319,r320]),(⟨1,1,1⟩,[r0,r1,r384,r385,r386,r387,r388,r389,r390,r391,r392,r393]),(⟨1,1,2⟩,[r0,r394,r158,r395,r396,r397,r398,r399,r400,r401,r402]),(⟨1,1,3⟩,[r91,r261,r30,r403,r404,r405,r406,r407,r408,r409]),(⟨1,1,4⟩,[r91,r273,r410,r214,r411,r412,r413,r414,r415]),(⟨1,1,5⟩,[0,r154,r155,r156,r157,r158,r159,-8192]),(⟨1,2,0⟩,[r321,r322,r323,r324,r325,r326,r327,r328,r329,r330,r331,r332]),(⟨1,2,1⟩,[r0,r394,r158,r395,r396,r397,r398,r399,r400,r401,r402]),(⟨1,2,2⟩,[0,r71,r416,r417,r418,r419,r420,r421,r422,49152]),(⟨1,2,4⟩,[r0,r394,r423,r424,r425,r426,r427,r428]),(⟨1,2,5⟩,[r28,r429,r430,r431,r432,r433,4096]),(⟨1,3,0⟩,[0,r122,r333,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨1,3,1⟩,[r91,r261,r30,r403,r404,r405,r406,r407,r408,r409]),(⟨1,3,4⟩,[0,r71,r365,r366,r161,r367,r368]),(⟨1,4,0⟩,[r91,r342,r343,r344,r345,r346,r347,r348,r349,r350]),(⟨1,4,1⟩,[r91,r273,r410,r214,r411,r412,r413,r414,r415]),(⟨1,4,2⟩,[r0,r394,r423,r424,r425,r426,r427,r428]),(⟨1,4,3⟩,[0,r71,r365,r366,r161,r367,r368]),(⟨1,5,0⟩,[0,r351,r352,r353,r354,r355,r356,r357,r358]),(⟨1,5,1⟩,[0,r154,r155,r156,r157,r158,r159,-8192]),(⟨1,5,2⟩,[r28,r429,r430,r431,r432,r433,4096]),(⟨1,6,0⟩,[r0,r359,r360,r361,r62,r362,r363,r364]),(⟨1,7,0⟩,[0,r71,r365,r366,r161,r367,r368]),(⟨2,0,0⟩,[r91,r261,r262,r263,r264,r265,r266,r267,r268,r269,r270,r271,r272]),(⟨2,0,1⟩,[r321,r322,r323,r324,r325,r326,r327,r328,r329,r330,r331,r332]),(⟨2,0,2⟩,[r0,r369,r370,r371,r372,r373,r374,r375,r376,r377,r378]),(⟨2,0,3⟩,[r233,r294,r295,r296,r297,r298,r299,r300,r301,r302]),(⟨2,0,4⟩,[0,r351,r352,r353,r354,r355,r356,r357,r358]),(⟨2,0,5⟩,[0,r130,r379,r380,r381,r382,r383,-4096]),(⟨2,1,0⟩,[r321,r322,r323,r324,r325,r326,r327,r328,r329,r330,r331,r332]),(⟨2,1,1⟩,[r0,r394,r158,r395,r396,r397,r398,r399,r400,r401,r402]),(⟨2,1,2⟩,[0,r71,r416,r417,r418,r419,r420,r421,r422,49152]),(⟨2,1,4⟩,[r0,r394,r423,r424,r425,r426,r427,r428]),(⟨2,1,5⟩,[r28,r429,r430,r431,r432,r433,4096]),(⟨2,2,0⟩,[r0,r369,r370,r371,r372,r373,r374,r375,r376,r377,r378]),(⟨2,2,1⟩,[0,r71,r416,r417,r418,r419,r420,r421,r422,49152]),(⟨2,3,0⟩,[r233,r294,r295,r296,r297,r298,r299,r300,r301,r302]),(⟨2,4,0⟩,[0,r351,r352,r353,r354,r355,r356,r357,r358]),(⟨2,4,1⟩,[r0,r394,r423,r424,r425,r426,r427,r428]),(⟨2,5,0⟩,[0,r130,r379,r380,r381,r382,r383,-4096]),(⟨2,5,1⟩,[r28,r429,r430,r431,r432,r433,4096]),(⟨3,0,0⟩,[r91,r273,r274,r275,r276,r277,r278,r279,r280,r281,r282,r283]),(⟨3,0,1⟩,[0,r122,r333,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨3,0,2⟩,[r233,r294,r295,r296,r297,r298,r299,r300,r301,r302]),(⟨3,0,3⟩,[0,r71,r72,r73,r74,r75,r76,r77,r78]),(⟨3,0,4⟩,[r0,r359,r360,r361,r62,r362,r363,r364]),(⟨3,1,0⟩,[0,r122,r333,r334,r335,r336,r337,r338,r339,r340,r341]),(⟨3,1,1⟩,[r91,r261,r30,r403,r404,r405,r406,r407,r408,r409]),(⟨3,1,4⟩,[0,r71,r365,r366,r161,r367,r368]),(⟨3,2,0⟩,[r233,r294,r295,r296,r297,r298,r299,r300,r301,r302]),(⟨3,3,0⟩,[0,r71,r72,r73,r74,r75,r76,r77,r78]),(⟨3,4,0⟩,[r0,r359,r360,r361,r62,r362,r363,r364]),(⟨3,4,1⟩,[0,r71,r365,r366,r161,r367,r368]),(⟨4,0,0⟩,[r233,r284,r285,r286,r287,r288,r289,r290,r291,r292,r293]),(⟨4,0,1⟩,[r91,r342,r343,r344,r345,r346,r347,r348,r349,r350]),(⟨4,0,2⟩,[0,r351,r352,r353,r354,r355,r356,r357,r358]),(⟨4,0,3⟩,[r0,r359,r360,r361,r62,r362,r363,r364]),(⟨4,0,4⟩,[0,r138,r139,r140,r141,r142,r143]),(⟨4,1,0⟩,[r91,r342,r343,r344,r345,r346,r347,r348,r349,r350]),(⟨4,1,1⟩,[r91,r273,r410,r214,r411,r412,r413,r414,r415]),(⟨4,1,2⟩,[r0,r394,r423,r424,r425,r426,r427,r428]),(⟨4,1,3⟩,[0,r71,r365,r366,r161,r367,r368]),(⟨4,2,0⟩,[0,r351,r352,r353,r354,r355,r356,r357,r358]),(⟨4,2,1⟩,[r0,r394,r423,r424,r425,r426,r427,r428]),(⟨4,3,0⟩,[r0,r359,r360,r361,r62,r362,r363,r364]),(⟨4,3,1⟩,[0,r71,r365,r366,r161,r367,r368]),(⟨4,4,0⟩,[0,r138,r139,r140,r141,r142,r143]),(⟨5,0,0⟩,[r233,r294,r295,r296,r297,r298,r299,r300,r301,r302]),(⟨5,0,1⟩,[0,r351,r352,r353,r354,r355,r356,r357,r358]),(⟨5,0,2⟩,[0,r130,r379,r380,r381,r382,r383,-4096]),(⟨5,1,0⟩,[0,r351,r352,r353,r354,r355,r356,r357,r358]),(⟨5,1,1⟩,[0,r154,r155,r156,r157,r158,r159,-8192]),(⟨5,1,2⟩,[r28,r429,r430,r431,r432,r433,4096]),(⟨5,2,0⟩,[0,r130,r379,r380,r381,r382,r383,-4096]),(⟨5,2,1⟩,[r28,r429,r430,r431,r432,r433,4096]),(⟨6,0,0⟩,[0,r227,r113,r303,r304,r305,r306,r307,r308]),(⟨6,0,1⟩,[r0,r359,r360,r361,r62,r362,r363,r364]),(⟨6,1,0⟩,[r0,r359,r360,r361,r62,r362,r363,r364]),(⟨7,0,1⟩,[0,r71,r365,r366,r161,r367,r368]),(⟨7,1,0⟩,[0,r71,r365,r366,r161,r367,r368])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[64,-768,-1856,71168,-470336,1581440,-3104960,3581696,-2132736,328832]),(⟨0,0,1⟩,[64,-1024,3136,27008,-255680,943360,-1884224,2076032,-1072512]),(⟨0,0,2⟩,[-64,512,4416,-54912,194112,-323840,260288,-31360]),(⟨0,0,3⟩,[-64,640,3648,-54528,197696,-331136,265664]),(⟨0,1,0⟩,[64,-1024,3136,27008,-255680,943360,-1884224,2076032,-1072512]),(⟨0,1,1⟩,[0,-512,7168,-29184,30720,51712,-177152,182784]),(⟨0,1,4⟩,[-128,1536,-3840,-4608,15232]),(⟨0,2,0⟩,[-64,512,4416,-54912,194112,-323840,260288,-31360]),(⟨0,3,0⟩,[-64,640,3648,-54528,197696,-331136,265664]),(⟨0,4,1⟩,[-128,1536,-3840,-4608,15232]),(⟨1,0,0⟩,[64,-1024,3136,27008,-255680,943360,-1884224,2076032,-1072512]),(⟨1,0,1⟩,[0,-512,7168,-29184,30720,51712,-177152,182784]),(⟨1,0,4⟩,[-128,1536,-3840,-4608,15232]),(⟨1,1,0⟩,[0,-512,7168,-29184,30720,51712,-177152,182784]),(⟨1,4,0⟩,[-128,1536,-3840,-4608,15232]),(⟨2,0,0⟩,[-64,512,4416,-54912,194112,-323840,260288,-31360]),(⟨3,0,0⟩,[-64,640,3648,-54528,197696,-331136,265664]),(⟨4,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨4,1,0⟩,[-128,1536,-3840,-4608,15232])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[16,-208,1008,-2480,2688,-512]),(⟨0,0,1⟩,[0,-96,704,-1760,1664]),(⟨0,0,2⟩,[-16,176,-304,-112]),(⟨0,0,3⟩,[0,128,-384]),(⟨0,1,0⟩,[0,-96,704,-1760,1664]),(⟨0,1,1⟩,[0,-32,320,-544]),(⟨0,2,0⟩,[-16,176,-304,-112]),(⟨0,3,0⟩,[0,128,-384]),(⟨1,0,0⟩,[0,-96,704,-1760,1664]),(⟨1,0,1⟩,[0,-32,320,-544]),(⟨1,1,0⟩,[0,-32,320,-544]),(⟨1,1,1⟩,[32,-320,544]),(⟨2,0,0⟩,[-16,176,-304,-112]),(⟨3,0,0⟩,[0,128,-384])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 5 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r434) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 10 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r435) sourceRight))).isZero := by decide +kernel

noncomputable def partial19 : Poly := []

theorem partial_sound19 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 19)
      sourceRight).eval u v t=partial19.eval u v t := by rfl

noncomputable def chunk16 : Poly := [(⟨3,0,0⟩,[-64,640,3648,-54528,197696,-331136,265664]),(⟨4,0,1⟩,[-128,1536,-3840,-4608,15232]),(⟨4,1,0⟩,[-128,1536,-3840,-4608,15232])]

noncomputable def partial16 : Poly := [(⟨3,0,0⟩,[-1024,23552,-139264,-827392,16422912,-108677120,417112064,-1027768320,1648331776,-1650160640,883646464,-136019968]),(⟨3,0,1⟩,[0,6144,-106496,212992,6569984,-62722048,273006592,-697303040,1098792960,-1018578944,442064896]),(⟨3,0,2⟩,[1024,-21504,73728,1327104,-13940736,56260608,-116523008,125280256,-43674624,-29754368]),(⟨3,0,3⟩,[0,-8192,106496,221184,-8380416,46243840,-118300672,161161216,-102014976]),(⟨3,1,0⟩,[0,6144,-106496,212992,6569984,-62722048,273006592,-697303040,1098792960,-1018578944,442064896]),(⟨3,1,1⟩,[0,2048,-40960,122880,2564096,-25759744,103522304,-222011392,265150464,-144521216]),(⟨3,2,0⟩,[1024,-21504,73728,1327104,-13940736,56260608,-116523008,125280256,-43674624,-29754368]),(⟨3,3,0⟩,[0,-8192,106496,221184,-8380416,46243840,-118300672,161161216,-102014976]),(⟨4,0,0⟩,[0,6144,-106496,212992,6569984,-62722048,273006592,-697303040,1098792960,-1018578944,442064896]),(⟨4,0,1⟩,[-2048,53248,-550912,2713600,-4257792,-19855360,119195648,-270206976,308453376,-152320000]),(⟨4,0,2⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨4,0,3⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨4,0,4⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨4,1,0⟩,[-2048,53248,-550912,2713600,-4257792,-19855360,119195648,-270206976,308453376,-152320000]),(⟨4,1,1⟩,[-2048,65536,-598016,786432,15405056,-94306304,246898688,-334102528,195213312]),(⟨4,1,2⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨4,1,3⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨4,2,0⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨4,2,1⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨4,3,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨4,3,1⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨4,4,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨5,0,0⟩,[1024,-21504,73728,1327104,-13940736,56260608,-116523008,125280256,-43674624,-29754368]),(⟨5,0,1⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨5,0,2⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨5,1,0⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨5,1,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨5,1,2⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨5,2,0⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨5,2,1⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨6,0,0⟩,[0,-8192,106496,221184,-8380416,46243840,-118300672,161161216,-102014976]),(⟨6,0,1⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨6,1,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨7,0,1⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨7,1,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088])]


theorem partial_checked16 :
    (Poly.add (Poly.add (Poly.mul chunk16 sourceRight) partial19)
      (Poly.scale (K.ofRat (-1)) partial16)).isZero := by decide +kernel

theorem partial_sound16 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 16)
      sourceRight).eval u v t=partial16.eval u v t := by
  change (Poly.mul (chunk16++(sourceLeft.drop 19))
    sourceRight).eval u v t=partial16.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound19 partial_checked16 u v t


noncomputable def chunk12 : Poly := [(⟨1,0,4⟩,[-128,1536,-3840,-4608,15232]),(⟨1,1,0⟩,[0,-512,7168,-29184,30720,51712,-177152,182784]),(⟨1,4,0⟩,[-128,1536,-3840,-4608,15232]),(⟨2,0,0⟩,[-64,512,4416,-54912,194112,-323840,260288,-31360])]

noncomputable def partial12 : Poly := [(⟨1,0,4⟩,[-2048,51200,-509952,2590720,-6821888,5904384,15673344,-48195584,43302912,-7798784]),(⟨1,0,5⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨1,0,6⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨1,0,7⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨1,1,0⟩,[0,-8192,221184,-2473984,15056896,-54132736,109281280,-66404352,-247316480,746856448,-955965440,582025216,-93585408]),(⟨1,1,1⟩,[0,0,49152,-1048576,8749056,-36962304,79953920,-49217536,-182157312,526516224,-616480768,304152576]),(⟨1,1,2⟩,[0,8192,-204800,1884160,-7749632,12648448,5865472,-53264384,80232448,-35725312,-20471808]),(⟨1,1,3⟩,[0,0,-65536,1114112,-6488064,15138816,-5177344,-42532864,91422720,-70189056]),(⟨1,1,4⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨1,1,5⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨1,2,0⟩,[0,0,49152,-1048576,8749056,-36962304,79953920,-49217536,-182157312,526516224,-616480768,304152576]),(⟨1,2,1⟩,[0,0,16384,-393216,3506176,-14221312,24051712,5505024,-90669056,154861568,-99434496]),(⟨1,2,4⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨1,3,0⟩,[0,8192,-204800,1884160,-7749632,12648448,5865472,-53264384,80232448,-35725312,-20471808]),(⟨1,3,4⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨1,4,0⟩,[-2048,51200,-575488,3704832,-13309952,21043200,10496000,-90728448,134725632,-77987840]),(⟨1,4,1⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨1,4,2⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨1,4,3⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨1,5,0⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨1,5,1⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨1,6,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨1,7,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨2,0,0⟩,[-1024,21504,-100352,-1122304,17537024,-110450688,414978048,-1012334592,1621904384,-1646992384,943233024,-217563136,16056320]),(⟨2,0,1⟩,[0,6144,-94208,49152,7372800,-64212992,271736832,-685981696,1079214080,-1019054080,488312832,-52183040]),(⟨2,0,2⟩,[1024,-19456,38912,1507328,-14170112,55543808,-114020352,123019264,-48376832,-19618816,3512320]),(⟨2,0,3⟩,[0,-8192,90112,368640,-8724480,45932544,-115990528,157671424,-103964672,12042240]),(⟨2,0,4⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨2,0,5⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨2,1,0⟩,[0,6144,-45056,-999424,16121856,-101175296,351690752,-735199232,897056768,-492537856,-128167936,251969536]),(⟨2,1,1⟩,[0,2048,-20480,-335872,6397952,-40407040,126402560,-212049920,169795584,3229696,-82374656]),(⟨2,1,4⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨2,1,5⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨2,2,0⟩,[1024,-19456,55296,1114112,-10663936,41322496,-89968640,128524288,-139045888,135242752,-95922176]),(⟨2,2,1⟩,[0,-16384,393216,-3506176,14221312,-24051712,-5505024,90669056,-154861568,99434496]),(⟨2,3,0⟩,[0,-8192,90112,368640,-8724480,45932544,-115990528,157671424,-103964672,12042240]),(⟨2,4,0⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨2,4,1⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨2,5,0⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨2,5,1⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨3,0,0⟩,[-1024,29696,-233472,-778240,23795712,-172890112,688848896,-1713750016,2727545856,-2669214720,1371959296,-188203008]),(⟨3,0,1⟩,[0,8192,-143360,270336,9461760,-88907776,375357440,-914857984,1359257600,-1170210816,459124736]),(⟨3,0,2⟩,[1024,-21504,73728,1327104,-13940736,56260608,-116523008,125280256,-43674624,-29754368]),(⟨3,0,3⟩,[0,-8192,106496,221184,-8380416,46243840,-118300672,161161216,-102014976]),(⟨3,0,4⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨3,1,0⟩,[0,16384,-348160,2154496,1712128,-76259328,381222912,-968122368,1439490048,-1205936128,438652928]),(⟨3,1,1⟩,[-2048,38912,-98304,-2768896,28749824,-128110592,321077248,-482476032,416782336,-161581056]),(⟨3,2,0⟩,[1024,-21504,73728,1327104,-13940736,56260608,-116523008,125280256,-43674624,-29754368]),(⟨3,3,0⟩,[0,-8192,106496,221184,-8380416,46243840,-118300672,161161216,-102014976]),(⟨3,4,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨4,0,0⟩,[1024,-13312,-67584,1720320,-7600128,-7178240,158986240,-574283776,1050416128,-1038197760,445577216]),(⟨4,0,1⟩,[-2048,53248,-550912,2713600,-4257792,-19855360,119195648,-270206976,308453376,-152320000]),(⟨4,0,2⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨4,0,3⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨4,0,4⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨4,1,0⟩,[-2048,53248,-616448,3827712,-10745856,-4716544,114018304,-312739840,399876096,-222509056]),(⟨4,1,1⟩,[-2048,65536,-598016,786432,15405056,-94306304,246898688,-334102528,195213312]),(⟨4,1,2⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨4,1,3⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨4,2,0⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨4,2,1⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨4,3,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨4,3,1⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨4,4,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨5,0,0⟩,[1024,-29696,163840,1695744,-22665216,102193152,-232513536,282951680,-147639296,-17712128]),(⟨5,0,1⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨5,0,2⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨5,1,0⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨5,1,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨5,1,2⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨5,2,0⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨5,2,1⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨6,0,0⟩,[0,-8192,106496,221184,-8380416,46243840,-118300672,161161216,-102014976]),(⟨6,0,1⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨6,1,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨7,0,1⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨7,1,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088])]


theorem partial_checked12 :
    (Poly.add (Poly.add (Poly.mul chunk12 sourceRight) partial16)
      (Poly.scale (K.ofRat (-1)) partial12)).isZero := by decide +kernel

theorem partial_sound12 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 12)
      sourceRight).eval u v t=partial12.eval u v t := by
  change (Poly.mul (chunk12++(sourceLeft.drop 16))
    sourceRight).eval u v t=partial12.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound16 partial_checked12 u v t


noncomputable def chunk8 : Poly := [(⟨0,3,0⟩,[-64,640,3648,-54528,197696,-331136,265664]),(⟨0,4,1⟩,[-128,1536,-3840,-4608,15232]),(⟨1,0,0⟩,[64,-1024,3136,27008,-255680,943360,-1884224,2076032,-1072512]),(⟨1,0,1⟩,[0,-512,7168,-29184,30720,51712,-177152,182784])]

noncomputable def partial8 : Poly := [(⟨0,3,0⟩,[-1024,23552,-139264,-827392,16422912,-108677120,417112064,-1027768320,1648331776,-1650160640,883646464,-136019968]),(⟨0,3,1⟩,[0,6144,-106496,212992,6569984,-62722048,273006592,-697303040,1098792960,-1018578944,442064896]),(⟨0,3,2⟩,[1024,-21504,73728,1327104,-13940736,56260608,-116523008,125280256,-43674624,-29754368]),(⟨0,3,3⟩,[0,-8192,106496,221184,-8380416,46243840,-118300672,161161216,-102014976]),(⟨0,4,0⟩,[0,6144,-106496,212992,6569984,-62722048,273006592,-697303040,1098792960,-1018578944,442064896]),(⟨0,4,1⟩,[-2048,53248,-550912,2713600,-4257792,-19855360,119195648,-270206976,308453376,-152320000]),(⟨0,4,2⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨0,4,3⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨0,4,4⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨0,5,0⟩,[1024,-21504,73728,1327104,-13940736,56260608,-116523008,125280256,-43674624,-29754368]),(⟨0,5,1⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨0,5,2⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨0,6,0⟩,[0,-8192,106496,221184,-8380416,46243840,-118300672,161161216,-102014976]),(⟨0,6,1⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨0,7,1⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨1,0,0⟩,[1024,-29696,327680,-1411072,-3835904,84936704,-542117888,2081120256,-5388901376,9655258112,-11777445888,9204926464,-3945840640,549126144]),(⟨1,0,1⟩,[0,-14336,364544,-3608576,16580608,-17797120,-203595776,1273544704,-3858874368,7197329408,-8500178944,5924163584,-1878245376]),(⟨1,0,2⟩,[-1024,27648,-200704,-624640,16754688,-105617408,350834688,-672202752,667532288,-82326528,-522952704,424273920]),(⟨1,0,3⟩,[0,16384,-360448,2678784,-5496832,-30449664,224796672,-656695296,1069506560,-970203136,391372800]),(⟨1,0,4⟩,[-2048,51200,-575488,3704832,-13309952,21043200,10496000,-90728448,134725632,-77987840]),(⟨1,0,5⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨1,0,6⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨1,0,7⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨1,1,0⟩,[0,-14336,364544,-3608576,16580608,-17797120,-203595776,1273544704,-3858874368,7197329408,-8500178944,5924163584,-1878245376]),(⟨1,1,1⟩,[0,-2048,151552,-2560000,18194432,-58806272,33210368,402825216,-1546887168,2776700928,-2705526784,1191751680]),(⟨1,1,2⟩,[0,8192,-188416,1490944,-4243456,-1572864,29917184,-47759360,-10436608,119136256,-119906304]),(⟨1,1,3⟩,[0,0,-65536,1114112,-6488064,15138816,-5177344,-42532864,91422720,-70189056]),(⟨1,1,4⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨1,1,5⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨1,2,0⟩,[-1024,27648,-200704,-624640,16754688,-105617408,350834688,-672202752,667532288,-82326528,-522952704,424273920]),(⟨1,2,1⟩,[0,8192,-188416,1490944,-4243456,-1572864,29917184,-47759360,-10436608,119136256,-119906304]),(⟨1,2,4⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨1,3,0⟩,[0,22528,-466944,2891776,1073152,-93171712,497803264,-1353998336,2168299520,-1988782080,833437696]),(⟨1,3,1⟩,[0,2048,-106496,1236992,-3923968,-10620928,98344960,-264544256,356573184,-214710272]),(⟨1,3,4⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨1,4,0⟩,[-2048,53248,-616448,3827712,-10745856,-4716544,114018304,-312739840,399876096,-222509056]),(⟨1,4,1⟩,[-2048,65536,-598016,786432,15405056,-94306304,246898688,-334102528,195213312]),(⟨1,4,2⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨1,4,3⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨1,5,0⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨1,5,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨1,5,2⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨1,6,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨1,7,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨2,0,0⟩,[-1024,15360,43008,-2256896,19060736,-74115072,102100992,327614464,-1989653504,4803480576,-6600980480,5124575232,-1768603648]),(⟨2,0,1⟩,[0,4096,8192,-1462272,16818176,-86056960,224993280,-233938944,-285515776,1231130624,-1600733184,835416064]),(⟨2,0,2⟩,[1024,-19456,55296,1114112,-10663936,41322496,-89968640,128524288,-139045888,135242752,-95922176]),(⟨2,0,3⟩,[0,-8192,90112,368640,-8724480,45932544,-115990528,157671424,-103964672,12042240]),(⟨2,0,4⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨2,0,5⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨2,1,0⟩,[0,4096,8192,-1462272,16818176,-86056960,224993280,-233938944,-285515776,1231130624,-1600733184,835416064]),(⟨2,1,1⟩,[2048,-51200,458752,-1425408,-5214208,72069120,-350806016,976027648,-1644541952,1630656512,-765255680]),(⟨2,1,2⟩,[0,-16384,393216,-3506176,14221312,-24051712,-5505024,90669056,-154861568,99434496]),(⟨2,1,4⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨2,1,5⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨2,2,0⟩,[1024,-19456,55296,1114112,-10663936,41322496,-89968640,128524288,-139045888,135242752,-95922176]),(⟨2,2,1⟩,[0,-16384,393216,-3506176,14221312,-24051712,-5505024,90669056,-154861568,99434496]),(⟨2,3,0⟩,[1024,-29696,163840,1695744,-22665216,102193152,-232513536,282951680,-147639296,-17712128]),(⟨2,4,0⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨2,4,1⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨2,5,0⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨2,5,1⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨3,0,0⟩,[-2048,57344,-483328,-354304,31801344,-241545216,959729664,-2336735232,3577235456,-3278057472,1465487360,-68081664]),(⟨3,0,1⟩,[0,16384,-348160,2154496,1712128,-76259328,381222912,-968122368,1439490048,-1205936128,438652928]),(⟨3,0,2⟩,[1024,-21504,73728,1327104,-13940736,56260608,-116523008,125280256,-43674624,-29754368]),(⟨3,0,3⟩,[0,-8192,106496,221184,-8380416,46243840,-118300672,161161216,-102014976]),(⟨3,0,4⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨3,1,0⟩,[0,16384,-348160,2154496,1712128,-76259328,381222912,-968122368,1439490048,-1205936128,438652928]),(⟨3,1,1⟩,[-2048,38912,-98304,-2768896,28749824,-128110592,321077248,-482476032,416782336,-161581056]),(⟨3,2,0⟩,[1024,-21504,73728,1327104,-13940736,56260608,-116523008,125280256,-43674624,-29754368]),(⟨3,3,0⟩,[0,-16384,212992,442368,-16760832,92487680,-236601344,322322432,-204029952]),(⟨3,4,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨3,4,1⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨4,0,0⟩,[1024,-5120,-223232,2514944,-5347328,-50276352,377917440,-1177714688,2039690240,-1972675584,857421824]),(⟨4,0,1⟩,[-2048,53248,-616448,3827712,-10745856,-4716544,114018304,-312739840,399876096,-222509056]),(⟨4,0,2⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨4,0,3⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨4,0,4⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨4,1,0⟩,[-2048,53248,-616448,3827712,-10745856,-4716544,114018304,-312739840,399876096,-222509056]),(⟨4,1,1⟩,[-2048,65536,-598016,786432,15405056,-94306304,246898688,-334102528,195213312]),(⟨4,1,2⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨4,1,3⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨4,2,0⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨4,2,1⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨4,3,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨4,3,1⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨4,4,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨5,0,0⟩,[1024,-29696,163840,1695744,-22665216,102193152,-232513536,282951680,-147639296,-17712128]),(⟨5,0,1⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨5,0,2⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨5,1,0⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨5,1,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨5,1,2⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨5,2,0⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨5,2,1⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨6,0,0⟩,[0,-8192,106496,221184,-8380416,46243840,-118300672,161161216,-102014976]),(⟨6,0,1⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨6,1,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨7,0,1⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨7,1,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088])]


theorem partial_checked8 :
    (Poly.add (Poly.add (Poly.mul chunk8 sourceRight) partial12)
      (Poly.scale (K.ofRat (-1)) partial8)).isZero := by decide +kernel

theorem partial_sound8 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 8)
      sourceRight).eval u v t=partial8.eval u v t := by
  change (Poly.mul (chunk8++(sourceLeft.drop 12))
    sourceRight).eval u v t=partial8.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound12 partial_checked8 u v t


noncomputable def chunk4 : Poly := [(⟨0,1,0⟩,[64,-1024,3136,27008,-255680,943360,-1884224,2076032,-1072512]),(⟨0,1,1⟩,[0,-512,7168,-29184,30720,51712,-177152,182784]),(⟨0,1,4⟩,[-128,1536,-3840,-4608,15232]),(⟨0,2,0⟩,[-64,512,4416,-54912,194112,-323840,260288,-31360])]

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[1024,-29696,327680,-1411072,-3835904,84936704,-542117888,2081120256,-5388901376,9655258112,-11777445888,9204926464,-3945840640,549126144]),(⟨0,1,1⟩,[0,-14336,364544,-3608576,16580608,-17797120,-203595776,1273544704,-3858874368,7197329408,-8500178944,5924163584,-1878245376]),(⟨0,1,2⟩,[-1024,27648,-200704,-624640,16754688,-105617408,350834688,-672202752,667532288,-82326528,-522952704,424273920]),(⟨0,1,3⟩,[0,16384,-360448,2678784,-5496832,-30449664,224796672,-656695296,1069506560,-970203136,391372800]),(⟨0,1,4⟩,[-2048,51200,-575488,3704832,-13309952,21043200,10496000,-90728448,134725632,-77987840]),(⟨0,1,5⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨0,1,6⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨0,1,7⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨0,2,0⟩,[-1024,15360,43008,-2256896,19060736,-74115072,102100992,327614464,-1989653504,4803480576,-6600980480,5124575232,-1768603648]),(⟨0,2,1⟩,[0,4096,8192,-1462272,16818176,-86056960,224993280,-233938944,-285515776,1231130624,-1600733184,835416064]),(⟨0,2,2⟩,[1024,-19456,55296,1114112,-10663936,41322496,-89968640,128524288,-139045888,135242752,-95922176]),(⟨0,2,3⟩,[0,-8192,90112,368640,-8724480,45932544,-115990528,157671424,-103964672,12042240]),(⟨0,2,4⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨0,2,5⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨0,3,0⟩,[-2048,57344,-483328,-354304,31801344,-241545216,959729664,-2336735232,3577235456,-3278057472,1465487360,-68081664]),(⟨0,3,1⟩,[0,16384,-348160,2154496,1712128,-76259328,381222912,-968122368,1439490048,-1205936128,438652928]),(⟨0,3,2⟩,[1024,-21504,73728,1327104,-13940736,56260608,-116523008,125280256,-43674624,-29754368]),(⟨0,3,3⟩,[0,-8192,106496,221184,-8380416,46243840,-118300672,161161216,-102014976]),(⟨0,3,4⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨0,4,0⟩,[1024,-5120,-223232,2514944,-5347328,-50276352,377917440,-1177714688,2039690240,-1972675584,857421824]),(⟨0,4,1⟩,[-2048,53248,-616448,3827712,-10745856,-4716544,114018304,-312739840,399876096,-222509056]),(⟨0,4,2⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨0,4,3⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨0,4,4⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨0,5,0⟩,[1024,-29696,163840,1695744,-22665216,102193152,-232513536,282951680,-147639296,-17712128]),(⟨0,5,1⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨0,5,2⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨0,6,0⟩,[0,-8192,106496,221184,-8380416,46243840,-118300672,161161216,-102014976]),(⟨0,6,1⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨0,7,1⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨1,0,0⟩,[1024,-29696,327680,-1411072,-3835904,84936704,-542117888,2081120256,-5388901376,9655258112,-11777445888,9204926464,-3945840640,549126144]),(⟨1,0,1⟩,[0,-14336,364544,-3608576,16580608,-17797120,-203595776,1273544704,-3858874368,7197329408,-8500178944,5924163584,-1878245376]),(⟨1,0,2⟩,[-1024,27648,-200704,-624640,16754688,-105617408,350834688,-672202752,667532288,-82326528,-522952704,424273920]),(⟨1,0,3⟩,[0,16384,-360448,2678784,-5496832,-30449664,224796672,-656695296,1069506560,-970203136,391372800]),(⟨1,0,4⟩,[-2048,51200,-575488,3704832,-13309952,21043200,10496000,-90728448,134725632,-77987840]),(⟨1,0,5⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨1,0,6⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨1,0,7⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨1,1,0⟩,[0,-20480,507904,-4743168,18104320,18538496,-516472832,2613493760,-7470432256,13647802368,-16044392448,11266301952,-3662905344]),(⟨1,1,1⟩,[0,-4096,253952,-4071424,27639808,-80650240,-13533184,854867968,-2911617024,5026885632,-4794572800,2079350784]),(⟨1,1,2⟩,[0,8192,-172032,1097728,-737280,-15794176,53968896,-42254336,-101105664,273997824,-219340800]),(⟨1,1,3⟩,[0,0,-65536,1114112,-6488064,15138816,-5177344,-42532864,91422720,-70189056]),(⟨1,1,4⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨1,1,5⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨1,2,0⟩,[-1024,31744,-241664,-1038336,24823808,-154712064,495874048,-856924160,564173824,622287872,-1507205120,955537408]),(⟨1,2,1⟩,[2048,-43008,253952,458752,-12963840,84717568,-344940544,922763264,-1564309504,1594931200,-785727488]),(⟨1,2,2⟩,[0,-16384,393216,-3506176,14221312,-24051712,-5505024,90669056,-154861568,99434496]),(⟨1,2,4⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨1,2,5⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨1,3,0⟩,[0,24576,-503808,2949120,3964928,-119357440,600154112,-1571553280,2428764160,-2140413952,850497536]),(⟨1,3,1⟩,[-2048,38912,-163840,-1654784,22261760,-112971776,315899904,-525008896,508205056,-231770112]),(⟨1,3,4⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨1,4,0⟩,[-2048,53248,-616448,3827712,-10745856,-4716544,114018304,-312739840,399876096,-222509056]),(⟨1,4,1⟩,[-2048,65536,-598016,786432,15405056,-94306304,246898688,-334102528,195213312]),(⟨1,4,2⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨1,4,3⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨1,5,0⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨1,5,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨1,5,2⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨1,6,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨1,7,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨2,0,0⟩,[-1024,15360,43008,-2256896,19060736,-74115072,102100992,327614464,-1989653504,4803480576,-6600980480,5124575232,-1768603648]),(⟨2,0,1⟩,[0,4096,8192,-1462272,16818176,-86056960,224993280,-233938944,-285515776,1231130624,-1600733184,835416064]),(⟨2,0,2⟩,[1024,-19456,55296,1114112,-10663936,41322496,-89968640,128524288,-139045888,135242752,-95922176]),(⟨2,0,3⟩,[0,-8192,90112,368640,-8724480,45932544,-115990528,157671424,-103964672,12042240]),(⟨2,0,4⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨2,0,5⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨2,1,0⟩,[-1024,31744,-241664,-1038336,24823808,-154712064,495874048,-856924160,564173824,622287872,-1507205120,955537408]),(⟨2,1,1⟩,[2048,-43008,253952,458752,-12963840,84717568,-344940544,922763264,-1564309504,1594931200,-785727488]),(⟨2,1,2⟩,[0,-16384,393216,-3506176,14221312,-24051712,-5505024,90669056,-154861568,99434496]),(⟨2,1,4⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨2,1,5⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨2,2,0⟩,[2048,-38912,94208,2621440,-24834048,96866304,-203988992,251543552,-187422720,115623936,-92409856]),(⟨2,2,1⟩,[0,-16384,393216,-3506176,14221312,-24051712,-5505024,90669056,-154861568,99434496]),(⟨2,3,0⟩,[1024,-29696,163840,1695744,-22665216,102193152,-232513536,282951680,-147639296,-17712128]),(⟨2,4,0⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨2,4,1⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨2,5,0⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨2,5,1⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨3,0,0⟩,[-2048,57344,-483328,-354304,31801344,-241545216,959729664,-2336735232,3577235456,-3278057472,1465487360,-68081664]),(⟨3,0,1⟩,[0,16384,-348160,2154496,1712128,-76259328,381222912,-968122368,1439490048,-1205936128,438652928]),(⟨3,0,2⟩,[1024,-21504,73728,1327104,-13940736,56260608,-116523008,125280256,-43674624,-29754368]),(⟨3,0,3⟩,[0,-8192,106496,221184,-8380416,46243840,-118300672,161161216,-102014976]),(⟨3,0,4⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨3,1,0⟩,[0,24576,-503808,2949120,3964928,-119357440,600154112,-1571553280,2428764160,-2140413952,850497536]),(⟨3,1,1⟩,[-2048,38912,-163840,-1654784,22261760,-112971776,315899904,-525008896,508205056,-231770112]),(⟨3,1,4⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨3,2,0⟩,[1024,-29696,163840,1695744,-22665216,102193152,-232513536,282951680,-147639296,-17712128]),(⟨3,3,0⟩,[0,-16384,212992,442368,-16760832,92487680,-236601344,322322432,-204029952]),(⟨3,4,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨3,4,1⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨4,0,0⟩,[1024,-5120,-223232,2514944,-5347328,-50276352,377917440,-1177714688,2039690240,-1972675584,857421824]),(⟨4,0,1⟩,[-2048,53248,-616448,3827712,-10745856,-4716544,114018304,-312739840,399876096,-222509056]),(⟨4,0,2⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨4,0,3⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨4,0,4⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨4,1,0⟩,[-2048,53248,-616448,3827712,-10745856,-4716544,114018304,-312739840,399876096,-222509056]),(⟨4,1,1⟩,[-2048,65536,-598016,786432,15405056,-94306304,246898688,-334102528,195213312]),(⟨4,1,2⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨4,1,3⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨4,2,0⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨4,2,1⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨4,3,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨4,3,1⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨4,4,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨5,0,0⟩,[1024,-29696,163840,1695744,-22665216,102193152,-232513536,282951680,-147639296,-17712128]),(⟨5,0,1⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨5,0,2⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨5,1,0⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨5,1,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨5,1,2⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨5,2,0⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨5,2,1⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨6,0,0⟩,[0,-8192,106496,221184,-8380416,46243840,-118300672,161161216,-102014976]),(⟨6,0,1⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨6,1,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨7,0,1⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨7,1,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088])]


theorem partial_checked4 :
    (Poly.add (Poly.add (Poly.mul chunk4 sourceRight) partial8)
      (Poly.scale (K.ofRat (-1)) partial4)).isZero := by decide +kernel

theorem partial_sound4 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 4)
      sourceRight).eval u v t=partial4.eval u v t := by
  change (Poly.mul (chunk4++(sourceLeft.drop 8))
    sourceRight).eval u v t=partial4.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound8 partial_checked4 u v t


noncomputable def chunk0 : Poly := [(⟨0,0,0⟩,[64,-768,-1856,71168,-470336,1581440,-3104960,3581696,-2132736,328832]),(⟨0,0,1⟩,[64,-1024,3136,27008,-255680,943360,-1884224,2076032,-1072512]),(⟨0,0,2⟩,[-64,512,4416,-54912,194112,-323840,260288,-31360]),(⟨0,0,3⟩,[-64,640,3648,-54528,197696,-331136,265664])]

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[1024,-25600,194560,591872,-22122496,197376000,-1033809920,3655913472,-9131588608,16251243520,-20256630784,16837986304,-8382126080,1975861248,-168361984]),(⟨0,0,1⟩,[1024,-35840,446464,-1886208,-10516480,182179840,-1153396736,4438745088,-11484609536,20477760512,-24780898304,19149981696,-8073457664,1096302592]),(⟨0,0,2⟩,[-2048,38912,-81920,-3495936,39761920,-203624448,565125120,-704245760,-558364672,3681777664,-6295904256,5263476736,-1805432832]),(⟨0,0,3⟩,[-2048,65536,-606208,-296960,41623552,-329076736,1342763008,-3341443072,5227997184,-4926418944,2326548480,-194353152]),(⟨0,0,4⟩,[1024,-5120,-223232,2514944,-5347328,-50276352,377917440,-1177714688,2039690240,-1972675584,857421824]),(⟨0,0,5⟩,[1024,-29696,163840,1695744,-22665216,102193152,-232513536,282951680,-147639296,-17712128]),(⟨0,0,6⟩,[0,-8192,106496,221184,-8380416,46243840,-118300672,161161216,-102014976]),(⟨0,1,0⟩,[1024,-35840,446464,-1886208,-10516480,182179840,-1153396736,4438745088,-11484609536,20477760512,-24780898304,19149981696,-8073457664,1096302592]),(⟨0,1,1⟩,[0,-22528,552960,-4964352,15650816,57372672,-756301824,3474776064,-9438937088,16551290880,-18685833216,12531736576,-3841789952]),(⟨0,1,2⟩,[-1024,31744,-241664,-1038336,24823808,-154712064,495874048,-856924160,564173824,622287872,-1507205120,955537408]),(⟨0,1,3⟩,[0,24576,-503808,2949120,3964928,-119357440,600154112,-1571553280,2428764160,-2140413952,850497536]),(⟨0,1,4⟩,[-2048,53248,-616448,3827712,-10745856,-4716544,114018304,-312739840,399876096,-222509056]),(⟨0,1,5⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨0,1,6⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨0,1,7⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨0,2,0⟩,[-2048,38912,-81920,-3495936,39761920,-203624448,565125120,-704245760,-558364672,3681777664,-6295904256,5263476736,-1805432832]),(⟨0,2,1⟩,[-1024,31744,-241664,-1038336,24823808,-154712064,495874048,-856924160,564173824,622287872,-1507205120,955537408]),(⟨0,2,2⟩,[2048,-38912,94208,2621440,-24834048,96866304,-203988992,251543552,-187422720,115623936,-92409856]),(⟨0,2,3⟩,[1024,-29696,163840,1695744,-22665216,102193152,-232513536,282951680,-147639296,-17712128]),(⟨0,2,4⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨0,2,5⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨0,3,0⟩,[-2048,65536,-606208,-296960,41623552,-329076736,1342763008,-3341443072,5227997184,-4926418944,2326548480,-194353152]),(⟨0,3,1⟩,[0,24576,-503808,2949120,3964928,-119357440,600154112,-1571553280,2428764160,-2140413952,850497536]),(⟨0,3,2⟩,[1024,-29696,163840,1695744,-22665216,102193152,-232513536,282951680,-147639296,-17712128]),(⟨0,3,3⟩,[0,-16384,212992,442368,-16760832,92487680,-236601344,322322432,-204029952]),(⟨0,3,4⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨0,4,0⟩,[1024,-5120,-223232,2514944,-5347328,-50276352,377917440,-1177714688,2039690240,-1972675584,857421824]),(⟨0,4,1⟩,[-2048,53248,-616448,3827712,-10745856,-4716544,114018304,-312739840,399876096,-222509056]),(⟨0,4,2⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨0,4,3⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨0,4,4⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨0,5,0⟩,[1024,-29696,163840,1695744,-22665216,102193152,-232513536,282951680,-147639296,-17712128]),(⟨0,5,1⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨0,5,2⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨0,6,0⟩,[0,-8192,106496,221184,-8380416,46243840,-118300672,161161216,-102014976]),(⟨0,6,1⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨0,7,1⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨1,0,0⟩,[1024,-35840,446464,-1886208,-10516480,182179840,-1153396736,4438745088,-11484609536,20477760512,-24780898304,19149981696,-8073457664,1096302592]),(⟨1,0,1⟩,[0,-22528,552960,-4964352,15650816,57372672,-756301824,3474776064,-9438937088,16551290880,-18685833216,12531736576,-3841789952]),(⟨1,0,2⟩,[-1024,31744,-241664,-1038336,24823808,-154712064,495874048,-856924160,564173824,622287872,-1507205120,955537408]),(⟨1,0,3⟩,[0,24576,-503808,2949120,3964928,-119357440,600154112,-1571553280,2428764160,-2140413952,850497536]),(⟨1,0,4⟩,[-2048,53248,-616448,3827712,-10745856,-4716544,114018304,-312739840,399876096,-222509056]),(⟨1,0,5⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨1,0,6⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨1,0,7⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨1,1,0⟩,[0,-22528,552960,-4964352,15650816,57372672,-756301824,3474776064,-9438937088,16551290880,-18685833216,12531736576,-3841789952]),(⟨1,1,1⟩,[2048,-51200,528384,-2080768,-10498048,174297088,-1001512960,3324633088,-6997678080,9391994880,-7532572672,2841681920]),(⟨1,1,2⟩,[2048,-43008,253952,458752,-12963840,84717568,-344940544,922763264,-1564309504,1594931200,-785727488]),(⟨1,1,3⟩,[-2048,38912,-163840,-1654784,22261760,-112971776,315899904,-525008896,508205056,-231770112]),(⟨1,1,4⟩,[-2048,65536,-598016,786432,15405056,-94306304,246898688,-334102528,195213312]),(⟨1,1,5⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨1,2,0⟩,[-1024,31744,-241664,-1038336,24823808,-154712064,495874048,-856924160,564173824,622287872,-1507205120,955537408]),(⟨1,2,1⟩,[2048,-43008,253952,458752,-12963840,84717568,-344940544,922763264,-1564309504,1594931200,-785727488]),(⟨1,2,2⟩,[0,-16384,393216,-3506176,14221312,-24051712,-5505024,90669056,-154861568,99434496]),(⟨1,2,4⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨1,2,5⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨1,3,0⟩,[0,24576,-503808,2949120,3964928,-119357440,600154112,-1571553280,2428764160,-2140413952,850497536]),(⟨1,3,1⟩,[-2048,38912,-163840,-1654784,22261760,-112971776,315899904,-525008896,508205056,-231770112]),(⟨1,3,4⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨1,4,0⟩,[-2048,53248,-616448,3827712,-10745856,-4716544,114018304,-312739840,399876096,-222509056]),(⟨1,4,1⟩,[-2048,65536,-598016,786432,15405056,-94306304,246898688,-334102528,195213312]),(⟨1,4,2⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨1,4,3⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨1,5,0⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨1,5,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨1,5,2⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨1,6,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨1,7,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨2,0,0⟩,[-2048,38912,-81920,-3495936,39761920,-203624448,565125120,-704245760,-558364672,3681777664,-6295904256,5263476736,-1805432832]),(⟨2,0,1⟩,[-1024,31744,-241664,-1038336,24823808,-154712064,495874048,-856924160,564173824,622287872,-1507205120,955537408]),(⟨2,0,2⟩,[2048,-38912,94208,2621440,-24834048,96866304,-203988992,251543552,-187422720,115623936,-92409856]),(⟨2,0,3⟩,[1024,-29696,163840,1695744,-22665216,102193152,-232513536,282951680,-147639296,-17712128]),(⟨2,0,4⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨2,0,5⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨2,1,0⟩,[-1024,31744,-241664,-1038336,24823808,-154712064,495874048,-856924160,564173824,622287872,-1507205120,955537408]),(⟨2,1,1⟩,[2048,-43008,253952,458752,-12963840,84717568,-344940544,922763264,-1564309504,1594931200,-785727488]),(⟨2,1,2⟩,[0,-16384,393216,-3506176,14221312,-24051712,-5505024,90669056,-154861568,99434496]),(⟨2,1,4⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨2,1,5⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨2,2,0⟩,[2048,-38912,94208,2621440,-24834048,96866304,-203988992,251543552,-187422720,115623936,-92409856]),(⟨2,2,1⟩,[0,-16384,393216,-3506176,14221312,-24051712,-5505024,90669056,-154861568,99434496]),(⟨2,3,0⟩,[1024,-29696,163840,1695744,-22665216,102193152,-232513536,282951680,-147639296,-17712128]),(⟨2,4,0⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨2,4,1⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨2,5,0⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨2,5,1⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨3,0,0⟩,[-2048,65536,-606208,-296960,41623552,-329076736,1342763008,-3341443072,5227997184,-4926418944,2326548480,-194353152]),(⟨3,0,1⟩,[0,24576,-503808,2949120,3964928,-119357440,600154112,-1571553280,2428764160,-2140413952,850497536]),(⟨3,0,2⟩,[1024,-29696,163840,1695744,-22665216,102193152,-232513536,282951680,-147639296,-17712128]),(⟨3,0,3⟩,[0,-16384,212992,442368,-16760832,92487680,-236601344,322322432,-204029952]),(⟨3,0,4⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨3,1,0⟩,[0,24576,-503808,2949120,3964928,-119357440,600154112,-1571553280,2428764160,-2140413952,850497536]),(⟨3,1,1⟩,[-2048,38912,-163840,-1654784,22261760,-112971776,315899904,-525008896,508205056,-231770112]),(⟨3,1,4⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨3,2,0⟩,[1024,-29696,163840,1695744,-22665216,102193152,-232513536,282951680,-147639296,-17712128]),(⟨3,3,0⟩,[0,-16384,212992,442368,-16760832,92487680,-236601344,322322432,-204029952]),(⟨3,4,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨3,4,1⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨4,0,0⟩,[1024,-5120,-223232,2514944,-5347328,-50276352,377917440,-1177714688,2039690240,-1972675584,857421824]),(⟨4,0,1⟩,[-2048,53248,-616448,3827712,-10745856,-4716544,114018304,-312739840,399876096,-222509056]),(⟨4,0,2⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨4,0,3⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨4,0,4⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨4,1,0⟩,[-2048,53248,-616448,3827712,-10745856,-4716544,114018304,-312739840,399876096,-222509056]),(⟨4,1,1⟩,[-2048,65536,-598016,786432,15405056,-94306304,246898688,-334102528,195213312]),(⟨4,1,2⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨4,1,3⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨4,2,0⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨4,2,1⟩,[2048,-43008,280576,-370688,-1976320,4638720,3266560,-9992192]),(⟨4,3,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨4,3,1⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨4,4,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨5,0,0⟩,[1024,-29696,163840,1695744,-22665216,102193152,-232513536,282951680,-147639296,-17712128]),(⟨5,0,1⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨5,0,2⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨5,1,0⟩,[0,12288,-237568,1675264,-5177344,4608000,12443648,-34476032,25346048]),(⟨5,1,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨5,1,2⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨5,2,0⟩,[0,4096,-90112,684032,-1916928,126976,7380992,-8286208]),(⟨5,2,1⟩,[-4096,90112,-684032,1916928,-126976,-7380992,8286208]),(⟨6,0,0⟩,[0,-8192,106496,221184,-8380416,46243840,-118300672,161161216,-102014976]),(⟨6,0,1⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨6,1,0⟩,[2048,-47104,370688,-1054720,-59392,4511744,-4114432,-1705984]),(⟨7,0,1⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088]),(⟨7,1,0⟩,[0,-16384,245760,-1081344,884736,3719168,-5849088])]


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
    (Poly.add (Poly.scale (K.ofRat r436) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 5 10).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r434*r435 : ℚ)=r436 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 5 10 r434 r435 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 5=10 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 5 10).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C110

#print axioms Coulomb8.Columns.C110.sound
