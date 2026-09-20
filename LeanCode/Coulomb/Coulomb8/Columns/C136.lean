import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C136

def r0 : ℚ := { num := -16384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 583680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -77824, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 87269376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -548550656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 2437672960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -7871332352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 18579202048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -31567564800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 36833601536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := -26144894976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := 6864633856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 554678272, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -2810101760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 59572224, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -8192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 59392, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -8302592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 13031424, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := -633344000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := 2985283584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := -1414578176, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := 3335131136, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := -5501607936, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := 42023491584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := -25750769664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := 3016402944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := 5572972544, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := -261046272, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := 32768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := -1028096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := 13400064, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := -95027200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := 399247360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := -973430784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 57569280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := 1611923456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := -7225913344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := 10965913600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := -7197452288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := 13074432, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 222566400, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 12288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -735232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 14270464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -138151936, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := 784719872, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := -2828496896, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := 6652755968, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := -9985806336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := 8551952384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := -2474039296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -1423785984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 68315136, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := 403456, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -2906112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -2383872, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 137355264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := -807456768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := 2379476992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := -3991920640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 3536134144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -936974336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := -75687936, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -4096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 327680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -6152192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 49963008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -208142336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 474734592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -562307072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 198385664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := 25260032, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := -5677056, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -1310720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 15695872, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -84475904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 237469696, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -20578304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 203980800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := 5308416, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 2048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -59392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 882688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -9930752, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 88244224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -573939712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 375279616, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -8398966784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := 18591795200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := -27549575168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := 24708208640, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -8911448064, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := -4188917760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := 556224512, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -96256, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 3743744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -40966144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 223821824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := -40964096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := 178282496, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -1121456128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := 28487680, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := -10635264, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := 12042240, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := -232515584, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := -2048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 55296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -718848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 7370752, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := -61337600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 20549632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -1276055552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 2971602944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -250841088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 3259635712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -625080320, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := -71874560, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := 16384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := -319488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := 2744320, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := -16277504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := 74342400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := -232660992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := 442146816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := -3399680, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -70459392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 2850816, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := -36864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := 1093632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -12877824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 77660160, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := -260956160, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := 497246208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := -467615744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := -39616512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := 84119552, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := -90632192, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 53788672, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := 204800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := -1974272, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := 1105920, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := 4104192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -145334272, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 537632768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -127492096, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 581173248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := 6160384, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := 49152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := -950272, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := 6701056, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := -20709376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := 18432000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 7110656, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := -137904128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 851968, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := 8192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -188416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 1482752, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -4218880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := -237568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 18046976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -2351104, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := -57344, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -65536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 983040, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -4325376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := 3538944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 14876672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := -196608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := -360448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := 2736128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -7667712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 507904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := 1736704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -4096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 282624, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := -3584000, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := 190480384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := -961126400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := 3339149312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -7946051584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 12337315840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -10541617152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 657453056, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := 7866216448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := -47677440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := 30720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := 169984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -6535168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 60215296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -303755264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 970477568, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := -1999933440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := 2495002624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := -193083392, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := -116021248, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := 11139072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := -1273856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := 13811712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := -82280448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := 295452672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := -38985728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := 896548864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := -79036416, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := 3452928, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := -385024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := 6184960, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := -47374336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := 27877376, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := -454729728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := 81518592, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := -275554304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := -442368, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := 4096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -106496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := 159744, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := -6389760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 22831104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -51200000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := 434176, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 4030464, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := -49942528, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := 4988928, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 360448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -2736128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 7667712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -507904, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := -1736704, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := -196608, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := 2949120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := -12976128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := 10616832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := 44630016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := -589824, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := 291840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := -38912, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := 43634688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -274275328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 1218836480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := -3935666176, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := 9289601024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := -15783782400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := 18416800768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := -13072447488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := 3432316928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := 277339136, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := -1405050880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := 29786112, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := 29696, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := -4151296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := 6515712, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := -316672000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := 1492641792, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := -707289088, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := 1667565568, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := -2750803968, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := 21011745792, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := -12875384832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := 1508201472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 2786486272, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -130523136, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := -514048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := 6700032, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := -47513600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := 199623680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -486715392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := 28784640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := 805961728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := -3612956672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := 5482956800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := -3598726144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := 6537216, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 111283200, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := 6144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := -367616, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := 7135232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := -69075968, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := 392359936, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := -1414248448, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := 3326377984, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := -4992903168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := 4275976192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -1237019648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := -711892992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := 34157568, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := 201728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := -1453056, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -1191936, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := 68677632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -403728384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 1189738496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -1995960320, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 1768067072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -468487168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := -37843968, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := 163840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -3076096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := 24981504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := -104071168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := 237367296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := -281153536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := 99192832, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := 12630016, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := -2838528, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := -655360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 7847936, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -42237952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 118734848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -10289152, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 101990400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := 2654208, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := 1024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := -29696, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 441344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -4965376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := 44122112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := -286969856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := 187639808, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := -4199483392, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := 9295897600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := -13774787584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := 12354104320, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := -4455724032, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -2094458880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 278112256, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -48128, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 1871872, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := -20483072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := 111910912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := -20482048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := 89141248, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -560728064, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 14243840, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -5317632, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 6021120, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -116257792, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := -1024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := 27648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := -359424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := 3685376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := -30668800, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := 10274816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := -638027776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := 1485801472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := -125420544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := 1629817856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := -312540160, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := -35937280, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := -159744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := 1372160, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := -8138752, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := 37171200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := -116330496, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := 221073408, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := -1699840, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := -35229696, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := 1425408, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := -18432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := 546816, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := -6438912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := 38830080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := -130478080, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := 248623104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := -233807872, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := -19808256, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := 42059776, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := -45316096, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := 26894336, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := 102400, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := -987136, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := 552960, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := 2052096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := -72667136, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := 268816384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := -63746048, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := 290586624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := 3080192, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := 24576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := -475136, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := 3350528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := -10354688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := 9216000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := 3555328, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := -68952064, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := 425984, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := -94208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := 741376, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := -2109440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := -118784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := 9023488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := -1175552, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := -28672, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := -32768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := 491520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := -2162688, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := 1769472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := 7438336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := -98304, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := -180224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := 1368064, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := -3833856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := 253952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := 868352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := -2048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := 141312, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := -1792000, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := 95240192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := -480563200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := 1669574656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := -3973025792, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := 6168657920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := -5270808576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := 328726528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := 3933108224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := -23838720, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := 15360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := 84992, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := -3267584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := 30107648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := -151877632, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := 485238784, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := -999966720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := 1247501312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := -96541696, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := -58010624, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := 5569536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := -636928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := 6905856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := -41140224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := 147726336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := -19492864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := 448274432, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := -39518208, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := 1726464, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := -192512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := 3092480, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := -23687168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := 13938688, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := -227364864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := 40759296, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := -137777152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := -221184, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := -53248, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := 79872, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := -3194880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := 11415552, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := -25600000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := 217088, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := 2015232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r450 : ℚ := { num := -24971264, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r451 : ℚ := { num := 2494464, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r452 : ℚ := { num := 180224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r453 : ℚ := { num := -1368064, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r454 : ℚ := { num := 3833856, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r455 : ℚ := { num := -253952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r456 : ℚ := { num := -868352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r457 : ℚ := { num := -98304, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r458 : ℚ := { num := 1474560, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r459 : ℚ := { num := -6488064, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r460 : ℚ := { num := 5308416, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r461 : ℚ := { num := 22315008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r462 : ℚ := { num := -294912, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r463 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r464 : ℚ := { num := 1, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r465 : ℚ := { num := 1, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14],[0,r15,r16,r17,r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28],[0,r29,r30,r31,r32,r33,r34,r35,r36,r37,r38,r39,r40,r41],[0,r42,r43,r44,r45,r46,r47,r48,r49,r50,r51,r52,r53],[0,r0,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63],[0,r64,r65,r66,r67,r68,r69,r70,r71,r72,r73],[0,0,r29,r74,r75,r76,r77,r78,r79,r80],[],[],[],[],[],[],[r81,r82,r83,r84,r85,r86,r87,r88,r89,r90,r91,r92,r93,r94],[0,r64,r95,r96,r97,r98,r99,r100,r101,r102,r103,r104,r105],[r106,r107,r108,r109,r110,r111,r112,r113,r114,r115,r116,r117],[0,r118,r119,r120,r121,r122,r123,r124,r125,r126,r127],[],[],[],[],[],[],[],[0,r128,r129,r130,r131,r132,r133,r134,r135,r136,r137,r138],[0,r64,r65,r66,r67,r68,r69,r70,r71,r72,r73],[],[],[],[],[],[],[],[r15,r139,r140,r141,r142,r143,r144,r145,r146,r147],[0,r148,r149,r150,r151,r152,r153,r154,r155],[r156,r157,r158,r159,r160,r161,r162,r163],[0,r164,r165,r166,r167,r168,r169],[],[],[],[0,r118,r170,r171,r172,r173,r174,-16384],[],[],[],[],[],[],[],[],[0,r175,r176,r177,r178,r179,r180,r181,r182,r183,r184,r185,r186],[r106,r187,r188,r189,r190,r191,r192,r193,r194,r195,r196,r197],[0,r148,r198,r199,r200,r201,r202,r203,r204,r68,r205],[0,r156,r206,r207,r208,r209,r210,r211,r212,r213],[],[],[],[],[],[],[r214,r215,r216,r217,r218,r219,r220,r221,r222,r223,-200704],[],[],[],[],[],[],[],[0,r148,r149,r150,r151,r152,r153,r154,r155],[0,r118,r170,r171,r172,r173,r174,-16384],[],[],[],[],[r0,r224,r225,r226,r227,r228,16384],[],[],[],[],[],[],[],[],[],[],[],[],[r156,r157,r158,r159,r160,r161,r162,r163],[],[],[],[],[],[],[],[],[0,r229,r230,r231,r232,r233,r234],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,r15,r235,r236,r237,r238,r239,r240,r241,r242,r243,r244,r245,r246,r247,r248]),(⟨0,0,1⟩,[0,r64,r249,r250,r251,r252,r253,r254,r255,r256,r257,r258,r259,r260,r261]),(⟨0,0,2⟩,[0,r118,r262,r263,r264,r265,r266,r267,r268,r269,r270,r271,r272,r273]),(⟨0,0,3⟩,[0,r274,r275,r276,r277,r278,r279,r280,r281,r282,r283,r284,r285]),(⟨0,0,4⟩,[0,r15,r286,r287,r288,r289,r290,r291,r292,r293,r294,r295]),(⟨0,0,5⟩,[0,r106,r296,r297,r298,r299,r300,r301,r302,r303,r304]),(⟨0,0,6⟩,[0,0,r118,r305,r306,r307,r308,r309,r310,r311]),(⟨0,1,0⟩,[0,r64,r249,r250,r251,r252,r253,r254,r255,r256,r257,r258,r259,r260,r261]),(⟨0,1,1⟩,[r312,r313,r314,r315,r316,r317,r318,r319,r320,r321,r322,r323,r324,r325]),(⟨0,1,2⟩,[0,r106,r326,r327,r328,r329,r330,r331,r332,r333,r334,r335,r336]),(⟨0,1,3⟩,[r337,r338,r339,r340,r341,r342,r343,r344,r345,r346,r347,r348]),(⟨0,1,4⟩,[0,r156,r349,r350,r351,r352,r353,r354,r355,r356,r357]),(⟨0,2,0⟩,[0,r118,r262,r263,r264,r265,r266,r267,r268,r269,r270,r271,r272,r273]),(⟨0,2,1⟩,[0,r106,r326,r327,r328,r329,r330,r331,r332,r333,r334,r335,r336]),(⟨0,2,2⟩,[0,r358,r359,r360,r361,r362,r363,r364,r365,r366,r367,r368]),(⟨0,2,3⟩,[0,r106,r296,r297,r298,r299,r300,r301,r302,r303,r304]),(⟨0,3,0⟩,[0,r274,r275,r276,r277,r278,r279,r280,r281,r282,r283,r284,r285]),(⟨0,3,1⟩,[r337,r338,r339,r340,r341,r342,r343,r344,r345,r346,r347,r348]),(⟨0,3,2⟩,[0,r106,r296,r297,r298,r299,r300,r301,r302,r303,r304]),(⟨0,3,3⟩,[r64,r369,r370,r371,r372,r373,r374,r375,r376,r377]),(⟨0,3,4⟩,[0,r378,r379,r380,r381,r382,r383,r384,r385]),(⟨0,3,5⟩,[r214,r386,r387,r388,r389,r390,r391,r392]),(⟨0,3,6⟩,[0,r393,r394,r395,r396,r397,r398]),(⟨0,4,0⟩,[0,r15,r286,r287,r288,r289,r290,r291,r292,r293,r294,r295]),(⟨0,4,1⟩,[0,r156,r349,r350,r351,r352,r353,r354,r355,r356,r357]),(⟨0,4,3⟩,[0,r378,r379,r380,r381,r382,r383,r384,r385]),(⟨0,4,4⟩,[0,r156,r399,r400,r401,r402,r403,-8192]),(⟨0,5,0⟩,[0,r106,r296,r297,r298,r299,r300,r301,r302,r303,r304]),(⟨0,5,3⟩,[r214,r386,r387,r388,r389,r390,r391,r392]),(⟨0,6,0⟩,[0,0,r118,r305,r306,r307,r308,r309,r310,r311]),(⟨0,6,3⟩,[0,r393,r394,r395,r396,r397,r398]),(⟨1,0,0⟩,[0,r64,r249,r250,r251,r252,r253,r254,r255,r256,r257,r258,r259,r260,r261]),(⟨1,0,1⟩,[r312,r313,r314,r315,r316,r317,r318,r319,r320,r321,r322,r323,r324,r325]),(⟨1,0,2⟩,[0,r106,r326,r327,r328,r329,r330,r331,r332,r333,r334,r335,r336]),(⟨1,0,3⟩,[r337,r338,r339,r340,r341,r342,r343,r344,r345,r346,r347,r348]),(⟨1,0,4⟩,[0,r156,r349,r350,r351,r352,r353,r354,r355,r356,r357]),(⟨1,1,0⟩,[r312,r313,r314,r315,r316,r317,r318,r319,r320,r321,r322,r323,r324,r325]),(⟨1,1,1⟩,[0,r404,r405,r406,r407,r408,r409,r410,r411,r412,r413,r414,r415]),(⟨1,1,2⟩,[r337,r416,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426]),(⟨1,1,3⟩,[0,r378,r427,r428,r429,r430,r431,r432,r433,r299,r434]),(⟨1,1,4⟩,[0,r214,r435,r436,r437,r438,r439,r440,r441,r442]),(⟨1,2,0⟩,[0,r106,r326,r327,r328,r329,r330,r331,r332,r333,r334,r335,r336]),(⟨1,2,1⟩,[r337,r416,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426]),(⟨1,2,2⟩,[r81,r443,r444,r445,r446,r447,r448,r449,r450,r451,-100352]),(⟨1,3,0⟩,[r337,r338,r339,r340,r341,r342,r343,r344,r345,r346,r347,r348]),(⟨1,3,1⟩,[0,r378,r427,r428,r429,r430,r431,r432,r433,r299,r434]),(⟨1,3,3⟩,[0,r378,r379,r380,r381,r382,r383,r384,r385]),(⟨1,3,4⟩,[0,r156,r399,r400,r401,r402,r403,-8192]),(⟨1,4,0⟩,[0,r156,r349,r350,r351,r352,r353,r354,r355,r356,r357]),(⟨1,4,1⟩,[0,r214,r435,r436,r437,r438,r439,r440,r441,r442]),(⟨1,4,3⟩,[0,r156,r399,r400,r401,r402,r403,-8192]),(⟨1,4,4⟩,[r15,r452,r453,r454,r455,r456,8192]),(⟨2,0,0⟩,[0,r118,r262,r263,r264,r265,r266,r267,r268,r269,r270,r271,r272,r273]),(⟨2,0,1⟩,[0,r106,r326,r327,r328,r329,r330,r331,r332,r333,r334,r335,r336]),(⟨2,0,2⟩,[0,r358,r359,r360,r361,r362,r363,r364,r365,r366,r367,r368]),(⟨2,0,3⟩,[0,r106,r296,r297,r298,r299,r300,r301,r302,r303,r304]),(⟨2,1,0⟩,[0,r106,r326,r327,r328,r329,r330,r331,r332,r333,r334,r335,r336]),(⟨2,1,1⟩,[r337,r416,r417,r418,r419,r420,r421,r422,r423,r424,r425,r426]),(⟨2,1,2⟩,[r81,r443,r444,r445,r446,r447,r448,r449,r450,r451,-100352]),(⟨2,2,0⟩,[0,r358,r359,r360,r361,r362,r363,r364,r365,r366,r367,r368]),(⟨2,2,1⟩,[r81,r443,r444,r445,r446,r447,r448,r449,r450,r451,-100352]),(⟨2,3,0⟩,[0,r106,r296,r297,r298,r299,r300,r301,r302,r303,r304]),(⟨2,3,3⟩,[r214,r386,r387,r388,r389,r390,r391,r392]),(⟨3,0,0⟩,[0,r274,r275,r276,r277,r278,r279,r280,r281,r282,r283,r284,r285]),(⟨3,0,1⟩,[r337,r338,r339,r340,r341,r342,r343,r344,r345,r346,r347,r348]),(⟨3,0,2⟩,[0,r106,r296,r297,r298,r299,r300,r301,r302,r303,r304]),(⟨3,0,3⟩,[r64,r369,r370,r371,r372,r373,r374,r375,r376,r377]),(⟨3,0,4⟩,[0,r378,r379,r380,r381,r382,r383,r384,r385]),(⟨3,0,5⟩,[r214,r386,r387,r388,r389,r390,r391,r392]),(⟨3,0,6⟩,[0,r393,r394,r395,r396,r397,r398]),(⟨3,1,0⟩,[r337,r338,r339,r340,r341,r342,r343,r344,r345,r346,r347,r348]),(⟨3,1,1⟩,[0,r378,r427,r428,r429,r430,r431,r432,r433,r299,r434]),(⟨3,1,3⟩,[0,r378,r379,r380,r381,r382,r383,r384,r385]),(⟨3,1,4⟩,[0,r156,r399,r400,r401,r402,r403,-8192]),(⟨3,2,0⟩,[0,r106,r296,r297,r298,r299,r300,r301,r302,r303,r304]),(⟨3,2,3⟩,[r214,r386,r387,r388,r389,r390,r391,r392]),(⟨3,3,0⟩,[r64,r369,r370,r371,r372,r373,r374,r375,r376,r377]),(⟨3,3,1⟩,[0,r378,r379,r380,r381,r382,r383,r384,r385]),(⟨3,3,2⟩,[r214,r386,r387,r388,r389,r390,r391,r392]),(⟨3,3,3⟩,[0,r457,r458,r459,r460,r461,r462]),(⟨3,4,0⟩,[0,r378,r379,r380,r381,r382,r383,r384,r385]),(⟨3,4,1⟩,[0,r156,r399,r400,r401,r402,r403,-8192]),(⟨3,5,0⟩,[r214,r386,r387,r388,r389,r390,r391,r392]),(⟨3,6,0⟩,[0,r393,r394,r395,r396,r397,r398]),(⟨4,0,0⟩,[0,r15,r286,r287,r288,r289,r290,r291,r292,r293,r294,r295]),(⟨4,0,1⟩,[0,r156,r349,r350,r351,r352,r353,r354,r355,r356,r357]),(⟨4,0,3⟩,[0,r378,r379,r380,r381,r382,r383,r384,r385]),(⟨4,0,4⟩,[0,r156,r399,r400,r401,r402,r403,-8192]),(⟨4,1,0⟩,[0,r156,r349,r350,r351,r352,r353,r354,r355,r356,r357]),(⟨4,1,1⟩,[0,r214,r435,r436,r437,r438,r439,r440,r441,r442]),(⟨4,1,3⟩,[0,r156,r399,r400,r401,r402,r403,-8192]),(⟨4,1,4⟩,[r15,r452,r453,r454,r455,r456,8192]),(⟨4,3,0⟩,[0,r378,r379,r380,r381,r382,r383,r384,r385]),(⟨4,3,1⟩,[0,r156,r399,r400,r401,r402,r403,-8192]),(⟨4,4,0⟩,[0,r156,r399,r400,r401,r402,r403,-8192]),(⟨4,4,1⟩,[r15,r452,r453,r454,r455,r456,8192]),(⟨5,0,0⟩,[0,r106,r296,r297,r298,r299,r300,r301,r302,r303,r304]),(⟨5,0,3⟩,[r214,r386,r387,r388,r389,r390,r391,r392]),(⟨5,3,0⟩,[r214,r386,r387,r388,r389,r390,r391,r392]),(⟨6,0,0⟩,[0,0,r118,r305,r306,r307,r308,r309,r310,r311]),(⟨6,0,3⟩,[0,r393,r394,r395,r396,r397,r398]),(⟨6,3,0⟩,[0,r393,r394,r395,r396,r397,r398])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,-512,11584,-106560,532736,-1621824,3051904,-3282624,1363712,606272,-407232]),(⟨0,0,1⟩,[0,-256,6592,-65600,337472,-994752,1716288,-1563072,348096,460992]),(⟨0,0,2⟩,[0,512,-9792,66304,-201792,309760,-192192,-87808,65856]),(⟨0,0,3⟩,[0,128,-4736,47104,-188672,361600,-281728,-48384]),(⟨0,1,0⟩,[0,-256,6592,-65600,337472,-994752,1716288,-1563072,348096,460992]),(⟨0,1,1⟩,[64,-1024,6144,-20992,42368,-19456,-107520,326144,-373184]),(⟨0,2,0⟩,[0,512,-9792,66304,-201792,309760,-192192,-87808,65856]),(⟨0,3,0⟩,[0,128,-4736,47104,-188672,361600,-281728,-48384]),(⟨0,3,3⟩,[-256,3072,-7680,-9216,30464]),(⟨1,0,0⟩,[0,-256,6592,-65600,337472,-994752,1716288,-1563072,348096,460992]),(⟨1,0,1⟩,[64,-1024,6144,-20992,42368,-19456,-107520,326144,-373184]),(⟨1,1,0⟩,[64,-1024,6144,-20992,42368,-19456,-107520,326144,-373184]),(⟨2,0,0⟩,[0,512,-9792,66304,-201792,309760,-192192,-87808,65856]),(⟨3,0,0⟩,[0,128,-4736,47104,-188672,361600,-281728,-48384]),(⟨3,0,3⟩,[-256,3072,-7680,-9216,30464]),(⟨3,3,0⟩,[-256,3072,-7680,-9216,30464])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[16,-208,1008,-2480,2688,-512]),(⟨0,0,1⟩,[0,-96,704,-1760,1664]),(⟨0,0,2⟩,[-16,176,-304,-112]),(⟨0,0,3⟩,[0,128,-384]),(⟨0,1,0⟩,[0,-96,704,-1760,1664]),(⟨0,1,1⟩,[0,-32,320,-544]),(⟨0,2,0⟩,[-16,176,-304,-112]),(⟨0,3,0⟩,[0,128,-384]),(⟨1,0,0⟩,[0,-96,704,-1760,1664]),(⟨1,0,1⟩,[0,-32,320,-544]),(⟨1,1,0⟩,[0,-32,320,-544]),(⟨1,1,1⟩,[32,-320,544]),(⟨2,0,0⟩,[-16,176,-304,-112]),(⟨3,0,0⟩,[0,128,-384])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 9 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r463) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 10 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r464) sourceRight))).isZero := by decide +kernel

noncomputable def partial16 : Poly := []

theorem partial_sound16 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 16)
      sourceRight).eval u v t=partial16.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨2,0,0⟩,[0,512,-9792,66304,-201792,309760,-192192,-87808,65856]),(⟨3,0,0⟩,[0,128,-4736,47104,-188672,361600,-281728,-48384]),(⟨3,0,3⟩,[-256,3072,-7680,-9216,30464]),(⟨3,3,0⟩,[-256,3072,-7680,-9216,30464])]

noncomputable def partial12 : Poly := [(⟨2,0,0⟩,[0,8192,-263168,3613696,-28160000,139423744,-461928448,1034491904,-1518981120,1310380032,-391062528,-300948480,221978624,-33718272]),(⟨2,0,1⟩,[0,0,-49152,1300480,-14159872,84135936,-304787456,702005248,-1007833088,785559552,-118902784,-262019072,109584384]),(⟨2,0,2⟩,[0,-8192,246784,-2939904,17817600,-59531264,111511552,-103987200,7225344,59809792,-10185728,-7375872]),(⟨2,0,3⟩,[0,0,65536,-1449984,12247040,-51290112,117137408,-143548416,62562304,42147840,-25288704]),(⟨2,1,0⟩,[0,0,-49152,1300480,-14159872,84135936,-304787456,702005248,-1007833088,785559552,-118902784,-262019072,109584384]),(⟨2,1,1⟩,[0,0,-16384,477184,-5533696,33001472,-110555136,215048192,-227201024,74346496,68841472,-35825664]),(⟨2,2,0⟩,[0,-8192,246784,-2939904,17817600,-59531264,111511552,-103987200,7225344,59809792,-10185728,-7375872]),(⟨2,3,0⟩,[0,0,65536,-1449984,12247040,-51290112,117137408,-143548416,62562304,42147840,-25288704]),(⟨3,0,0⟩,[0,2048,-151552,3168256,-32067584,188735488,-704303104,1721270272,-2709786624,2504054784,-941334528,-247830528,134356992]),(⟨3,0,1⟩,[0,0,-28672,1021952,-13615104,92823552,-368877568,907104256,-1371258880,1137827840,-314798080,-116336640]),(⟨3,0,2⟩,[0,-2048,98304,-1626112,12734464,-52781056,120229888,-137605120,36630528,46262272,5419008]),(⟨3,0,3⟩,[-4096,102400,-1003520,4526080,-5795840,-30429184,150081536,-271306752,188596224,2981888]),(⟨3,0,4⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨3,0,5⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨3,0,6⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨3,1,0⟩,[0,0,-28672,1021952,-13615104,92823552,-368877568,907104256,-1371258880,1137827840,-314798080,-116336640]),(⟨3,1,1⟩,[0,16384,-481280,5726208,-36093952,134242304,-312619008,454565888,-359661568,68935680,62146560]),(⟨3,1,3⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨3,1,4⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,2,0⟩,[0,-2048,98304,-1626112,12734464,-52781056,120229888,-137605120,36630528,46262272,5419008]),(⟨3,2,3⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨3,3,0⟩,[-4096,102400,-1003520,4526080,-5795840,-30429184,150081536,-271306752,188596224,2981888]),(⟨3,3,1⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨3,3,2⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨3,3,3⟩,[0,-65536,983040,-4325376,3538944,14876672,-23396352]),(⟨3,4,0⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨3,4,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,5,0⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨3,6,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨4,0,0⟩,[0,-8192,234496,-2395136,9736192,290816,-146810880,588068864,-1136832512,1123291136,-393825280,-87886848]),(⟨4,0,1⟩,[0,0,-4096,192512,-3092480,23687168,-97570816,227364864,-285315072,137777152,26320896]),(⟨4,0,3⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨4,0,4⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨4,1,0⟩,[0,0,-4096,192512,-3092480,23687168,-97570816,227364864,-285315072,137777152,26320896]),(⟨4,1,1⟩,[0,4096,-192512,3092480,-23687168,97570816,-227364864,285315072,-137777152,-26320896]),(⟨4,1,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨4,1,4⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨4,3,0⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨4,3,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨4,4,0⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨4,4,1⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨5,0,0⟩,[0,-2048,163840,-3076096,24981504,-104071168,237367296,-281153536,99192832,88410112,-19869696]),(⟨5,0,3⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨5,3,0⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨6,0,0⟩,[0,0,16384,-655360,7847936,-42237952,118734848,-174915584,101990400,18579456]),(⟨6,0,3⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨6,3,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176])]


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

noncomputable def partial8 : Poly := [(⟨0,3,3⟩,[-4096,102400,-1019904,5181440,-13643776,11808768,31346688,-96391168,86605824,-15597568]),(⟨0,3,4⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨0,3,5⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨0,3,6⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨0,4,3⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨0,4,4⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨0,5,3⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨0,6,3⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨1,0,0⟩,[0,-4096,158720,-2678784,26323968,-169271296,755079168,-2401345536,5468403712,-8743677952,9254108160,-5478875136,592714752,1060921344,-236027904]),(⟨1,0,1⟩,[1024,-29696,400384,-3617792,25337856,-138913792,573634560,-1724852224,3661333504,-5210719232,4343655424,-1031840768,-1402218496,958160896]),(⟨1,0,2⟩,[0,-2048,-7168,864256,-10671104,63152128,-218916864,478810112,-693270528,759130112,-865270784,1020379136,-672609280]),(⟨1,0,3⟩,[-1024,27648,-330752,2663424,-17053696,81848320,-269150208,578697216,-760890368,491990016,2257920,-135224320]),(⟨1,0,4⟩,[0,8192,-155648,1179648,-5046272,13484032,-18759680,-6291456,83034112,-173006848,143302656]),(⟨1,1,0⟩,[1024,-29696,400384,-3617792,25337856,-138913792,573634560,-1724852224,3661333504,-5210719232,4343655424,-1031840768,-1402218496,958160896]),(⟨1,1,1⟩,[0,-12288,294912,-3139584,20846592,-98103296,333238272,-782573568,1135853568,-600399872,-1084346368,2357168128,-1492736000]),(⟨1,1,2⟩,[-1024,25600,-244736,1162240,-2930688,2045952,13367296,-48805888,63978496,22012928,-219921408,244808704]),(⟨1,1,3⟩,[0,8192,-155648,1179648,-5046272,13484032,-18759680,-6291456,83034112,-173006848,143302656]),(⟨1,2,0⟩,[0,-2048,-7168,864256,-10671104,63152128,-218916864,478810112,-693270528,759130112,-865270784,1020379136,-672609280]),(⟨1,2,1⟩,[-1024,25600,-244736,1162240,-2930688,2045952,13367296,-48805888,63978496,22012928,-219921408,244808704]),(⟨1,3,0⟩,[-1024,27648,-330752,2663424,-17053696,81848320,-269150208,578697216,-760890368,491990016,2257920,-135224320]),(⟨1,3,1⟩,[0,8192,-155648,1179648,-5046272,13484032,-18759680,-6291456,83034112,-173006848,143302656]),(⟨1,3,3⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨1,3,4⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨1,4,0⟩,[0,8192,-155648,1179648,-5046272,13484032,-18759680,-6291456,83034112,-173006848,143302656]),(⟨1,4,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨1,4,4⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨2,0,0⟩,[0,8192,-238592,2800640,-16771072,48816128,-2426880,-533686272,2151657472,-4499374080,5416651776,-3190010880,-10135552,733372416]),(⟨2,0,1⟩,[0,-6144,102400,-415744,-1562624,17395712,-50413568,32305152,130281472,-237131776,-187600896,895641600,-762173440]),(⟨2,0,2⟩,[0,-10240,300032,-3499008,21012480,-70946816,137111552,-129820672,-27033600,234608640,-307026944,195636224]),(⟨2,0,3⟩,[0,0,65536,-1449984,12247040,-51290112,117137408,-143548416,62562304,42147840,-25288704]),(⟨2,1,0⟩,[0,-6144,102400,-415744,-1562624,17395712,-50413568,32305152,130281472,-237131776,-187600896,895641600,-762173440]),(⟨2,1,1⟩,[0,-12288,382976,-4988928,36233216,-165339136,497471488,-976994304,1149263872,-523005952,-482994176,620978176]),(⟨2,1,2⟩,[2048,-53248,559104,-3194880,11415552,-25600000,25833472,34258944,-174798848,296841216,-203012096]),(⟨2,2,0⟩,[0,-10240,300032,-3499008,21012480,-70946816,137111552,-129820672,-27033600,234608640,-307026944,195636224]),(⟨2,2,1⟩,[2048,-53248,559104,-3194880,11415552,-25600000,25833472,34258944,-174798848,296841216,-203012096]),(⟨2,3,0⟩,[0,0,65536,-1449984,12247040,-51290112,117137408,-143548416,62562304,42147840,-25288704]),(⟨2,3,3⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨3,0,0⟩,[0,6144,-302080,5455872,-50988032,283250688,-1002084352,2312953856,-3400796160,2840893440,-790957056,-426958848,82725888]),(⟨3,0,1⟩,[-1024,27648,-326656,2743296,-19740672,106285056,-381110272,884131840,-1273021440,985041920,-237878272,-74540032]),(⟨3,0,2⟩,[0,-2048,98304,-1626112,12734464,-52781056,120229888,-137605120,36630528,46262272,5419008]),(⟨3,0,3⟩,[-4096,102400,-1003520,4526080,-5795840,-30429184,150081536,-271306752,188596224,2981888]),(⟨3,0,4⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨3,0,5⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨3,0,6⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨3,1,0⟩,[-1024,27648,-326656,2743296,-19740672,106285056,-381110272,884131840,-1273021440,985041920,-237878272,-74540032]),(⟨3,1,1⟩,[0,16384,-481280,5726208,-36093952,134242304,-312619008,454565888,-359661568,68935680,62146560]),(⟨3,1,3⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨3,1,4⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,2,0⟩,[0,-2048,98304,-1626112,12734464,-52781056,120229888,-137605120,36630528,46262272,5419008]),(⟨3,2,3⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨3,3,0⟩,[-4096,102400,-1003520,4526080,-5795840,-30429184,150081536,-271306752,188596224,2981888]),(⟨3,3,1⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨3,3,2⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨3,3,3⟩,[0,-98304,1474560,-6488064,5308416,22315008,-35094528]),(⟨3,4,0⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨3,4,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,5,0⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨3,6,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨4,0,0⟩,[0,-8192,201728,-1453056,-1191936,68677632,-403728384,1189738496,-1995960320,1768067072,-468487168,-264907776]),(⟨4,0,1⟩,[0,8192,-159744,1372160,-8138752,37171200,-116330496,221073408,-202280960,-35229696,169623552]),(⟨4,0,3⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨4,0,4⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨4,1,0⟩,[0,8192,-159744,1372160,-8138752,37171200,-116330496,221073408,-202280960,-35229696,169623552]),(⟨4,1,1⟩,[0,4096,-192512,3092480,-23687168,97570816,-227364864,285315072,-137777152,-26320896]),(⟨4,1,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨4,1,4⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨4,3,0⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨4,3,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨4,4,0⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨4,4,1⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨5,0,0⟩,[0,-2048,163840,-3076096,24981504,-104071168,237367296,-281153536,99192832,88410112,-19869696]),(⟨5,0,3⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨5,3,0⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨6,0,0⟩,[0,0,16384,-655360,7847936,-42237952,118734848,-174915584,101990400,18579456]),(⟨6,0,3⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨6,3,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176])]


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

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[0,-4096,158720,-2678784,26323968,-169271296,755079168,-2401345536,5468403712,-8743677952,9254108160,-5478875136,592714752,1060921344,-236027904]),(⟨0,1,1⟩,[1024,-29696,400384,-3617792,25337856,-138913792,573634560,-1724852224,3661333504,-5210719232,4343655424,-1031840768,-1402218496,958160896]),(⟨0,1,2⟩,[0,-2048,-7168,864256,-10671104,63152128,-218916864,478810112,-693270528,759130112,-865270784,1020379136,-672609280]),(⟨0,1,3⟩,[-1024,27648,-330752,2663424,-17053696,81848320,-269150208,578697216,-760890368,491990016,2257920,-135224320]),(⟨0,1,4⟩,[0,8192,-155648,1179648,-5046272,13484032,-18759680,-6291456,83034112,-173006848,143302656]),(⟨0,2,0⟩,[0,8192,-238592,2800640,-16771072,48816128,-2426880,-533686272,2151657472,-4499374080,5416651776,-3190010880,-10135552,733372416]),(⟨0,2,1⟩,[0,-6144,102400,-415744,-1562624,17395712,-50413568,32305152,130281472,-237131776,-187600896,895641600,-762173440]),(⟨0,2,2⟩,[0,-10240,300032,-3499008,21012480,-70946816,137111552,-129820672,-27033600,234608640,-307026944,195636224]),(⟨0,2,3⟩,[0,0,65536,-1449984,12247040,-51290112,117137408,-143548416,62562304,42147840,-25288704]),(⟨0,3,0⟩,[0,6144,-302080,5455872,-50988032,283250688,-1002084352,2312953856,-3400796160,2840893440,-790957056,-426958848,82725888]),(⟨0,3,1⟩,[-1024,27648,-326656,2743296,-19740672,106285056,-381110272,884131840,-1273021440,985041920,-237878272,-74540032]),(⟨0,3,2⟩,[0,-2048,98304,-1626112,12734464,-52781056,120229888,-137605120,36630528,46262272,5419008]),(⟨0,3,3⟩,[-4096,102400,-1003520,4526080,-5795840,-30429184,150081536,-271306752,188596224,2981888]),(⟨0,3,4⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨0,3,5⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨0,3,6⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨0,4,0⟩,[0,-8192,201728,-1453056,-1191936,68677632,-403728384,1189738496,-1995960320,1768067072,-468487168,-264907776]),(⟨0,4,1⟩,[0,8192,-159744,1372160,-8138752,37171200,-116330496,221073408,-202280960,-35229696,169623552]),(⟨0,4,3⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨0,4,4⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨0,5,0⟩,[0,-2048,163840,-3076096,24981504,-104071168,237367296,-281153536,99192832,88410112,-19869696]),(⟨0,5,3⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨0,6,0⟩,[0,0,16384,-655360,7847936,-42237952,118734848,-174915584,101990400,18579456]),(⟨0,6,3⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨1,0,0⟩,[0,-4096,158720,-2678784,26323968,-169271296,755079168,-2401345536,5468403712,-8743677952,9254108160,-5478875136,592714752,1060921344,-236027904]),(⟨1,0,1⟩,[1024,-29696,400384,-3617792,25337856,-138913792,573634560,-1724852224,3661333504,-5210719232,4343655424,-1031840768,-1402218496,958160896]),(⟨1,0,2⟩,[0,-2048,-7168,864256,-10671104,63152128,-218916864,478810112,-693270528,759130112,-865270784,1020379136,-672609280]),(⟨1,0,3⟩,[-1024,27648,-330752,2663424,-17053696,81848320,-269150208,578697216,-760890368,491990016,2257920,-135224320]),(⟨1,0,4⟩,[0,8192,-155648,1179648,-5046272,13484032,-18759680,-6291456,83034112,-173006848,143302656]),(⟨1,1,0⟩,[1024,-29696,424960,-4430848,36726784,-229521408,1033136128,-3293030400,7331972096,-11020473344,10151369728,-3920903168,-1634332672,1725251584]),(⟨1,1,1⟩,[0,-18432,446464,-4855808,33443840,-164843520,587612160,-1452273664,2273968128,-1623091200,-1153044480,3514828800,-2364493824]),(⟨1,1,2⟩,[-1024,23552,-191488,603136,264192,-9369600,38967296,-74639360,29719552,196811776,-516762624,447820800]),(⟨1,1,3⟩,[0,8192,-155648,1179648,-5046272,13484032,-18759680,-6291456,83034112,-173006848,143302656]),(⟨1,2,0⟩,[0,-2048,-48128,1871872,-20483072,111910912,-348194816,623988736,-560728064,99706880,-37223424,716513280,-813804544]),(⟨1,2,1⟩,[-1024,15360,84992,-3267584,30107648,-151877632,485238784,-999966720,1247501312,-675791872,-406074368,662774784]),(⟨1,2,2⟩,[2048,-53248,559104,-3194880,11415552,-25600000,25833472,34258944,-174798848,296841216,-203012096]),(⟨1,3,0⟩,[-1024,27648,-359424,3685376,-30668800,174671872,-638027776,1485801472,-2132149248,1629817856,-312540160,-251560960]),(⟨1,3,1⟩,[0,24576,-636928,6905856,-41140224,147726336,-331378688,448274432,-276627456,-104071168,205449216]),(⟨1,3,3⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨1,3,4⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨1,4,0⟩,[0,8192,-159744,1372160,-8138752,37171200,-116330496,221073408,-202280960,-35229696,169623552]),(⟨1,4,1⟩,[0,4096,-192512,3092480,-23687168,97570816,-227364864,285315072,-137777152,-26320896]),(⟨1,4,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨1,4,4⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨2,0,0⟩,[0,8192,-238592,2800640,-16771072,48816128,-2426880,-533686272,2151657472,-4499374080,5416651776,-3190010880,-10135552,733372416]),(⟨2,0,1⟩,[0,-6144,102400,-415744,-1562624,17395712,-50413568,32305152,130281472,-237131776,-187600896,895641600,-762173440]),(⟨2,0,2⟩,[0,-10240,300032,-3499008,21012480,-70946816,137111552,-129820672,-27033600,234608640,-307026944,195636224]),(⟨2,0,3⟩,[0,0,65536,-1449984,12247040,-51290112,117137408,-143548416,62562304,42147840,-25288704]),(⟨2,1,0⟩,[0,-2048,-48128,1871872,-20483072,111910912,-348194816,623988736,-560728064,99706880,-37223424,716513280,-813804544]),(⟨2,1,1⟩,[-1024,15360,84992,-3267584,30107648,-151877632,485238784,-999966720,1247501312,-675791872,-406074368,662774784]),(⟨2,1,2⟩,[2048,-53248,559104,-3194880,11415552,-25600000,25833472,34258944,-174798848,296841216,-203012096]),(⟨2,2,0⟩,[0,-18432,546816,-6438912,38830080,-130478080,248623104,-233807872,-19808256,294418432,-317212672,188260352]),(⟨2,2,1⟩,[2048,-53248,559104,-3194880,11415552,-25600000,25833472,34258944,-174798848,296841216,-203012096]),(⟨2,3,0⟩,[0,-2048,163840,-3076096,24981504,-104071168,237367296,-281153536,99192832,88410112,-19869696]),(⟨2,3,3⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨3,0,0⟩,[0,6144,-302080,5455872,-50988032,283250688,-1002084352,2312953856,-3400796160,2840893440,-790957056,-426958848,82725888]),(⟨3,0,1⟩,[-1024,27648,-326656,2743296,-19740672,106285056,-381110272,884131840,-1273021440,985041920,-237878272,-74540032]),(⟨3,0,2⟩,[0,-2048,98304,-1626112,12734464,-52781056,120229888,-137605120,36630528,46262272,5419008]),(⟨3,0,3⟩,[-4096,102400,-1003520,4526080,-5795840,-30429184,150081536,-271306752,188596224,2981888]),(⟨3,0,4⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨3,0,5⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨3,0,6⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨3,1,0⟩,[-1024,27648,-359424,3685376,-30668800,174671872,-638027776,1485801472,-2132149248,1629817856,-312540160,-251560960]),(⟨3,1,1⟩,[0,24576,-636928,6905856,-41140224,147726336,-331378688,448274432,-276627456,-104071168,205449216]),(⟨3,1,3⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨3,1,4⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,2,0⟩,[0,-2048,163840,-3076096,24981504,-104071168,237367296,-281153536,99192832,88410112,-19869696]),(⟨3,2,3⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨3,3,0⟩,[-4096,102400,-987136,3870720,2052096,-72667136,268816384,-446222336,290586624,21561344]),(⟨3,3,1⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨3,3,2⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨3,3,3⟩,[0,-98304,1474560,-6488064,5308416,22315008,-35094528]),(⟨3,4,0⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨3,4,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,5,0⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨3,6,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨4,0,0⟩,[0,-8192,201728,-1453056,-1191936,68677632,-403728384,1189738496,-1995960320,1768067072,-468487168,-264907776]),(⟨4,0,1⟩,[0,8192,-159744,1372160,-8138752,37171200,-116330496,221073408,-202280960,-35229696,169623552]),(⟨4,0,3⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨4,0,4⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨4,1,0⟩,[0,8192,-159744,1372160,-8138752,37171200,-116330496,221073408,-202280960,-35229696,169623552]),(⟨4,1,1⟩,[0,4096,-192512,3092480,-23687168,97570816,-227364864,285315072,-137777152,-26320896]),(⟨4,1,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨4,1,4⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨4,3,0⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨4,3,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨4,4,0⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨4,4,1⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨5,0,0⟩,[0,-2048,163840,-3076096,24981504,-104071168,237367296,-281153536,99192832,88410112,-19869696]),(⟨5,0,3⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨5,3,0⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨6,0,0⟩,[0,0,16384,-655360,7847936,-42237952,118734848,-174915584,101990400,18579456]),(⟨6,0,3⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨6,3,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,-8192,291840,-4630528,43634688,-274275328,1218836480,-3935666176,9289601024,-15783782400,18416800768,-13072447488,3432316928,1941373952,-1405050880,208502784]),(⟨0,0,1⟩,[0,-4096,207872,-4151296,45609984,-316672000,1492641792,-4951023616,11672958976,-19255627776,21011745792,-12875384832,1508201472,2786486272,-913661952]),(⟨0,0,2⟩,[0,16384,-514048,6700032,-47513600,199623680,-486715392,489338880,805961728,-3612956672,5482956800,-3598726144,45760512,778982400]),(⟨0,0,3⟩,[0,6144,-367616,7135232,-69075968,392359936,-1414248448,3326377984,-4992903168,4275976192,-1237019648,-711892992,239102976]),(⟨0,0,4⟩,[0,-8192,201728,-1453056,-1191936,68677632,-403728384,1189738496,-1995960320,1768067072,-468487168,-264907776]),(⟨0,0,5⟩,[0,-2048,163840,-3076096,24981504,-104071168,237367296,-281153536,99192832,88410112,-19869696]),(⟨0,0,6⟩,[0,0,16384,-655360,7847936,-42237952,118734848,-174915584,101990400,18579456]),(⟨0,1,0⟩,[0,-4096,207872,-4151296,45609984,-316672000,1492641792,-4951023616,11672958976,-19255627776,21011745792,-12875384832,1508201472,2786486272,-913661952]),(⟨0,1,1⟩,[1024,-29696,441344,-4965376,44122112,-286969856,1313478656,-4199483392,9295897600,-13774787584,12354104320,-4455724032,-2094458880,1946785792]),(⟨0,1,2⟩,[0,-2048,-48128,1871872,-20483072,111910912,-348194816,623988736,-560728064,99706880,-37223424,716513280,-813804544]),(⟨0,1,3⟩,[-1024,27648,-359424,3685376,-30668800,174671872,-638027776,1485801472,-2132149248,1629817856,-312540160,-251560960]),(⟨0,1,4⟩,[0,8192,-159744,1372160,-8138752,37171200,-116330496,221073408,-202280960,-35229696,169623552]),(⟨0,2,0⟩,[0,16384,-514048,6700032,-47513600,199623680,-486715392,489338880,805961728,-3612956672,5482956800,-3598726144,45760512,778982400]),(⟨0,2,1⟩,[0,-2048,-48128,1871872,-20483072,111910912,-348194816,623988736,-560728064,99706880,-37223424,716513280,-813804544]),(⟨0,2,2⟩,[0,-18432,546816,-6438912,38830080,-130478080,248623104,-233807872,-19808256,294418432,-317212672,188260352]),(⟨0,2,3⟩,[0,-2048,163840,-3076096,24981504,-104071168,237367296,-281153536,99192832,88410112,-19869696]),(⟨0,3,0⟩,[0,6144,-367616,7135232,-69075968,392359936,-1414248448,3326377984,-4992903168,4275976192,-1237019648,-711892992,239102976]),(⟨0,3,1⟩,[-1024,27648,-359424,3685376,-30668800,174671872,-638027776,1485801472,-2132149248,1629817856,-312540160,-251560960]),(⟨0,3,2⟩,[0,-2048,163840,-3076096,24981504,-104071168,237367296,-281153536,99192832,88410112,-19869696]),(⟨0,3,3⟩,[-4096,102400,-987136,3870720,2052096,-72667136,268816384,-446222336,290586624,21561344]),(⟨0,3,4⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨0,3,5⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨0,3,6⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨0,4,0⟩,[0,-8192,201728,-1453056,-1191936,68677632,-403728384,1189738496,-1995960320,1768067072,-468487168,-264907776]),(⟨0,4,1⟩,[0,8192,-159744,1372160,-8138752,37171200,-116330496,221073408,-202280960,-35229696,169623552]),(⟨0,4,3⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨0,4,4⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨0,5,0⟩,[0,-2048,163840,-3076096,24981504,-104071168,237367296,-281153536,99192832,88410112,-19869696]),(⟨0,5,3⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨0,6,0⟩,[0,0,16384,-655360,7847936,-42237952,118734848,-174915584,101990400,18579456]),(⟨0,6,3⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨1,0,0⟩,[0,-4096,207872,-4151296,45609984,-316672000,1492641792,-4951023616,11672958976,-19255627776,21011745792,-12875384832,1508201472,2786486272,-913661952]),(⟨1,0,1⟩,[1024,-29696,441344,-4965376,44122112,-286969856,1313478656,-4199483392,9295897600,-13774787584,12354104320,-4455724032,-2094458880,1946785792]),(⟨1,0,2⟩,[0,-2048,-48128,1871872,-20483072,111910912,-348194816,623988736,-560728064,99706880,-37223424,716513280,-813804544]),(⟨1,0,3⟩,[-1024,27648,-359424,3685376,-30668800,174671872,-638027776,1485801472,-2132149248,1629817856,-312540160,-251560960]),(⟨1,0,4⟩,[0,8192,-159744,1372160,-8138752,37171200,-116330496,221073408,-202280960,-35229696,169623552]),(⟨1,1,0⟩,[1024,-29696,441344,-4965376,44122112,-286969856,1313478656,-4199483392,9295897600,-13774787584,12354104320,-4455724032,-2094458880,1946785792]),(⟨1,1,1⟩,[0,-34816,989184,-12544000,95240192,-480563200,1669574656,-3973025792,6168657920,-5270808576,328726528,3933108224,-2836807680]),(⟨1,1,2⟩,[-1024,15360,84992,-3267584,30107648,-151877632,485238784,-999966720,1247501312,-675791872,-406074368,662774784]),(⟨1,1,3⟩,[0,24576,-636928,6905856,-41140224,147726336,-331378688,448274432,-276627456,-104071168,205449216]),(⟨1,1,4⟩,[0,4096,-192512,3092480,-23687168,97570816,-227364864,285315072,-137777152,-26320896]),(⟨1,2,0⟩,[0,-2048,-48128,1871872,-20483072,111910912,-348194816,623988736,-560728064,99706880,-37223424,716513280,-813804544]),(⟨1,2,1⟩,[-1024,15360,84992,-3267584,30107648,-151877632,485238784,-999966720,1247501312,-675791872,-406074368,662774784]),(⟨1,2,2⟩,[2048,-53248,559104,-3194880,11415552,-25600000,25833472,34258944,-174798848,296841216,-203012096]),(⟨1,3,0⟩,[-1024,27648,-359424,3685376,-30668800,174671872,-638027776,1485801472,-2132149248,1629817856,-312540160,-251560960]),(⟨1,3,1⟩,[0,24576,-636928,6905856,-41140224,147726336,-331378688,448274432,-276627456,-104071168,205449216]),(⟨1,3,3⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨1,3,4⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨1,4,0⟩,[0,8192,-159744,1372160,-8138752,37171200,-116330496,221073408,-202280960,-35229696,169623552]),(⟨1,4,1⟩,[0,4096,-192512,3092480,-23687168,97570816,-227364864,285315072,-137777152,-26320896]),(⟨1,4,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨1,4,4⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨2,0,0⟩,[0,16384,-514048,6700032,-47513600,199623680,-486715392,489338880,805961728,-3612956672,5482956800,-3598726144,45760512,778982400]),(⟨2,0,1⟩,[0,-2048,-48128,1871872,-20483072,111910912,-348194816,623988736,-560728064,99706880,-37223424,716513280,-813804544]),(⟨2,0,2⟩,[0,-18432,546816,-6438912,38830080,-130478080,248623104,-233807872,-19808256,294418432,-317212672,188260352]),(⟨2,0,3⟩,[0,-2048,163840,-3076096,24981504,-104071168,237367296,-281153536,99192832,88410112,-19869696]),(⟨2,1,0⟩,[0,-2048,-48128,1871872,-20483072,111910912,-348194816,623988736,-560728064,99706880,-37223424,716513280,-813804544]),(⟨2,1,1⟩,[-1024,15360,84992,-3267584,30107648,-151877632,485238784,-999966720,1247501312,-675791872,-406074368,662774784]),(⟨2,1,2⟩,[2048,-53248,559104,-3194880,11415552,-25600000,25833472,34258944,-174798848,296841216,-203012096]),(⟨2,2,0⟩,[0,-18432,546816,-6438912,38830080,-130478080,248623104,-233807872,-19808256,294418432,-317212672,188260352]),(⟨2,2,1⟩,[2048,-53248,559104,-3194880,11415552,-25600000,25833472,34258944,-174798848,296841216,-203012096]),(⟨2,3,0⟩,[0,-2048,163840,-3076096,24981504,-104071168,237367296,-281153536,99192832,88410112,-19869696]),(⟨2,3,3⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨3,0,0⟩,[0,6144,-367616,7135232,-69075968,392359936,-1414248448,3326377984,-4992903168,4275976192,-1237019648,-711892992,239102976]),(⟨3,0,1⟩,[-1024,27648,-359424,3685376,-30668800,174671872,-638027776,1485801472,-2132149248,1629817856,-312540160,-251560960]),(⟨3,0,2⟩,[0,-2048,163840,-3076096,24981504,-104071168,237367296,-281153536,99192832,88410112,-19869696]),(⟨3,0,3⟩,[-4096,102400,-987136,3870720,2052096,-72667136,268816384,-446222336,290586624,21561344]),(⟨3,0,4⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨3,0,5⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨3,0,6⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨3,1,0⟩,[-1024,27648,-359424,3685376,-30668800,174671872,-638027776,1485801472,-2132149248,1629817856,-312540160,-251560960]),(⟨3,1,1⟩,[0,24576,-636928,6905856,-41140224,147726336,-331378688,448274432,-276627456,-104071168,205449216]),(⟨3,1,3⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨3,1,4⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,2,0⟩,[0,-2048,163840,-3076096,24981504,-104071168,237367296,-281153536,99192832,88410112,-19869696]),(⟨3,2,3⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨3,3,0⟩,[-4096,102400,-987136,3870720,2052096,-72667136,268816384,-446222336,290586624,21561344]),(⟨3,3,1⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨3,3,2⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨3,3,3⟩,[0,-98304,1474560,-6488064,5308416,22315008,-35094528]),(⟨3,4,0⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨3,4,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨3,5,0⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨3,6,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨4,0,0⟩,[0,-8192,201728,-1453056,-1191936,68677632,-403728384,1189738496,-1995960320,1768067072,-468487168,-264907776]),(⟨4,0,1⟩,[0,8192,-159744,1372160,-8138752,37171200,-116330496,221073408,-202280960,-35229696,169623552]),(⟨4,0,3⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨4,0,4⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨4,1,0⟩,[0,8192,-159744,1372160,-8138752,37171200,-116330496,221073408,-202280960,-35229696,169623552]),(⟨4,1,1⟩,[0,4096,-192512,3092480,-23687168,97570816,-227364864,285315072,-137777152,-26320896]),(⟨4,1,3⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨4,1,4⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨4,3,0⟩,[0,24576,-475136,3350528,-10354688,9216000,24887296,-68952064,50692096]),(⟨4,3,1⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨4,4,0⟩,[0,8192,-180224,1368064,-3833856,253952,14761984,-16572416]),(⟨4,4,1⟩,[-8192,180224,-1368064,3833856,-253952,-14761984,16572416]),(⟨5,0,0⟩,[0,-2048,163840,-3076096,24981504,-104071168,237367296,-281153536,99192832,88410112,-19869696]),(⟨5,0,3⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨5,3,0⟩,[4096,-94208,741376,-2109440,-118784,9023488,-8228864,-3411968]),(⟨6,0,0⟩,[0,0,16384,-655360,7847936,-42237952,118734848,-174915584,101990400,18579456]),(⟨6,0,3⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176]),(⟨6,3,0⟩,[0,-32768,491520,-2162688,1769472,7438336,-11698176])]


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
    (Poly.add (Poly.scale (K.ofRat r465) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 9 10).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r463*r464 : ℚ)=r465 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 9 10 r463 r464 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 9=10 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 9 10).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C136

#print axioms Coulomb8.Columns.C136.sound
