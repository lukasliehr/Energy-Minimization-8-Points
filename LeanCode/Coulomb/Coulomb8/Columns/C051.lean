import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C051

def r0 : ℚ := { num := -384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 1248, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -83520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 453888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -229056, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 570432, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -1047360, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 9638016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := -7456320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := 1103136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 2006016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -285312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -448, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 34176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -221504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 957888, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -2946368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := 6747968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := -11692224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := 14564800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := -10983040, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := 2711360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 1223168, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := 160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := -3520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := 32608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := -10880, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := 755456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -329728, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 5279104, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -9017216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 10777952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -7229504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 200928, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 7424, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -8320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 249216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := -93952, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := 1135616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -1223552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := 5504, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 2093440, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -2098176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := -32, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := 11456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -92416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 401088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -1120576, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 2248256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -466944, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 2821696, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -721824, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -1728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := -320, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := 3776, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := -270016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 40128, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -1175872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 137920, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := 64, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := -7680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := 41920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := -105984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := 197952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -267264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 4416, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -384, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := 15616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := -40192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := 84608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := -123008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := 64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -128, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 26944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -178176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 740736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -2179840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 5012352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -1298432, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 11450944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -8047744, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 295616, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 128, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := -1920, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := 36224, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := -8832, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -310400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 1370240, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -3149184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := 3940096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := -304128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := 512, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -34560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 10240, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -556544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 1238528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := -1850624, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := 1524736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := -368000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := -64, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := 1856, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := -16064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := 63936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := -10176, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 449728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -114880, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 86976, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := 1024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := -12288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := 30720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := 36864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := -320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := 5760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := -2304, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := 147584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := -23168, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := 779136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := -950016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := 335232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := 60992, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := 384, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := -5760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := 27520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := -6016, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := -2944, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := 337024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := -690560, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := 79232, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := -6912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := 4928, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := -10240, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := 3904, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 33536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -22080, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := -256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := 3328, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := -1536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := -1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := 39680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := 3072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -9216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 256, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -5632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 36608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := -111616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := 249600, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := -415232, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := 246016, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 1536, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -152064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 348672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := -47616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := -1181184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := 1921536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 8192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -2560, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := 12288, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 27136, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -53248, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := -13312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := 6144, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 6144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := -158720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := 12672, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := -29056, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := 3968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := 98432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := -160128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -6144, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := 1920, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -9216, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := -20352, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := 39936, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := -192, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := 624, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := -41760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := 226944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -114528, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 285216, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -523680, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 4819008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := -3728160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := 551568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := 1003008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := -142656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := -224, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := 17088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := -110752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := 478944, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := -1473184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := 3373984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := -5846112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := 7282400, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := -5491520, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := 1355680, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := 611584, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := 80, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := -1760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := 16304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := -5440, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := 377728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := -164864, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := 2639552, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := -4508608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := 5388976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -3614752, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := 100464, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := 3712, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := -4160, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := 124608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := -46976, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := 567808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := -611776, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := 2752, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := 1046720, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := -1049088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := -16, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 5728, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := -46208, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := 200544, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := -560288, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := 1124128, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := -233472, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := 1410848, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := -360912, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := 96, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := -864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := -160, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := 1888, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := -135008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := 20064, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := -587936, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 68960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := 32, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := -3840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 20960, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := -52992, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := 98976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := -133632, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := 2208, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := -192, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := 7808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := -20096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := 42304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := -61504, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := 32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := -64, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := 13472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := -89088, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := 370368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := -1089920, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := 2506176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := -649216, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := 5725472, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := -4023872, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := 147808, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := 64, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := -960, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := 18112, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := -4416, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := -155200, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := 685120, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -1574592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := 1970048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := -152064, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := 256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := -17280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := 5120, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := -278272, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 619264, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := -925312, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := 762368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := -184000, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := -32, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := 928, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := -8032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := 31968, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := -5088, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := 224864, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := -57440, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := 43488, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := 512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := 15360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := 18432, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -160, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := 2880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -1152, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 73792, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -11584, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 389568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -475008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := 167616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := 30496, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -2880, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := 13760, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := -3008, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := -1472, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := 168512, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := -345280, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := 39616, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := -3456, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := 2464, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := -5120, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := 1952, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 16768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -11040, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 1664, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := -768, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := -768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := 19840, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 1536, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := -4608, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := -2816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := 18304, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := -55808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := 124800, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := -207616, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := 123008, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := 768, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := -76032, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := 174336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := -23808, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -590592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := 960768, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := 4096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := -1280, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := 13568, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := -26624, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := -6656, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := 3072, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -79360, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 6336, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -14528, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 1984, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := 49216, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := -80064, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := -3072, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := 960, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := -4608, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := -10176, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := 19968, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := 1, den := 4, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := 1, den := 476, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[0,r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11],[r12,r13,r14,r15,r16,r17,r18,r19,r20,r21,r22,r23],[r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34],[r0,r35,r36,r37,r38,r39,r40,r41,r42,r43],[r44,r45,r46,r47,r48,r49,r50,r51,r52],[r53,r54,r55,r56,r57,r58,r59,r60],[r61,r62,r63,r64,r65,r66,r67],[r12,r68,r69,r70,r71,r72],[],[],[],[],[],[r73,r74,r75,r76,r77,r78,r79,r80,r81,r82,r83],[r84,r85,r86,r87,r88,r89,r90,r91,r92,r93],[r84,r94,r95,r96,r97,r98,r99,r100,r101],[r102,r103,r104,r105,r106,r107,r108,r109],[0,0,r110,r111,r112,r113,-1024],[],[],[],[],[],[],[r114,r115,r116,r117,r118,r119,r120,r121,r122],[r123,r124,r125,r126,r127,r128,r129,r130],[r61,r131,r132,r133,r134,r135,r136],[r137,r138,r139,r140,r141,-256],[r137,r142,r62,r143,256],[],[],[],[],[r144,r145,r146,r147,r148,r149,r150],[r12,r68,r69,r70,r71,r72],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[0,0,r140,r151,r152,r153,r154,r155,r156,-7680],[0,0,r157,r158,r159,r160,r161,r162,3584],[0,0,r110,r163,r164,r165,r166,1024],[0,0,r110,r111,r112,r113,-1024],[],[],[],[],[],[],[r12,r74,r167,r168,r169,r170,r171,640],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[r123,r172,r173,r174,r175,r176,-2688],[r137,r138,r139,r140,r141,-256],[r137,r142,r62,r143,256],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[0,r177,r178,r179,r180,r181,r182,r183,r184,r185,r186,r187,r188]),(⟨0,0,1⟩,[r73,r189,r190,r191,r192,r193,r194,r195,r196,r197,r198,r199]),(⟨0,0,2⟩,[r200,r201,r202,r203,r204,r205,r206,r207,r208,r209,r210]),(⟨0,0,3⟩,[r177,r211,r212,r213,r214,r215,r216,r217,r218,r219]),(⟨0,0,4⟩,[r220,r221,r222,r223,r224,r225,r226,r227,r228]),(⟨0,0,5⟩,[r229,r230,r231,r232,r233,r234,r235,r236]),(⟨0,0,6⟩,[r237,r238,r239,r240,r241,r242,r243]),(⟨0,0,7⟩,[r73,r244,r245,r246,r247,r248]),(⟨0,1,0⟩,[r73,r189,r190,r191,r192,r193,r194,r195,r196,r197,r198,r199]),(⟨0,1,1⟩,[r249,r250,r251,r252,r253,r254,r255,r256,r257,r258,r259]),(⟨0,1,2⟩,[r102,r260,r261,r262,r263,r264,r265,r266,r267,r268]),(⟨0,1,3⟩,[r102,r269,r270,r271,r272,r273,r274,r275,r276]),(⟨0,1,4⟩,[r277,r278,r279,r280,r281,r282,r283,r284]),(⟨0,1,5⟩,[0,0,r285,r172,r286,r287,-512]),(⟨0,2,0⟩,[r200,r201,r202,r203,r204,r205,r206,r207,r208,r209,r210]),(⟨0,2,1⟩,[r102,r260,r261,r262,r263,r264,r265,r266,r267,r268]),(⟨0,2,2⟩,[r288,r289,r290,r291,r292,r293,r294,r295,r296]),(⟨0,2,3⟩,[r53,r297,r298,r299,r300,r301,r302,r303]),(⟨0,2,4⟩,[r237,r304,r305,r306,r307,r308,r309]),(⟨0,2,5⟩,[r84,r310,r311,r312,r313,-128]),(⟨0,2,6⟩,[r84,r314,r238,r315,128]),(⟨0,3,0⟩,[r177,r211,r212,r213,r214,r215,r216,r217,r218,r219]),(⟨0,3,1⟩,[r102,r269,r270,r271,r272,r273,r274,r275,r276]),(⟨0,3,2⟩,[r53,r297,r298,r299,r300,r301,r302,r303]),(⟨0,3,3⟩,[r12,r316,r317,r318,r319,r320,r321]),(⟨0,3,4⟩,[r73,r244,r245,r246,r247,r248]),(⟨0,4,0⟩,[r220,r221,r222,r223,r224,r225,r226,r227,r228]),(⟨0,4,1⟩,[r277,r278,r279,r280,r281,r282,r283,r284]),(⟨0,4,2⟩,[r237,r304,r305,r306,r307,r308,r309]),(⟨0,4,3⟩,[r73,r244,r245,r246,r247,r248]),(⟨0,5,0⟩,[r229,r230,r231,r232,r233,r234,r235,r236]),(⟨0,5,1⟩,[0,0,r285,r172,r286,r287,-512]),(⟨0,5,2⟩,[r84,r310,r311,r312,r313,-128]),(⟨0,6,0⟩,[r237,r238,r239,r240,r241,r242,r243]),(⟨0,6,2⟩,[r84,r314,r238,r315,128]),(⟨0,7,0⟩,[r73,r244,r245,r246,r247,r248]),(⟨1,0,0⟩,[r73,r189,r190,r191,r192,r193,r194,r195,r196,r197,r198,r199]),(⟨1,0,1⟩,[r249,r250,r251,r252,r253,r254,r255,r256,r257,r258,r259]),(⟨1,0,2⟩,[r102,r260,r261,r262,r263,r264,r265,r266,r267,r268]),(⟨1,0,3⟩,[r102,r269,r270,r271,r272,r273,r274,r275,r276]),(⟨1,0,4⟩,[r277,r278,r279,r280,r281,r282,r283,r284]),(⟨1,0,5⟩,[0,0,r285,r172,r286,r287,-512]),(⟨1,1,0⟩,[r249,r250,r251,r252,r253,r254,r255,r256,r257,r258,r259]),(⟨1,1,1⟩,[0,0,r312,r322,r323,r324,r325,r326,r327,-3840]),(⟨1,1,2⟩,[0,0,r137,r328,r329,r164,r330,r331,1792]),(⟨1,1,3⟩,[0,0,r285,r332,r333,r142,r334,512]),(⟨1,1,4⟩,[0,0,r285,r172,r286,r287,-512]),(⟨1,2,0⟩,[r102,r260,r261,r262,r263,r264,r265,r266,r267,r268]),(⟨1,2,1⟩,[0,0,r137,r328,r329,r164,r330,r331,1792]),(⟨1,2,2⟩,[r73,r250,r335,r336,r337,r338,r339,320]),(⟨1,3,0⟩,[r102,r269,r270,r271,r272,r273,r274,r275,r276]),(⟨1,3,1⟩,[0,0,r285,r332,r333,r142,r334,512]),(⟨1,4,0⟩,[r277,r278,r279,r280,r281,r282,r283,r284]),(⟨1,4,1⟩,[0,0,r285,r172,r286,r287,-512]),(⟨1,5,0⟩,[0,0,r285,r172,r286,r287,-512]),(⟨2,0,0⟩,[r200,r201,r202,r203,r204,r205,r206,r207,r208,r209,r210]),(⟨2,0,1⟩,[r102,r260,r261,r262,r263,r264,r265,r266,r267,r268]),(⟨2,0,2⟩,[r288,r289,r290,r291,r292,r293,r294,r295,r296]),(⟨2,0,3⟩,[r53,r297,r298,r299,r300,r301,r302,r303]),(⟨2,0,4⟩,[r237,r304,r305,r306,r307,r308,r309]),(⟨2,0,5⟩,[r84,r310,r311,r312,r313,-128]),(⟨2,0,6⟩,[r84,r314,r238,r315,128]),(⟨2,1,0⟩,[r102,r260,r261,r262,r263,r264,r265,r266,r267,r268]),(⟨2,1,1⟩,[0,0,r137,r328,r329,r164,r330,r331,1792]),(⟨2,1,2⟩,[r73,r250,r335,r336,r337,r338,r339,320]),(⟨2,2,0⟩,[r288,r289,r290,r291,r292,r293,r294,r295,r296]),(⟨2,2,1⟩,[r73,r250,r335,r336,r337,r338,r339,320]),(⟨2,2,2⟩,[r53,r340,r341,r342,r343,r344,-1344]),(⟨2,2,3⟩,[r84,r310,r311,r312,r313,-128]),(⟨2,2,4⟩,[r84,r314,r238,r315,128]),(⟨2,3,0⟩,[r53,r297,r298,r299,r300,r301,r302,r303]),(⟨2,3,2⟩,[r84,r310,r311,r312,r313,-128]),(⟨2,4,0⟩,[r237,r304,r305,r306,r307,r308,r309]),(⟨2,4,2⟩,[r84,r314,r238,r315,128]),(⟨2,5,0⟩,[r84,r310,r311,r312,r313,-128]),(⟨2,6,0⟩,[r84,r314,r238,r315,128]),(⟨3,0,0⟩,[r177,r211,r212,r213,r214,r215,r216,r217,r218,r219]),(⟨3,0,1⟩,[r102,r269,r270,r271,r272,r273,r274,r275,r276]),(⟨3,0,2⟩,[r53,r297,r298,r299,r300,r301,r302,r303]),(⟨3,0,3⟩,[r12,r316,r317,r318,r319,r320,r321]),(⟨3,0,4⟩,[r73,r244,r245,r246,r247,r248]),(⟨3,1,0⟩,[r102,r269,r270,r271,r272,r273,r274,r275,r276]),(⟨3,1,1⟩,[0,0,r285,r332,r333,r142,r334,512]),(⟨3,2,0⟩,[r53,r297,r298,r299,r300,r301,r302,r303]),(⟨3,2,2⟩,[r84,r310,r311,r312,r313,-128]),(⟨3,3,0⟩,[r12,r316,r317,r318,r319,r320,r321]),(⟨3,4,0⟩,[r73,r244,r245,r246,r247,r248]),(⟨4,0,0⟩,[r220,r221,r222,r223,r224,r225,r226,r227,r228]),(⟨4,0,1⟩,[r277,r278,r279,r280,r281,r282,r283,r284]),(⟨4,0,2⟩,[r237,r304,r305,r306,r307,r308,r309]),(⟨4,0,3⟩,[r73,r244,r245,r246,r247,r248]),(⟨4,1,0⟩,[r277,r278,r279,r280,r281,r282,r283,r284]),(⟨4,1,1⟩,[0,0,r285,r172,r286,r287,-512]),(⟨4,2,0⟩,[r237,r304,r305,r306,r307,r308,r309]),(⟨4,2,2⟩,[r84,r314,r238,r315,128]),(⟨4,3,0⟩,[r73,r244,r245,r246,r247,r248]),(⟨5,0,0⟩,[r229,r230,r231,r232,r233,r234,r235,r236]),(⟨5,0,1⟩,[0,0,r285,r172,r286,r287,-512]),(⟨5,0,2⟩,[r84,r310,r311,r312,r313,-128]),(⟨5,1,0⟩,[0,0,r285,r172,r286,r287,-512]),(⟨5,2,0⟩,[r84,r310,r311,r312,r313,-128]),(⟨6,0,0⟩,[r237,r238,r239,r240,r241,r242,r243]),(⟨6,0,2⟩,[r84,r314,r238,r315,128]),(⟨6,2,0⟩,[r84,r314,r238,r315,128]),(⟨7,0,0⟩,[r73,r244,r245,r246,r247,r248])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[0,3,-12,9,6]),(⟨0,0,1⟩,[-1,5,-9,5]),(⟨0,0,2⟩,[-1,4,-7]),(⟨0,0,3⟩,[2,-2]),(⟨0,0,4⟩,[2]),(⟨0,1,0⟩,[-1,5,-9,5]),(⟨0,2,0⟩,[-1,4,-7]),(⟨0,3,0⟩,[2,-2]),(⟨0,4,0⟩,[2]),(⟨1,0,0⟩,[-1,5,-9,5]),(⟨2,0,0⟩,[-1,4,-7]),(⟨3,0,0⟩,[2,-2]),(⟨4,0,0⟩,[2])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[-256,4800,-35712,145856,-387968,744000,-1039488,811328,-95104]),(⟨0,0,1⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨0,0,2⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨0,0,3⟩,[128,-2688,15616,-40192,84608,-123008]),(⟨0,1,0⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨0,1,1⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨0,2,0⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨0,2,2⟩,[-256,3072,-7680,-9216,30464]),(⟨0,3,0⟩,[128,-2688,15616,-40192,84608,-123008]),(⟨1,0,0⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨1,0,1⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨1,1,0⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨2,0,0⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨2,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨2,2,0⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[128,-2688,15616,-40192,84608,-123008])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 0 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r345) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 6 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r346) sourceRight))).isZero := by decide +kernel

noncomputable def partial13 : Poly := []

theorem partial_sound13 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 13)
      sourceRight).eval u v t=partial13.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨4,0,0⟩,[2])]

noncomputable def partial12 : Poly := [(⟨4,0,0⟩,[-512,9600,-71424,291712,-775936,1488000,-2078976,1622656,-190208]),(⟨4,0,1⟩,[-128,3712,-34176,154496,-432000,887168,-1290880,973952]),(⟨4,0,2⟩,[640,-9728,47232,-100352,146304,-119296,-95872]),(⟨4,0,3⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨4,1,0⟩,[-128,3712,-34176,154496,-432000,887168,-1290880,973952]),(⟨4,1,1⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨4,2,0⟩,[640,-9728,47232,-100352,146304,-119296,-95872]),(⟨4,2,2⟩,[-512,6144,-15360,-18432,60928]),(⟨4,3,0⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨5,0,0⟩,[-128,3712,-34176,154496,-432000,887168,-1290880,973952]),(⟨5,0,1⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨5,1,0⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨6,0,0⟩,[640,-9728,47232,-100352,146304,-119296,-95872]),(⟨6,0,2⟩,[-512,6144,-15360,-18432,60928]),(⟨6,2,0⟩,[-512,6144,-15360,-18432,60928]),(⟨7,0,0⟩,[256,-5376,31232,-80384,169216,-246016])]


theorem partial_checked12 :
    (Poly.add (Poly.add (Poly.mul chunk12 sourceRight) partial13)
      (Poly.scale (K.ofRat (-1)) partial12)).isZero := by decide +kernel

theorem partial_sound12 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 12)
      sourceRight).eval u v t=partial12.eval u v t := by
  change (Poly.mul (chunk12++(sourceLeft.drop 13))
    sourceRight).eval u v t=partial12.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound13 partial_checked12 u v t


noncomputable def chunk8 : Poly := [(⟨0,4,0⟩,[2]),(⟨1,0,0⟩,[-1,5,-9,5]),(⟨2,0,0⟩,[-1,4,-7]),(⟨3,0,0⟩,[2,-2])]

noncomputable def partial8 : Poly := [(⟨0,4,0⟩,[-512,9600,-71424,291712,-775936,1488000,-2078976,1622656,-190208]),(⟨0,4,1⟩,[-128,3712,-34176,154496,-432000,887168,-1290880,973952]),(⟨0,4,2⟩,[640,-9728,47232,-100352,146304,-119296,-95872]),(⟨0,4,3⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨0,5,0⟩,[-128,3712,-34176,154496,-432000,887168,-1290880,973952]),(⟨0,5,1⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨0,6,0⟩,[640,-9728,47232,-100352,146304,-119296,-95872]),(⟨0,6,2⟩,[-512,6144,-15360,-18432,60928]),(⟨0,7,0⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨1,0,0⟩,[256,-6080,62016,-368896,1462656,-4175104,8980480,-14644608,17227136,-12974912,4912576,-475520]),(⟨1,0,1⟩,[64,-2176,26944,-179712,765312,-2304256,5193600,-8786432,10461760,-7609984,2434880]),(⟨1,0,2⟩,[-320,6464,-50816,213632,-560896,995072,-1159552,662912,133184,-239680]),(⟨1,0,3⟩,[-128,3328,-30208,143104,-439552,985856,-1577472,1530112,-615040]),(⟨1,1,0⟩,[64,-2176,26944,-179712,765312,-2304256,5193600,-8786432,10461760,-7609984,2434880]),(⟨1,1,1⟩,[0,0,-1024,17408,-101376,232448,-31744,-787456,1281024,-609280]),(⟨1,2,0⟩,[-320,6464,-50816,213632,-560896,995072,-1159552,662912,133184,-239680]),(⟨1,2,2⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨1,3,0⟩,[-128,3328,-30208,143104,-439552,985856,-1577472,1530112,-615040]),(⟨1,4,0⟩,[-128,3712,-34176,154496,-432000,887168,-1290880,973952]),(⟨1,4,1⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨1,5,0⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨2,0,0⟩,[320,-8000,83648,-502016,1986688,-5621120,11924864,-18963712,21078592,-13669696,3100608]),(⟨2,0,1⟩,[64,-2112,23936,-141184,543232,-1615872,3900032,-6961280,7747008,-4018112]),(⟨2,0,2⟩,[-320,6144,-45312,178688,-439168,703488,-702720,225792,335552]),(⟨2,0,3⟩,[-128,3200,-27264,121472,-354688,742784,-1084288,861056]),(⟨2,1,0⟩,[64,-2112,23936,-141184,543232,-1615872,3900032,-6961280,7747008,-4018112]),(⟨2,1,1⟩,[0,0,-1024,16384,-87040,172032,54272,-745472,852992]),(⟨2,2,0⟩,[-320,6144,-45312,178688,-439168,703488,-702720,225792,335552]),(⟨2,2,2⟩,[256,-4096,21760,-43008,-13568,186368,-213248]),(⟨2,3,0⟩,[-128,3200,-27264,121472,-354688,742784,-1084288,861056]),(⟨2,4,0⟩,[640,-9728,47232,-100352,146304,-119296,-95872]),(⟨2,4,2⟩,[-512,6144,-15360,-18432,60928]),(⟨2,6,0⟩,[-512,6144,-15360,-18432,60928]),(⟨3,0,0⟩,[-768,14464,-106880,418176,-983936,1410688,-794752,-1809280,4786304,-3458304]),(⟨3,0,1⟩,[-128,3840,-38912,205056,-673536,1491200,-2123776,1519360,-120960]),(⟨3,0,2⟩,[896,-14720,82304,-205696,254592,-68736,-296832,248192]),(⟨3,0,3⟩,[256,-5632,36608,-111616,249600,-415232,246016]),(⟨3,1,0⟩,[-128,3840,-38912,205056,-673536,1491200,-2123776,1519360,-120960]),(⟨3,1,1⟩,[0,0,2048,-26624,86016,12288,-317440,243712]),(⟨3,2,0⟩,[896,-14720,82304,-205696,254592,-68736,-296832,248192]),(⟨3,2,2⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨3,3,0⟩,[256,-5632,36608,-111616,249600,-415232,246016]),(⟨3,4,0⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨4,0,0⟩,[-1088,22912,-184832,802176,-2241152,4496512,-6537216,5643392,-1443648]),(⟨4,0,1⟩,[-128,3712,-32128,127872,-345984,899456,-1608320,1217664]),(⟨4,0,2⟩,[896,-13824,68992,-143360,132736,67072,-309120]),(⟨4,0,3⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨4,1,0⟩,[-128,3712,-32128,127872,-345984,899456,-1608320,1217664]),(⟨4,1,1⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨4,2,0⟩,[896,-13824,68992,-143360,132736,67072,-309120]),(⟨4,2,2⟩,[-512,6144,-15360,-18432,60928]),(⟨4,3,0⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨5,0,0⟩,[384,-3456,-4480,128384,-540032,1364352,-2351744,1930880]),(⟨5,0,1⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨5,0,2⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨5,1,0⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨5,2,0⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨6,0,0⟩,[896,-15360,83840,-211968,395904,-534528,150144]),(⟨6,0,2⟩,[-512,6144,-15360,-18432,60928]),(⟨6,2,0⟩,[-512,6144,-15360,-18432,60928]),(⟨7,0,0⟩,[256,-5376,31232,-80384,169216,-246016])]


theorem partial_checked8 :
    (Poly.add (Poly.add (Poly.mul chunk8 sourceRight) partial12)
      (Poly.scale (K.ofRat (-1)) partial8)).isZero := by decide +kernel

theorem partial_sound8 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 8)
      sourceRight).eval u v t=partial8.eval u v t := by
  change (Poly.mul (chunk8++(sourceLeft.drop 12))
    sourceRight).eval u v t=partial8.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound12 partial_checked8 u v t


noncomputable def chunk4 : Poly := [(⟨0,0,4⟩,[2]),(⟨0,1,0⟩,[-1,5,-9,5]),(⟨0,2,0⟩,[-1,4,-7]),(⟨0,3,0⟩,[2,-2])]

noncomputable def partial4 : Poly := [(⟨0,0,4⟩,[-512,9600,-71424,291712,-775936,1488000,-2078976,1622656,-190208]),(⟨0,0,5⟩,[-128,3712,-34176,154496,-432000,887168,-1290880,973952]),(⟨0,0,6⟩,[640,-9728,47232,-100352,146304,-119296,-95872]),(⟨0,0,7⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨0,1,0⟩,[256,-6080,62016,-368896,1462656,-4175104,8980480,-14644608,17227136,-12974912,4912576,-475520]),(⟨0,1,1⟩,[64,-2176,26944,-179712,765312,-2304256,5193600,-8786432,10461760,-7609984,2434880]),(⟨0,1,2⟩,[-320,6464,-50816,213632,-560896,995072,-1159552,662912,133184,-239680]),(⟨0,1,3⟩,[-128,3328,-30208,143104,-439552,985856,-1577472,1530112,-615040]),(⟨0,1,4⟩,[-128,3712,-34176,154496,-432000,887168,-1290880,973952]),(⟨0,1,5⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨0,2,0⟩,[320,-8000,83648,-502016,1986688,-5621120,11924864,-18963712,21078592,-13669696,3100608]),(⟨0,2,1⟩,[64,-2112,23936,-141184,543232,-1615872,3900032,-6961280,7747008,-4018112]),(⟨0,2,2⟩,[-320,6144,-45312,178688,-439168,703488,-702720,225792,335552]),(⟨0,2,3⟩,[-128,3200,-27264,121472,-354688,742784,-1084288,861056]),(⟨0,2,4⟩,[640,-9728,47232,-100352,146304,-119296,-95872]),(⟨0,2,6⟩,[-512,6144,-15360,-18432,60928]),(⟨0,3,0⟩,[-768,14464,-106880,418176,-983936,1410688,-794752,-1809280,4786304,-3458304]),(⟨0,3,1⟩,[-128,3840,-38912,205056,-673536,1491200,-2123776,1519360,-120960]),(⟨0,3,2⟩,[896,-14720,82304,-205696,254592,-68736,-296832,248192]),(⟨0,3,3⟩,[256,-5632,36608,-111616,249600,-415232,246016]),(⟨0,3,4⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨0,4,0⟩,[-1088,22912,-184832,802176,-2241152,4496512,-6537216,5643392,-1443648]),(⟨0,4,1⟩,[-128,3712,-32128,127872,-345984,899456,-1608320,1217664]),(⟨0,4,2⟩,[896,-13824,68992,-143360,132736,67072,-309120]),(⟨0,4,3⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨0,5,0⟩,[384,-3456,-4480,128384,-540032,1364352,-2351744,1930880]),(⟨0,5,1⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨0,5,2⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨0,6,0⟩,[896,-15360,83840,-211968,395904,-534528,150144]),(⟨0,6,2⟩,[-512,6144,-15360,-18432,60928]),(⟨0,7,0⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨1,0,0⟩,[256,-6080,62016,-368896,1462656,-4175104,8980480,-14644608,17227136,-12974912,4912576,-475520]),(⟨1,0,1⟩,[64,-2176,26944,-179712,765312,-2304256,5193600,-8786432,10461760,-7609984,2434880]),(⟨1,0,2⟩,[-320,6464,-50816,213632,-560896,995072,-1159552,662912,133184,-239680]),(⟨1,0,3⟩,[-128,3328,-30208,143104,-439552,985856,-1577472,1530112,-615040]),(⟨1,0,4⟩,[-128,3712,-34176,154496,-432000,887168,-1290880,973952]),(⟨1,0,5⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨1,1,0⟩,[128,-4352,53888,-359424,1530624,-4608512,10387200,-17572864,20923520,-15219968,4869760]),(⟨1,1,1⟩,[0,0,-2048,34816,-202752,464896,-63488,-1574912,2562048,-1218560]),(⟨1,1,4⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨1,2,0⟩,[-256,4352,-26880,72448,-17664,-620800,2740480,-6298368,7880192,-4257792]),(⟨1,2,1⟩,[0,0,-1024,16384,-87040,172032,54272,-745472,852992]),(⟨1,2,2⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨1,3,0⟩,[-256,7168,-69120,348160,-1113088,2477056,-3701248,3049472,-736000]),(⟨1,3,1⟩,[0,0,2048,-26624,86016,12288,-317440,243712]),(⟨1,4,0⟩,[-128,3712,-32128,127872,-345984,899456,-1608320,1217664]),(⟨1,4,1⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨1,5,0⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨2,0,0⟩,[320,-8000,83648,-502016,1986688,-5621120,11924864,-18963712,21078592,-13669696,3100608]),(⟨2,0,1⟩,[64,-2112,23936,-141184,543232,-1615872,3900032,-6961280,7747008,-4018112]),(⟨2,0,2⟩,[-320,6144,-45312,178688,-439168,703488,-702720,225792,335552]),(⟨2,0,3⟩,[-128,3200,-27264,121472,-354688,742784,-1084288,861056]),(⟨2,0,4⟩,[640,-9728,47232,-100352,146304,-119296,-95872]),(⟨2,0,6⟩,[-512,6144,-15360,-18432,60928]),(⟨2,1,0⟩,[-256,4352,-26880,72448,-17664,-620800,2740480,-6298368,7880192,-4257792]),(⟨2,1,1⟩,[0,0,-1024,16384,-87040,172032,54272,-745472,852992]),(⟨2,1,2⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨2,2,0⟩,[-640,12288,-90624,357376,-878336,1406976,-1405440,451584,671104]),(⟨2,2,2⟩,[512,-8192,43520,-86016,-27136,372736,-426496]),(⟨2,2,4⟩,[-512,6144,-15360,-18432,60928]),(⟨2,3,0⟩,[768,-11520,55040,-84224,-100096,674048,-1381120,1109248]),(⟨2,3,2⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨2,4,0⟩,[896,-13824,68992,-143360,132736,67072,-309120]),(⟨2,4,2⟩,[-512,6144,-15360,-18432,60928]),(⟨2,5,0⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨2,6,0⟩,[-512,6144,-15360,-18432,60928]),(⟨3,0,0⟩,[-768,14464,-106880,418176,-983936,1410688,-794752,-1809280,4786304,-3458304]),(⟨3,0,1⟩,[-128,3840,-38912,205056,-673536,1491200,-2123776,1519360,-120960]),(⟨3,0,2⟩,[896,-14720,82304,-205696,254592,-68736,-296832,248192]),(⟨3,0,3⟩,[256,-5632,36608,-111616,249600,-415232,246016]),(⟨3,0,4⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨3,1,0⟩,[-256,7168,-69120,348160,-1113088,2477056,-3701248,3049472,-736000]),(⟨3,1,1⟩,[0,0,2048,-26624,86016,12288,-317440,243712]),(⟨3,2,0⟩,[768,-11520,55040,-84224,-100096,674048,-1381120,1109248]),(⟨3,2,2⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨3,3,0⟩,[512,-11264,73216,-223232,499200,-830464,492032]),(⟨3,4,0⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨4,0,0⟩,[-1088,22912,-184832,802176,-2241152,4496512,-6537216,5643392,-1443648]),(⟨4,0,1⟩,[-128,3712,-32128,127872,-345984,899456,-1608320,1217664]),(⟨4,0,2⟩,[896,-13824,68992,-143360,132736,67072,-309120]),(⟨4,0,3⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨4,1,0⟩,[-128,3712,-32128,127872,-345984,899456,-1608320,1217664]),(⟨4,1,1⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨4,2,0⟩,[896,-13824,68992,-143360,132736,67072,-309120]),(⟨4,2,2⟩,[-512,6144,-15360,-18432,60928]),(⟨4,3,0⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨5,0,0⟩,[384,-3456,-4480,128384,-540032,1364352,-2351744,1930880]),(⟨5,0,1⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨5,0,2⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨5,1,0⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨5,2,0⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨6,0,0⟩,[896,-15360,83840,-211968,395904,-534528,150144]),(⟨6,0,2⟩,[-512,6144,-15360,-18432,60928]),(⟨6,2,0⟩,[-512,6144,-15360,-18432,60928]),(⟨7,0,0⟩,[256,-5376,31232,-80384,169216,-246016])]


theorem partial_checked4 :
    (Poly.add (Poly.add (Poly.mul chunk4 sourceRight) partial8)
      (Poly.scale (K.ofRat (-1)) partial4)).isZero := by decide +kernel

theorem partial_sound4 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 4)
      sourceRight).eval u v t=partial4.eval u v t := by
  change (Poly.mul (chunk4++(sourceLeft.drop 8))
    sourceRight).eval u v t=partial4.eval u v t
  exact Block.mul_chunk_cached _ _ _ _ _ partial_sound8 partial_checked4 u v t


noncomputable def chunk0 : Poly := [(⟨0,0,0⟩,[0,3,-12,9,6]),(⟨0,0,1⟩,[-1,5,-9,5]),(⟨0,0,2⟩,[-1,4,-7]),(⟨0,0,3⟩,[2,-2])]

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[0,-768,17472,-167040,907776,-3206784,7986048,-14663040,19276032,-14912640,2206272,4012032,-570624]),(⟨0,0,1⟩,[256,-6272,68352,-443008,1915776,-5892736,13495936,-23384448,29129600,-21966080,5422720,2446336]),(⟨0,0,2⟩,[320,-7040,65216,-369920,1510912,-4616192,10558208,-18034432,21555904,-14459008,2812992]),(⟨0,0,3⟩,[-768,14848,-116480,498432,-1315328,2271232,-2447104,187136,4186880,-4196352]),(⟨0,0,4⟩,[-1088,22912,-184832,802176,-2241152,4496512,-6537216,5643392,-1443648]),(⟨0,0,5⟩,[384,-3456,-4480,128384,-540032,1364352,-2351744,1930880]),(⟨0,0,6⟩,[896,-15360,83840,-211968,395904,-534528,150144]),(⟨0,0,7⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨0,1,0⟩,[256,-6272,68352,-443008,1915776,-5892736,13495936,-23384448,29129600,-21966080,5422720,2446336]),(⟨0,1,1⟩,[128,-4352,53888,-356352,1481472,-4359680,10024704,-18178048,22901888,-16095488,4138624]),(⟨0,1,2⟩,[-256,4352,-26880,72448,-17664,-620800,2740480,-6298368,7880192,-4257792]),(⟨0,1,3⟩,[-256,7168,-69120,348160,-1113088,2477056,-3701248,3049472,-736000]),(⟨0,1,4⟩,[-128,3712,-32128,127872,-345984,899456,-1608320,1217664]),(⟨0,1,5⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨0,2,0⟩,[320,-7040,65216,-369920,1510912,-4616192,10558208,-18034432,21555904,-14459008,2812992]),(⟨0,2,1⟩,[-256,4352,-26880,72448,-17664,-620800,2740480,-6298368,7880192,-4257792]),(⟨0,2,2⟩,[-640,11520,-78336,295168,-787712,1558272,-1900032,670464,853888]),(⟨0,2,3⟩,[768,-11520,55040,-84224,-100096,674048,-1381120,1109248]),(⟨0,2,4⟩,[896,-13824,68992,-143360,132736,67072,-309120]),(⟨0,2,5⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨0,2,6⟩,[-512,6144,-15360,-18432,60928]),(⟨0,3,0⟩,[-768,14848,-116480,498432,-1315328,2271232,-2447104,187136,4186880,-4196352]),(⟨0,3,1⟩,[-256,7168,-69120,348160,-1113088,2477056,-3701248,3049472,-736000]),(⟨0,3,2⟩,[768,-11520,55040,-84224,-100096,674048,-1381120,1109248]),(⟨0,3,3⟩,[512,-11264,73216,-223232,499200,-830464,492032]),(⟨0,3,4⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨0,4,0⟩,[-1088,22912,-184832,802176,-2241152,4496512,-6537216,5643392,-1443648]),(⟨0,4,1⟩,[-128,3712,-32128,127872,-345984,899456,-1608320,1217664]),(⟨0,4,2⟩,[896,-13824,68992,-143360,132736,67072,-309120]),(⟨0,4,3⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨0,5,0⟩,[384,-3456,-4480,128384,-540032,1364352,-2351744,1930880]),(⟨0,5,1⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨0,5,2⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨0,6,0⟩,[896,-15360,83840,-211968,395904,-534528,150144]),(⟨0,6,2⟩,[-512,6144,-15360,-18432,60928]),(⟨0,7,0⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨1,0,0⟩,[256,-6272,68352,-443008,1915776,-5892736,13495936,-23384448,29129600,-21966080,5422720,2446336]),(⟨1,0,1⟩,[128,-4352,53888,-356352,1481472,-4359680,10024704,-18178048,22901888,-16095488,4138624]),(⟨1,0,2⟩,[-256,4352,-26880,72448,-17664,-620800,2740480,-6298368,7880192,-4257792]),(⟨1,0,3⟩,[-256,7168,-69120,348160,-1113088,2477056,-3701248,3049472,-736000]),(⟨1,0,4⟩,[-128,3712,-32128,127872,-345984,899456,-1608320,1217664]),(⟨1,0,5⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨1,1,0⟩,[128,-4352,53888,-356352,1481472,-4359680,10024704,-18178048,22901888,-16095488,4138624]),(⟨1,1,1⟩,[0,0,-3072,52224,-304128,697344,-95232,-2362368,3843072,-1827840]),(⟨1,1,2⟩,[0,0,-1024,16384,-87040,172032,54272,-745472,852992]),(⟨1,1,3⟩,[0,0,2048,-26624,86016,12288,-317440,243712]),(⟨1,1,4⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨1,2,0⟩,[-256,4352,-26880,72448,-17664,-620800,2740480,-6298368,7880192,-4257792]),(⟨1,2,1⟩,[0,0,-1024,16384,-87040,172032,54272,-745472,852992]),(⟨1,2,2⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨1,3,0⟩,[-256,7168,-69120,348160,-1113088,2477056,-3701248,3049472,-736000]),(⟨1,3,1⟩,[0,0,2048,-26624,86016,12288,-317440,243712]),(⟨1,4,0⟩,[-128,3712,-32128,127872,-345984,899456,-1608320,1217664]),(⟨1,4,1⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨1,5,0⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨2,0,0⟩,[320,-7040,65216,-369920,1510912,-4616192,10558208,-18034432,21555904,-14459008,2812992]),(⟨2,0,1⟩,[-256,4352,-26880,72448,-17664,-620800,2740480,-6298368,7880192,-4257792]),(⟨2,0,2⟩,[-640,11520,-78336,295168,-787712,1558272,-1900032,670464,853888]),(⟨2,0,3⟩,[768,-11520,55040,-84224,-100096,674048,-1381120,1109248]),(⟨2,0,4⟩,[896,-13824,68992,-143360,132736,67072,-309120]),(⟨2,0,5⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨2,0,6⟩,[-512,6144,-15360,-18432,60928]),(⟨2,1,0⟩,[-256,4352,-26880,72448,-17664,-620800,2740480,-6298368,7880192,-4257792]),(⟨2,1,1⟩,[0,0,-1024,16384,-87040,172032,54272,-745472,852992]),(⟨2,1,2⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨2,2,0⟩,[-640,11520,-78336,295168,-787712,1558272,-1900032,670464,853888]),(⟨2,2,1⟩,[256,-4352,25344,-58112,7936,196864,-320256,152320]),(⟨2,2,2⟩,[768,-12288,65280,-129024,-40704,559104,-639744]),(⟨2,2,3⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨2,2,4⟩,[-512,6144,-15360,-18432,60928]),(⟨2,3,0⟩,[768,-11520,55040,-84224,-100096,674048,-1381120,1109248]),(⟨2,3,2⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨2,4,0⟩,[896,-13824,68992,-143360,132736,67072,-309120]),(⟨2,4,2⟩,[-512,6144,-15360,-18432,60928]),(⟨2,5,0⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨2,6,0⟩,[-512,6144,-15360,-18432,60928]),(⟨3,0,0⟩,[-768,14848,-116480,498432,-1315328,2271232,-2447104,187136,4186880,-4196352]),(⟨3,0,1⟩,[-256,7168,-69120,348160,-1113088,2477056,-3701248,3049472,-736000]),(⟨3,0,2⟩,[768,-11520,55040,-84224,-100096,674048,-1381120,1109248]),(⟨3,0,3⟩,[512,-11264,73216,-223232,499200,-830464,492032]),(⟨3,0,4⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨3,1,0⟩,[-256,7168,-69120,348160,-1113088,2477056,-3701248,3049472,-736000]),(⟨3,1,1⟩,[0,0,2048,-26624,86016,12288,-317440,243712]),(⟨3,2,0⟩,[768,-11520,55040,-84224,-100096,674048,-1381120,1109248]),(⟨3,2,2⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨3,3,0⟩,[512,-11264,73216,-223232,499200,-830464,492032]),(⟨3,4,0⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨4,0,0⟩,[-1088,22912,-184832,802176,-2241152,4496512,-6537216,5643392,-1443648]),(⟨4,0,1⟩,[-128,3712,-32128,127872,-345984,899456,-1608320,1217664]),(⟨4,0,2⟩,[896,-13824,68992,-143360,132736,67072,-309120]),(⟨4,0,3⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨4,1,0⟩,[-128,3712,-32128,127872,-345984,899456,-1608320,1217664]),(⟨4,1,1⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨4,2,0⟩,[896,-13824,68992,-143360,132736,67072,-309120]),(⟨4,2,2⟩,[-512,6144,-15360,-18432,60928]),(⟨4,3,0⟩,[256,-5376,31232,-80384,169216,-246016]),(⟨5,0,0⟩,[384,-3456,-4480,128384,-540032,1364352,-2351744,1930880]),(⟨5,0,1⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨5,0,2⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨5,1,0⟩,[0,0,2048,-24576,61440,73728,-243712]),(⟨5,2,0⟩,[-512,6656,-21504,-3072,79360,-60928]),(⟨6,0,0⟩,[896,-15360,83840,-211968,395904,-534528,150144]),(⟨6,0,2⟩,[-512,6144,-15360,-18432,60928]),(⟨6,2,0⟩,[-512,6144,-15360,-18432,60928]),(⟨7,0,0⟩,[256,-5376,31232,-80384,169216,-246016])]


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
    (Poly.add (Poly.scale (K.ofRat r347) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 0 6).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r345*r346 : ℚ)=r347 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 0 6 r345 r346 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 0=6 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 0 6).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C051

#print axioms Coulomb8.Columns.C051.sound
