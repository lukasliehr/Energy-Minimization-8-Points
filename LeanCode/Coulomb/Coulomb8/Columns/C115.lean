import Coulomb8.Data
import Coulomb8.CoefficientBasis
import Coulomb8.SOSCaching

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Coulomb8.Columns.C115

def r0 : ℚ := { num := -65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r1 : ℚ := { num := 2441216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r2 : ℚ := { num := -40165376, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r3 : ℚ := { num := 386981888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r4 : ℚ := { num := -2430795776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r5 : ℚ := { num := 10362617856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r6 : ℚ := { num := -29211058176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r7 : ℚ := { num := 6095659008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r8 : ℚ := { num := 51474235392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r9 : ℚ := { num := -31051956224, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r10 : ℚ := { num := 1808028819456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r11 : ℚ := { num := -587392819200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r12 : ℚ := { num := 6818565128192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r13 : ℚ := { num := -8255012438016, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r14 : ℚ := { num := 6918187245568, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r15 : ℚ := { num := -3523714588672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r16 : ℚ := { num := 810132078592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r17 : ℚ := { num := -8643051520, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r18 : ℚ := { num := -49152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r19 : ℚ := { num := 2146304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r20 : ℚ := { num := -39903232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r21 : ℚ := { num := 422985728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r22 : ℚ := { num := -409878528, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r23 : ℚ := { num := 13088014336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r24 : ℚ := { num := -39886839808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r25 : ℚ := { num := 69791727616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r26 : ℚ := { num := 2048180224, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r27 : ℚ := { num := -552158412800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r28 : ℚ := { num := 298859470848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r29 : ℚ := { num := -4944871505920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r30 : ℚ := { num := 8310461743104, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r31 : ℚ := { num := -9962044211200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r32 : ℚ := { num := 1137940537344, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r33 : ℚ := { num := -506165575680, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r34 : ℚ := { num := 9670000640, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r35 : ℚ := { num := 8192, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r36 : ℚ := { num := -4481024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r37 : ℚ := { num := 59858944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r38 : ℚ := { num := -428941312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r39 : ℚ := { num := 1725587456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r40 : ℚ := { num := -3093897216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r41 : ℚ := { num := -5421883392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r42 : ℚ := { num := 52996022272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r43 : ℚ := { num := -173394632704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r44 : ℚ := { num := 323977895936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r45 : ℚ := { num := -266796294144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r46 : ℚ := { num := -52520755200, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r47 : ℚ := { num := 13465378816, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r48 : ℚ := { num := -2633088688128, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r49 : ℚ := { num := 2320337100800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r50 : ℚ := { num := -123689951232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r51 : ℚ := { num := 122880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r52 : ℚ := { num := -4833280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r53 : ℚ := { num := 77602816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r54 : ℚ := { num := -674562048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r55 : ℚ := { num := 206462976, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r56 : ℚ := { num := -11023335424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r57 : ℚ := { num := 16737607680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r58 : ℚ := { num := 21555576832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r59 : ℚ := { num := -29987086336, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r60 : ℚ := { num := 40021573632, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r61 : ℚ := { num := -201516605440, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r62 : ℚ := { num := 287383420928, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r63 : ℚ := { num := -1884644433920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r64 : ℚ := { num := 54563946496, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r65 : ℚ := { num := -7663706112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r66 : ℚ := { num := -8192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r67 : ℚ := { num := 1269760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r68 : ℚ := { num := -6848512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r69 : ℚ := { num := -44908544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r70 : ℚ := { num := 727425024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r71 : ℚ := { num := -3859963904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r72 : ℚ := { num := 10511974400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r73 : ℚ := { num := -10961387520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r74 : ℚ := { num := -33985634304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r75 : ℚ := { num := 195870629888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r76 : ℚ := { num := -502780100608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r77 : ℚ := { num := 811783077888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r78 : ℚ := { num := -116500455424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r79 : ℚ := { num := 7983620096, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r80 : ℚ := { num := -73728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r81 : ℚ := { num := 2588672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r82 : ℚ := { num := -34766848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r83 : ℚ := { num := 229310464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r84 : ℚ := { num := -766713856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r85 : ℚ := { num := 903413760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r86 : ℚ := { num := 3001024512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r87 : ℚ := { num := -18608029696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r88 : ℚ := { num := 1054253056, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r89 : ℚ := { num := -87778164736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r90 : ℚ := { num := 804093952, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r91 : ℚ := { num := -52178124800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r92 : ℚ := { num := -1634770944, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r93 : ℚ := { num := -16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r94 : ℚ := { num := 671744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r95 : ℚ := { num := -10502144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r96 : ℚ := { num := 79839232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r97 : ℚ := { num := -314343424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r98 : ℚ := { num := 556302336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r99 : ℚ := { num := 72515584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r100 : ℚ := { num := -6563397632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r101 : ℚ := { num := 22923231232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r102 : ℚ := { num := -47490711552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r103 : ℚ := { num := 63137300480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r104 : ℚ := { num := -6376734720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r105 : ℚ := { num := 983040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r106 : ℚ := { num := -22315008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r107 : ℚ := { num := 269697024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r108 : ℚ := { num := -2004926464, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r109 : ℚ := { num := 9901277184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r110 : ℚ := { num := -4801101824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r111 : ℚ := { num := 75631673344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r112 : ℚ := { num := -78463483904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r113 : ℚ := { num := -183731748864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r114 : ℚ := { num := 1169250025472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r115 : ℚ := { num := -3269686280192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r116 : ℚ := { num := 5951144509440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r117 : ℚ := { num := -7225731219456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r118 : ℚ := { num := 761309822976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r119 : ℚ := { num := -36692934656, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r120 : ℚ := { num := 8192, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r121 : ℚ := { num := -319488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r122 : ℚ := { num := 35348480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r123 : ℚ := { num := -299040768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r124 : ℚ := { num := 1484152832, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r125 : ℚ := { num := -4200570880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r126 : ℚ := { num := 75980800, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r127 : ℚ := { num := 23372431360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r128 : ℚ := { num := -18316894208, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r129 : ℚ := { num := 345929588736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r130 : ℚ := { num := -570569449472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r131 : ℚ := { num := 506954252288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r132 : ℚ := { num := 18157412352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r133 : ℚ := { num := -82695168000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r134 : ℚ := { num := 9734463488, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r135 : ℚ := { num := 24576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r136 : ℚ := { num := -1286144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r137 : ℚ := { num := 25165824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r138 : ℚ := { num := -251494400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r139 : ℚ := { num := 1460690944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r140 : ℚ := { num := -5240004608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r141 : ℚ := { num := 11190075392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r142 : ℚ := { num := -6086197248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r143 : ℚ := { num := -55889682432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r144 : ℚ := { num := 248644771840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r145 : ℚ := { num := -589432029184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r146 : ℚ := { num := 908385681408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r147 : ℚ := { num := -122438623232, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r148 : ℚ := { num := 7639375872, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r149 : ℚ := { num := 2162688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r150 : ℚ := { num := -3866624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r151 : ℚ := { num := 175177728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r152 : ℚ := { num := -734134272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r153 : ℚ := { num := 2528247808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r154 : ℚ := { num := -7119962112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r155 : ℚ := { num := 11838029824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r156 : ℚ := { num := -888995840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r157 : ℚ := { num := -46241349632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r158 : ℚ := { num := 16064774144, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r159 : ℚ := { num := -116064256, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r160 : ℚ := { num := -32768, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r161 : ℚ := { num := 6782976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r162 : ℚ := { num := -79790080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r163 : ℚ := { num := 470941696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r164 : ℚ := { num := -1365508096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r165 : ℚ := { num := 635207680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r166 : ℚ := { num := 1403715584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r167 : ℚ := { num := -40465858560, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r168 : ℚ := { num := 4678516736, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r169 : ℚ := { num := -69941297152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r170 : ℚ := { num := -25348505600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r171 : ℚ := { num := 119555096576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r172 : ℚ := { num := -11204231168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r173 : ℚ := { num := -570458112, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r174 : ℚ := { num := -40960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r175 : ℚ := { num := 245760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r176 : ℚ := { num := -24903680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r177 : ℚ := { num := 161038336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r178 : ℚ := { num := -58056704, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r179 : ℚ := { num := -694386688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r180 : ℚ := { num := 1208942592, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r181 : ℚ := { num := -1797488640, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r182 : ℚ := { num := 61262340096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r183 : ℚ := { num := -61574922240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r184 : ℚ := { num := 4360962048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r185 : ℚ := { num := 62271930368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r186 : ℚ := { num := -9554993152, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r187 : ℚ := { num := 81920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r188 : ℚ := { num := -2375680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r189 : ℚ := { num := 26755072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r190 : ℚ := { num := -147996672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r191 : ℚ := { num := 416448512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r192 : ℚ := { num := -532447232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r193 : ℚ := { num := 15302656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r194 : ℚ := { num := 545619968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r195 : ℚ := { num := -1774436352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r196 : ℚ := { num := 6052954112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r197 : ℚ := { num := -2003779584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r198 : ℚ := { num := 16039936, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r199 : ℚ := { num := 1179648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r200 : ℚ := { num := -1622016, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r201 : ℚ := { num := 61079552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r202 : ℚ := { num := -236158976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r203 : ℚ := { num := 747110400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r204 : ℚ := { num := -1548648448, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r205 : ℚ := { num := 610009088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r206 : ℚ := { num := 5413814272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r207 : ℚ := { num := -1821769728, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r208 : ℚ := { num := 11517952, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r209 : ℚ := { num := -32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r210 : ℚ := { num := 1081344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r211 : ℚ := { num := -13238272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r212 : ℚ := { num := 77725696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r213 : ℚ := { num := -236388352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r214 : ℚ := { num := 374276096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r215 : ℚ := { num := -181534720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r216 : ℚ := { num := -1059454976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r217 : ℚ := { num := 3711139840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r218 : ℚ := { num := -31490048, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r219 : ℚ := { num := 131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r220 : ℚ := { num := -3276800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r221 : ℚ := { num := 21757952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r222 : ℚ := { num := 20447232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r223 : ℚ := { num := -869531648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r224 : ℚ := { num := 5039718400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r225 : ℚ := { num := -2533359616, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r226 : ℚ := { num := 42426957824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r227 : ℚ := { num := -64797671424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r228 : ℚ := { num := 66399895552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r229 : ℚ := { num := -6658719744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r230 : ℚ := { num := -81920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r231 : ℚ := { num := 131072, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r232 : ℚ := { num := -23707648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r233 : ℚ := { num := 126091264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r234 : ℚ := { num := -353140736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r235 : ℚ := { num := 61341696, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r236 : ℚ := { num := 502038528, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r237 : ℚ := { num := -3206807552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r238 : ℚ := { num := 4678336512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r239 : ℚ := { num := 124387328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r240 : ℚ := { num := -6209536, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r241 : ℚ := { num := 65536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r242 : ℚ := { num := -1572864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r243 : ℚ := { num := 786432, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r244 : ℚ := { num := -42467328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r245 : ℚ := { num := 328728576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r246 : ℚ := { num := -382992384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r247 : ℚ := { num := -4718592, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r248 : ℚ := { num := 98304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r249 : ℚ := { num := -3833856, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r250 : ℚ := { num := 58392576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r251 : ℚ := { num := -478740480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r252 : ℚ := { num := 2544402432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r253 : ℚ := { num := -10493067264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r254 : ℚ := { num := 37451071488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r255 : ℚ := { num := -53084160, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r256 : ℚ := { num := 201070903296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r257 : ℚ := { num := -16798875648, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r258 : ℚ := { num := -73769091072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r259 : ℚ := { num := 239154561024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r260 : ℚ := { num := -46094647296, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r261 : ℚ := { num := 1504935936, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r262 : ℚ := { num := -163840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r263 : ℚ := { num := 4521984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r264 : ℚ := { num := -51183616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r265 : ℚ := { num := 46727168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r266 : ℚ := { num := -1430093824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r267 : ℚ := { num := 4631691264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r268 : ℚ := { num := -9475325952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r269 : ℚ := { num := 92143616, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r270 : ℚ := { num := 31413927936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r271 : ℚ := { num := -91675361280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r272 : ℚ := { num := 95382863872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r273 : ℚ := { num := 5525274624, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r274 : ℚ := { num := -142245888, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r275 : ℚ := { num := 163840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r276 : ℚ := { num := -15990784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r277 : ℚ := { num := 113278976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r278 : ℚ := { num := -409305088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r279 : ℚ := { num := 429326336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r280 : ℚ := { num := 2362441728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r281 : ℚ := { num := -10853220352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r282 : ℚ := { num := 17779687424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r283 : ℚ := { num := 481263616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r284 : ℚ := { num := -7558922240, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r285 : ℚ := { num := 1813413888, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r286 : ℚ := { num := -63078400, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r287 : ℚ := { num := 16384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r288 : ℚ := { num := -540672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r289 : ℚ := { num := 7159808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r290 : ℚ := { num := -51986432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r291 : ℚ := { num := 244350976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r292 : ℚ := { num := -825786368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r293 : ℚ := { num := 2070183936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r294 : ℚ := { num := -202145792, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r295 : ℚ := { num := 113688576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r296 : ℚ := { num := 850706432, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r297 : ℚ := { num := -5103435776, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r298 : ℚ := { num := 33406976, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r299 : ℚ := { num := -262144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r300 : ℚ := { num := 6291456, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r301 : ℚ := { num := -3145728, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r302 : ℚ := { num := 169869312, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r303 : ℚ := { num := 52953088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r304 : ℚ := { num := -1314914304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r305 : ℚ := { num := 1531969536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r306 : ℚ := { num := 18874368, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r307 : ℚ := { num := -524288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r308 : ℚ := { num := 12582912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r309 : ℚ := { num := -6291456, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r310 : ℚ := { num := 339738624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r311 : ℚ := { num := 105906176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r312 : ℚ := { num := -2629828608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r313 : ℚ := { num := 3063939072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r314 : ℚ := { num := 37748736, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r315 : ℚ := { num := 196608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r316 : ℚ := { num := -5111808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r317 : ℚ := { num := 48562176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r318 : ℚ := { num := -186187776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r319 : ℚ := { num := 34996224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r320 : ℚ := { num := 15728640, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r321 : ℚ := { num := -325976064, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r322 : ℚ := { num := 5147590656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r323 : ℚ := { num := 7322664960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r324 : ℚ := { num := -29006364672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r325 : ℚ := { num := 4338941952, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r326 : ℚ := { num := -5308416, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r327 : ℚ := { num := -131072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r328 : ℚ := { num := 3407872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r329 : ℚ := { num := -34799616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r330 : ℚ := { num := 180879360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r331 : ℚ := { num := -76546048, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r332 : ℚ := { num := 1006632960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r333 : ℚ := { num := -1099563008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r334 : ℚ := { num := -1281884160, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r335 : ℚ := { num := 8560181248, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r336 : ℚ := { num := -2018246656, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r337 : ℚ := { num := 9764864, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r338 : ℚ := { num := -3145728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r339 : ℚ := { num := 1572864, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r340 : ℚ := { num := -84934656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r341 : ℚ := { num := -26476544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r342 : ℚ := { num := 657457152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r343 : ℚ := { num := -765984768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r344 : ℚ := { num := -9437184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r345 : ℚ := { num := 155451392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r346 : ℚ := { num := -472776704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r347 : ℚ := { num := 748552192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r348 : ℚ := { num := -363069440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r349 : ℚ := { num := -2118909952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r350 : ℚ := { num := 7422279680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r351 : ℚ := { num := -62980096, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r352 : ℚ := { num := 1220608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r353 : ℚ := { num := -20082688, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r354 : ℚ := { num := 193490944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r355 : ℚ := { num := -1215397888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r356 : ℚ := { num := 5181308928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r357 : ℚ := { num := -14605529088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r358 : ℚ := { num := 3047829504, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r359 : ℚ := { num := 25737117696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r360 : ℚ := { num := -15525978112, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r361 : ℚ := { num := 904014409728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r362 : ℚ := { num := -293696409600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r363 : ℚ := { num := 3409282564096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r364 : ℚ := { num := -4127506219008, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r365 : ℚ := { num := 3459093622784, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r366 : ℚ := { num := -1761857294336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r367 : ℚ := { num := 405066039296, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r368 : ℚ := { num := -4321525760, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r369 : ℚ := { num := -24576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r370 : ℚ := { num := 1073152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r371 : ℚ := { num := -19951616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r372 : ℚ := { num := 211492864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r373 : ℚ := { num := -204939264, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r374 : ℚ := { num := 6544007168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r375 : ℚ := { num := -19943419904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r376 : ℚ := { num := 34895863808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r377 : ℚ := { num := 1024090112, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r378 : ℚ := { num := -276079206400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r379 : ℚ := { num := 149429735424, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r380 : ℚ := { num := -2472435752960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r381 : ℚ := { num := 4155230871552, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r382 : ℚ := { num := -4981022105600, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r383 : ℚ := { num := 568970268672, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r384 : ℚ := { num := -253082787840, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r385 : ℚ := { num := 4835000320, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r386 : ℚ := { num := 4096, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r387 : ℚ := { num := -2240512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r388 : ℚ := { num := 29929472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r389 : ℚ := { num := -214470656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r390 : ℚ := { num := 862793728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r391 : ℚ := { num := -1546948608, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r392 : ℚ := { num := -2710941696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r393 : ℚ := { num := 26498011136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r394 : ℚ := { num := -86697316352, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r395 : ℚ := { num := 161988947968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r396 : ℚ := { num := -133398147072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r397 : ℚ := { num := -26260377600, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r398 : ℚ := { num := 6732689408, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r399 : ℚ := { num := -1316544344064, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r400 : ℚ := { num := 1160168550400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r401 : ℚ := { num := -61844975616, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r402 : ℚ := { num := 61440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r403 : ℚ := { num := -2416640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r404 : ℚ := { num := 38801408, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r405 : ℚ := { num := -337281024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r406 : ℚ := { num := 103231488, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r407 : ℚ := { num := -5511667712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r408 : ℚ := { num := 8368803840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r409 : ℚ := { num := 10777788416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r410 : ℚ := { num := -14993543168, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r411 : ℚ := { num := 20010786816, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r412 : ℚ := { num := -100758302720, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r413 : ℚ := { num := 143691710464, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r414 : ℚ := { num := -942322216960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r415 : ℚ := { num := 27281973248, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r416 : ℚ := { num := -3831853056, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r417 : ℚ := { num := -4096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r418 : ℚ := { num := 634880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r419 : ℚ := { num := -3424256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r420 : ℚ := { num := -22454272, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r421 : ℚ := { num := 363712512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r422 : ℚ := { num := -1929981952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r423 : ℚ := { num := 5255987200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r424 : ℚ := { num := -5480693760, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r425 : ℚ := { num := -16992817152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r426 : ℚ := { num := 97935314944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r427 : ℚ := { num := -251390050304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r428 : ℚ := { num := 405891538944, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r429 : ℚ := { num := -58250227712, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r430 : ℚ := { num := 3991810048, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r431 : ℚ := { num := -36864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r432 : ℚ := { num := 1294336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r433 : ℚ := { num := -17383424, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r434 : ℚ := { num := 114655232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r435 : ℚ := { num := -383356928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r436 : ℚ := { num := 451706880, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r437 : ℚ := { num := 1500512256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r438 : ℚ := { num := -9304014848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r439 : ℚ := { num := 527126528, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r440 : ℚ := { num := -43889082368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r441 : ℚ := { num := 402046976, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r442 : ℚ := { num := -26089062400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r443 : ℚ := { num := -817385472, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r444 : ℚ := { num := -8192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r445 : ℚ := { num := 335872, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r446 : ℚ := { num := -5251072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r447 : ℚ := { num := 39919616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r448 : ℚ := { num := -157171712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r449 : ℚ := { num := 278151168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r450 : ℚ := { num := 36257792, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r451 : ℚ := { num := -3281698816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r452 : ℚ := { num := 11461615616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r453 : ℚ := { num := -23745355776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r454 : ℚ := { num := 31568650240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r455 : ℚ := { num := -3188367360, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r456 : ℚ := { num := 491520, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r457 : ℚ := { num := -11157504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r458 : ℚ := { num := 134848512, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r459 : ℚ := { num := -1002463232, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r460 : ℚ := { num := 4950638592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r461 : ℚ := { num := -2400550912, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r462 : ℚ := { num := 37815836672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r463 : ℚ := { num := -39231741952, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r464 : ℚ := { num := -91865874432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r465 : ℚ := { num := 584625012736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r466 : ℚ := { num := -1634843140096, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r467 : ℚ := { num := 2975572254720, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r468 : ℚ := { num := -3612865609728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r469 : ℚ := { num := 380654911488, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r470 : ℚ := { num := -18346467328, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r471 : ℚ := { num := 4096, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r472 : ℚ := { num := -159744, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r473 : ℚ := { num := 17674240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r474 : ℚ := { num := -149520384, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r475 : ℚ := { num := 742076416, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r476 : ℚ := { num := -2100285440, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r477 : ℚ := { num := 37990400, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r478 : ℚ := { num := 11686215680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r479 : ℚ := { num := -9158447104, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r480 : ℚ := { num := 172964794368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r481 : ℚ := { num := -285284724736, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r482 : ℚ := { num := 253477126144, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r483 : ℚ := { num := 9078706176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r484 : ℚ := { num := -41347584000, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r485 : ℚ := { num := 4867231744, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r486 : ℚ := { num := 12288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r487 : ℚ := { num := -643072, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r488 : ℚ := { num := -125747200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r489 : ℚ := { num := 730345472, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r490 : ℚ := { num := -2620002304, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r491 : ℚ := { num := 5595037696, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r492 : ℚ := { num := -3043098624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r493 : ℚ := { num := -27944841216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r494 : ℚ := { num := 124322385920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r495 : ℚ := { num := -294716014592, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r496 : ℚ := { num := 454192840704, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r497 : ℚ := { num := -61219311616, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r498 : ℚ := { num := 3819687936, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r499 : ℚ := { num := -1933312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r500 : ℚ := { num := 87588864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r501 : ℚ := { num := -367067136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r502 : ℚ := { num := 1264123904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r503 : ℚ := { num := -3559981056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r504 : ℚ := { num := 5919014912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r505 : ℚ := { num := -444497920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r506 : ℚ := { num := -23120674816, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r507 : ℚ := { num := 8032387072, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r508 : ℚ := { num := -58032128, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r509 : ℚ := { num := -16384, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r510 : ℚ := { num := 3391488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r511 : ℚ := { num := -39895040, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r512 : ℚ := { num := 235470848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r513 : ℚ := { num := -682754048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r514 : ℚ := { num := 317603840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r515 : ℚ := { num := 701857792, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r516 : ℚ := { num := -20232929280, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r517 : ℚ := { num := 2339258368, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r518 : ℚ := { num := -34970648576, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r519 : ℚ := { num := -12674252800, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r520 : ℚ := { num := 59777548288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r521 : ℚ := { num := -5602115584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r522 : ℚ := { num := -285229056, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r523 : ℚ := { num := -20480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r524 : ℚ := { num := 122880, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r525 : ℚ := { num := -12451840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r526 : ℚ := { num := 80519168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r527 : ℚ := { num := -29028352, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r528 : ℚ := { num := -347193344, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r529 : ℚ := { num := 604471296, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r530 : ℚ := { num := -898744320, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r531 : ℚ := { num := 30631170048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r532 : ℚ := { num := -30787461120, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r533 : ℚ := { num := 2180481024, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r534 : ℚ := { num := 31135965184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r535 : ℚ := { num := -4777496576, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r536 : ℚ := { num := 40960, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r537 : ℚ := { num := -1187840, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r538 : ℚ := { num := 13377536, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r539 : ℚ := { num := -73998336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r540 : ℚ := { num := 208224256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r541 : ℚ := { num := -266223616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r542 : ℚ := { num := 7651328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r543 : ℚ := { num := 272809984, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r544 : ℚ := { num := -887218176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r545 : ℚ := { num := 3026477056, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r546 : ℚ := { num := -1001889792, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r547 : ℚ := { num := 8019968, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r548 : ℚ := { num := 589824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r549 : ℚ := { num := -811008, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r550 : ℚ := { num := 30539776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r551 : ℚ := { num := -118079488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r552 : ℚ := { num := 373555200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r553 : ℚ := { num := -774324224, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r554 : ℚ := { num := 305004544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r555 : ℚ := { num := 2706907136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r556 : ℚ := { num := -910884864, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r557 : ℚ := { num := 5758976, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r558 : ℚ := { num := 540672, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r559 : ℚ := { num := -6619136, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r560 : ℚ := { num := 38862848, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r561 : ℚ := { num := -118194176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r562 : ℚ := { num := 187138048, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r563 : ℚ := { num := -90767360, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r564 : ℚ := { num := -529727488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r565 : ℚ := { num := 1855569920, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r566 : ℚ := { num := -15745024, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r567 : ℚ := { num := -1638400, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r568 : ℚ := { num := 10878976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r569 : ℚ := { num := 10223616, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r570 : ℚ := { num := -434765824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r571 : ℚ := { num := 2519859200, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r572 : ℚ := { num := -1266679808, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r573 : ℚ := { num := 21213478912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r574 : ℚ := { num := -32398835712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r575 : ℚ := { num := 33199947776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r576 : ℚ := { num := -3329359872, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r577 : ℚ := { num := 65536, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r578 : ℚ := { num := -11853824, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r579 : ℚ := { num := 63045632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r580 : ℚ := { num := -176570368, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r581 : ℚ := { num := 30670848, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r582 : ℚ := { num := 251019264, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r583 : ℚ := { num := -1603403776, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r584 : ℚ := { num := 2339168256, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r585 : ℚ := { num := 62193664, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r586 : ℚ := { num := -3104768, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r587 : ℚ := { num := 32768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r588 : ℚ := { num := -786432, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r589 : ℚ := { num := 393216, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r590 : ℚ := { num := -21233664, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r591 : ℚ := { num := 164364288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r592 : ℚ := { num := -191496192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r593 : ℚ := { num := -2359296, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r594 : ℚ := { num := 49152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r595 : ℚ := { num := -1916928, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r596 : ℚ := { num := 29196288, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r597 : ℚ := { num := -239370240, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r598 : ℚ := { num := 1272201216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r599 : ℚ := { num := -5246533632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r600 : ℚ := { num := 18725535744, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r601 : ℚ := { num := -26542080, den := 7, den_nz := by decide +kernel, reduced := by decide +kernel }
def r602 : ℚ := { num := 100535451648, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r603 : ℚ := { num := -8399437824, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r604 : ℚ := { num := -36884545536, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r605 : ℚ := { num := 119577280512, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r606 : ℚ := { num := -23047323648, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r607 : ℚ := { num := 752467968, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r608 : ℚ := { num := 2260992, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r609 : ℚ := { num := -25591808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r610 : ℚ := { num := 23363584, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r611 : ℚ := { num := -715046912, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r612 : ℚ := { num := 2315845632, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r613 : ℚ := { num := -4737662976, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r614 : ℚ := { num := 46071808, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r615 : ℚ := { num := 15706963968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r616 : ℚ := { num := -45837680640, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r617 : ℚ := { num := 47691431936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r618 : ℚ := { num := 2762637312, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r619 : ℚ := { num := -71122944, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r620 : ℚ := { num := 81920, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r621 : ℚ := { num := -7995392, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r622 : ℚ := { num := 56639488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r623 : ℚ := { num := -204652544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r624 : ℚ := { num := 214663168, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r625 : ℚ := { num := 1181220864, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r626 : ℚ := { num := -5426610176, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r627 : ℚ := { num := 8889843712, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r628 : ℚ := { num := 240631808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r629 : ℚ := { num := -3779461120, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r630 : ℚ := { num := 906706944, den := 289, den_nz := by decide +kernel, reduced := by decide +kernel }
def r631 : ℚ := { num := -31539200, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r632 : ℚ := { num := 8192, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r633 : ℚ := { num := -270336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r634 : ℚ := { num := 3579904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r635 : ℚ := { num := -25993216, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r636 : ℚ := { num := 122175488, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r637 : ℚ := { num := -412893184, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r638 : ℚ := { num := 1035091968, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r639 : ℚ := { num := -101072896, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r640 : ℚ := { num := 56844288, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r641 : ℚ := { num := 425353216, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r642 : ℚ := { num := -2551717888, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r643 : ℚ := { num := 16703488, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r644 : ℚ := { num := 3145728, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r645 : ℚ := { num := -1572864, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r646 : ℚ := { num := 84934656, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r647 : ℚ := { num := 26476544, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r648 : ℚ := { num := -657457152, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r649 : ℚ := { num := 765984768, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r650 : ℚ := { num := 9437184, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r651 : ℚ := { num := -2555904, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r652 : ℚ := { num := 24281088, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r653 : ℚ := { num := -93093888, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r654 : ℚ := { num := 17498112, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r655 : ℚ := { num := 7864320, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r656 : ℚ := { num := -162988032, den := 833, den_nz := by decide +kernel, reduced := by decide +kernel }
def r657 : ℚ := { num := 2573795328, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r658 : ℚ := { num := 3661332480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r659 : ℚ := { num := -14503182336, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r660 : ℚ := { num := 2169470976, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r661 : ℚ := { num := -2654208, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r662 : ℚ := { num := 1703936, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r663 : ℚ := { num := -17399808, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r664 : ℚ := { num := 90439680, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r665 : ℚ := { num := -38273024, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r666 : ℚ := { num := 503316480, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r667 : ℚ := { num := -549781504, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r668 : ℚ := { num := -640942080, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r669 : ℚ := { num := 4280090624, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }
def r670 : ℚ := { num := -1009123328, den := 2023, den_nz := by decide +kernel, reduced := by decide +kernel }
def r671 : ℚ := { num := 4882432, den := 17, den_nz := by decide +kernel, reduced := by decide +kernel }
def r672 : ℚ := { num := 1, den := 119, den_nz := by decide +kernel, reduced := by decide +kernel }
def r673 : ℚ := { num := 1, den := 14161, den_nz := by decide +kernel, reduced := by decide +kernel }

noncomputable def coefficients : List K := [[r0,r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15,r16,r17],[r18,r19,r20,r21,r22,r23,r24,r25,r26,r27,r28,r29,r30,r31,r32,r33,r34],[r35,r36,r37,r38,r39,r40,r41,r42,r43,r44,r45,r46,r47,r48,r49,r50],[r51,r52,r53,r54,r55,r56,r57,r58,r59,r60,r61,r62,r63,r64,r65],[r66,r67,r68,r69,r70,r71,r72,r73,r74,r75,r76,r77,r78,r79],[r80,r81,r82,r83,r84,r85,r86,r87,r88,r89,r90,r91,r92],[r93,r94,r95,r96,r97,r98,r99,r100,r101,r102,r103,r104],[],[],[],[],[],[],[r93,r105,r106,r107,r108,r109,r110,r111,r112,r113,r114,r115,r116,r117,r118,r119],[r120,r121,r122,r123,r124,r125,r126,r127,r128,r129,r130,r131,r132,r133,r134],[r135,r136,r137,r138,r139,r140,r141,r142,r143,r144,r145,r146,r147,r148],[0,r0,r149,r150,r151,r152,r153,r154,r155,r156,r157,r158,r159],[],[],[],[],[],[],[],[r160,r161,r162,r163,r164,r165,r166,r167,r168,r169,r170,r171,r172,r173],[r174,r175,r176,r177,r178,r179,r180,r181,r182,r183,r184,r185,r186],[r187,r188,r189,r190,r191,r192,r193,r194,r195,r196,r197,r198],[r18,r199,r200,r201,r202,r203,r204,r205,r206,r207,r208],[r209,r210,r211,r212,r213,r214,r215,r216,r217,r218],[],[],[],[],[0,r219,r220,r221,r222,r223,r224,r225,r226,r227,r228,r229],[r230,r231,r232,r233,r234,r235,r236,r237,r238,r239,r240],[r209,r210,r211,r212,r213,r214,r215,r216,r217,r218],[],[],[],[],[],[r241,r242,r243,r244,r211,r245,r246,r247,65536],[],[],[],[],[],[],[],[0,r248,r249,r250,r251,r252,r253,r254,r255,r256,r257,r258,r259,r260,r261],[0,r262,r263,r264,r265,r266,r267,r268,r269,r270,r271,r272,r273,r274],[0,r0,r149,r150,r151,r152,r153,r154,r155,r156,r157,r158,r159],[],[],[],[],[],[],[],[r209,r275,r276,r277,r278,r279,r280,r281,r282,r283,r284,r285,r286],[r287,r288,r289,r290,r291,r292,r293,r294,r295,r296,r297,r298],[0,0,r299,r300,r301,r302,r303,r304,r305,r306,-262144],[],[],[],[],[],[0,0,r307,r308,r309,r310,r311,r312,r313,r314,-524288],[],[],[],[],[],[],[],[],[],[],[],[r315,r316,r317,r318,r319,r320,r321,r322,r323,r324,r325,r326],[r327,r328,r329,r330,r331,r332,r333,r334,r335,r336,r337],[],[r219,r338,r339,r340,r341,r342,r343,r344,131072],[],[],[],[r0,r149,r341,r345,r346,r347,r348,r349,r350,r351],[r241,r242,r243,r244,r211,r245,r246,r247,65536],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def cachedProduct : Poly := [(⟨0,0,0⟩,[r209,r352,r353,r354,r355,r356,r357,r358,r359,r360,r361,r362,r363,r364,r365,r366,r367,r368]),(⟨0,0,1⟩,[r369,r370,r371,r372,r373,r374,r375,r376,r377,r378,r379,r380,r381,r382,r383,r384,r385]),(⟨0,0,2⟩,[r386,r387,r388,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398,r399,r400,r401]),(⟨0,0,3⟩,[r402,r403,r404,r405,r406,r407,r408,r409,r410,r411,r412,r413,r414,r415,r416]),(⟨0,0,4⟩,[r417,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427,r428,r429,r430]),(⟨0,0,5⟩,[r431,r432,r433,r434,r435,r436,r437,r438,r439,r440,r441,r442,r443]),(⟨0,0,6⟩,[r444,r445,r446,r447,r448,r449,r450,r451,r452,r453,r454,r455]),(⟨0,1,0⟩,[r369,r370,r371,r372,r373,r374,r375,r376,r377,r378,r379,r380,r381,r382,r383,r384,r385]),(⟨0,1,1⟩,[r444,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466,r467,r468,r469,r470]),(⟨0,1,2⟩,[r471,r472,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483,r484,r485]),(⟨0,1,3⟩,[r486,r487,r308,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498]),(⟨0,1,4⟩,[0,r209,r210,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508]),(⟨0,2,0⟩,[r386,r387,r388,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398,r399,r400,r401]),(⟨0,2,1⟩,[r471,r472,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483,r484,r485]),(⟨0,2,2⟩,[r509,r510,r511,r512,r513,r514,r515,r516,r517,r518,r519,r520,r521,r522]),(⟨0,2,3⟩,[r523,r524,r525,r526,r527,r528,r529,r530,r531,r532,r533,r534,r535]),(⟨0,2,4⟩,[r536,r537,r538,r539,r540,r541,r542,r543,r544,r545,r546,r547]),(⟨0,2,5⟩,[r369,r548,r549,r550,r551,r552,r553,r554,r555,r556,r557]),(⟨0,2,6⟩,[r93,r558,r559,r560,r561,r562,r563,r564,r565,r566]),(⟨0,3,0⟩,[r402,r403,r404,r405,r406,r407,r408,r409,r410,r411,r412,r413,r414,r415,r416]),(⟨0,3,1⟩,[r486,r487,r308,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498]),(⟨0,3,2⟩,[r523,r524,r525,r526,r527,r528,r529,r530,r531,r532,r533,r534,r535]),(⟨0,3,3⟩,[0,r241,r567,r568,r569,r570,r571,r572,r573,r574,r575,r576]),(⟨0,3,4⟩,[r174,r577,r578,r579,r580,r581,r582,r583,r584,r585,r586]),(⟨0,3,5⟩,[r93,r558,r559,r560,r561,r562,r563,r564,r565,r566]),(⟨0,4,0⟩,[r417,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427,r428,r429,r430]),(⟨0,4,1⟩,[0,r209,r210,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508]),(⟨0,4,2⟩,[r536,r537,r538,r539,r540,r541,r542,r543,r544,r545,r546,r547]),(⟨0,4,3⟩,[r174,r577,r578,r579,r580,r581,r582,r583,r584,r585,r586]),(⟨0,4,5⟩,[r587,r588,r589,r590,r559,r591,r592,r593,32768]),(⟨0,5,0⟩,[r431,r432,r433,r434,r435,r436,r437,r438,r439,r440,r441,r442,r443]),(⟨0,5,2⟩,[r369,r548,r549,r550,r551,r552,r553,r554,r555,r556,r557]),(⟨0,5,3⟩,[r93,r558,r559,r560,r561,r562,r563,r564,r565,r566]),(⟨0,5,4⟩,[r587,r588,r589,r590,r559,r591,r592,r593,32768]),(⟨0,6,0⟩,[r444,r445,r446,r447,r448,r449,r450,r451,r452,r453,r454,r455]),(⟨0,6,2⟩,[r93,r558,r559,r560,r561,r562,r563,r564,r565,r566]),(⟨1,0,0⟩,[r369,r370,r371,r372,r373,r374,r375,r376,r377,r378,r379,r380,r381,r382,r383,r384,r385]),(⟨1,0,1⟩,[r444,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466,r467,r468,r469,r470]),(⟨1,0,2⟩,[r471,r472,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483,r484,r485]),(⟨1,0,3⟩,[r486,r487,r308,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498]),(⟨1,0,4⟩,[0,r209,r210,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508]),(⟨1,1,0⟩,[r444,r456,r457,r458,r459,r460,r461,r462,r463,r464,r465,r466,r467,r468,r469,r470]),(⟨1,1,1⟩,[0,r594,r595,r596,r597,r598,r599,r600,r601,r602,r603,r604,r605,r606,r607]),(⟨1,1,2⟩,[0,r230,r608,r609,r610,r611,r612,r613,r614,r615,r616,r617,r618,r619]),(⟨1,1,3⟩,[0,r209,r210,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508]),(⟨1,2,0⟩,[r471,r472,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483,r484,r485]),(⟨1,2,1⟩,[0,r230,r608,r609,r610,r611,r612,r613,r614,r615,r616,r617,r618,r619]),(⟨1,2,2⟩,[r93,r620,r621,r622,r623,r624,r625,r626,r627,r628,r629,r630,r631]),(⟨1,2,3⟩,[r632,r633,r634,r635,r636,r637,r638,r639,r640,r641,r642,r643]),(⟨1,2,4⟩,[0,0,r327,r644,r645,r646,r647,r648,r649,r650,-131072]),(⟨1,3,0⟩,[r486,r487,r308,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498]),(⟨1,3,1⟩,[0,r209,r210,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508]),(⟨1,3,2⟩,[r632,r633,r634,r635,r636,r637,r638,r639,r640,r641,r642,r643]),(⟨1,3,3⟩,[0,0,r299,r300,r301,r302,r303,r304,r305,r306,-262144]),(⟨1,4,0⟩,[0,r209,r210,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508]),(⟨1,4,2⟩,[0,0,r327,r644,r645,r646,r647,r648,r649,r650,-131072]),(⟨2,0,0⟩,[r386,r387,r388,r389,r390,r391,r392,r393,r394,r395,r396,r397,r398,r399,r400,r401]),(⟨2,0,1⟩,[r471,r472,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483,r484,r485]),(⟨2,0,2⟩,[r509,r510,r511,r512,r513,r514,r515,r516,r517,r518,r519,r520,r521,r522]),(⟨2,0,3⟩,[r523,r524,r525,r526,r527,r528,r529,r530,r531,r532,r533,r534,r535]),(⟨2,0,4⟩,[r536,r537,r538,r539,r540,r541,r542,r543,r544,r545,r546,r547]),(⟨2,0,5⟩,[r369,r548,r549,r550,r551,r552,r553,r554,r555,r556,r557]),(⟨2,0,6⟩,[r93,r558,r559,r560,r561,r562,r563,r564,r565,r566]),(⟨2,1,0⟩,[r471,r472,r473,r474,r475,r476,r477,r478,r479,r480,r481,r482,r483,r484,r485]),(⟨2,1,1⟩,[0,r230,r608,r609,r610,r611,r612,r613,r614,r615,r616,r617,r618,r619]),(⟨2,1,2⟩,[r93,r620,r621,r622,r623,r624,r625,r626,r627,r628,r629,r630,r631]),(⟨2,1,3⟩,[r632,r633,r634,r635,r636,r637,r638,r639,r640,r641,r642,r643]),(⟨2,1,4⟩,[0,0,r327,r644,r645,r646,r647,r648,r649,r650,-131072]),(⟨2,2,0⟩,[r509,r510,r511,r512,r513,r514,r515,r516,r517,r518,r519,r520,r521,r522]),(⟨2,2,1⟩,[r93,r620,r621,r622,r623,r624,r625,r626,r627,r628,r629,r630,r631]),(⟨2,2,2⟩,[r248,r651,r652,r653,r654,r655,r656,r657,r658,r659,r660,r661]),(⟨2,2,3⟩,[r0,r662,r663,r664,r665,r666,r667,r668,r669,r670,r671]),(⟨2,2,5⟩,[r241,r242,r243,r244,r211,r245,r246,r247,65536]),(⟨2,3,0⟩,[r523,r524,r525,r526,r527,r528,r529,r530,r531,r532,r533,r534,r535]),(⟨2,3,1⟩,[r632,r633,r634,r635,r636,r637,r638,r639,r640,r641,r642,r643]),(⟨2,3,2⟩,[r0,r662,r663,r664,r665,r666,r667,r668,r669,r670,r671]),(⟨2,3,3⟩,[r209,r210,r211,r212,r213,r214,r215,r216,r217,r218]),(⟨2,3,4⟩,[r587,r588,r589,r590,r559,r591,r592,r593,32768]),(⟨2,4,0⟩,[r536,r537,r538,r539,r540,r541,r542,r543,r544,r545,r546,r547]),(⟨2,4,1⟩,[0,0,r327,r644,r645,r646,r647,r648,r649,r650,-131072]),(⟨2,4,3⟩,[r587,r588,r589,r590,r559,r591,r592,r593,32768]),(⟨2,5,0⟩,[r369,r548,r549,r550,r551,r552,r553,r554,r555,r556,r557]),(⟨2,5,2⟩,[r241,r242,r243,r244,r211,r245,r246,r247,65536]),(⟨2,6,0⟩,[r93,r558,r559,r560,r561,r562,r563,r564,r565,r566]),(⟨3,0,0⟩,[r402,r403,r404,r405,r406,r407,r408,r409,r410,r411,r412,r413,r414,r415,r416]),(⟨3,0,1⟩,[r486,r487,r308,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498]),(⟨3,0,2⟩,[r523,r524,r525,r526,r527,r528,r529,r530,r531,r532,r533,r534,r535]),(⟨3,0,3⟩,[0,r241,r567,r568,r569,r570,r571,r572,r573,r574,r575,r576]),(⟨3,0,4⟩,[r174,r577,r578,r579,r580,r581,r582,r583,r584,r585,r586]),(⟨3,0,5⟩,[r93,r558,r559,r560,r561,r562,r563,r564,r565,r566]),(⟨3,1,0⟩,[r486,r487,r308,r488,r489,r490,r491,r492,r493,r494,r495,r496,r497,r498]),(⟨3,1,1⟩,[0,r209,r210,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508]),(⟨3,1,2⟩,[r632,r633,r634,r635,r636,r637,r638,r639,r640,r641,r642,r643]),(⟨3,1,3⟩,[0,0,r299,r300,r301,r302,r303,r304,r305,r306,-262144]),(⟨3,2,0⟩,[r523,r524,r525,r526,r527,r528,r529,r530,r531,r532,r533,r534,r535]),(⟨3,2,1⟩,[r632,r633,r634,r635,r636,r637,r638,r639,r640,r641,r642,r643]),(⟨3,2,2⟩,[r0,r662,r663,r664,r665,r666,r667,r668,r669,r670,r671]),(⟨3,2,3⟩,[r209,r210,r211,r212,r213,r214,r215,r216,r217,r218]),(⟨3,2,4⟩,[r587,r588,r589,r590,r559,r591,r592,r593,32768]),(⟨3,3,0⟩,[0,r241,r567,r568,r569,r570,r571,r572,r573,r574,r575,r576]),(⟨3,3,1⟩,[0,0,r299,r300,r301,r302,r303,r304,r305,r306,-262144]),(⟨3,3,2⟩,[r209,r210,r211,r212,r213,r214,r215,r216,r217,r218]),(⟨3,4,0⟩,[r174,r577,r578,r579,r580,r581,r582,r583,r584,r585,r586]),(⟨3,4,2⟩,[r587,r588,r589,r590,r559,r591,r592,r593,32768]),(⟨3,5,0⟩,[r93,r558,r559,r560,r561,r562,r563,r564,r565,r566]),(⟨4,0,0⟩,[r417,r418,r419,r420,r421,r422,r423,r424,r425,r426,r427,r428,r429,r430]),(⟨4,0,1⟩,[0,r209,r210,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508]),(⟨4,0,2⟩,[r536,r537,r538,r539,r540,r541,r542,r543,r544,r545,r546,r547]),(⟨4,0,3⟩,[r174,r577,r578,r579,r580,r581,r582,r583,r584,r585,r586]),(⟨4,0,5⟩,[r587,r588,r589,r590,r559,r591,r592,r593,32768]),(⟨4,1,0⟩,[0,r209,r210,r499,r500,r501,r502,r503,r504,r505,r506,r507,r508]),(⟨4,1,2⟩,[0,0,r327,r644,r645,r646,r647,r648,r649,r650,-131072]),(⟨4,2,0⟩,[r536,r537,r538,r539,r540,r541,r542,r543,r544,r545,r546,r547]),(⟨4,2,1⟩,[0,0,r327,r644,r645,r646,r647,r648,r649,r650,-131072]),(⟨4,2,3⟩,[r587,r588,r589,r590,r559,r591,r592,r593,32768]),(⟨4,3,0⟩,[r174,r577,r578,r579,r580,r581,r582,r583,r584,r585,r586]),(⟨4,3,2⟩,[r587,r588,r589,r590,r559,r591,r592,r593,32768]),(⟨4,5,0⟩,[r587,r588,r589,r590,r559,r591,r592,r593,32768]),(⟨5,0,0⟩,[r431,r432,r433,r434,r435,r436,r437,r438,r439,r440,r441,r442,r443]),(⟨5,0,2⟩,[r369,r548,r549,r550,r551,r552,r553,r554,r555,r556,r557]),(⟨5,0,3⟩,[r93,r558,r559,r560,r561,r562,r563,r564,r565,r566]),(⟨5,0,4⟩,[r587,r588,r589,r590,r559,r591,r592,r593,32768]),(⟨5,2,0⟩,[r369,r548,r549,r550,r551,r552,r553,r554,r555,r556,r557]),(⟨5,2,2⟩,[r241,r242,r243,r244,r211,r245,r246,r247,65536]),(⟨5,3,0⟩,[r93,r558,r559,r560,r561,r562,r563,r564,r565,r566]),(⟨5,4,0⟩,[r587,r588,r589,r590,r559,r591,r592,r593,32768]),(⟨6,0,0⟩,[r444,r445,r446,r447,r448,r449,r450,r451,r452,r453,r454,r455]),(⟨6,0,2⟩,[r93,r558,r559,r560,r561,r562,r563,r564,r565,r566]),(⟨6,2,0⟩,[r93,r558,r559,r560,r561,r562,r563,r564,r565,r566])]


noncomputable def sourceLeft : Poly := [(⟨0,0,0⟩,[-256,4800,-35712,145856,-387968,744000,-1039488,811328,-95104]),(⟨0,0,1⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨0,0,2⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨0,0,3⟩,[128,-2688,15616,-40192,84608,-123008]),(⟨0,1,0⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨0,1,1⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨0,2,0⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨0,2,2⟩,[-256,3072,-7680,-9216,30464]),(⟨0,3,0⟩,[128,-2688,15616,-40192,84608,-123008]),(⟨1,0,0⟩,[-64,1856,-17088,77248,-216000,443584,-645440,486976]),(⟨1,0,1⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨1,1,0⟩,[0,0,1024,-12288,30720,36864,-121856]),(⟨2,0,0⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨2,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨2,2,0⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[128,-2688,15616,-40192,84608,-123008])]
noncomputable def sourceRight : Poly := [(⟨0,0,0⟩,[128,-2368,16192,-48960,27712,296128,-1096256,1862976,-1545664,318080]),(⟨0,0,1⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨0,0,2⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨0,0,3⟩,[-64,1280,-6336,2560,43072,-131840,181440]),(⟨0,1,0⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨0,1,1⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248]),(⟨0,2,0⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨0,2,3⟩,[-128,1536,-3840,-4608,15232]),(⟨0,3,0⟩,[-64,1280,-6336,2560,43072,-131840,181440]),(⟨0,3,2⟩,[-128,1536,-3840,-4608,15232]),(⟨1,0,0⟩,[64,-1472,11648,-39616,35200,177856,-723584,1197504,-862400]),(⟨1,0,1⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248]),(⟨1,1,0⟩,[0,-256,3584,-15616,27648,-4864,-125440,213248]),(⟨2,0,0⟩,[-128,1792,-6272,-3200,47232,-116736,158848,-24192]),(⟨2,0,3⟩,[-128,1536,-3840,-4608,15232]),(⟨2,3,0⟩,[-128,1536,-3840,-4608,15232]),(⟨3,0,0⟩,[-64,1280,-6336,2560,43072,-131840,181440]),(⟨3,0,2⟩,[-128,1536,-3840,-4608,15232]),(⟨3,2,0⟩,[-128,1536,-3840,-4608,15232])]

theorem left_checked :
    (Poly.add (Data.S6_trivial.polys.getD 6 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r672) sourceLeft))).isZero := by decide +kernel

theorem right_checked :
    (Poly.add (Data.S6_trivial.polys.getD 7 [])
      (Poly.scale (K.ofRat (-1)) (Poly.scale (K.ofRat r672) sourceRight))).isZero := by decide +kernel

noncomputable def partial16 : Poly := []

theorem partial_sound16 (u v t : ℝ) :
    (Poly.mul (sourceLeft.drop 16)
      sourceRight).eval u v t=partial16.eval u v t := by rfl

noncomputable def chunk12 : Poly := [(⟨2,0,0⟩,[320,-4864,23616,-50176,73152,-59648,-47936]),(⟨2,0,2⟩,[-256,3072,-7680,-9216,30464]),(⟨2,2,0⟩,[-256,3072,-7680,-9216,30464]),(⟨3,0,0⟩,[128,-2688,15616,-40192,84608,-123008])]

noncomputable def partial12 : Poly := [(⟨2,0,0⟩,[40960,-1380352,19722240,-156770304,757579776,-2189578240,2639482880,7097393152,-46132453376,128978014208,-230711390208,272541720576,-187601059840,26160336896,55120113664,-15247482880]),(⟨2,0,1⟩,[20480,-782336,12398592,-107307008,557576192,-1745817600,2659225600,2814558208,-27733282816,81591463936,-145680117760,165506228224,-99829280768,-5963116544,41340006400]),(⟨2,0,2⟩,[-73728,2195456,-26148864,157507584,-472850432,274735104,3257073664,-13718798336,26326114304,-19758071808,-20184825856,62906884096,-56190066688,10849656832]),(⟨2,0,3⟩,[-36864,1294336,-17760256,121716736,-421859328,438796288,2232516608,-11080007680,23091761152,-21199536128,-7384236032,39925989376,-34969661440]),(⟨2,0,4⟩,[32768,-851968,8093696,-31031296,5832704,311951360,-923598848,857931776,1220444160,-4834394112,5062098944,-736985088]),(⟨2,0,5⟩,[16384,-524288,6045696,-29360128,31752192,243793920,-998866944,1250951168,1133723648,-5688524800,5527388160]),(⟨2,1,0⟩,[20480,-782336,12398592,-107307008,557576192,-1745817600,2659225600,2814558208,-27733282816,81591463936,-145680117760,165506228224,-99829280768,-5963116544,41340006400]),(⟨2,1,1⟩,[0,-81920,2392064,-28475392,182288384,-703381504,1697447936,-2167603200,-973406208,10073751552,-20911325184,23314923520,-6706724864,-10222256128]),(⟨2,1,2⟩,[-16384,573440,-7995392,56639488,-204652544,214663168,1181220864,-5426610176,8889843712,240631808,-26456227840,44428640256,-26272153600]),(⟨2,1,3⟩,[0,65536,-1703936,16973824,-80216064,165281792,57933824,-1133117440,2505572352,-629866496,-5786697728,6496387072]),(⟨2,2,0⟩,[-73728,2195456,-26148864,157507584,-472850432,274735104,3257073664,-13718798336,26326114304,-19758071808,-20184825856,62906884096,-56190066688,10849656832]),(⟨2,2,1⟩,[-16384,573440,-7995392,56639488,-204652544,214663168,1181220864,-5426610176,8889843712,240631808,-26456227840,44428640256,-26272153600]),(⟨2,2,2⟩,[65536,-1703936,16187392,-62062592,11665408,623902720,-1847197696,1715863552,2440888320,-9668788224,10124197888,-1473970176]),(⟨2,2,3⟩,[-24576,589824,-5677056,30539776,-118079488,373555200,-774324224,305004544,2706907136,-6376194048,4797227008]),(⟨2,2,5⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,3,0⟩,[-36864,1294336,-17760256,121716736,-421859328,438796288,2232516608,-11080007680,23091761152,-21199536128,-7384236032,39925989376,-34969661440]),(⟨2,3,1⟩,[0,65536,-1703936,16973824,-80216064,165281792,57933824,-1133117440,2505572352,-629866496,-5786697728,6496387072]),(⟨2,3,2⟩,[-24576,589824,-5677056,30539776,-118079488,373555200,-774324224,305004544,2706907136,-6376194048,4797227008]),(⟨2,3,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,4,0⟩,[32768,-851968,8093696,-31031296,5832704,311951360,-923598848,857931776,1220444160,-4834394112,5062098944,-736985088]),(⟨2,4,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,5,0⟩,[16384,-524288,6045696,-29360128,31752192,243793920,-998866944,1250951168,1133723648,-5688524800,5527388160]),(⟨2,5,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,0,0⟩,[36864,-1429504,22835200,-199221248,1051586560,-3413848064,5784719360,3376136192,-53592788992,180585877504,-374727077888,525067624448,-472550043648,211078033408,2213621760]),(⟨3,0,1⟩,[8192,-442368,8839168,-90415104,539754496,-1994448896,4435263488,-3491315712,-14899273728,70892552192,-165607350272,248301543424,-226975236096,95859843072]),(⟨3,0,2⟩,[-32768,1146880,-15613952,106217472,-370802688,442236928,1630437376,-9077227520,20517126144,-22208282624,2315370496,22842228736,-23296344064]),(⟨3,0,3⟩,[-8192,401408,-6955008,56893440,-237387776,443432960,311738368,-4414816256,13967187968,-24375222272,25781952512,-15822184448]),(⟨3,1,0⟩,[8192,-442368,8839168,-90415104,539754496,-1994448896,4435263488,-3491315712,-14899273728,70892552192,-165607350272,248301543424,-226975236096,95859843072]),(⟨3,1,1⟩,[0,-32768,1146880,-15630336,111771648,-484507648,1391132672,-2584805376,1923547136,4559306752,-18585780224,33472610304,-26231209984]),(⟨3,1,2⟩,[0,65536,-1703936,16973824,-80216064,165281792,57933824,-1133117440,2505572352,-629866496,-5786697728,6496387072]),(⟨3,2,0⟩,[-32768,1146880,-15613952,106217472,-370802688,442236928,1630437376,-9077227520,20517126144,-22208282624,2315370496,22842228736,-23296344064]),(⟨3,2,1⟩,[0,65536,-1703936,16973824,-80216064,165281792,57933824,-1133117440,2505572352,-629866496,-5786697728,6496387072]),(⟨3,2,3⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨3,3,0⟩,[-8192,401408,-6955008,56893440,-237387776,443432960,311738368,-4414816256,13967187968,-24375222272,25781952512,-15822184448]),(⟨3,3,2⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨4,0,0⟩,[-32768,835584,-7299072,16285696,140746752,-1180303360,4072882176,-7176716288,-252854272,41073754112,-127163162624,219337818112,-226440044544,107241766912]),(⟨4,0,1⟩,[0,-32768,1146880,-15630336,111771648,-484507648,1391132672,-2584805376,1923547136,4559306752,-18585780224,33472610304,-26231209984]),(⟨4,0,2⟩,[32768,-851968,8093696,-31031296,5832704,311951360,-923598848,857931776,1220444160,-4834394112,5062098944,-736985088]),(⟨4,0,3⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨4,0,5⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,1,0⟩,[0,-32768,1146880,-15630336,111771648,-484507648,1391132672,-2584805376,1923547136,4559306752,-18585780224,33472610304,-26231209984]),(⟨4,2,0⟩,[32768,-851968,8093696,-31031296,5832704,311951360,-923598848,857931776,1220444160,-4834394112,5062098944,-736985088]),(⟨4,2,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,3,0⟩,[-40960,1114112,-11722752,59899904,-149831680,129761280,224542720,-945946624,1573183488,-687669248,-730161152]),(⟨4,3,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,5,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,0,0⟩,[-36864,1294336,-17383424,114655232,-383356928,451706880,1500512256,-9304014848,25829199872,-43889082368,47843590144,-26089062400,-5721698304]),(⟨5,0,2⟩,[-24576,589824,-5677056,30539776,-118079488,373555200,-774324224,305004544,2706907136,-6376194048,4797227008]),(⟨5,0,3⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨5,0,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,2,0⟩,[-24576,589824,-5677056,30539776,-118079488,373555200,-774324224,305004544,2706907136,-6376194048,4797227008]),(⟨5,2,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,3,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨5,4,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,0,0⟩,[-8192,335872,-5251072,39919616,-157171712,278151168,253804544,-3281698816,11461615616,-23745355776,31568650240,-22318571520]),(⟨6,0,2⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨6,2,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856])]


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

noncomputable def partial8 : Poly := [(⟨0,3,0⟩,[16384,-647168,10436608,-91914240,494010368,-1668030464,3125493760,561577984,-25859506176,98994413568,-229046960128,359561396224,-372720762880,217041149952,-39126384640]),(⟨0,3,1⟩,[8192,-360448,6447104,-61939712,357466112,-1291067392,2737815552,-1323712512,-13925867520,60818800640,-144696025088,224986619904,-220268511232,106082099200]),(⟨0,3,2⟩,[-16384,573440,-7618560,49577984,-166150144,227573760,449216512,-3650617344,11627282432,-22448914432,28771598336,-21586411520,2975809536]),(⟨0,3,3⟩,[-8192,335872,-5251072,39919616,-157171712,278151168,253804544,-3281698816,11461615616,-23745355776,31568650240,-22318571520]),(⟨0,4,0⟩,[8192,-360448,6447104,-61939712,357466112,-1291067392,2737815552,-1323712512,-13925867520,60818800640,-144696025088,224986619904,-220268511232,106082099200]),(⟨0,4,1⟩,[0,-32768,1146880,-15630336,111771648,-484507648,1391132672,-2584805376,1923547136,4559306752,-18585780224,33472610304,-26231209984]),(⟨0,5,0⟩,[-16384,573440,-7618560,49577984,-166150144,227573760,449216512,-3650617344,11627282432,-22448914432,28771598336,-21586411520,2975809536]),(⟨0,5,3⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨0,6,0⟩,[-8192,335872,-5251072,39919616,-157171712,278151168,253804544,-3281698816,11461615616,-23745355776,31568650240,-22318571520]),(⟨0,6,2⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨1,0,0⟩,[-8192,389120,-7618560,83537920,-579903488,2688176128,-8266326016,14275186688,5856935936,-131592417280,497333993472,-1191157018624,2036595515392,-2490626691072,2045953171456,-958002827264,154897326080]),(⟨1,0,1⟩,[-4096,212992,-4440064,50253824,-352743424,1659904000,-5471051776,12309606400,-12717780992,-38056493056,249805766656,-743851544576,1421984428032,-1782054608896,1339857297408,-458728058880]),(⟨1,0,2⟩,[8192,-352256,5980160,-54239232,296271872,-1005092864,1769758720,1771159552,-23202521088,79567953920,-155565293568,173072310272,-64280756224,-84744912896,93307691008]),(⟨1,0,3⟩,[4096,-200704,3743744,-35332096,190590976,-625553408,1159774208,448217088,-13045567488,53429833728,-129108664320,205891297280,-201559945216,91304865792]),(⟨1,0,4⟩,[0,0,-65536,2097152,-24182784,117440512,-127008768,-975175680,3995467776,-5003804672,-4534894592,22754099200,-22109552640]),(⟨1,1,0⟩,[-4096,212992,-4440064,50253824,-352743424,1659904000,-5471051776,12309606400,-12717780992,-38056493056,249805766656,-743851544576,1421984428032,-1782054608896,1339857297408,-458728058880]),(⟨1,1,1⟩,[0,16384,-573440,7438336,-47808512,197509120,-930234368,5383192576,-22623092736,55218257920,-55158063104,-87026466816,384838565888,-554154180608,314023886848]),(⟨1,1,2⟩,[0,0,-131072,3145728,-25559040,56229888,297533440,-1908932608,3462660096,1100742656,-14904066048,21857042432,2898395136,-23037607936]),(⟨1,1,3⟩,[0,0,-65536,2097152,-24182784,117440512,-127008768,-975175680,3995467776,-5003804672,-4534894592,22754099200,-22109552640]),(⟨1,2,0⟩,[8192,-352256,5980160,-54239232,296271872,-1005092864,1769758720,1771159552,-23202521088,79567953920,-155565293568,173072310272,-64280756224,-84744912896,93307691008]),(⟨1,2,1⟩,[0,0,-131072,3145728,-25559040,56229888,297533440,-1908932608,3462660096,1100742656,-14904066048,21857042432,2898395136,-23037607936]),(⟨1,2,3⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨1,2,4⟩,[0,0,-131072,3145728,-26738688,84934656,26476544,-657457152,765984768,1123024896,-1856110592]),(⟨1,3,0⟩,[12288,-561152,10190848,-97271808,548057088,-1916620800,3897589760,-875495424,-26971435008,114248634368,-273804689408,430877917184,-421828456448,197386964992]),(⟨1,3,1⟩,[0,-32768,1081344,-13533184,87588864,-367067136,1264123904,-3559981056,5919014912,-444497920,-23120674816,56226709504,-48340762624]),(⟨1,3,2⟩,[8192,-335872,5283840,-42967040,202391552,-578174976,977158144,-585121792,-2107662336,7860871168,-12075327488,7417618432]),(⟨1,3,3⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨1,4,0⟩,[0,-32768,1081344,-13533184,87588864,-367067136,1264123904,-3559981056,5919014912,-444497920,-23120674816,56226709504,-48340762624]),(⟨1,4,2⟩,[0,0,-131072,3145728,-26738688,84934656,26476544,-657457152,765984768,1123024896,-1856110592]),(⟨2,0,0⟩,[36864,-1167360,15151104,-102518784,355225600,-212545536,-3856093184,20062883840,-51162206208,59458342912,69706780672,-471361925120,1083512614912,-1481671528448,1194903277568,-435215585280]),(⟨2,0,1⟩,[20480,-765952,11759616,-97574912,477786112,-1321750528,910381056,9056403456,-45631492096,115103281152,-165278806016,79442288640,179184373760,-382402736128,250275278848]),(⟨2,0,2⟩,[-73728,2195456,-26148864,157245440,-466034688,206839808,3577937920,-14379925504,26094379008,-15225602048,-30207115264,65426350080,-33043275776,-15135891456]),(⟨2,0,3⟩,[-36864,1294336,-17760256,121716736,-421859328,438796288,2232516608,-11080007680,23091761152,-21199536128,-7384236032,39925989376,-34969661440]),(⟨2,0,4⟩,[32768,-851968,8093696,-31031296,5832704,311951360,-923598848,857931776,1220444160,-4834394112,5062098944,-736985088]),(⟨2,0,5⟩,[16384,-524288,6045696,-29360128,31752192,243793920,-998866944,1250951168,1133723648,-5688524800,5527388160]),(⟨2,1,0⟩,[20480,-765952,11759616,-97574912,477786112,-1321750528,910381056,9056403456,-45631492096,115103281152,-165278806016,79442288640,179184373760,-382402736128,250275278848]),(⟨2,1,1⟩,[0,-81920,2392064,-28999680,195919872,-839172096,2339176448,-3489857536,-1436876800,19138691072,-40955904000,28353855488,39586856960,-62193352704]),(⟨2,1,2⟩,[-16384,573440,-7995392,56639488,-204652544,214663168,1181220864,-5426610176,8889843712,240631808,-26456227840,44428640256,-26272153600]),(⟨2,1,3⟩,[0,65536,-1703936,16973824,-80216064,165281792,57933824,-1133117440,2505572352,-629866496,-5786697728,6496387072]),(⟨2,2,0⟩,[-73728,2195456,-26148864,157245440,-466034688,206839808,3577937920,-14379925504,26094379008,-15225602048,-30207115264,65426350080,-33043275776,-15135891456]),(⟨2,2,1⟩,[-16384,573440,-7995392,56639488,-204652544,214663168,1181220864,-5426610176,8889843712,240631808,-26456227840,44428640256,-26272153600]),(⟨2,2,2⟩,[65536,-1703936,16187392,-62062592,11665408,623902720,-1847197696,1715863552,2440888320,-9668788224,10124197888,-1473970176]),(⟨2,2,3⟩,[-24576,589824,-5677056,30539776,-118079488,373555200,-774324224,305004544,2706907136,-6376194048,4797227008]),(⟨2,2,5⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,3,0⟩,[-53248,1867776,-25378816,171294720,-588009472,666370048,2681733120,-14730625024,34719043584,-43648450560,21387362304,18339577856,-31993851904]),(⟨2,3,1⟩,[0,65536,-1703936,16973824,-80216064,165281792,57933824,-1133117440,2505572352,-629866496,-5786697728,6496387072]),(⟨2,3,2⟩,[-24576,589824,-5677056,30539776,-118079488,373555200,-774324224,305004544,2706907136,-6376194048,4797227008]),(⟨2,3,3⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨2,3,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,4,0⟩,[32768,-851968,8093696,-31031296,5832704,311951360,-923598848,857931776,1220444160,-4834394112,5062098944,-736985088]),(⟨2,4,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,5,0⟩,[16384,-524288,6045696,-29360128,31752192,243793920,-998866944,1250951168,1133723648,-5688524800,5527388160]),(⟨2,5,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,6,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨3,0,0⟩,[45056,-1781760,28749824,-251166720,1315876864,-4192382976,6735867904,6005948416,-72070426624,238447390720,-494732996608,699102461952,-642655711232,304047681536,-9567301632]),(⟨3,0,1⟩,[8192,-442368,8708096,-87007232,507379712,-1870323712,4411932672,-4739121152,-11204878336,67460825088,-170489126912,267639119872,-247223631872,98807783424]),(⟨3,0,2⟩,[-32768,1146880,-15613952,106217472,-370802688,442236928,1630437376,-9077227520,20517126144,-22208282624,2315370496,22842228736,-23296344064]),(⟨3,0,3⟩,[0,65536,-1671168,13926400,-34996224,-134742016,1288896512,-4999938048,11859525632,-16514351104,13706625024,-8404566016]),(⟨3,0,4⟩,[0,0,-131072,3145728,-26738688,84934656,26476544,-657457152,765984768,1123024896,-1856110592]),(⟨3,1,0⟩,[8192,-442368,8708096,-87007232,507379712,-1870323712,4411932672,-4739121152,-11204878336,67460825088,-170489126912,267639119872,-247223631872,98807783424]),(⟨3,1,1⟩,[0,-32768,1146880,-15630336,111771648,-484507648,1391132672,-2584805376,1923547136,4559306752,-18585780224,33472610304,-26231209984]),(⟨3,1,2⟩,[0,65536,-1703936,16973824,-80216064,165281792,57933824,-1133117440,2505572352,-629866496,-5786697728,6496387072]),(⟨3,1,3⟩,[0,0,-131072,3145728,-26738688,84934656,26476544,-657457152,765984768,1123024896,-1856110592]),(⟨3,2,0⟩,[-32768,1146880,-15613952,106217472,-370802688,442236928,1630437376,-9077227520,20517126144,-22208282624,2315370496,22842228736,-23296344064]),(⟨3,2,1⟩,[0,65536,-1703936,16973824,-80216064,165281792,57933824,-1133117440,2505572352,-629866496,-5786697728,6496387072]),(⟨3,2,3⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨3,3,0⟩,[-8192,401408,-6922240,53846016,-192167936,143409152,1542701056,-8281636864,23321141248,-40259706880,45275275264,-30723137536]),(⟨3,3,1⟩,[0,0,-131072,3145728,-26738688,84934656,26476544,-657457152,765984768,1123024896,-1856110592]),(⟨3,3,2⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨3,4,0⟩,[0,0,-131072,3145728,-26738688,84934656,26476544,-657457152,765984768,1123024896,-1856110592]),(⟨3,5,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨4,0,0⟩,[-28672,634880,-3424256,-22454272,363712512,-1929981952,5255987200,-5480693760,-16992817152,97935314944,-251390050304,405891538944,-407751593984,195598692352]),(⟨4,0,1⟩,[0,-32768,1081344,-13533184,87588864,-367067136,1264123904,-3559981056,5919014912,-444497920,-23120674816,56226709504,-48340762624]),(⟨4,0,2⟩,[40960,-1187840,13377536,-73998336,208224256,-266223616,53559296,272809984,-887218176,3026477056,-7013228544,6680633344]),(⟨4,0,3⟩,[-40960,1114112,-11853824,63045632,-176570368,214695936,251019264,-1603403776,2339168256,435355648,-2586271744]),(⟨4,0,5⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,1,0⟩,[0,-32768,1081344,-13533184,87588864,-367067136,1264123904,-3559981056,5919014912,-444497920,-23120674816,56226709504,-48340762624]),(⟨4,1,2⟩,[0,0,-131072,3145728,-26738688,84934656,26476544,-657457152,765984768,1123024896,-1856110592]),(⟨4,2,0⟩,[40960,-1187840,13377536,-73998336,208224256,-266223616,53559296,272809984,-887218176,3026477056,-7013228544,6680633344]),(⟨4,2,1⟩,[0,0,-131072,3145728,-26738688,84934656,26476544,-657457152,765984768,1123024896,-1856110592]),(⟨4,2,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,3,0⟩,[-40960,1114112,-11853824,63045632,-176570368,214695936,251019264,-1603403776,2339168256,435355648,-2586271744]),(⟨4,3,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,5,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,0,0⟩,[-36864,1294336,-17383424,114655232,-383356928,451706880,1500512256,-9304014848,25829199872,-43889082368,47843590144,-26089062400,-5721698304]),(⟨5,0,2⟩,[-24576,589824,-5677056,30539776,-118079488,373555200,-774324224,305004544,2706907136,-6376194048,4797227008]),(⟨5,0,3⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨5,0,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,2,0⟩,[-24576,589824,-5677056,30539776,-118079488,373555200,-774324224,305004544,2706907136,-6376194048,4797227008]),(⟨5,2,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,3,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨5,4,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,0,0⟩,[-8192,335872,-5251072,39919616,-157171712,278151168,253804544,-3281698816,11461615616,-23745355776,31568650240,-22318571520]),(⟨6,0,2⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨6,2,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856])]


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

noncomputable def partial4 : Poly := [(⟨0,1,0⟩,[-8192,389120,-7618560,83537920,-579903488,2688176128,-8266326016,14275186688,5856935936,-131592417280,497333993472,-1191157018624,2036595515392,-2490626691072,2045953171456,-958002827264,154897326080]),(⟨0,1,1⟩,[-4096,212992,-4440064,50253824,-352743424,1659904000,-5471051776,12309606400,-12717780992,-38056493056,249805766656,-743851544576,1421984428032,-1782054608896,1339857297408,-458728058880]),(⟨0,1,2⟩,[8192,-352256,5980160,-54239232,296271872,-1005092864,1769758720,1771159552,-23202521088,79567953920,-155565293568,173072310272,-64280756224,-84744912896,93307691008]),(⟨0,1,3⟩,[4096,-200704,3743744,-35332096,190590976,-625553408,1159774208,448217088,-13045567488,53429833728,-129108664320,205891297280,-201559945216,91304865792]),(⟨0,1,4⟩,[0,0,-65536,2097152,-24182784,117440512,-127008768,-975175680,3995467776,-5003804672,-4534894592,22754099200,-22109552640]),(⟨0,2,0⟩,[36864,-1167360,15151104,-102518784,355225600,-212545536,-3856093184,20062883840,-51162206208,59458342912,69706780672,-471361925120,1083512614912,-1481671528448,1194903277568,-435215585280]),(⟨0,2,1⟩,[20480,-765952,11759616,-97574912,477786112,-1321750528,910381056,9056403456,-45631492096,115103281152,-165278806016,79442288640,179184373760,-382402736128,250275278848]),(⟨0,2,2⟩,[-73728,2195456,-26148864,157245440,-466034688,206839808,3577937920,-14379925504,26094379008,-15225602048,-30207115264,65426350080,-33043275776,-15135891456]),(⟨0,2,3⟩,[-36864,1294336,-17760256,121716736,-421859328,438796288,2232516608,-11080007680,23091761152,-21199536128,-7384236032,39925989376,-34969661440]),(⟨0,2,4⟩,[32768,-851968,8093696,-31031296,5832704,311951360,-923598848,857931776,1220444160,-4834394112,5062098944,-736985088]),(⟨0,2,5⟩,[16384,-524288,6045696,-29360128,31752192,243793920,-998866944,1250951168,1133723648,-5688524800,5527388160]),(⟨0,3,0⟩,[45056,-1781760,28749824,-251166720,1315876864,-4192382976,6735867904,6005948416,-72070426624,238447390720,-494732996608,699102461952,-642655711232,304047681536,-9567301632]),(⟨0,3,1⟩,[8192,-442368,8708096,-87007232,507379712,-1870323712,4411932672,-4739121152,-11204878336,67460825088,-170489126912,267639119872,-247223631872,98807783424]),(⟨0,3,2⟩,[-32768,1146880,-15613952,106217472,-370802688,442236928,1630437376,-9077227520,20517126144,-22208282624,2315370496,22842228736,-23296344064]),(⟨0,3,3⟩,[0,65536,-1671168,13926400,-34996224,-134742016,1288896512,-4999938048,11859525632,-16514351104,13706625024,-8404566016]),(⟨0,3,4⟩,[0,0,-131072,3145728,-26738688,84934656,26476544,-657457152,765984768,1123024896,-1856110592]),(⟨0,4,0⟩,[-28672,634880,-3424256,-22454272,363712512,-1929981952,5255987200,-5480693760,-16992817152,97935314944,-251390050304,405891538944,-407751593984,195598692352]),(⟨0,4,1⟩,[0,-32768,1081344,-13533184,87588864,-367067136,1264123904,-3559981056,5919014912,-444497920,-23120674816,56226709504,-48340762624]),(⟨0,4,2⟩,[40960,-1187840,13377536,-73998336,208224256,-266223616,53559296,272809984,-887218176,3026477056,-7013228544,6680633344]),(⟨0,4,3⟩,[-40960,1114112,-11853824,63045632,-176570368,214695936,251019264,-1603403776,2339168256,435355648,-2586271744]),(⟨0,4,5⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨0,5,0⟩,[-36864,1294336,-17383424,114655232,-383356928,451706880,1500512256,-9304014848,25829199872,-43889082368,47843590144,-26089062400,-5721698304]),(⟨0,5,2⟩,[-24576,589824,-5677056,30539776,-118079488,373555200,-774324224,305004544,2706907136,-6376194048,4797227008]),(⟨0,5,3⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨0,5,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨0,6,0⟩,[-8192,335872,-5251072,39919616,-157171712,278151168,253804544,-3281698816,11461615616,-23745355776,31568650240,-22318571520]),(⟨0,6,2⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨1,0,0⟩,[-8192,389120,-7618560,83537920,-579903488,2688176128,-8266326016,14275186688,5856935936,-131592417280,497333993472,-1191157018624,2036595515392,-2490626691072,2045953171456,-958002827264,154897326080]),(⟨1,0,1⟩,[-4096,212992,-4440064,50253824,-352743424,1659904000,-5471051776,12309606400,-12717780992,-38056493056,249805766656,-743851544576,1421984428032,-1782054608896,1339857297408,-458728058880]),(⟨1,0,2⟩,[8192,-352256,5980160,-54239232,296271872,-1005092864,1769758720,1771159552,-23202521088,79567953920,-155565293568,173072310272,-64280756224,-84744912896,93307691008]),(⟨1,0,3⟩,[4096,-200704,3743744,-35332096,190590976,-625553408,1159774208,448217088,-13045567488,53429833728,-129108664320,205891297280,-201559945216,91304865792]),(⟨1,0,4⟩,[0,0,-65536,2097152,-24182784,117440512,-127008768,-975175680,3995467776,-5003804672,-4534894592,22754099200,-22109552640]),(⟨1,1,0⟩,[-8192,425984,-9011200,104505344,-755097600,3636936704,-11966627840,25275097088,-17747533824,-107576164352,550223937536,-1487755190272,2693098102784,-3289886474240,2479640461312,-878696161280]),(⟨1,1,1⟩,[0,32768,-1212416,17170432,-127598592,621576192,-2679078912,11625037824,-40521302016,88730075136,-74756751360,-173090406400,663852220416,-930593800192,522959159296]),(⟨1,1,2⟩,[0,0,-131072,2883584,-18743296,-11665408,618397696,-2570059776,3230924800,5633212416,-24926355456,24376508416,26045186048,-49023156224]),(⟨1,1,3⟩,[0,0,-65536,2097152,-24182784,117440512,-127008768,-975175680,3995467776,-5003804672,-4534894592,22754099200,-22109552640]),(⟨1,2,0⟩,[28672,-1118208,17674240,-149520384,742076416,-2100285440,1861529600,11686215680,-64109129728,172964794368,-285284724736,253477126144,9078706176,-289433088000,238494355456]),(⟨1,2,1⟩,[0,-81920,2260992,-25591808,163545088,-715046912,2315845632,-4737662976,2257518592,15706963968,-45837680640,47691431936,19338461184,-59245412352]),(⟨1,2,2⟩,[-16384,573440,-7995392,56639488,-204652544,214663168,1181220864,-5426610176,8889843712,240631808,-26456227840,44428640256,-26272153600]),(⟨1,2,3⟩,[8192,-270336,3579904,-25993216,122175488,-412893184,1035091968,-1718239232,397910016,7231004672,-17862025216,13914005504]),(⟨1,2,4⟩,[0,0,-131072,3145728,-26738688,84934656,26476544,-657457152,765984768,1123024896,-1856110592]),(⟨1,3,0⟩,[12288,-643072,12582912,-125747200,730345472,-2620002304,5595037696,-3043098624,-27944841216,124322385920,-294716014592,454192840704,-428535181312,187164708864]),(⟨1,3,1⟩,[0,-32768,1081344,-13533184,87588864,-367067136,1264123904,-3559981056,5919014912,-444497920,-23120674816,56226709504,-48340762624]),(⟨1,3,2⟩,[8192,-270336,3579904,-25993216,122175488,-412893184,1035091968,-1718239232,397910016,7231004672,-17862025216,13914005504]),(⟨1,3,3⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨1,4,0⟩,[0,-32768,1081344,-13533184,87588864,-367067136,1264123904,-3559981056,5919014912,-444497920,-23120674816,56226709504,-48340762624]),(⟨1,4,2⟩,[0,0,-131072,3145728,-26738688,84934656,26476544,-657457152,765984768,1123024896,-1856110592]),(⟨2,0,0⟩,[36864,-1167360,15151104,-102518784,355225600,-212545536,-3856093184,20062883840,-51162206208,59458342912,69706780672,-471361925120,1083512614912,-1481671528448,1194903277568,-435215585280]),(⟨2,0,1⟩,[20480,-765952,11759616,-97574912,477786112,-1321750528,910381056,9056403456,-45631492096,115103281152,-165278806016,79442288640,179184373760,-382402736128,250275278848]),(⟨2,0,2⟩,[-73728,2195456,-26148864,157245440,-466034688,206839808,3577937920,-14379925504,26094379008,-15225602048,-30207115264,65426350080,-33043275776,-15135891456]),(⟨2,0,3⟩,[-36864,1294336,-17760256,121716736,-421859328,438796288,2232516608,-11080007680,23091761152,-21199536128,-7384236032,39925989376,-34969661440]),(⟨2,0,4⟩,[32768,-851968,8093696,-31031296,5832704,311951360,-923598848,857931776,1220444160,-4834394112,5062098944,-736985088]),(⟨2,0,5⟩,[16384,-524288,6045696,-29360128,31752192,243793920,-998866944,1250951168,1133723648,-5688524800,5527388160]),(⟨2,1,0⟩,[28672,-1118208,17674240,-149520384,742076416,-2100285440,1861529600,11686215680,-64109129728,172964794368,-285284724736,253477126144,9078706176,-289433088000,238494355456]),(⟨2,1,1⟩,[0,-81920,2260992,-25591808,163545088,-715046912,2315845632,-4737662976,2257518592,15706963968,-45837680640,47691431936,19338461184,-59245412352]),(⟨2,1,2⟩,[-16384,573440,-7995392,56639488,-204652544,214663168,1181220864,-5426610176,8889843712,240631808,-26456227840,44428640256,-26272153600]),(⟨2,1,3⟩,[8192,-270336,3579904,-25993216,122175488,-412893184,1035091968,-1718239232,397910016,7231004672,-17862025216,13914005504]),(⟨2,1,4⟩,[0,0,-131072,3145728,-26738688,84934656,26476544,-657457152,765984768,1123024896,-1856110592]),(⟨2,2,0⟩,[-114688,3391488,-39895040,235470848,-682754048,317603840,4913004544,-20232929280,39767392256,-34970648576,-12674252800,59777548288,-39214809088,-13976223744]),(⟨2,2,1⟩,[-16384,573440,-7995392,56639488,-204652544,214663168,1181220864,-5426610176,8889843712,240631808,-26456227840,44428640256,-26272153600]),(⟨2,2,2⟩,[98304,-2555904,24281088,-93093888,17498112,935854080,-2770796544,2573795328,3661332480,-14503182336,15186296832,-2210955264]),(⟨2,2,3⟩,[-65536,1703936,-17399808,90439680,-267911168,503316480,-549781504,-640942080,4280090624,-7063863296,4067065856]),(⟨2,2,5⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,3,0⟩,[-53248,1867776,-25378816,171294720,-588009472,666370048,2681733120,-14730625024,34719043584,-43648450560,21387362304,18339577856,-31993851904]),(⟨2,3,1⟩,[0,65536,-1703936,16973824,-80216064,165281792,57933824,-1133117440,2505572352,-629866496,-5786697728,6496387072]),(⟨2,3,2⟩,[-24576,589824,-5677056,30539776,-118079488,373555200,-774324224,305004544,2706907136,-6376194048,4797227008]),(⟨2,3,3⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨2,3,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,4,0⟩,[40960,-1187840,13377536,-73998336,208224256,-266223616,53559296,272809984,-887218176,3026477056,-7013228544,6680633344]),(⟨2,4,1⟩,[0,0,-131072,3145728,-26738688,84934656,26476544,-657457152,765984768,1123024896,-1856110592]),(⟨2,4,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,5,0⟩,[-24576,589824,-5677056,30539776,-118079488,373555200,-774324224,305004544,2706907136,-6376194048,4797227008]),(⟨2,5,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,6,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨3,0,0⟩,[45056,-1781760,28749824,-251166720,1315876864,-4192382976,6735867904,6005948416,-72070426624,238447390720,-494732996608,699102461952,-642655711232,304047681536,-9567301632]),(⟨3,0,1⟩,[8192,-442368,8708096,-87007232,507379712,-1870323712,4411932672,-4739121152,-11204878336,67460825088,-170489126912,267639119872,-247223631872,98807783424]),(⟨3,0,2⟩,[-32768,1146880,-15613952,106217472,-370802688,442236928,1630437376,-9077227520,20517126144,-22208282624,2315370496,22842228736,-23296344064]),(⟨3,0,3⟩,[0,65536,-1671168,13926400,-34996224,-134742016,1288896512,-4999938048,11859525632,-16514351104,13706625024,-8404566016]),(⟨3,0,4⟩,[0,0,-131072,3145728,-26738688,84934656,26476544,-657457152,765984768,1123024896,-1856110592]),(⟨3,1,0⟩,[12288,-643072,12582912,-125747200,730345472,-2620002304,5595037696,-3043098624,-27944841216,124322385920,-294716014592,454192840704,-428535181312,187164708864]),(⟨3,1,1⟩,[0,-32768,1081344,-13533184,87588864,-367067136,1264123904,-3559981056,5919014912,-444497920,-23120674816,56226709504,-48340762624]),(⟨3,1,2⟩,[8192,-270336,3579904,-25993216,122175488,-412893184,1035091968,-1718239232,397910016,7231004672,-17862025216,13914005504]),(⟨3,1,3⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨3,2,0⟩,[-53248,1867776,-25378816,171294720,-588009472,666370048,2681733120,-14730625024,34719043584,-43648450560,21387362304,18339577856,-31993851904]),(⟨3,2,1⟩,[0,65536,-1703936,16973824,-80216064,165281792,57933824,-1133117440,2505572352,-629866496,-5786697728,6496387072]),(⟨3,2,2⟩,[-24576,589824,-5677056,30539776,-118079488,373555200,-774324224,305004544,2706907136,-6376194048,4797227008]),(⟨3,2,3⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨3,2,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,3,0⟩,[0,65536,-1638400,10878976,10223616,-434765824,2519859200,-8866758656,21213478912,-32398835712,33199947776,-23305519104]),(⟨3,3,1⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨3,3,2⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨3,4,0⟩,[-40960,1114112,-11853824,63045632,-176570368,214695936,251019264,-1603403776,2339168256,435355648,-2586271744]),(⟨3,4,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,5,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨4,0,0⟩,[-28672,634880,-3424256,-22454272,363712512,-1929981952,5255987200,-5480693760,-16992817152,97935314944,-251390050304,405891538944,-407751593984,195598692352]),(⟨4,0,1⟩,[0,-32768,1081344,-13533184,87588864,-367067136,1264123904,-3559981056,5919014912,-444497920,-23120674816,56226709504,-48340762624]),(⟨4,0,2⟩,[40960,-1187840,13377536,-73998336,208224256,-266223616,53559296,272809984,-887218176,3026477056,-7013228544,6680633344]),(⟨4,0,3⟩,[-40960,1114112,-11853824,63045632,-176570368,214695936,251019264,-1603403776,2339168256,435355648,-2586271744]),(⟨4,0,5⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,1,0⟩,[0,-32768,1081344,-13533184,87588864,-367067136,1264123904,-3559981056,5919014912,-444497920,-23120674816,56226709504,-48340762624]),(⟨4,1,2⟩,[0,0,-131072,3145728,-26738688,84934656,26476544,-657457152,765984768,1123024896,-1856110592]),(⟨4,2,0⟩,[40960,-1187840,13377536,-73998336,208224256,-266223616,53559296,272809984,-887218176,3026477056,-7013228544,6680633344]),(⟨4,2,1⟩,[0,0,-131072,3145728,-26738688,84934656,26476544,-657457152,765984768,1123024896,-1856110592]),(⟨4,2,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,3,0⟩,[-40960,1114112,-11853824,63045632,-176570368,214695936,251019264,-1603403776,2339168256,435355648,-2586271744]),(⟨4,3,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,5,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,0,0⟩,[-36864,1294336,-17383424,114655232,-383356928,451706880,1500512256,-9304014848,25829199872,-43889082368,47843590144,-26089062400,-5721698304]),(⟨5,0,2⟩,[-24576,589824,-5677056,30539776,-118079488,373555200,-774324224,305004544,2706907136,-6376194048,4797227008]),(⟨5,0,3⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨5,0,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,2,0⟩,[-24576,589824,-5677056,30539776,-118079488,373555200,-774324224,305004544,2706907136,-6376194048,4797227008]),(⟨5,2,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,3,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨5,4,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,0,0⟩,[-8192,335872,-5251072,39919616,-157171712,278151168,253804544,-3281698816,11461615616,-23745355776,31568650240,-22318571520]),(⟨6,0,2⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨6,2,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856])]


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

noncomputable def partial0 : Poly := [(⟨0,0,0⟩,[-32768,1220608,-20082688,193490944,-1215397888,5181308928,-14605529088,21334806528,25737117696,-263941627904,904014409728,-2055874867200,3409282564096,-4127506219008,3459093622784,-1761857294336,405066039296,-30250680320]),(⟨0,0,1⟩,[-24576,1073152,-19951616,211492864,-1434574848,6544007168,-19943419904,34895863808,7168630784,-276079206400,1046008147968,-2472435752960,4155230871552,-4981022105600,3982791880704,-1771579514880,236915015680]),(⟨0,0,2⟩,[69632,-2240512,29929472,-214470656,862793728,-1546948608,-2710941696,26498011136,-86697316352,161988947968,-133398147072,-183822643200,801190039552,-1316544344064,1160168550400,-432914829312]),(⟨0,0,3⟩,[61440,-2416640,38801408,-337281024,1754935296,-5511667712,8368803840,10777788416,-104954802176,340183375872,-705308119040,1005841973248,-942322216960,463793545216,-26822971392]),(⟨0,0,4⟩,[-28672,634880,-3424256,-22454272,363712512,-1929981952,5255987200,-5480693760,-16992817152,97935314944,-251390050304,405891538944,-407751593984,195598692352]),(⟨0,0,5⟩,[-36864,1294336,-17383424,114655232,-383356928,451706880,1500512256,-9304014848,25829199872,-43889082368,47843590144,-26089062400,-5721698304]),(⟨0,0,6⟩,[-8192,335872,-5251072,39919616,-157171712,278151168,253804544,-3281698816,11461615616,-23745355776,31568650240,-22318571520]),(⟨0,1,0⟩,[-24576,1073152,-19951616,211492864,-1434574848,6544007168,-19943419904,34895863808,7168630784,-276079206400,1046008147968,-2472435752960,4155230871552,-4981022105600,3982791880704,-1771579514880,236915015680]),(⟨0,1,1⟩,[-8192,491520,-11157504,134848512,-1002463232,4950638592,-16803856384,37815836672,-39231741952,-91865874432,584625012736,-1634843140096,2975572254720,-3612865609728,2664584380416,-898976899072]),(⟨0,1,2⟩,[28672,-1118208,17674240,-149520384,742076416,-2100285440,1861529600,11686215680,-64109129728,172964794368,-285284724736,253477126144,9078706176,-289433088000,238494355456]),(⟨0,1,3⟩,[12288,-643072,12582912,-125747200,730345472,-2620002304,5595037696,-3043098624,-27944841216,124322385920,-294716014592,454192840704,-428535181312,187164708864]),(⟨0,1,4⟩,[0,-32768,1081344,-13533184,87588864,-367067136,1264123904,-3559981056,5919014912,-444497920,-23120674816,56226709504,-48340762624]),(⟨0,2,0⟩,[69632,-2240512,29929472,-214470656,862793728,-1546948608,-2710941696,26498011136,-86697316352,161988947968,-133398147072,-183822643200,801190039552,-1316544344064,1160168550400,-432914829312]),(⟨0,2,1⟩,[28672,-1118208,17674240,-149520384,742076416,-2100285440,1861529600,11686215680,-64109129728,172964794368,-285284724736,253477126144,9078706176,-289433088000,238494355456]),(⟨0,2,2⟩,[-114688,3391488,-39895040,235470848,-682754048,317603840,4913004544,-20232929280,39767392256,-34970648576,-12674252800,59777548288,-39214809088,-13976223744]),(⟨0,2,3⟩,[-20480,860160,-12451840,80519168,-203198464,-347193344,4231299072,-15278653440,30631170048,-30787461120,2180481024,31135965184,-33442476032]),(⟨0,2,4⟩,[40960,-1187840,13377536,-73998336,208224256,-266223616,53559296,272809984,-887218176,3026477056,-7013228544,6680633344]),(⟨0,2,5⟩,[-24576,589824,-5677056,30539776,-118079488,373555200,-774324224,305004544,2706907136,-6376194048,4797227008]),(⟨0,2,6⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨0,3,0⟩,[61440,-2416640,38801408,-337281024,1754935296,-5511667712,8368803840,10777788416,-104954802176,340183375872,-705308119040,1005841973248,-942322216960,463793545216,-26822971392]),(⟨0,3,1⟩,[12288,-643072,12582912,-125747200,730345472,-2620002304,5595037696,-3043098624,-27944841216,124322385920,-294716014592,454192840704,-428535181312,187164708864]),(⟨0,3,2⟩,[-20480,860160,-12451840,80519168,-203198464,-347193344,4231299072,-15278653440,30631170048,-30787461120,2180481024,31135965184,-33442476032]),(⟨0,3,3⟩,[0,65536,-1638400,10878976,10223616,-434765824,2519859200,-8866758656,21213478912,-32398835712,33199947776,-23305519104]),(⟨0,3,4⟩,[-40960,1114112,-11853824,63045632,-176570368,214695936,251019264,-1603403776,2339168256,435355648,-2586271744]),(⟨0,3,5⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨0,4,0⟩,[-28672,634880,-3424256,-22454272,363712512,-1929981952,5255987200,-5480693760,-16992817152,97935314944,-251390050304,405891538944,-407751593984,195598692352]),(⟨0,4,1⟩,[0,-32768,1081344,-13533184,87588864,-367067136,1264123904,-3559981056,5919014912,-444497920,-23120674816,56226709504,-48340762624]),(⟨0,4,2⟩,[40960,-1187840,13377536,-73998336,208224256,-266223616,53559296,272809984,-887218176,3026477056,-7013228544,6680633344]),(⟨0,4,3⟩,[-40960,1114112,-11853824,63045632,-176570368,214695936,251019264,-1603403776,2339168256,435355648,-2586271744]),(⟨0,4,5⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨0,5,0⟩,[-36864,1294336,-17383424,114655232,-383356928,451706880,1500512256,-9304014848,25829199872,-43889082368,47843590144,-26089062400,-5721698304]),(⟨0,5,2⟩,[-24576,589824,-5677056,30539776,-118079488,373555200,-774324224,305004544,2706907136,-6376194048,4797227008]),(⟨0,5,3⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨0,5,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨0,6,0⟩,[-8192,335872,-5251072,39919616,-157171712,278151168,253804544,-3281698816,11461615616,-23745355776,31568650240,-22318571520]),(⟨0,6,2⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨1,0,0⟩,[-24576,1073152,-19951616,211492864,-1434574848,6544007168,-19943419904,34895863808,7168630784,-276079206400,1046008147968,-2472435752960,4155230871552,-4981022105600,3982791880704,-1771579514880,236915015680]),(⟨1,0,1⟩,[-8192,491520,-11157504,134848512,-1002463232,4950638592,-16803856384,37815836672,-39231741952,-91865874432,584625012736,-1634843140096,2975572254720,-3612865609728,2664584380416,-898976899072]),(⟨1,0,2⟩,[28672,-1118208,17674240,-149520384,742076416,-2100285440,1861529600,11686215680,-64109129728,172964794368,-285284724736,253477126144,9078706176,-289433088000,238494355456]),(⟨1,0,3⟩,[12288,-643072,12582912,-125747200,730345472,-2620002304,5595037696,-3043098624,-27944841216,124322385920,-294716014592,454192840704,-428535181312,187164708864]),(⟨1,0,4⟩,[0,-32768,1081344,-13533184,87588864,-367067136,1264123904,-3559981056,5919014912,-444497920,-23120674816,56226709504,-48340762624]),(⟨1,1,0⟩,[-8192,491520,-11157504,134848512,-1002463232,4950638592,-16803856384,37815836672,-39231741952,-91865874432,584625012736,-1634843140096,2975572254720,-3612865609728,2664584380416,-898976899072]),(⟨1,1,1⟩,[0,49152,-1916928,29196288,-239370240,1272201216,-5246533632,18725535744,-53694627840,100535451648,-58796064768,-258191818752,837040963584,-1129318858752,626805817344]),(⟨1,1,2⟩,[0,-81920,2260992,-25591808,163545088,-715046912,2315845632,-4737662976,2257518592,15706963968,-45837680640,47691431936,19338461184,-59245412352]),(⟨1,1,3⟩,[0,-32768,1081344,-13533184,87588864,-367067136,1264123904,-3559981056,5919014912,-444497920,-23120674816,56226709504,-48340762624]),(⟨1,2,0⟩,[28672,-1118208,17674240,-149520384,742076416,-2100285440,1861529600,11686215680,-64109129728,172964794368,-285284724736,253477126144,9078706176,-289433088000,238494355456]),(⟨1,2,1⟩,[0,-81920,2260992,-25591808,163545088,-715046912,2315845632,-4737662976,2257518592,15706963968,-45837680640,47691431936,19338461184,-59245412352]),(⟨1,2,2⟩,[-16384,573440,-7995392,56639488,-204652544,214663168,1181220864,-5426610176,8889843712,240631808,-26456227840,44428640256,-26272153600]),(⟨1,2,3⟩,[8192,-270336,3579904,-25993216,122175488,-412893184,1035091968,-1718239232,397910016,7231004672,-17862025216,13914005504]),(⟨1,2,4⟩,[0,0,-131072,3145728,-26738688,84934656,26476544,-657457152,765984768,1123024896,-1856110592]),(⟨1,3,0⟩,[12288,-643072,12582912,-125747200,730345472,-2620002304,5595037696,-3043098624,-27944841216,124322385920,-294716014592,454192840704,-428535181312,187164708864]),(⟨1,3,1⟩,[0,-32768,1081344,-13533184,87588864,-367067136,1264123904,-3559981056,5919014912,-444497920,-23120674816,56226709504,-48340762624]),(⟨1,3,2⟩,[8192,-270336,3579904,-25993216,122175488,-412893184,1035091968,-1718239232,397910016,7231004672,-17862025216,13914005504]),(⟨1,3,3⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨1,4,0⟩,[0,-32768,1081344,-13533184,87588864,-367067136,1264123904,-3559981056,5919014912,-444497920,-23120674816,56226709504,-48340762624]),(⟨1,4,2⟩,[0,0,-131072,3145728,-26738688,84934656,26476544,-657457152,765984768,1123024896,-1856110592]),(⟨2,0,0⟩,[69632,-2240512,29929472,-214470656,862793728,-1546948608,-2710941696,26498011136,-86697316352,161988947968,-133398147072,-183822643200,801190039552,-1316544344064,1160168550400,-432914829312]),(⟨2,0,1⟩,[28672,-1118208,17674240,-149520384,742076416,-2100285440,1861529600,11686215680,-64109129728,172964794368,-285284724736,253477126144,9078706176,-289433088000,238494355456]),(⟨2,0,2⟩,[-114688,3391488,-39895040,235470848,-682754048,317603840,4913004544,-20232929280,39767392256,-34970648576,-12674252800,59777548288,-39214809088,-13976223744]),(⟨2,0,3⟩,[-20480,860160,-12451840,80519168,-203198464,-347193344,4231299072,-15278653440,30631170048,-30787461120,2180481024,31135965184,-33442476032]),(⟨2,0,4⟩,[40960,-1187840,13377536,-73998336,208224256,-266223616,53559296,272809984,-887218176,3026477056,-7013228544,6680633344]),(⟨2,0,5⟩,[-24576,589824,-5677056,30539776,-118079488,373555200,-774324224,305004544,2706907136,-6376194048,4797227008]),(⟨2,0,6⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨2,1,0⟩,[28672,-1118208,17674240,-149520384,742076416,-2100285440,1861529600,11686215680,-64109129728,172964794368,-285284724736,253477126144,9078706176,-289433088000,238494355456]),(⟨2,1,1⟩,[0,-81920,2260992,-25591808,163545088,-715046912,2315845632,-4737662976,2257518592,15706963968,-45837680640,47691431936,19338461184,-59245412352]),(⟨2,1,2⟩,[-16384,573440,-7995392,56639488,-204652544,214663168,1181220864,-5426610176,8889843712,240631808,-26456227840,44428640256,-26272153600]),(⟨2,1,3⟩,[8192,-270336,3579904,-25993216,122175488,-412893184,1035091968,-1718239232,397910016,7231004672,-17862025216,13914005504]),(⟨2,1,4⟩,[0,0,-131072,3145728,-26738688,84934656,26476544,-657457152,765984768,1123024896,-1856110592]),(⟨2,2,0⟩,[-114688,3391488,-39895040,235470848,-682754048,317603840,4913004544,-20232929280,39767392256,-34970648576,-12674252800,59777548288,-39214809088,-13976223744]),(⟨2,2,1⟩,[-16384,573440,-7995392,56639488,-204652544,214663168,1181220864,-5426610176,8889843712,240631808,-26456227840,44428640256,-26272153600]),(⟨2,2,2⟩,[98304,-2555904,24281088,-93093888,17498112,935854080,-2770796544,2573795328,3661332480,-14503182336,15186296832,-2210955264]),(⟨2,2,3⟩,[-65536,1703936,-17399808,90439680,-267911168,503316480,-549781504,-640942080,4280090624,-7063863296,4067065856]),(⟨2,2,5⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,3,0⟩,[-20480,860160,-12451840,80519168,-203198464,-347193344,4231299072,-15278653440,30631170048,-30787461120,2180481024,31135965184,-33442476032]),(⟨2,3,1⟩,[8192,-270336,3579904,-25993216,122175488,-412893184,1035091968,-1718239232,397910016,7231004672,-17862025216,13914005504]),(⟨2,3,2⟩,[-65536,1703936,-17399808,90439680,-267911168,503316480,-549781504,-640942080,4280090624,-7063863296,4067065856]),(⟨2,3,3⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨2,3,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,4,0⟩,[40960,-1187840,13377536,-73998336,208224256,-266223616,53559296,272809984,-887218176,3026477056,-7013228544,6680633344]),(⟨2,4,1⟩,[0,0,-131072,3145728,-26738688,84934656,26476544,-657457152,765984768,1123024896,-1856110592]),(⟨2,4,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨2,5,0⟩,[-24576,589824,-5677056,30539776,-118079488,373555200,-774324224,305004544,2706907136,-6376194048,4797227008]),(⟨2,5,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨2,6,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨3,0,0⟩,[61440,-2416640,38801408,-337281024,1754935296,-5511667712,8368803840,10777788416,-104954802176,340183375872,-705308119040,1005841973248,-942322216960,463793545216,-26822971392]),(⟨3,0,1⟩,[12288,-643072,12582912,-125747200,730345472,-2620002304,5595037696,-3043098624,-27944841216,124322385920,-294716014592,454192840704,-428535181312,187164708864]),(⟨3,0,2⟩,[-20480,860160,-12451840,80519168,-203198464,-347193344,4231299072,-15278653440,30631170048,-30787461120,2180481024,31135965184,-33442476032]),(⟨3,0,3⟩,[0,65536,-1638400,10878976,10223616,-434765824,2519859200,-8866758656,21213478912,-32398835712,33199947776,-23305519104]),(⟨3,0,4⟩,[-40960,1114112,-11853824,63045632,-176570368,214695936,251019264,-1603403776,2339168256,435355648,-2586271744]),(⟨3,0,5⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨3,1,0⟩,[12288,-643072,12582912,-125747200,730345472,-2620002304,5595037696,-3043098624,-27944841216,124322385920,-294716014592,454192840704,-428535181312,187164708864]),(⟨3,1,1⟩,[0,-32768,1081344,-13533184,87588864,-367067136,1264123904,-3559981056,5919014912,-444497920,-23120674816,56226709504,-48340762624]),(⟨3,1,2⟩,[8192,-270336,3579904,-25993216,122175488,-412893184,1035091968,-1718239232,397910016,7231004672,-17862025216,13914005504]),(⟨3,1,3⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨3,2,0⟩,[-20480,860160,-12451840,80519168,-203198464,-347193344,4231299072,-15278653440,30631170048,-30787461120,2180481024,31135965184,-33442476032]),(⟨3,2,1⟩,[8192,-270336,3579904,-25993216,122175488,-412893184,1035091968,-1718239232,397910016,7231004672,-17862025216,13914005504]),(⟨3,2,2⟩,[-65536,1703936,-17399808,90439680,-267911168,503316480,-549781504,-640942080,4280090624,-7063863296,4067065856]),(⟨3,2,3⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨3,2,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,3,0⟩,[0,65536,-1638400,10878976,10223616,-434765824,2519859200,-8866758656,21213478912,-32398835712,33199947776,-23305519104]),(⟨3,3,1⟩,[0,0,-262144,6291456,-53477376,169869312,52953088,-1314914304,1531969536,2246049792,-3712221184]),(⟨3,3,2⟩,[-32768,1081344,-13238272,77725696,-236388352,374276096,-181534720,-1059454976,3711139840,-3747315712]),(⟨3,4,0⟩,[-40960,1114112,-11853824,63045632,-176570368,214695936,251019264,-1603403776,2339168256,435355648,-2586271744]),(⟨3,4,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨3,5,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨4,0,0⟩,[-28672,634880,-3424256,-22454272,363712512,-1929981952,5255987200,-5480693760,-16992817152,97935314944,-251390050304,405891538944,-407751593984,195598692352]),(⟨4,0,1⟩,[0,-32768,1081344,-13533184,87588864,-367067136,1264123904,-3559981056,5919014912,-444497920,-23120674816,56226709504,-48340762624]),(⟨4,0,2⟩,[40960,-1187840,13377536,-73998336,208224256,-266223616,53559296,272809984,-887218176,3026477056,-7013228544,6680633344]),(⟨4,0,3⟩,[-40960,1114112,-11853824,63045632,-176570368,214695936,251019264,-1603403776,2339168256,435355648,-2586271744]),(⟨4,0,5⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,1,0⟩,[0,-32768,1081344,-13533184,87588864,-367067136,1264123904,-3559981056,5919014912,-444497920,-23120674816,56226709504,-48340762624]),(⟨4,1,2⟩,[0,0,-131072,3145728,-26738688,84934656,26476544,-657457152,765984768,1123024896,-1856110592]),(⟨4,2,0⟩,[40960,-1187840,13377536,-73998336,208224256,-266223616,53559296,272809984,-887218176,3026477056,-7013228544,6680633344]),(⟨4,2,1⟩,[0,0,-131072,3145728,-26738688,84934656,26476544,-657457152,765984768,1123024896,-1856110592]),(⟨4,2,3⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,3,0⟩,[-40960,1114112,-11853824,63045632,-176570368,214695936,251019264,-1603403776,2339168256,435355648,-2586271744]),(⟨4,3,2⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨4,5,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,0,0⟩,[-36864,1294336,-17383424,114655232,-383356928,451706880,1500512256,-9304014848,25829199872,-43889082368,47843590144,-26089062400,-5721698304]),(⟨5,0,2⟩,[-24576,589824,-5677056,30539776,-118079488,373555200,-774324224,305004544,2706907136,-6376194048,4797227008]),(⟨5,0,3⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨5,0,4⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨5,2,0⟩,[-24576,589824,-5677056,30539776,-118079488,373555200,-774324224,305004544,2706907136,-6376194048,4797227008]),(⟨5,2,2⟩,[65536,-1572864,13369344,-42467328,-13238272,328728576,-382992384,-561512448,928055296]),(⟨5,3,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨5,4,0⟩,[32768,-786432,6684672,-21233664,-6619136,164364288,-191496192,-280756224,464027648]),(⟨6,0,0⟩,[-8192,335872,-5251072,39919616,-157171712,278151168,253804544,-3281698816,11461615616,-23745355776,31568650240,-22318571520]),(⟨6,0,2⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856]),(⟨6,2,0⟩,[-16384,540672,-6619136,38862848,-118194176,187138048,-90767360,-529727488,1855569920,-1873657856])]


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
    (Poly.add (Poly.scale (K.ofRat r673) (Poly.mul Data.S6_trivial.weight partial0))
      (Poly.scale (K.ofRat (-1)) cachedProduct)).isZero := by
  decide +kernel

theorem weighted_sound (u v t : ℝ) :
    (Data.S6_trivial.weightedProduct 6 7).eval u v t=cachedProduct.eval u v t := by
  have hcd : (r672*r672 : ℚ)=r673 := by decide +kernel
  exact Block.sos_scaled_product Data.S6_trivial 6 7 r672 r672 sourceLeft sourceRight
    partial0 cachedProduct
    (fun u v t => Poly.eval_eq_of_check _ _ left_checked u v t)
    (fun u v t => Poly.eval_eq_of_check _ _ right_checked u v t)
    partial_sound0 (by simpa only [hcd] using weighted_checked) u v t

theorem symmetry_checked :
    (Poly.add (Poly.scale (K.ofRat (if 6=7 then 1 else 2)) (Poly.symmetrize cachedProduct))
      (Poly.scale (K.ofRat (-1)) (expandColumn coefficients))).isZero := by
  decide +kernel

theorem sound (u v t : ℝ) :
    (Data.S6_trivial.upperColumn 6 7).eval u v t =
      (expandColumn coefficients).eval u v t :=
  Block.sos_cached_sound_of_eq _ rfl _ _ _ _ weighted_sound symmetry_checked u v t

end Coulomb8.Columns.C115

#print axioms Coulomb8.Columns.C115.sound
