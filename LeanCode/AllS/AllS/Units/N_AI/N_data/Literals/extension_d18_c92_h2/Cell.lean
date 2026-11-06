import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Block_F0
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Block_F1
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Block_F2
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Block_F3
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Block_F4
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Block_F5
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Block_F6
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Block_F7
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Block_F8
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Block_M0_plus
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Block_M0_sign
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Block_M0_standard
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Block_M1_even
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Block_M1_odd
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Block_Mdet_plus
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Block_Mdet_sign
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Block_Mdet_standard

namespace Blueprint.CAP.Literals.extension_d18_c92_h2
def value : Cell := {
  id := "extension_d18_c92_h2"
  degree := 18
  center := (92 / 1 : Rat)
  halfwidth := (5 / 1 : Rat)
  validationOrder := 22
  bernsteinDegree := 10
  profile := .general
  balance := .riesz
  factorBits := 72
  metricBits := 64
  floorExponent := -5
  momentPivots := [0, 1, 0, 1, 0, 0, 0, 0, 0]
  auxiliaryNodes := [.B, .B, .B, .B, .B]
  rootCoefficients := [61925608946583919979730603924327868958918184007424386462919612609885924669692, 1425659891485209585227888331391662840950884762835892080680558177, -1235225778151572255310477190959106635435337279181438104489635336, 713483819282056845704191273540533615090922802349565072410411299, -309087489397152041039867384798553836460416723130817343564827246, 107118995442814910659719622524334275393802159770820241612953246, -30936236917061962883640079679259591468802167107393816588668863, 7658048237576372667097063465252234064614352409639134247249409, -1658716619971604935418109860243723698591270459843477789721904, 319350767905743152491311290301682420386373739094630816912962, -55334865357021975331642568980271270533693630024900297271503, 8716209761084710172961841775501599735308982693589298172957, -1258508009823414949392436646714241781808684073909569057754, 167728551963327870002393663732286833106237425886937308788, -20756494402460864020593289857334481219132308821309420921, 2397249382541777483944511726244787687496641188934156496, -259544861431134242972598073107246635577234644112138653, 26444961279783708417652685082279899909049522508469228, -2544481099703684065369518085386026332806859485467119, 231904935506463504406959908159184996140806553580423, -20075312653950843812331098758267466877199824894862, 1654706023990042302276312405553551698391857979138, -130149597623726574949802243994473279492710376793]
  jointDepth := 0
  jointExactBlocks := []
  blocks := [block_F0, block_F1, block_F2, block_F3, block_F4, block_F5, block_F6, block_F7, block_F8, block_M0_plus, block_M0_sign, block_M0_standard, block_M1_even, block_M1_odd, block_Mdet_plus, block_Mdet_sign, block_Mdet_standard]
}
theorem value_shape : value.Shape := by
  simp [Cell.Shape, value, block_F0_shape, block_F1_shape, block_F2_shape, block_F3_shape, block_F4_shape, block_F5_shape, block_F6_shape, block_F7_shape, block_F8_shape, block_M0_plus_shape, block_M0_sign_shape, block_M0_standard_shape, block_M1_even_shape, block_M1_odd_shape, block_Mdet_plus_shape, block_Mdet_sign_shape, block_Mdet_standard_shape]
#print axioms value_shape
end Blueprint.CAP.Literals.extension_d18_c92_h2
