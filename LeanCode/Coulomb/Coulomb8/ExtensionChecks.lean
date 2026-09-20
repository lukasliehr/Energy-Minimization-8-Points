import Coulomb8.ExtensionChecks.B00
import Coulomb8.ExtensionChecks.B01
import Coulomb8.ExtensionChecks.B02
import Coulomb8.ExtensionChecks.B03
import Coulomb8.ExtensionChecks.B04
import Coulomb8.ExtensionChecks.B05
import Coulomb8.ExtensionChecks.B06
import Coulomb8.ExtensionChecks.B07
import Coulomb8.ExtensionChecks.B08
import Coulomb8.ExtensionChecks.B09
import Coulomb8.ExtensionChecks.B10
import Coulomb8.ExtensionChecks.B11
import Coulomb8.ExtensionChecks.B12
import Coulomb8.ExtensionChecks.B13
import Coulomb8.ExtensionChecks.B14
import Coulomb8.ExtensionChecks.B15
import Coulomb8.ExtensionChecks.B16
import Coulomb8.ExtensionChecks.B17
import Coulomb8.ExtensionChecks.B18
import Coulomb8.ExtensionChecks.B19
import Coulomb8.ExtensionChecks.B20
import Coulomb8.ExtensionChecks.B21
import Coulomb8.ExtensionChecks.B22
import Coulomb8.ExtensionChecks.B23
import Coulomb8.ExtensionChecks.B24
import Coulomb8.ExtensionChecks.B25
import Coulomb8.ExtensionChecks.B26
import Coulomb8.ExtensionChecks.B27
import Coulomb8.ExtensionChecks.B28
import Coulomb8.ExtensionChecks.B29
import Coulomb8.ExtensionChecks.B30
import Coulomb8.ExtensionChecks.B31
import Coulomb8.ExtensionChecks.B32
import Coulomb8.ExtensionChecks.B33
import Coulomb8.ExtensionChecks.B34
import Coulomb8.ExtensionChecks.B35
import Coulomb8.ExtensionChecks.B36
import Coulomb8.ExtensionChecks.B37
import Coulomb8.ExtensionChecks.B38
import Coulomb8.ExtensionChecks.B39
import Coulomb8.ExtensionChecks.B40
import Coulomb8.ExtensionChecks.B41
import Coulomb8.ExtensionChecks.B42
import Coulomb8.ExtensionChecks.B43
import Coulomb8.ExtensionChecks.B44
import Coulomb8.ExtensionChecks.B45
import Coulomb8.ExtensionChecks.B46
import Coulomb8.ExtensionChecks.B47
import Coulomb8.ExtensionChecks.B48
import Coulomb8.ExtensionChecks.B49
import Coulomb8.ExtensionChecks.B50
import Coulomb8.ExtensionChecks.B51
import Coulomb8.ExtensionChecks.B52
import Coulomb8.ExtensionChecks.B53
import Coulomb8.ExtensionChecks.B54
import Coulomb8.ExtensionChecks.B55
import Coulomb8.ExtensionChecks.B56
import Coulomb8.ExtensionChecks.B57
import Coulomb8.ExtensionChecks.B58
import Coulomb8.ExtensionChecks.B59
import Coulomb8.ExtensionChecks.B60
import Coulomb8.ExtensionChecks.B61
import Coulomb8.ExtensionChecks.B62
import Coulomb8.ExtensionChecks.B63

namespace Coulomb8

theorem all_extension_checks (u v t r s w : Fin 4) : extensionCheck u v t r s w := by
  fin_cases u <;> fin_cases v <;> fin_cases t
  · exact ExtensionChecks.base0 r s w
  · exact ExtensionChecks.base1 r s w
  · exact ExtensionChecks.base2 r s w
  · exact ExtensionChecks.base3 r s w
  · exact ExtensionChecks.base4 r s w
  · exact ExtensionChecks.base5 r s w
  · exact ExtensionChecks.base6 r s w
  · exact ExtensionChecks.base7 r s w
  · exact ExtensionChecks.base8 r s w
  · exact ExtensionChecks.base9 r s w
  · exact ExtensionChecks.base10 r s w
  · exact ExtensionChecks.base11 r s w
  · exact ExtensionChecks.base12 r s w
  · exact ExtensionChecks.base13 r s w
  · exact ExtensionChecks.base14 r s w
  · exact ExtensionChecks.base15 r s w
  · exact ExtensionChecks.base16 r s w
  · exact ExtensionChecks.base17 r s w
  · exact ExtensionChecks.base18 r s w
  · exact ExtensionChecks.base19 r s w
  · exact ExtensionChecks.base20 r s w
  · exact ExtensionChecks.base21 r s w
  · exact ExtensionChecks.base22 r s w
  · exact ExtensionChecks.base23 r s w
  · exact ExtensionChecks.base24 r s w
  · exact ExtensionChecks.base25 r s w
  · exact ExtensionChecks.base26 r s w
  · exact ExtensionChecks.base27 r s w
  · exact ExtensionChecks.base28 r s w
  · exact ExtensionChecks.base29 r s w
  · exact ExtensionChecks.base30 r s w
  · exact ExtensionChecks.base31 r s w
  · exact ExtensionChecks.base32 r s w
  · exact ExtensionChecks.base33 r s w
  · exact ExtensionChecks.base34 r s w
  · exact ExtensionChecks.base35 r s w
  · exact ExtensionChecks.base36 r s w
  · exact ExtensionChecks.base37 r s w
  · exact ExtensionChecks.base38 r s w
  · exact ExtensionChecks.base39 r s w
  · exact ExtensionChecks.base40 r s w
  · exact ExtensionChecks.base41 r s w
  · exact ExtensionChecks.base42 r s w
  · exact ExtensionChecks.base43 r s w
  · exact ExtensionChecks.base44 r s w
  · exact ExtensionChecks.base45 r s w
  · exact ExtensionChecks.base46 r s w
  · exact ExtensionChecks.base47 r s w
  · exact ExtensionChecks.base48 r s w
  · exact ExtensionChecks.base49 r s w
  · exact ExtensionChecks.base50 r s w
  · exact ExtensionChecks.base51 r s w
  · exact ExtensionChecks.base52 r s w
  · exact ExtensionChecks.base53 r s w
  · exact ExtensionChecks.base54 r s w
  · exact ExtensionChecks.base55 r s w
  · exact ExtensionChecks.base56 r s w
  · exact ExtensionChecks.base57 r s w
  · exact ExtensionChecks.base58 r s w
  · exact ExtensionChecks.base59 r s w
  · exact ExtensionChecks.base60 r s w
  · exact ExtensionChecks.base61 r s w
  · exact ExtensionChecks.base62 r s w
  · exact ExtensionChecks.base63 r s w

end Coulomb8

#print axioms Coulomb8.all_extension_checks
