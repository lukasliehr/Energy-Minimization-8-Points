import ThomsonNegative.Structure.Recovery
import ThomsonNegative.Structure.Concrete.HighImage
import ThomsonNegative.Certificate.Bridges.RawBridge
import ThomsonNegative.Certificate.Bridges.ImageCompatibility

noncomputable section
namespace ThomsonNegative.Structure.Concrete
open ThomsonNegative.Certificate.Bridges

def system (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) : HybridCoefficientSystem where
  family := sourcePolynomialFamily a
  coefficientMap := ThomsonNegative.Certificate.Bridges.coefficientMap a
  coefficient_spec := coefficientMap_physical a
  compatibility := coefficientCompatibility a hb
  compatibility_one := rfl
  compatibility_square := rfl
  high_image := coefficientMap_high_image a
  ell0_image := coefficientMap_ell0_image a ha hb
  ell1_image := coefficientMap_ell1_image a ha hb

@[simp] theorem system_family (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) :
    (system a ha hb).family=sourcePolynomialFamily a := rfl
@[simp] theorem system_coefficientMap (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) :
    (system a ha hb).coefficientMap=ThomsonNegative.Certificate.Bridges.coefficientMap a := rfl
@[simp] theorem system_ell0 (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) :
    (system a ha hb).compatibility.ell0=coefficientEll0 a := rfl
@[simp] theorem system_ell1 (a : ℝ) (ha : (5:ℝ)/16≤a) (hb : a<1/3) :
    (system a ha hb).compatibility.ell1=coefficientEll1 a := rfl

#print axioms system
end ThomsonNegative.Structure.Concrete
