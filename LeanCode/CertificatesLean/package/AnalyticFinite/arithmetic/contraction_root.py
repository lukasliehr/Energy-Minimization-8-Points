"""Complete one-composition contraction-defect root-model check."""
from fractions import Fraction
from flint import fmpz_mat

def check(tm,center,halfwidth,coefficient_integers,invariant_upper):
    from scalar_cauchy import transform
    from exact_iv import D,SCALE
    TM,iv,ORDER=tm.TM,tm.iv,tm.ORDER
    q_min=1+(Fraction(center)-Fraction(halfwidth))/2
    if q_min<Fraction(1,2):raise ArithmeticError('Exponent below contraction domain')
    if len(coefficient_integers)!=ORDER+1 or any(type(x)is not int for x in coefficient_integers):
        raise ValueError('Malformed root polynomial witness')
    V=TM([D.raw(x)for x in coefficient_integers])
    S=TM([iv.mpf(center),iv.mpf(halfwidth)]);Q=1+S/2
    r=iv.sqrt(2);alpha,beta=1+r/2,1-r/2;c=iv.log(alpha)
    C=Fraction(invariant_upper)
    if C<=0 or C>Fraction(c.lo,SCALE):raise ArithmeticError('Unproved contraction interval endpoint')
    den,T,_=transform(ORDER)
    controls=T*fmpz_mat(ORDER+1,1,coefficient_integers)
    vlo=Fraction(min(int(x)for x in controls.entries()),den*SCALE)
    vhi=Fraction(max(int(x)for x in controls.entries()),den*SCALE)
    if not 0<=vlo<=vhi<=C:raise ArithmeticError('Root polynomial leaves contraction interval')
    contraction=(Fraction(1,10)if q_min<1 else
                 Fraction(1,19)*Fraction(5,12)**(q_min.numerator//q_min.denominator-1))
    # Complete affine scalar quotient residual, the same universal lemma as before.
    coefficients=[V.c[0]/Q.c[0]]
    for k in range(1,ORDER+1):
        coefficients.append((V.c[k]-Q.c[1]*coefficients[k-1])/Q.c[0])
    P=TM(coefficients);residual=V-Q*P
    quotient=TM(coefficients,residual.bound()/iv.mpf(str(q_min)))
    U=quotient.exp()
    tail_two=(-Q*iv.log(2)).exp()
    image=c-(1+tail_two-beta*(-Q*(r+U).log()).exp()).log()
    defect=V-image
    coefficient_bound=Fraction(sum(max(abs(x.lo),abs(x.hi))for x in defect.c),SCALE)
    remainder_bound=Fraction(defect.e.hi,SCALE)
    defect_bound=coefficient_bound+remainder_bound
    height_lipschitz=Fraction(5,17)/q_min
    correction=height_lipschitz*defect_bound/(1-contraction)
    A=(2*U-2+r)/(2*U+2+r)
    composition_error=A.e
    polynomial_enclosure=TM(A.c).interval()
    A.e=(A.e+iv.mpf(str(correction))).b
    return S,A,dict(root_validation='global_contraction_polynomial_defect',
        analytic_root_theorem='lem:contraction-polynomial-defect',
        root_q_lower=str(q_min),root_contraction_bound=str(contraction),
        root_height_lipschitz_bound=str(height_lipschitz),
        root_invariant_upper=str(C),root_proposal_enclosure=[str(vlo),str(vhi)],
        root_defect_coefficient_bound=str(coefficient_bound),
        root_defect_remainder_bound=str(remainder_bound),
        root_fixed_point_defect_upper=str(defect_bound),root_contraction_error=str(correction),
        root_quotient_evaluation='direct_scalar_residual_over_q_min',
        root_scalar_quotient_model_calls=1,root_contraction_map_evaluations=1,
        root_proposal_polynomial_degree=ORDER,
        root_composition_error=str(composition_error),root_model_error=str(A.e),
        root_polynomial_enclosure=str(polynomial_enclosure),a_enclosure=str(A.interval()),
        numerical_root_residual_predicates=1,root_stationarity_residual_evaluations=0,
        numerical_root_existence_predicates=0,numerical_root_derivative_predicates=0,
        numerical_root_tube_predicates=0)



def candidate_root(center, halfwidth):
    import taylor_models as tm
    from AnalyticFinite.root_proposals import root_proposal, ROOT_INVARIANT_UPPER
    return check(tm, center, halfwidth,
                 root_proposal(center, halfwidth, tm.ORDER), ROOT_INVARIANT_UPPER)
