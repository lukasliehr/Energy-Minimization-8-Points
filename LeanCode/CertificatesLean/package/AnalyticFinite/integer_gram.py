"""Exact common-denominator expansion of dyadic Bernstein square factors."""
from math import comb
from flint import fmpz_mat, fmpq_mat, fmpq
from exact_iv import D, PRECISION, iv, ceildiv

def exact_gram(block, degree, factor_bits, metric_bits, delta):
    n=block['order']
    q=int(delta.denominator);p=int(delta.numerator)
    if p<=0 or p&(p-1) or q<=0 or q&(q-1):
        raise ValueError('The floor must be a positive power of two')
    floor_exponent=(p.bit_length()-1)-(q.bit_length()-1)
    mb=max(metric_bits, -min(block['K_diagonal_exponents'],default=0))
    kr=fmpz_mat(n,n)
    for i in range(n):
        kr[i,i]=1<<(mb+block['K_diagonal_exponents'][i])
        for j in range(i): kr[i,j]=block['K_strict_lower'][i][j]<<(mb-metric_bits)
    K=fmpq_mat(n,n,[fmpq(int(kr[i,j]),1<<mb) for i in range(n) for j in range(n)])
    squares=[]
    for packed in block['F']:
        F=fmpz_mat(n,n,[packed[i][j] if j<=i else 0 for i in range(n) for j in range(n)])
        squares.append(F*F.transpose())
    denominator_bits=max(2*factor_bits+degree,2*mb-floor_exponent,0)
    gram_scale=1<<(denominator_bits-2*factor_bits-degree)
    floor=(kr*kr.transpose())*(1<<(denominator_bits-2*mb+floor_exponent))
    coefficients=[]
    shift=PRECISION-denominator_bits
    for k in range(degree+1):
        C=fmpz_mat(floor) if k==0 else fmpz_mat(n,n)
        for i,square in enumerate(squares):
            numerator=comb(degree,i)*sum((-1)**(k-j)*comb(i,j)*comb(degree-i,k-j)
                for j in range(max(0,k-(degree-i)),min(i,k)+1))
            if numerator: C+=square*(numerator*gram_scale)
        output=iv.matrix(n,n)
        if shift>=0:
            output.data=[D.raw(int(x)<<shift) for x in C.entries()]
        else:
            denominator=1<<(-shift)
            output.data=[D.raw(int(x)//denominator,ceildiv(int(x),denominator)) for x in C.entries()]
        coefficients.append(output)
    return K,coefficients
