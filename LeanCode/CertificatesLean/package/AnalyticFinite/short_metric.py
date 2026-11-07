"""Bounded dyadic left inverse and its analytic floor-loss bound.

The triangular row recurrence gives |(ZK-I)_ij| <= K_jj*2^(-bits-1).
The proof uses exact integer dot products and nearest rounding only.
"""
from fractions import Fraction
from flint import fmpq,fmpq_mat

def nearest_power_two(n,shift):
    if type(n)is not int or type(shift)is not int or shift<0:
        raise ValueError('Invalid integer dyadic rounding')
    return n if shift==0 else (n+(1<<(shift-1)))>>shift

def short_left_inverse(block,metric_bits,bits=128):
    n=block['order'];exponents=block['K_diagonal_exponents']
    if (type(n)is not int or n<1 or type(metric_bits)is not int or metric_bits<0
            or type(bits)is not int or bits<0 or len(exponents)!=n
            or any(type(e)is not int for e in exponents)
            or bits<max(exponents,default=0)):
        raise ValueError('Short inverse diagonal is not exactly representable')
    lower=block['K_strict_lower']
    if (type(lower)is not list or len(lower)!=n
            or any(type(row)is not list or len(row)!=i or any(type(q)is not int for q in row)
                   for i,row in enumerate(lower))):
        raise ValueError('Malformed exact dyadic metric triangle')
    mb=max(metric_bits,-min(exponents,default=0));K=[[0]*n for _ in range(n)]
    for i in range(n):
        K[i][i]=1<<(mb+exponents[i])
        for j in range(i):K[i][j]=block['K_strict_lower'][i][j]<<(mb-metric_bits)
    Z=[[0]*n for _ in range(n)]
    for i in range(n):
        Z[i][i]=1<<(bits-exponents[i])
        for j in reversed(range(i)):
            total=sum(Z[i][k]*K[k][j]for k in range(j+1,i+1))
            Z[i][j]=nearest_power_two(-total,mb+exponents[j])
    theta=Fraction(n-1)*Fraction(2)**(max(exponents)-bits-1)
    matrix=fmpq_mat(n,n,[fmpq(Z[i][j],1<<bits)for i in range(n)for j in range(n)])
    return matrix,theta,dict(order=n,short_inverse_bits=bits,metric_common_bits=mb,
        exponent_max=max(exponents,default=0),floor_loss_bound=str(theta),
        stored_integer_bits=sum(abs(v).bit_length()for row in Z for v in row),
        maximum_integer_bits=max((abs(v).bit_length()for row in Z for v in row),default=0))
