"""Fixed-precision dyadic intervals, using only Python integers and Fraction."""
from fractions import Fraction
from math import isqrt
BITS=128
SCALE=1 << BITS

def ceildiv(a,b):return -((-a)//b)

class I:
 __slots__=('lo','hi')
 def __init__(self,lo,hi=None):
  self.lo=int(lo);self.hi=int(lo if hi is None else hi)
  if self.lo>self.hi:raise ArithmeticError('Reversed interval')
 @classmethod
 def rat(cls,x):
  x=Fraction(x)
  return cls(x.numerator*SCALE//x.denominator,ceildiv(x.numerator*SCALE,x.denominator))
 @classmethod
 def coerce(cls,x):return x if isinstance(x,I) else cls.rat(x)
 def __add__(self,x):
  x=self.coerce(x);return I(self.lo+x.lo,self.hi+x.hi)
 __radd__=__add__
 def __neg__(self):return I(-self.hi,-self.lo)
 def __sub__(self,x):return self+-self.coerce(x)
 def __rsub__(self,x):return self.coerce(x)+-self
 def __mul__(self,x):
  x=self.coerce(x);p=[self.lo*x.lo,self.lo*x.hi,self.hi*x.lo,self.hi*x.hi]
  return I(min(p)//SCALE,ceildiv(max(p),SCALE))
 __rmul__=__mul__
 def __truediv__(self,x):
  x=self.coerce(x)
  if x.lo<=0<=x.hi:raise ZeroDivisionError('Zero in divisor')
  return self*I(SCALE*SCALE//x.hi,ceildiv(SCALE*SCALE,x.lo))
 def __rtruediv__(self,x):return self.coerce(x)/self
 def __pow__(self,n):
  if n<0:return I.rat(1)/(self**(-n))
  r=I.rat(1);a=self
  while n:
   if n&1:r=r*a
   a=a*a;n//=2
  return r
 def sqrt(self):
  if self.lo<0:raise ArithmeticError('Negative square-root argument')
  l=isqrt(self.lo*SCALE);u=isqrt(self.hi*SCALE)
  if u*u<self.hi*SCALE:u+=1
  return I(l,u)
 def mag(self):return max(abs(self.lo),abs(self.hi))
 def nonzero(self):return self.hi<0 or self.lo>0
 def encode(self):return [str(self.lo),str(self.hi)]

def dot(a,b):return sum((x*y for x,y in zip(a,b)),I(0))
def transpose(a):return list(map(list,zip(*a)))
def matmul(a,b):
 if not a or not b or len(a[0])!=len(b):raise ArithmeticError('Matrix dimensions')
 return [[dot(row,col) for col in zip(*b)] for row in a]
