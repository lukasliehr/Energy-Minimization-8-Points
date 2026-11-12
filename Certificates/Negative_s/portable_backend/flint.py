"""GMP-backed exact fmpz_mat API subset. This is NOT python-flint.
Only arbitrary-precision integer construction, addition, multiplication and
indexing are provided, for replaying the supplied exact-integer checker.
"""
import ctypes as ct
from pathlib import Path
lib=ct.CDLL(str(Path(__file__).with_name('gmp_matrix.so')))
lib.gm_new.argtypes=[ct.c_size_t,ct.c_size_t,ct.c_char_p,ct.c_size_t];lib.gm_new.restype=ct.c_void_p
lib.gm_delete.argtypes=[ct.c_void_p]
lib.gm_mul.argtypes=[ct.c_void_p,ct.c_void_p];lib.gm_mul.restype=ct.c_void_p
lib.gm_iadd.argtypes=[ct.c_void_p,ct.c_void_p];lib.gm_iadd.restype=ct.c_int
lib.gm_width.argtypes=[ct.c_void_p];lib.gm_width.restype=ct.c_size_t
lib.gm_export.argtypes=[ct.c_void_p,ct.c_char_p,ct.c_size_t];lib.gm_export.restype=ct.c_int
class fmpz_mat:
 def __init__(self,rows,cols=None,entries=None):
  if cols is None:
   rows=list(rows);self.r=len(rows);self.c=len(rows[0]) if rows else 0
   if any(len(row)!=self.c for row in rows):raise ValueError('ragged matrix')
   entries=[int(x) for row in rows for x in row]
  else:self.r,self.c=int(rows),int(cols)
  if self.r<0 or self.c<0:raise ValueError('negative shape')
  if entries is None:self._p=lib.gm_new(self.r,self.c,None,1)
  else:
   entries=list(map(int,entries))
   if len(entries)!=self.r*self.c:raise ValueError('wrong entry count')
   width=max([1]+[(abs(x).bit_length()+7)//8 for x in entries]);buf=b''.join(bytes([x<0])+abs(x).to_bytes(width,'big') for x in entries)
   self._p=lib.gm_new(self.r,self.c,buf,width)
  if not self._p:raise MemoryError('GMP matrix allocation failed')
  self._values=None
 @classmethod
 def _take(cls,p,r,c):
  if not p:raise ArithmeticError('GMP matrix operation failed')
  v=object.__new__(cls);v.r,v.c,v._p,v._values=r,c,p,None;return v
 def __del__(self):
  p=getattr(self,'_p',None)
  if p:lib.gm_delete(p);self._p=None
 def __mul__(self,b):
  if self.c!=b.r:raise ValueError('product dimension mismatch')
  return self._take(lib.gm_mul(self._p,b._p),self.r,b.c)
 def __iadd__(self,b):
  if not lib.gm_iadd(self._p,b._p):raise ValueError('addition dimension mismatch')
  self._values=None;return self
 def __add__(self,b):
  c=fmpz_mat(self.r,self.c,self.tolist_flat());c+=b;return c
 def tolist_flat(self):
  if self._values is None:
   width=lib.gm_width(self._p);buf=ct.create_string_buffer(self.r*self.c*(width+1))
   if not lib.gm_export(self._p,buf,width):raise ArithmeticError('GMP matrix export failed')
   data=buf.raw;self._values=[(-1 if data[i] else 1)*int.from_bytes(data[i+1:i+1+width],'big') for i in range(0,len(data),width+1)]
  return self._values
 def __getitem__(self,ij):
  i,j=ij
  if not 0<=i<self.r or not 0<=j<self.c:raise IndexError('matrix index')
  return self.tolist_flat()[i*self.c+j]
