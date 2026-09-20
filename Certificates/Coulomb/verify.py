"""Rigorous reduced Coulomb CAP checker. Default: Python standard library only.
The independent Lean proof is in ../../LeanCode/Coulomb; this run invokes Python only.
"""
from pathlib import Path
from fractions import Fraction as Q
import json,time,hashlib,sys
from dyadic import I,SCALE,BITS,matmul,transpose,dot
from polycheck import P,EXPS,INDEX,block_columns,check_annihilators,check_candidate_geometry,FAST
from scalar_checks import constants,hermite,squared_minorant,uniqueness,LEFT,RIGHT,CODES,require
ROOT=Path(__file__).resolve().parent

def dyadic(n,bits):return I.rat(Q(int(n),1<<bits))
def shape(m,r,c):return len(m)==r and all(len(row)==c for row in m)

def main():
 start=time.time();raw=(ROOT/'certificate.json').read_bytes();w=json.loads(raw)
 require(w['format']=='Coulomb-N8-polynomial-bases-v1','Format')
 require(w['interval_bits']==BITS,'Interval precision')
 require(list(map(Q,w['root_bracket']))==[LEFT,RIGHT],'Root bracket agreement')
 check_candidate_geometry(CODES)
 a,q,nodes=constants();h=hermite(nodes);quotient,bern=squared_minorant(nodes,h)
 print('PASS root and squared minorant',flush=True)
 cols=[];sizes=[]
 require(len({b['name'] for b in w['blocks']})==len(w['blocks']),'Distinct block names')
 for b in w['blocks']:
  if b['kind']=='moment':
   require(isinstance(b['k'],int) and 0<=b['k']<=5,'Moment index')
   n=len(b['basis'][0]);require(n>0 and shape(b['basis'],7-b['k'],n),'Moment basis shape')
  else:
   require(b['kind']=='sos','Block kind');n=len(b['polys']);require(n>0,'Nonempty SOS vector')
  sizes.append(n);cs=block_columns(b)
  require(len(cs)==n*(n+1)//2,'Coordinate count')
  cols+=cs
  print('Rebuilt polynomial block',b['name'],n,flush=True)
 L0,L1=check_annihilators(cols)
 print('PASS exact coefficient annihilator identities',len(cols),'columns',flush=True)
 zero_rows=[i for i in range(102) if not any(col.get(i,P()) for col in cols)]
 require(zero_rows==w['structural_zero_rows'],'Structural zero rows')
 require(all(EXPS[i][0]!=0 or EXPS[i][1]!=0 for i in zero_rows),'Zero-row target')
 rows=[i for i in range(102) if i not in [0,INDEX[(0,0,2)],*zero_rows]];dim=len(rows)
 selected=w['selected_columns']
 require(len(selected)==dim==len(set(selected)) and all(isinstance(j,int) and 0<=j<len(cols) for j in selected),'Correction column selection')
 require(len(w['center_numerators'])==len(cols),'Center length')
 center=[dyadic(n,w['center_scale']) for n in w['center_numerators']]
 require(shape(w['correction_inverse_numerators'],dim,dim),'Correction preconditioner shape')
 C=[[dyadic(n,w['correction_inverse_scale']) for n in row] for row in w['correction_inverse_numerators']]
 A=[[col.get(i,P()).evaluate(a) for col in cols] for i in rows]
 # The zero polynomial evaluates to interval zero through I.__mul__.
 require(all(isinstance(v,I) for row in A for v in row),'Interval coefficients')
 M=[[row[j] for j in selected] for row in A]
 CM=matmul(C,M)
 qnum=max(sum((v-(1 if i==j else 0)).mag() for j,v in enumerate(row)) for i,row in enumerate(CM))
 require(qnum<SCALE//2,'Correction inverse norm < 1/2')
 print('PASS invertibility enclosure for',dim,'x',dim,'system',flush=True)
 energy=sum((n/(2-2*t).sqrt() for n,t in zip([8,4,8,8],nodes)),I(0))
 target=[I(0)]*102;target[0]=h[0]-energy/28
 for j in range(1,13):target[INDEX[(0,0,j)]]=h[j]/3
 residual=[target[i]-dot(row,center) for i,row in zip(rows,A)]
 Cnorm=max(sum(v.mag() for v in row) for row in C)
 rnorm=max(v.mag() for v in residual)
 require(Cnorm<=65536*SCALE,'Preconditioner row norm <= 2^16')
 require(rnorm*(1<<55)<=SCALE,'Residual norm <= 2^-55')
 # q <= 1/2 gives ||z|| <= 2 * 2^16 * 2^-55 = 2^-38.
 cnorm=(Cnorm*rnorm+SCALE-1)//SCALE
 eta=SCALE//(1<<38)
 # Use the same enlarged box as Lean, including the unchanged coordinates.
 corrected=[entry+I(-eta,eta) for entry in center]
 require(len(w['PSD_preconditioner_numerators'])==len(sizes),'PSD preconditioner count')
 offset=0;deltas=[]
 for b,n,rec in zip(w['blocks'],sizes,w['PSD_preconditioner_numerators']):
  require(shape(rec,n,n),'PSD preconditioner shape')
  PP=[[dyadic(v,w['PSD_preconditioner_scale']) for v in row] for row in rec]
  W=[[I(0) for _ in range(n)] for _ in range(n)]
  for i in range(n):
   for j in range(i,n):W[i][j]=W[j][i]=corrected[offset];offset+=1
  V=matmul(matmul(PP,W),transpose(PP))
  d=max(sum((v-(1 if i==j else 0)).mag() for j,v in enumerate(row)) for i,row in enumerate(V))
  require(d<SCALE//2,'Positive definiteness '+b['name'])
  deltas.append(str(d));print('PASS positive corrected block',b['name'],n,flush=True)
 unique=uniqueness(nodes)
 report={'certificate_sha256':hashlib.sha256(raw).hexdigest(),'all_finite_checks_passed':True,
  'execution_kind':'standalone Python check; independent Lean proof supplied in ../../LeanCode/Coulomb','arithmetic':'Python Fraction and integer dyadic intervals' if not FAST else 'FLINT rational polynomials and integer dyadic intervals',
  'interval_bits':BITS,'matrix_sizes':sizes,'matrix_coordinates':len(cols),
  'coefficient_count':102,'structural_zero_rows':zero_rows,'correction_dimension':dim,
  'inverse_error_upper_numerator':str(qnum),'preconditioner_norm_upper_numerator':str(Cnorm),'residual_norm_upper_numerator':str(rnorm),'preconditioned_residual_upper_numerator':str(cnorm),
  'uniform_correction_radius_upper_numerator':str(eta),'PSD_error_upper_numerators':deltas,
  'bound_denominator':str(SCALE),'minorant_Bernstein_lower_numerator':str(min(x.lo for x in bern)),
  'uniqueness':unique,'elapsed_seconds':time.time()-start,'python':sys.version,
  'qualification':'Uses the same exact identity, with uniform correction radius 2^-38 from ||I-CM|| <= 1/2, ||C|| <= 2^16, and ||r|| <= 2^-55; no residual is accepted as zero.'}
 name='verification_fast.json' if FAST else 'verification.json'
 (ROOT/name).write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps(report,indent=2),flush=True)

if __name__=='__main__':main()
